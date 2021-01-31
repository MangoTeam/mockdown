import json
from typing import Tuple

import sympy as sym
from selenium import webdriver
from selenium.common.exceptions import WebDriverException

from logging import getLogger

log = getLogger(__name__)

# Exclusions taken from Tree.js in auto-mock.
# TODO: Ask John about some inclusions (select?).
DEFAULT_EXCLUDED_SELECTORS = [
    'p > *',
    'h1 > *',
    'h2 > *',
    'h3 > *',
    'h4 > *',
    'h5 > *',
    'h6 > *',
    'select > *'
]

# language=JavaScript
PAYLOAD = """
    const rootElement = arguments[0];
    const excludedSelectors = arguments[1];
    
    // This has to be a WeakMap, as in a normal object, DOM node keys will be
    // coerced to strings, which are not unique and will cause collisions.
    var seenElements = new WeakMap();
    var seenPrefixes = {};
    
    function mangle(el) {
        if (seenElements.has(el)) {
            return seenElements.get(el);
        }
    
        let prefix = `${el.tagName.toLowerCase()}`;
        
        if (el.id) {
            prefix += `#${el.id}`;
        }
        if (el.className) { 
            prefix += `.${String(el.className).replace(/\\s+/g, '.')}`; 
        }
        
        // Ensure duplicate prefixes get unique numeric suffixes.
        let timesSeen = seenPrefixes[prefix] || 0;
        seenPrefixes[prefix] = ++timesSeen;
        
        // Store the mangled name for this element and return it.
        const name = `[${prefix}@${timesSeen}]`;
        seenElements.set(el, name);
        return name;
    }
    
    function isVisible(rect) {
        return rect.width > 0 && rect.height > 0; 
    }
    
    function isExcluded(el) {
        return excludedSelectors.some((sel) => el.matches(sel));
    }
    
    function isContained(child, parent) {
        /* Is rect1 contained in rect2? */
        return child.left   >= parent.left 
            && child.top    >= parent.top
            && child.right  <= parent.right
            && child.bottom <= parent.bottom;
    }
    
    function isDisjoint(rect1, rect2) {
        return rect1.left   > rect2.right  // R1 is completely right of R2.
            || rect1.right  < rect2.left   // R1 is completely left of R2.
            || rect1.top    > rect2.bottom // R1 is completely below R2.
            || rect1.bottom < rect2.top    // R1 is completely above R2.
    }
    
    function scrape(el, parent) {
        const children = Array.from(el.children);
        const rect = el.getBoundingClientRect();
        
        if (isExcluded(el)) return [];
        if (!isVisible(rect)) return [];
        if (parent) {
            const parentRect = parent.getBoundingClientRect();
            if (isDisjoint(rect, parentRect)) {
                console.warn(`${mangle(el)} is disjoint from ${mangle(parent)}!`)
                return [];  // todo: too strict?
            }
        }

        // A bunch of duplication, but it's convenient for debugging.
        const data = {
            name: mangle(el),
            children: children.flatMap(c => scrape(c, el)),
            rect: [
                rect.left + window.scrollX,
                rect.top + window.scrollY,
                rect.right,
                rect.bottom
            ]           
        };
        return data;
    }
    
    return scrape(rootElement, undefined);
"""

SANITIZED_KEY_ORDER = ('name', 'rect', 'children')


class Scraper:
    root_selector: str
    driver: webdriver.Chrome

    def __init__(self):
        caps = webdriver.DesiredCapabilities.CHROME
        caps['goog:loggingPrefs'] = {'browser': 'ALL'}

        opts = webdriver.ChromeOptions()
        opts.headless = True

        try:
            self.driver = webdriver.Chrome(chrome_options=opts, desired_capabilities=caps)
            self.driver.set_window_size(1920, 1080)
        except WebDriverException as wde:
            log.error("Hey there. You need to install a driver such as chromedriver or geckodriver.")
            raise wde

    def scrape(self,
               url: str,
               dims: Tuple[int, int],
               root_selector="body") -> dict:
        width, height = dims

        try:
            self.driver.set_window_size(width, height)
            self.driver.get(url)

            el = self.driver.find_element_by_css_selector(root_selector)
            data = self.driver.execute_script(PAYLOAD, el, DEFAULT_EXCLUDED_SELECTORS)
            screenshot = "data:image/png;base64," + self.driver.get_screenshot_as_base64()

            cleaned_data = self.clean_output(data)

            return {
                'meta': {
                    'scrape': {
                        'origin': url,
                        'width': width,
                        'height': height,
                    }
                },
                'examples': [cleaned_data],
                'captures': [screenshot]
            }
        finally:
            for entry in self.driver.get_log('browser'):
                if entry['source'] == 'console-api':
                    log.info(entry['message'])

    def clean_output(self, data, order=SANITIZED_KEY_ORDER):
        """
        Recursively reorders the keys in the output JSON. In particular, puts `children` last.
        While this adds a little computational time, it's invaluable for inspection and debugging.

        Contents remain unchanged.
        """
        # children = [sanitize_output(child) for child in data['children']]
        return {
            k: [self.clean_output(c, order) for c in data[k]] if k == 'children' else data[k]
            for k
            in order
        }

    def cleanup(self):
        self.driver.quit()