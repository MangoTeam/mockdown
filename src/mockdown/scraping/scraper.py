import json

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
    'select > *',
]

# language=JavaScript
PAYLOAD = """
    const rootElement = arguments[0];
    const excludedSelectors = arguments[1];
    
    var seenPrefixes = {};
    
    function mangle(el) {
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
        return `[${prefix}@${timesSeen}]`;
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
        /* Is rect1 disjoint from rect2? */
        throw Error("not implemented");
    }
    
    function scrape(el, parent) {
        const children = Array.from(el.children);
        const rect = el.getBoundingClientRect();
        
        if (isExcluded(el)) return [];
        if (!isVisible(rect)) return [];
        if (parent) {
            const parentRect = parent.getBoundingClientRect();
            if (!isContained(rect, parentRect)) {
                console.warn(`${mangle(el)} is not contained in ${mangle(parent)}!`)
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


class Scraper:
    root_selector: str
    driver: webdriver.Chrome

    def __init__(self, root_selector="body"):
        self.root_selector = root_selector

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

    def scrape(self, url: str) -> dict:
        try:
            self.driver.set_window_size(1920, 1080)
            self.driver.get(url)

            el = self.driver.find_element_by_css_selector(self.root_selector)
            data = self.driver.execute_script(PAYLOAD, el, DEFAULT_EXCLUDED_SELECTORS)

            return data
        finally:
            for entry in self.driver.get_log('browser'):
                if entry['source'] == 'console-api':
                    log.info(entry['message'])

