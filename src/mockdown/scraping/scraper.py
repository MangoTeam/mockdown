import json

import sympy as sym
from selenium import webdriver
from selenium.common.exceptions import WebDriverException

from mockdown.model import IView, ViewBuilder, ViewLoader
from mockdown.types import NT

from logging import getLogger

log = getLogger(__name__)

# Exclusions taken from Tree.js in auto-mock.
# TODO: Ask John about some inclusions (select?).
DEFAULT_EXCLUDED_SELECTORS = [
    'p',
    'h1',
    'h2',
    'h3',
    'h4',
    'h5',
    'h6',
    'hr',
    'select'
]

# language=JavaScript
PAYLOAD = """
    const rootElement = arguments[0];
    const excludedSelectors = arguments[1];
    
    var seen = {};
    
    function mangle(el) {
        let name = `${el.tagName.toLowerCase()}`;
        
        if (el.id) {
            name += `#${el.id}`;
        }
        if (el.className) { 
            name += `.${String(el.className).replace(/\\s+/g, '.')}`; 
        }
        
        let timesSeen = seen[name] || 0;
        seen[name] = ++timesSeen;
        
        return `[${name}@${timesSeen}]`;
    }
    
    function isVisible(rect) {
        return rect.width > 0 && rect.height > 0; 
    }
    
    function isExcluded(el) {
        return excludedSelectors.some((sel) => el.matches(sel));
    }
    
    function scrape(el, seen) {
        const children = Array.from(el.children);
        const rect = el.getBoundingClientRect();

        if (isExcluded(el)) return [];
        if (!isVisible(rect)) return [];

        // A bunch of duplication, but it's convenient for debugging.
        const data = {
            name: mangle(el),
            children: children.flatMap(c => scrape(c)),
            rect: [
                rect.left + window.scrollX,
                rect.top + window.scrollY,
                rect.right,
                rect.bottom
            ]           
        };
        return data;
    }
    
    return scrape(rootElement);
"""


class Scraper:
    root_selector: str
    driver: webdriver.Chrome

    def __init__(self, root_selector="body"):
        self.root_selector = root_selector

        caps = webdriver.DesiredCapabilities.CHROME
        caps['loggingPrefs'] = {'browser': 'ALL'}

        opts = webdriver.ChromeOptions()
        opts.headless = True

        try:
            self.driver = webdriver.Chrome(chrome_options=opts, desired_capabilities=caps)
            self.driver.set_window_size(1920, 1080)
        except WebDriverException as wde:
            log.error("Hey there. You need to install a driver such as chromedriver or geckodriver.")
            raise wde

    def scrape(self, url: str) -> IView[NT]:
        try:
            self.driver.set_window_size(1920, 1080)
            self.driver.get(url)

            el = self.driver.find_element_by_css_selector(self.root_selector)
            data = self.driver.execute_script(PAYLOAD, el, DEFAULT_EXCLUDED_SELECTORS)

            loader = ViewLoader(number_type=sym.Number)
            tree = loader.load_dict(data)

            log.debug(json.dumps(data, indent=2))
            # log.info(tree)
            return tree;
        finally:
            for entry in self.driver.get_log('browser'):
                log.debug(entry)
