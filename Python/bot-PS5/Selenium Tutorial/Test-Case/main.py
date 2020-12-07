# -*- coding: utf-8 -*-
"""
Created on Fri Dec  4 00:56:25 2020

from selenium.webdriver.common.action_chains import ActionChains
@author: santi
"""
import unittest
from selenium import webdriver
import page

# Recordar que sólo va a interpretar los que empiecen con "test"
class PythonOrgSearch(unittest.TestCase):
    
    def setUp(self):
        print("setup")
        self.driver = webdriver.Chrome('..\..\chromedriver')
        self.driver.get("http://www.python.org")
        
    '''def test_title(self):
        mainPage = page.MainPage()
        assert mainPage.is_title_matches()'''
        
    def test_search_python(self):
        mainPage = page.MainPage(self.driver)
        assert mainPage.is_title_matches()
        mainPage.search_text_element = "pycon"
        mainPage.click_go_button()
        search_result_page = page.SearchResultPage(self.driver)
        assert search_result_page.is_results_found()
        
    def tearDown(self):
        self.driver.close()
        
if __name__ == "__main__":
    unittest.main()
        

