# -*- coding: utf-8 -*-
"""
Created on Fri Dec  4 00:57:32 2020

@author: santi
"""
from selenium.webdriver.support.ui import WebDriverWait

class BasePageElement(object):
    locator = "q"
    def __set__(self, obj, value):
        driver = obj.driver
        # Función lambda usada!
        WebDriverWait(driver, 100).until(lambda driver: driver.find_element_by_name(self.locator))
        driver.find_element_by_name(self.locator).clear()
        driver.find_element_by_name(self.locator).send_keys(value)
        
    def __get__(self, obj, owner):
        driver = obj.driver
        # Función lambda usada!
        WebDriverWait(driver, 100).until(lambda driver: driver.find_element_by_name(self.locator))
        element = driver.find_element_by_name(self.locator)
        return element.get_attribute("value")
    
search_text_element = 5