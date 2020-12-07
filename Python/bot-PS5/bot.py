# -*- coding: utf-8 -*-
"""
Created on Thu Dec  3 20:37:15 2020

@author: Santiago Arroyo
"""
from selenium import webdriver 
from config import keys

def order(k):
    driver = webdriver.Chrome('.\chromedriver')
    driver.get(k['url'])
    driver.find_element_by_xpath('')
        

if __name__ == '__main__':
    order(keys)
