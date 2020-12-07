# -*- coding: utf-8 -*-
"""
Created on Thu Dec  3 23:28:19 2020

@author: santi

Tutorial 2 - Navegar y dar click
"""
from selenium import webdriver 
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
import time

driver = webdriver.Chrome('..\chromedriver')

driver.get('https://techwithtim.net')

try:
    element = WebDriverWait(driver, 10).until(
        EC.presence_of_element_located((By.LINK_TEXT, "Python Programming"))
    )
    element.click()
    element = WebDriverWait(driver, 10).until(
        EC.presence_of_element_located((By.LINK_TEXT, "Beginner Python Tutorials"))
    )
    element.click()
    element = WebDriverWait(driver, 10).until(
        EC.presence_of_element_located((By.ID, "sow-button-19310003"))
    )
    element.click()
    time.sleep(3)
    #Vamos de regreso
    driver.back()
    driver.back()
    driver.back()
    # Para ir hacia adelante:
    driver.forward()
except:
    driver.quit()