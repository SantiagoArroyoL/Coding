# -*- coding: utf-8 -*-
"""
Created on Sat Dec  5 01:14:01 2020

@author: santi
"""
from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.common.action_chains import ActionChains

keys = {"correo" : "santiago-sonic@hotmail.com", "contra":"Sonic080601" }

driver = webdriver.Chrome('..\chromedriver')
driver.get('https://orteil.dashnet.org/cookieclicker/')
driver.implicitly_wait(5)

carrito = driver.find_element_by_id("btnaddtocart")
direccion = driver.find_element_by_id("cambiarDireccion1")

try:
    element = WebDriverWait(driver, 10).until(
        EC.presence_of_element_located((By.LINK_TEXT, "Proceder al pago"))
    )
except:
    driver.close()
actions = ActionChains(driver)
actions.click(carrito)
cookie_count = driver.find_element_by_id("cookies")
# Una lista por comprensión

for i in range(50000):
    actions.perform()
    count = int(cookie_count.text.split(" ")[0])
    for item in items:
        value = int(item.text)
        if value <= count:
            upgrade_actions = ActionChains(driver)
            upgrade_actions.move_to_element(item)
            upgrade_actions.click()
            upgrade_actions.perform()
