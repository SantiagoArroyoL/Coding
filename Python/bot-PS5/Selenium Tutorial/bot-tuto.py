# -*- coding: utf-8 -*-
"""
Created on Thu Dec  3 22:49:18 2020

@author: santi

Tutorial 1 - Escribir cosas, teclas y obtener elementos 
"""
from selenium import webdriver
from selenium.webdriver.common.keys import Keys 
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
import time

driver = webdriver.Chrome('..\chromedriver')

driver.get('https://techwithtim.net')
print(driver.title)

# Busquemos en la barra de búsqueda del sitio la palabra "test"
# Después buscamos todos los resumenes de los articulos que aparecen al buscar "test"
search = driver.find_element_by_name("s")
search.clear() #Limpia la barra de búsqueda
search.send_keys("test")
search.send_keys(Keys.RETURN)

# Esperamos hasta que exista <main>
try:
    main = WebDriverWait(driver, 10).until(
        EC.presence_of_element_located((By.ID, "main"))
    )
    articles = main.find_elements_by_tag_name("article")
    for article in articles:
        header = article.find_element_by_class_name("entry-summary")
        print(header.text)
finally:
    time.sleep(5)
    driver.quit()