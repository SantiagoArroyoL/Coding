# -*- coding: utf-8 -*-
"""
Created on Sat Dec  5 01:14:01 2020

@author: Santiago Arroyo
@param: URL (Amazon)

El script revisa las páginas de Gameplanet, Walmart y Amazon al mismo tiempo a través de Firefox y Google Chrome
Busca por PS5

"""
from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.common.action_chains import ActionChains
from selenium.webdriver.firefox.options import Options
from selenium.webdriver.common.keys import Keys
import time, datetime, random,sys
import smtplib
credentials = {"correo" : "santiago-sonic@hotmail.com", "contra":"Sonic080601", "usuario": "SantiagoArroyoL" }

#************ GAMEPLANET/WALMART *************

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



# ****************** AMAZON ******************
class Product:
    
    def __init__(self,**kwargs):
        """ Constructor. 
        Delay para evitar bloqueo temporal de Amazon. """

        self.amazon_credential = credential['usuario']
        self.email_credential = credentials['correo]
        self.product = kwargs['p_url']
    
    def launch_bot(self):
        """ Inicializa bot y simula selenium (Firefox). Vamos al login de Amazon"""

        options = Options()
        options.set_headless(headless=True)
        self.browser_emulator = webdriver.Firefox(firefox_options=options)
        self.browser_emulator.get\
        ('''https://www.amazon.in/ap/signin?openid.assoc_handle=inflex&openid.claimed_id=http%3A%2F%2Fspecs.openid.net%2Fauth%2F2.0%2Fidentifier_select&openid.identity=http%3A%2F%2Fspecs.openid.net%2Fauth%2F2.0%2Fidentifier_select&openid.mode=checkid_setup&openid.ns=http%3A%2F%2Fspecs.openid.net%2Fauth%2F2.0''')
        
    def user_login_session(self):
        """ Introducimos credenciales """

        self.browser_emulator.find_element_by_xpath\
        ('''//*[@id="ap_email"]''').send_keys(self.amazon_credential.UNAME,Keys.RETURN)
        time.sleep(10)
        self.browser_emulator.find_element_by_xpath\
        ('''//*[@id="ap_password"]''').send_keys(self.amazon_credential.PASSWD,Keys.RETURN)
        time.sleep(10)
        
        """ URL - AMAZON MX - PS5 DISC """
        self.browser_emulator.get(self.product)
        #self.browser_emulator.get\('''https://www.amazon.com.mx/dp/B08BQ9X5CN/ref=cm_sw_r_wa_apa_fabt1_HHwVFb2GDMBV9''')
        
    def check_availability(self):
        """ Revisamos disponibilidad """
        
        try:
        	self.browser_emulator.find_element_by_xpath\
            ('''//*[@id="priceblock_ourprice"]''')
        
        except:
            try:
            	self.browser_emulator.find_element_by_xpath\
                ('''//*[@id="priceblock_dealprice"]''')
            except:
                try:
                    self.browser_emulator.find_element_by_xpath\
                    ('''//*[@id="priceblock_saleprice"]''')
                except:
                    pass
                else:
                    self.add_to_cart()
            else:
                self.add_to_cart()

        else:
            self.add_to_cart()
            
        finally:
            self.browser_emulator.refresh()
            time.sleep(random.randint(10,45))
            print('It is not is Stock yet.')

    def add_to_cart(self):
        """ Añadir al carrito"""

        self.browser_emulator.find_element_by_xpath('//*[@id="add-to-cart-button"]').click()
        self.email_notification()
        self.browser_emulator.quit()

    def email_notification(self):

        email = '''FROM: {user}\nTO: {to}\nSUBJECT: {subject}\n\n{body}'''\
        .format(user = self.email_credential.EMAIL,to=self.email_credential.RECEIVER,\
            subject=self.email_credential.SUBJECT,body=self.email_credential.BODY)
        server = smtplib.SMTP('smtp-mail.outlook.com',25)
        server.starttls()
        server.login(self.email_credential.EMAIL,self.email_credential.EMAILPASSWD)
        server.sendmail(self.email_credential.EMAIL,self.email_credential.RECEIVER, email)
        server.quit()

if __name__ == '__main__':
    """ This script is executed, when you run .py file. """

    product = sys.argv[1]
    bot = Product(p_url=product)
    bot.launch_bot()
    bot.user_login_session()
    while 1:
        bot.check_availability()
