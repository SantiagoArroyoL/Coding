# -*- coding: utf-8 -*-
"""
Created on Mon Oct 10 21:40:56 2022

@author: santi
"""

import re

regex = r"(?i)\b((?:https?://|www\d{0,3}[.]|youtube.com+[.][a-z]{2,4}/)(?:[^\s()<>]+|\(([^\s()<>]+|(\([^\s()<>]+\)))*\))+(?:\(([^\s()<>]+|(\([^\s()<>]+\)))*\)|[^\s`!()\[\]{};:'\".,<>?«»“”‘’]))"
test_string = 'https://www.youtube.com/watch?v=WVjtK71qqXU'
result = re.match(regex, test_string)

if result:
  print("Search successful.")
else:
  print("Search unsuccessful.")
 
factorial = 1
  

for i in range(1,1):
    factorial = factorial * i
    
print(factorial)