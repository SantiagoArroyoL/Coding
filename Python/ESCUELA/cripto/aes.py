import PyPDF2
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad, unpad
from Crypto.Random import get_random_bytes

file_path = './Criptografia_tarea_2.pdf'
with open(file_path, 'rb') as file:
    reader = PyPDF2.PdfReader(file)
    data = ""
    for i in reader.pages:
        data += i.extract_text()
    # data = file.read()

#data = b'EsteMensajeEstaCifrado'
data = data.encode('utf-8')
key = b'qawsedrftgyhujik'
iv = b'1234567890qwerty'
#key = get_random_bytes(16) #16 bytes

# Cifrado
cipher = AES.new(key, AES.MODE_CBC, iv)
cipher_text = cipher.encrypt(pad(data, AES.block_size))

#Decifrado
decrypt_cipher = AES.new(key, AES.MODE_CBC, iv)
plain_text = decrypt_cipher.decrypt(cipher_text)
plain_text = unpad(plain_text, AES.block_size)

# Extraer el último bloque cifrado
bloque = cipher_text[-16:]

print("El último bloque de cifrado es:", bloque)
print("El último bloque de cifrado en HEX es:", bloque.hex())
#print(cipher_text)
#print(plain_text.hex())
#print("Texto plano recuperado correctamente:", plain_text)
