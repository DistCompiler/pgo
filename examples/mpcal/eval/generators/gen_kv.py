# This file is a modified version of gen_kv.py from NetCache at
# https://github.com/netx-repo/netcache-p4/blob/c8834a73d803abff936ae7994e28153f14dceb6e/generator/gen_kv.py

import random

path_kv = "kv.txt"  #The path to save generated keys and values
path_hot = "hot.txt" #The path to save the hot keys
len_key = 16  #The number of bytes in the key
len_val = 128 #The number of bytes in the value
max_key = 1000  #The number of keys
max_hot = 100 #The number of hot keys

f = open(path_kv, "w")
f_hot = open(path_hot, "w")
f.write(str(max_key) + "\n\n")
for i in range(1, max_key + 1):
    ## Generate a key-value item
    #Select a key
    key_header = i
    key_body = [0] * (len_key - 4)
    #Select a value
    val = [1] * len_val #The value
    ###################################################################################################

    ## Output the key and the value to the file
    f.write(str(key_header) + " ")
    for i in range(len(key_body)):
        f.write(hex(key_body[i]) + " ")
    f.write("\n")

    for i in range(len(val)):
        f.write(hex(val[i]) + " ")
    f.write("\n\n")
    ###################################################################################################

    ##Output the hot key to the file
    if (key_header <= max_hot and key_header % 2 == 1):
        f_hot.write(str(key_header) + " ")
        for i in range(len(key_body)):
            f_hot.write(hex(key_body[i]) + " ")
        f_hot.write("\n")
    ###################################################################################################

f.flush()
f.close()
f_hot.flush()
f_hot.close()
