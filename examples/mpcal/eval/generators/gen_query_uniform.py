# This file is a modified version of gen_query_uniform.py from NetCache at
# https://github.com/netx-repo/netcache-p4/blob/c8834a73d803abff936ae7994e28153f14dceb6e/generator/gen_query_uniform.py

import random

path_query = "query.txt"
num_query = 1000000

len_key = 16
len_val = 128
max_key = 1000

f = open(path_query, "w")
for i in range(num_query):
    #Randomly select a key
    key_header = random.randint(1, max_key)
    key_body = [0] * (len_key - 4)

    #Save the generated query to the file
    f.write("get ")
    f.write(str(key_header) + ' ')
    for i in range(len(key_body)):
        f.write(hex(key_body[i]) + ' ')
    f.write('\n')
f.flush()
f.close()
