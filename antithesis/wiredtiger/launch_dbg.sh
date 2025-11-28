#!/usr/bin/env bash

curl --fail -u "$(cat ../mongoresearch.user.txt):$(cat ../mongoresearch.password.txt)" \
-X POST https://mongoresearch.antithesis.com/api/v1/launch/debugging \
-d '{"params": { 
        "antithesis.debugging.session_id":"b84867761648dd2f9f08fe69908f7d7d-34-7",  
        "antithesis.debugging.input_hash":"6064453807095512361" , 
        "antithesis.debugging.vtime":"22.950513483257964", 
        "antithesis.report.recipients":"finn.hackett@mongodb.com" 
    }}'
