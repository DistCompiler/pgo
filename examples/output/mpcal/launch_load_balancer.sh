#!/usr/bin/env bash

set -m

CLIENT_COUNT=1
CLIENT_MAX=$((CLIENT_COUNT - 1))

./load_balancer_main 'ALoadBalancer(0)' '127.0.0.1:2222' &
./load_balancer_main 'AServer(1)' '127.0.0.1:3333' 'pages' &
./load_balancer_main 'AServer(2)' '127.0.0.1:4444' 'pages' &
./load_balancer_main 'AServer(3)' '127.0.0.1:5555' 'pages' &

for client in $(eval echo "{0..$CLIENT_MAX}"); do
  ./load_balancer_main "AClient($(( client + 4 )))" "127.0.0.1:$(( 6000 + client ))" &
done

fg

#for client in $(eval echo "{0..$CLIENT_MAX}"); do
#  fg
#done

#kill $(pidof load_balancer_main)
