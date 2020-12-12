#!/usr/bin/env bash

set -m

CLIENT_COUNT=3
SERVER_COUNT=2
CLIENT_MAX=$((SERVER_COUNT + CLIENT_COUNT - 1))
SERVER_MAX=$((SERVER_COUNT - 1))

for server in $(eval echo "{0..$SERVER_MAX}"); do
  #echo "replica $server"
  ./replicated_kv_main "Replica($server)" "127.0.0.1:$(( 6000 + server ))" &
done

for client in $(eval echo "{$SERVER_COUNT..$CLIENT_MAX}"); do
  #echo "client $client"
  ./replicated_kv_main "Client($client)" "127.0.0.1:$(( 6000 + client ))" &
done

fg

#for client in $(eval echo "{0..$CLIENT_MAX}"); do
#  fg
#done

#kill $(pidof load_balancer_main)
