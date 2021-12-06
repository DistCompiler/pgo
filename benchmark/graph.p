set terminal png size 1200,800
set output 'graph.png'
set xlabel "# of Nodes"
set ylabel "Time (ms)"
plot 'shopcart-crdt/results.txt' t "Shopcart-CRDT" with linespoints, \
     '../test/files/general/gcounter.tla.gotests/results.txt' t "Counter-CRDT" with linespoints