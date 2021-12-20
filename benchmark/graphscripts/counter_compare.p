set output 'graphs/counter_compare.png'
set xlabel "# of Nodes"
set ylabel "Time (s)"

plot 'gcounter/results.txt' using 1:($2/1000) t "CRDT" with linespoints ls 1, \
     'shcounter/results.txt' using 1:($2/1000) t "2PC" with linespoints ls 2,
