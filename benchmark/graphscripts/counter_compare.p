set output 'graphs/counter_compare.png'
set xlabel "# of Nodes"
set ylabel "Time (ms)"
plot 'crdt.txt' t "Counter (CRDT)" with linespoints ls 1, \
     'shcounter/results_short.txt' t "Counter (2PC)" with linespoints ls 2
