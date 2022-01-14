set output 'graphs/counter_compare.pdf'
set xlabel "# of Nodes"
set ylabel "Time (s)"
set size ratio 0.33
set key left top

plot 'gcounter/results.txt' using 1:($2/1000) t "CRDT" with linespoints ls 1, \
     'shcounter/results.txt' using 1:($2/1000) t "2PC" with linespoints ls 2,
