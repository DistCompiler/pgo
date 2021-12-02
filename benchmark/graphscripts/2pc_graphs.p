set output 'graphs/2pc_graphs.png'
set xlabel "# of Nodes"
set ylabel "Time (ms)"
plot 'lock/results.txt' t "Lock" with linespoints ls 1, \
     'shcounter/results.txt' t "Counter" with linespoints ls 2
