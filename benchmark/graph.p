set terminal png size 1200,800
set output 'graph.png'
set xlabel "# of Nodes"
set ylabel "Time (ms)"
plot 'lock/results.txt' t "Lock" with linespoints, \
     'shcounter/results.txt' t "Counter" with linespoints
