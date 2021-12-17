set output 'graphs/2pc_graphs.png'
set xlabel "# of Nodes"
set ylabel "Time (s)"

plot 'lock/results.txt' using 1:($2/1000) t "Lock" with linespoints ls 1, \
     'shcounter/results.txt' using 1:($2/1000) t "Counter" with linespoints ls 2, \
     'shopcart/results.txt' using 1:($2/1000) t "Shopping Cart" with linespoints ls 3
