set output 'graphs/cart_graph.png'
set xlabel "# of Nodes"
set ylabel "Time (ms)"
plot 'shopcart/results.txt' t "Cart" with linespoints ls 1
