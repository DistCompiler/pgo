set terminal png size 1200,800
set output 'cart_graph.png'
set xlabel "# of Nodes"
set ylabel "Time (ms)"
plot 'shopcart/results.txt' t "Cart" with linespoints
