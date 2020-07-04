#!/usr/bin/gnuplot

# set term wxt size 1920,1080
set terminal pngcairo size 720,405 enhanced font 'Verdana,10'
set output 'vroom.png'
set title "Push time"
set xlabel "Index"
set ylabel "Latency [ms]"
set xrange [0:4194304]
# set logscale y
# set yrange [0.001:*]

set style line 1 lc rgb '#1b9e77'
set style line 2 lc rgb '#d95f02'
set style line 3 lc rgb '#7570b3'

set key left top
set key box linestyle 3

plot "< awk '$2 == \"atone\"' vroom.dat" u 1:3 t "atone::Vc" ls 1 lw 2 ps 1.5,\
     "< awk '$2 == \"vecdeque\"' vroom.dat" u 1:3 t "std::VecDeque" ls 2 lw 2 ps 1.5,\
     "< awk '$2 == \"vec\"' vroom.dat" u 1:3 t "std::Vec" ls 3 lw 2 ps 1.5
