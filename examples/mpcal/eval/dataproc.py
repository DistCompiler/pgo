import csv, statistics
from pathlib import Path

import argparse

def main():
    parser = argparse.ArgumentParser(description='Statistical analysis of PGo eval data')
    parser.add_argument('folder', help='a folder with a series of *.out files')

    args = parser.parse_args()

    data = []

    folder = Path(args.folder)
    for infile in folder.glob('*.out'):
        with infile.open(newline='') as f:
            reader = csv.reader(f, delimiter=' ')
            data += (int(d) for _, _, d in reader)

    data = sorted(data)

    mean = statistics.mean(data)
    stdev = statistics.stdev(data)
    throughput = 1 / (mean / 1000000000)

    print(f'Summary of perf data in {folder}')
    print(f'All data in ns per query unless otherwise noted.') 
    print(f'Throughput (trans/sec): {throughput}')
    print(f'Min: {data[0]}, Max: {data[-1]}')
    print(f'Mean: {mean}, StDev: {stdev}')

if __name__ == '__main__':
    main()

