import sys, json, matplotlib, datetime
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker

matplotlib.use('pdf')

data = json.loads(sys.stdin.read())

fig, ax = plt.subplots()

def plot_pair(pair, *, label, marker):
    [counts, durations] = pair
    ax.scatter(counts, durations, label=label, marker=marker)

plot_pair(data['omnilink_success'], label='OmniLink (valid)', marker='1')
plot_pair(data['omnilink_failure'], label='OmniLink (invalid)', marker='2')
plot_pair(data['porcupine_success'], label='Porcupine (valid)', marker='3')
plot_pair(data['porcupine_failure'], label='Porcupine (invalid)', marker='4')

ax.set_xlabel("Operation count")
ax.set_xticks(data['ticks'], labels=data['tick_labels'])
ax.set_ylabel('Peak memory usage (GB)')

fig.legend(loc='upper center', ncols=2)

plt.savefig('mem_plot.pdf')
