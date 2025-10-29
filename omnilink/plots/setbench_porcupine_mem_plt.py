import sys, json, matplotlib, datetime
import matplotlib.pyplot as plt

matplotlib.use('pdf')

data = json.loads(sys.stdin.read())

fig, ax = plt.subplots()

def plot_pair(pair, *, label):
    [counts, durations] = pair
    ax.scatter(counts, durations, label=label)

plot_pair(data['omnilink_success'], label='OmniLink (valid)')
plot_pair(data['omnilink_failure'], label='OmniLink (invalid)')
plot_pair(data['porcupine_success'], label='Porcupine (valid)')
plot_pair(data['porcupine_failure'], label='Porcupine (invalid)')

ax.set_xlabel("Operation count")
ax.set_ylabel("Peak memory usage (GB)")

fig.legend(loc='upper center')

plt.savefig('mem_plot.pdf')
