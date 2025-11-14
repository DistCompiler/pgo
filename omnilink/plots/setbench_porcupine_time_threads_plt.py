import sys, json, matplotlib, datetime
import matplotlib.pyplot as plt

matplotlib.use('pdf')

data = json.loads(sys.stdin.read())
plt.rc('font', size=6)          # controls default text sizes
plt.rc('axes', titlesize=7)     # fontsize of the axes title
plt.rc('axes', labelsize=7)    # fontsize of the x and y labels
plt.rc('xtick', labelsize=5)    # fontsize of the tick labels
plt.rc('ytick', labelsize=5)    # fontsize of the tick labels
plt.rc('legend', fontsize=5)    # legend fontsize

fig, ax = plt.subplots(1, 1,
    sharex=True,
    figsize=(5.46, 1),
)
fig.tight_layout()

def plot_pair(pair, *, label, **kwargs):
    [counts, durations] = pair
    ax.scatter(counts, durations, s=5, linewidth=.5, label=label, **kwargs)

plot_pair(data['omnilink_success'], label='OmniLink (valid)', marker='x', color='purple')
plot_pair(data['omnilink_failure'], label='OmniLink (invalid)', marker='+', color='orange')
plot_pair(data['porcupine_success'], label='Porcupine (valid)', marker='s', color='purple', facecolors='none')
plot_pair(data['porcupine_failure'], label='Porcupine (invalid)', marker='D', color='orange', facecolors='none')

ax.set_xlabel('Thread count', labelpad=0.75)
ax.set_xticks(data['ticks'], labels=data['tick_labels'])
ax.set_ylabel('Runtime (s)', labelpad=.75)
ax.tick_params(axis="y", pad=0.5)
ax.tick_params(axis="x", pad=0.5)

fig.legend(loc='upper center', ncols=2, bbox_to_anchor=(.525, .85), columnspacing=.7, handletextpad=.3)

plt.subplots_adjust(left=0.06, bottom=0.25, right=0.98, top=0.86, wspace=0, hspace=0)

plt.savefig('time_threads_plot.pdf')
