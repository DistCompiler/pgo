import sys, json, matplotlib, datetime
import matplotlib.pyplot as plt

matplotlib.use('pdf')

data = json.loads(sys.stdin.read())
plt.rc('font', size=5)          # controls default text sizes
plt.rc('axes', titlesize=7)     # fontsize of the axes title
plt.rc('axes', labelsize=7)    # fontsize of the x and y labels
plt.rc('xtick', labelsize=5)    # fontsize of the tick labels
plt.rc('ytick', labelsize=5)    # fontsize of the tick labels
plt.rc('legend', fontsize=5)    # legend fontsize

fig, (ax_top, ax_bottom) = plt.subplots(2, 1,
    sharex=True,
    figsize=(2.73, 2),
    gridspec_kw={'height_ratios': [1, 6]},
)

ax_bottom.set_ylim(0, 300) # zoom-in region
ax_top.set_ylim(600, 650) 

def plot_pair(pair, *, label, **kwargs):
    [counts, durations] = pair
    ax_top.scatter(counts, durations, s=5, linewidth=.5, **kwargs)
    ax_bottom.scatter(counts, durations, s=5, linewidth=.5, label=label, **kwargs)

plot_pair(data['omnilink_success'], label='OmniLink (valid)', marker='x', color='purple')
plot_pair(data['omnilink_failure'], label='OmniLink (invalid)', marker='+', color='orange')
plot_pair(data['porcupine_success'], label='Porcupine (valid)', marker='s', color='purple', facecolors='none')
plot_pair(data['porcupine_failure'], label='Porcupine (invalid)', marker='D', color='orange', facecolors='none')

ax_bottom.set_xlabel('Operation count', labelpad=0.75)
ax_bottom.set_xticks(data['ticks'], labels=data['tick_labels'])
ax_bottom.set_ylabel('Runtime (s)', labelpad=0.75)
ax_bottom.tick_params(axis="y", pad=0.5)
ax_bottom.tick_params(axis="x", pad=0.5)

ax_top.set_ylabel('')
ax_top.tick_params(axis="y", pad=0.5)

ax_top.spines['bottom'].set_visible(False)
ax_bottom.spines['top'].set_visible(False)
ax_top.tick_params(axis='x', which='both', bottom=False, top=False, labelbottom=False)
ax_bottom.tick_params(axis='x', which='both', top=False)

fig.legend(loc='upper center', ncols=2, bbox_to_anchor=(.525, .98), columnspacing=.7, handletextpad=.3)

plt.subplots_adjust(left=0.125, bottom=0.125, right=0.98, top=0.98, wspace=0, hspace=.1)

plt.savefig('time_plot.pdf')
