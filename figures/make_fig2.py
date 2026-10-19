import numpy as np, matplotlib
matplotlib.use('pgf')
import matplotlib.pyplot as plt
plt.rcParams.update({'pgf.texsystem': 'pdflatex', 'pgf.rcfonts': False, 'text.usetex': True, 'font.family': 'serif', 'font.size': 9,
                     'axes.linewidth': 0.6, 'xtick.major.width': 0.6, 'ytick.major.width': 0.6,
                     'xtick.minor.width': 0.4, 'ytick.minor.width': 0.4})
d = {}
for line in open('speed_data.txt'):
    K, v = line.split(); d.setdefault(int(K), []).append(float(v))
Ks = np.array(sorted(d)); m = np.array([np.mean(d[k]) for k in Ks]); sd = np.array([np.std(d[k]) for k in Ks])
fig, ax = plt.subplots(figsize=(5.0, 3.0))
ax.axhline(3.0, color='black', lw=0.8)
ax.axhline(4.0, color='black', lw=0.8, ls=(0, (5, 3)))
ax.text(3.15e3, 3.02, r'proved lower bound $3$', ha='right', va='bottom', fontsize=8)
ax.text(3.15e3, 3.965, r'conjectured value $4$', ha='right', va='top', fontsize=8)
# rigorous brackets from exact enumeration (K = 4, 5, 6)
br = {4: 3.2096858, 5: 3.5086643, 6: 3.7546927}
for k, up in br.items():
    ax.plot([k, k], [3.0, up], color='0.55', lw=2.2, solid_capstyle='butt', zorder=1)
    ax.plot([k*0.94, k*1.06], [up, up], color='0.55', lw=1.0, zorder=1)
ax.plot(Ks, m, color='0.35', lw=0.7, zorder=2)
ax.errorbar(Ks, m, yerr=2*sd, fmt='o', ms=3.6, mfc='black', mec='black', ecolor='black', elinewidth=0.6, capsize=0, zorder=3)
ax.set_xscale('log'); ax.set_xlim(2.6, 5.5e3); ax.set_ylim(2.9, 4.18)
ax.set_xlabel(r'number of sites $K$'); ax.set_ylabel(r'$K\,v_K$')
ax.set_yticks([3.0, 3.2, 3.4, 3.6, 3.8, 4.0])
ax.annotate(r'rigorous bracket (exact enumeration)', xy=(5, 3.40), xytext=(9, 3.22), fontsize=8,
            arrowprops=dict(arrowstyle='-', lw=0.5, color='0.3'), va='center')
ax.annotate(r'simulation', xy=(100, 4.0227), xytext=(130, 3.80), fontsize=8,
            arrowprops=dict(arrowstyle='-', lw=0.5, color='0.3'), va='center')
ax.text(2.75, 4.13, r'proved upper bound $3e\approx8.15$ (off scale)', fontsize=7.5, color='0.25', va='top')
for s in ('top', 'right'): ax.spines[s].set_visible(False)
fig.tight_layout(pad=0.3)
fig.savefig('fig_speed.pdf')
print(dict(zip(Ks.tolist(), np.round(m, 4).tolist())))
