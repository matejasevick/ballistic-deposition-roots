import numpy as np
from math import exp, factorial
from task34_numbers import a_cf, b_cf
rng = np.random.default_rng(12345)
def D_counts(T, g):
    """T: (reps, K) first-arrival times on the cycle; returns D_{g-1,K} per row."""
    xi = (T < np.roll(T, 1, axis=1)) & (T < np.roll(T, -1, axis=1))
    x = xi.astype(np.int32)
    K = x.shape[1]
    xx = np.concatenate([x, x[:, :g+1]], axis=1)
    cs = np.concatenate([np.zeros((x.shape[0], 1), np.int32), np.cumsum(xx, axis=1)], axis=1)
    inner = cs[:, g:g+K] - cs[:, 1:1+K]          # roots at j+1..j+g-1
    Y = x * xx[:, g:g+K] * (inner == 0)
    return Y.sum(axis=1)
# Task 4: Poisson regime, i=6 (g=7), K=5250 -> lambda = 10
i, K, reps = 6, 5250, 20000; g = i + 1
Ds = np.concatenate([D_counts(rng.random((2000, K)), g) for _ in range(reps // 2000)])
lam = float(a_cf(i)) * K
kmax = Ds.max() + 20
emp = np.bincount(Ds, minlength=kmax)[:kmax] / reps
poi = np.array([exp(-lam) * lam**k / factorial(k) for k in range(kmax)])
print(f"[T4] i=6,K=5250: mean={Ds.mean():.3f} (a_iK={lam:.3f}), var={Ds.var():.3f} (b_iK={float(b_cf(i))*K:.3f}), empirical dTV to Poi(lam)={0.5*np.abs(emp-poi).sum():.4f} (eps_6=0.054; MC noise ~0.02)")
# Task 5: period-2 rates (1, 3); roots = local minima of independent Exp(rate_j) times
i, K, reps = 1, 2000, 20000; g = 2
rates = np.tile([1.0, 3.0], K // 2)
Ds = np.concatenate([D_counts(rng.exponential(1.0 / rates, size=(2000, K)), g) for _ in range(reps // 2000)])
z = (Ds - Ds.mean()) / Ds.std()
print(f"[T5] period-2 rates (1,3), i=1, K=2000: E D/K={Ds.mean()/K:.4f} (uniform: {float(a_cf(1)):.4f}), Var/K={Ds.var()/K:.4f} (uniform: {float(b_cf(1)):.4f}), skew={np.mean(z**3):.3f}, kurt-3={np.mean(z**4)-3:.3f}")
# Task 5: iid random rates (annealed) -> same as uniform model
Ds = np.concatenate([D_counts(rng.exponential(1.0 / rng.gamma(0.5, 2.0, size=(2000, K))), g) for _ in range(reps // 2000)])
print(f"[T5] iid Gamma rates annealed, i=1, K=2000: E D/K={Ds.mean()/K:.4f}, Var/K={Ds.var()/K:.4f} (uniform: {float(a_cf(1)):.4f}, {float(b_cf(1)):.4f})")
