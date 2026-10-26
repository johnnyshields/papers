r"""Paper section `app:aligned` (Aligned reconstruction before minimality).

Smallest positive coincident instance of the returned section (app:aligned, eq:positive-section):
records on which variables Phi(h_j)/Y_j depends, for j = 1, 2, 3.  Reports; asserts only exact
independence of Phi(h_1)/Y_1 from S, Y."""
import random
from fractions import Fraction as F
import check_noncell_section as c
from check_row_probe_caps import *

E = frozenset([(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1)])
w, v, tau = 2, (-2, 1), 1
assert any(m[0] == w and m[1] == v and m[2] == (1, 1) for m in legal_marks(E))
q = c.N_E_(E) - w
J = 3
probes = {j: probe(E, v, j) for j in (1, 2, 3)}
for seed in range(1, 200):
    rng = random.Random(seed)
    lo = {m: F(rng.randint(-5, 5), rng.randint(1, 4)) for m in range(1, q)}
    hh = dict(lo)
    for m in range(q, 4 * q + w + 8):
        hh[m] = F(rng.randint(-9, 9), rng.randint(1, 5))
    try:
        g = c.coframe_low(probes[2], hh, q)
    except (StopIteration, ZeroDivisionError):
        continue
    if g[tau] != 0:
        break
print('q', q, 'g', g)
cs = [content(x) for x in E]; lo_c = min(cs)
band = sorted(x for x in E if content(x) < lo_c + w)
W = None
for mask in range(1, 1 << len(band)):
    Wm = {band[k] for k in range(len(band)) if mask >> k & 1}
    if len({content(x) for x in Wm}) == w and is_cs(Wm):
        top = max(map(content, E)); hi_w = lo_c + w - 1
        r0 = min(x[0] for x in Wm if content(x) == hi_w); nr = min(x[0] for x in E if content(x) == top)
        if (nr - r0, nr + top - r0 - hi_w) == v and tr(Wm, v) <= set(E):
            W = normalize(Wm); print('window', sorted(Wm))
ncut = J * q + w + 2


def phi(Y, S):
    H = c.section(g, lo, q, tau, Y, S, ncut)
    hv = {m: H[m] for m in range(1, ncut)}
    A = c.schur(W, hv)
    out = []
    for j in range(1, J + 1):
        h2 = dict(hv)
        for m in range(ncut, j * q + w + 3):
            h2[m] = F(0)
        out.append(A ** (j - 1) * c.schur(probes[j], h2))
    return out

one = F(1)
base_Y = [one, F(2), F(3), F(5)]; base_S = [one, F(-1), F(4), F(7)]
for name, Y, S in [('base', base_Y, base_S), ('S changed', base_Y, [one, F(2), F(-3), F(1)]),
                   ('Y1 changed', [one, F(7), F(3), F(5)], base_S),
                   ('Y2 changed', [one, F(2), F(9), F(5)], base_S)]:
    p = phi(Y, S)
    print(name, [p[j] / Y[j + 1] for j in range(3)])
print('Phi at Y_j = 0 (j=1,2,3), other Y generic:')
for j in (1, 2, 3):
    Y = [one, F(2), F(3), F(5)]; Y[j] = F(0)
    print(' j', j, phi(Y, base_S)[j - 1])
for Y2 in (F(0), F(1), F(2), F(3)):
    print(' Y=(1,2,Y2,5) Phi(h_2) =', phi([one, F(2), Y2, F(5)], base_S)[1])
print('Phi(e_j)/Y_j (e_2 = h1^2-h2, e_3 = h1^3-2h1h2+h3):')
for Y, S in [(base_Y, base_S), ([one, F(7), F(3), F(5)], base_S), ([one, F(2), F(9), F(-4)], [one, F(3), F(1), F(2)])]:
    p = phi(Y, S)
    e2 = p[0] ** 2 - p[1]; e3 = p[0] ** 3 - 2 * p[0] * p[1] + p[2]
    print(' ', p[0] / Y[1], e2 / Y[2], e3 / Y[3])
