"""Shared exact-coefficient machinery for the wall-fan probes (not a check itself)."""
from mpmath import mp, mpf, psi, gamma, factorial, besseli, log, diff


def build_S(a, N):
    z = [1/(factorial(k)*gamma(a+k)) for k in range(N+1)]
    return [sum(z[i]*z[m-i] for i in range(m+1)) for m in range(N+1)]


def M_endpoint(a, g, m):
    """endpoint fiber M_m of eq. (matrix-series): entries (11, 12, 22)."""
    al = psi(1, a+m)
    be = mpf(1) if m == 0 else (2*a+m-2)/(2*(a+m-1))
    cm = mpf(0) if m < 2 else mpf(m*(m-1))/(2*(2*a+2*m-3))
    return al, mp.sqrt(g)*be, 1 + g*cm


def wall_data(a, S, ns):
    """Delta_n, p_n, q_n of eq. (pq-coefficients) from the exact fibers."""
    g = psi(1, a)
    M = [M_endpoint(a, g, m) for m in range(max(ns)+1)]
    out = {}
    for n in ns:
        D = p = q = mp.mpf(0)
        for k in range(n+1):
            w = S[k]*S[n-k]
            x11, x12, x22 = M[k]
            y11, y12, y22 = M[n-k]
            D += w*(x11*y22 + x22*y11 - 2*x12*y12)/2
            p += w*psi(1, a+k)
            q += (n-k)*w*psi(1, a+k)
        out[n] = (D, p, q*g/2)
    return out


def richardson(ns, vals):
    xs = [mpf(1)/n for n in ns]
    ys = list(vals)
    while len(ys) > 1:
        ys = [(ys[i+1]*xs[i]-ys[i]*xs[i+1])/(xs[i]-xs[i+1]) for i in range(len(ys)-1)]
        xs = xs[1:]
    return ys[0]


def D_bessel(nu, z, kappa, tau):
    """D_nu^{(kappa,tau)}(z) of eq. (Dnu-kt-def), by exact differentiation of log I_nu."""
    def F(n_, z_):
        return log(besseli(n_, z_))
    g = psi(1, nu+1)
    Fz = diff(F, (nu, z), (0, 1))
    Fzz = diff(F, (nu, z), (0, 2))
    Fnn = diff(F, (nu, z), (2, 0))
    Fnz = diff(F, (nu, z), (1, 1))
    H = 2*kappa*(z*Fz - nu) - (z*Fz + z*z*Fzz)
    return (-Fnn)*(H + 4*tau/g) - (1 + z*Fnz)**2


def c_tau(a, tau):
    return 4*tau/psi(1, a) - 4*a + mpf(7)/2


def d_tau(a, tau):
    return mpf(1)/12 - 2*tau/psi(1, a)


def e_tau(a, tau):
    return 2*tau/psi(1, a) - 3*(a-1) - mpf(1)/3


def tau_infty(a):
    return psi(1, a)*(a - mpf(7)/8)
