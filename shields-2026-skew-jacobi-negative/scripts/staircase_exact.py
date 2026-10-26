"""Exact linear-real feasibility and an independent whole-space recognizer."""
from collections import Counter
from fractions import Fraction
import staircase_matching as matching
try:
    import z3
except ImportError:
    z3 = None

def plus(a, b):
    return tuple(x + y for x, y in zip(a, b))


def minus(a, b):
    return tuple(x - y for x, y in zip(a, b))


def project(form, basis):
    out = list(map(Fraction, form))
    for row in basis:
        pivot = next((i for i, c in enumerate(row) if c), None)
        assert pivot is not None
        scale = out[pivot] / row[pivot]
        out = [a - scale * b for a, b in zip(out, row)]
    return tuple(out)


def reversed_profile(profile):
    r, g = profile
    return r[::-1], g[::-1]


def family_pair(tag, p, m, z, w=None):
    """Gap labels, not actual overlaps; independently transcribed templates."""
    if tag == "A1":
        k = minus(plus(p, m), z)
        return (((p, m, m, m, k), (z, z, z, p)),
                ((p, m, k, m, m), (z, p, z, z)))
    if tag == "A2":
        k = minus(plus(p, m), z)
        return (((p, m, m, k, k), (z, z, p, p)),
                ((p, m, k, k, m), (z, p, p, z)))
    assert tag == "B" and w is not None
    k = minus(plus(p, m), w)
    return (((p, m, p, k, m), (z, w, z, z)),
            ((p, k, m, p, m), (z, z, w, z)))


def leaf_kind(basis, source, mate):
    """Check an implication on the WHOLE linear space, not a sample point."""
    f, h = [tuple(tuple(project(v, basis) for v in word) for word in profile)
            for profile in (source, mate)]
    if f == h:
        return "identity"
    if reversed_profile(f) == h:
        return "reversal"
    for oriented in (f, reversed_profile(f)):
        r, g = oriented
        for tag in ("A1", "A2", "B"):
            parameters = [(r[0], r[1], g[0], g[1]),
                          (r[0], r[2], g[0], g[2])]
            for p, m, z, w in parameters:
                pair = family_pair(tag, p, m, z, w)
                orbit = pair + tuple(reversed_profile(q) for q in pair)
                if f in orbit and h in orbit:
                    return "family"
    return None


class ExactDomain:
    def __init__(self, inequalities):
        if z3 is None:
            raise RuntimeError("Install z3-solver==4.15.3.0 for the second backend")
        self.inequalities = tuple(inequalities)
        self.xs = z3.Reals(" ".join(f"x{i}" for i in range(matching.NV)))
        self.solver = z3.SolverFor("QF_LRA")
        self.solver.add(*(self.expression(f) >= 1 for f in inequalities))
        self.cache = {}
        self.answers = Counter()

    def expression(self, form):
        assert len(form) == matching.NV + 1
        return z3.Sum([z3.RealVal(str(c)) * x
                       for c, x in zip(form[:-1], self.xs) if c]
                      + [z3.RealVal(str(form[-1]))])

    def feasible(self, equations, inequalities):
        assert tuple(inequalities) == self.inequalities
        basis = matching.rref(equations)
        if basis in self.cache:
            return self.cache[basis]
        self.solver.push()
        self.solver.add(*(self.expression(f) == 0 for f in basis))
        verdict = self.solver.check()
        assert verdict in (z3.sat, z3.unsat), verdict
        answer = verdict == z3.sat
        if answer:
            model = self.solver.model()
            point = tuple(model.eval(x, model_completion=True).as_fraction()
                          for x in self.xs)
            value = lambda f: sum(a * b for a, b in zip(f[:-1], point)) + f[-1]
            assert all(value(f) >= 1 for f in inequalities)
            assert all(value(f) == 0 for f in basis)
        self.solver.pop()
        self.cache[basis] = answer
        self.answers["sat" if answer else "unsat"] += 1
        return answer


