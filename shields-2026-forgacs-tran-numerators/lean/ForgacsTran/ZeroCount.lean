/-
# Exceptional-zero counting engine

Formalizes the combinatorial core of
`../shields-2026-forgacs-tran-numerators.tex`, §5 «Proof of the fixed-numerator
theorem» (`sec:proof`, `prop:univariate-main`): the elementary step that turns a
lower bound on the number of *interior* zeros of a polynomial into an upper
bound on the number of its zeros lying *outside* a prescribed set.

* `exceptionalRoots P S` — the multiset of roots of `P` (with multiplicity)
  lying outside `S`; the "exceptional zeros" of `thm:main`.
* `le_card_roots_filter` — a finite set `Z` of distinct roots of `P` lying in
  `S` embeds, with multiplicity, into the interior part of the root multiset.
* `exceptionalRoots_card_le` — if `Z` has at least `deg P - C` elements, then
  `P` has at most `C` roots outside `S`, counted with multiplicity.

In the paper `S = I_{Q,r}` (or `(0,∞)`), `Z` is the family of `⌊M/r⌋ - C`
distinct positive zeros produced by the phase count of `prop:univariate-main`,
and `deg P = deg P_m = ⌊M/r⌋`, so the exceptional zeros number at most `C`.

Stated over an arbitrary integral domain, so it applies both to the real
coefficient polynomials and to their complex zero sets.  Sorry-free; uses only
`Polynomial.roots` cardinality (`card_roots'`) and `Multiset` bookkeeping.
-/
import Mathlib

open Classical Polynomial

namespace ForgacsTran

variable {K : Type*} [CommRing K] [IsDomain K]

/-- The roots of `P` (with multiplicity) lying outside `S`; the "exceptional
zeros" of `thm:main`. -/
noncomputable def exceptionalRoots (P : K[X]) (S : Set K) : Multiset K :=
  P.roots.filter (fun x => x ∉ S)

omit [CommRing K] [IsDomain K] in
/-- Paper §5 `sec:proof` — supporting Multiset lemma for the counting engine
(no separate paper statement).  Partition of a multiset by a decidable predicate
`p`: the counts satisfying `p` and its negation add to the total.  Immediate from
`Multiset.filter_add_not` and additivity of `card`. -/
theorem card_filter_add_card_filter_not_pred (p : K → Prop) [DecidablePred p]
    (s : Multiset K) :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [← Multiset.card_add, Multiset.filter_add_not]

omit [CommRing K] [IsDomain K] in
/-- Paper §5 `sec:proof` — supporting lemma for the counting engine (no separate
paper statement).  Partition by membership in `S`: the counts inside and outside
add to the total. -/
theorem card_filter_add_card_filter_not (s : Multiset K) (S : Set K) :
    (s.filter (fun x => x ∈ S)).card + (s.filter (fun x => x ∉ S)).card = s.card :=
  card_filter_add_card_filter_not_pred (fun x => x ∈ S) s

/-- Paper §5 `sec:proof` — supporting step for `prop:univariate-main`.  The
distinct roots of `P` satisfying a decidable predicate `p` embed, with
multiplicity, into the `p`-part of the root multiset. -/
theorem le_card_filter {p : K → Prop} [DecidablePred p] {P : K[X]} {Z : Finset K}
    (hP : P ≠ 0) (hZr : ∀ x ∈ Z, P.IsRoot x) (hZp : ∀ x ∈ Z, p x) :
    Z.card ≤ (P.roots.filter p).card := by
  refine Multiset.card_le_card ((Multiset.le_iff_subset Z.nodup).mpr ?_)
  intro a ha
  rw [Finset.mem_val] at ha
  exact Multiset.mem_filter.mpr ⟨mem_roots'.mpr ⟨hP, hZr a ha⟩, hZp a ha⟩

/-- Paper §5 `sec:proof` — set-membership wrapper for `le_card_filter`. -/
theorem le_card_roots_filter {P : K[X]} {S : Set K} {Z : Finset K} (hP : P ≠ 0)
    (hZr : ∀ x ∈ Z, P.IsRoot x) (hZS : ∀ x ∈ Z, x ∈ S) :
    Z.card ≤ (P.roots.filter (fun x => x ∈ S)).card :=
  le_card_filter hP hZr hZS

/-- **Exceptional-zero counting engine** (mechanism of `prop:univariate-main`).
A nonzero polynomial `P` with at least `deg P - C` distinct roots inside `S` has
at most `C` roots outside `S`, counted with multiplicity. -/
theorem exceptionalRoots_card_le {P : K[X]} {S : Set K} {C : ℕ} {Z : Finset K}
    (hP : P ≠ 0) (hZr : ∀ x ∈ Z, P.IsRoot x) (hZS : ∀ x ∈ Z, x ∈ S)
    (hZc : P.natDegree - C ≤ Z.card) :
    (exceptionalRoots P S).card ≤ C := by
  have hpart := card_filter_add_card_filter_not P.roots S
  have hdeg : P.roots.card ≤ P.natDegree := P.card_roots'
  have hZcard : Z.card ≤ (P.roots.filter (fun x => x ∈ S)).card :=
    le_card_roots_filter hP hZr hZS
  have hex : (exceptionalRoots P S).card = (P.roots.filter (fun x => x ∉ S)).card := rfl
  rw [hex]
  omega

/-! ### The geometry of the conclusion

The complex zero set is the object of `thm:main`; the positive ray and the
Forgács–Tran interval are viewed as subsets of `ℂ`. -/

/-- The positive real ray `(0,∞)`, as a subset of `ℂ`. `thm:main` bounds the
zeros lying in its complement. -/
def posRay : Set ℂ := Complex.ofReal '' Set.Ioi 0

/-- Paper §3 `sec:geometry`, `thm:FT-geometry` (`eq:ab-def`) — the Forgács–Tran
interval `I_{Q,r} = (a,b)`, as a subset of `ℂ`. -/
def ftInterval (a b : ℝ) : Set ℂ := Complex.ofReal '' Set.Ioo a b

/-- Paper §3 `sec:geometry` — `I_{Q,r} ⊂ (0,∞)` once the left endpoint is
nonnegative.  Nonnegativity, not positivity, is the right hypothesis: the paper
has `a = 0` exactly when the smallest zero of `Q` is repeated (`ρ ≥ 2`), and
openness of `Set.Ioo` already forces the members to be positive. -/
theorem ftInterval_subset_posRay {a b : ℝ} (ha : 0 ≤ a) : ftInterval a b ⊆ posRay := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, lt_of_le_of_lt ha hx.1, rfl⟩

/-- Paper §3 `sec:geometry`, `eq:ab-def` — the Forgács–Tran interval in the case
`b = +∞`, which by `eq:ab-def` is exactly the case `r > 1`.  A real right endpoint
cannot express this, so the unbounded interval gets its own constructor. -/
def ftRay (a : ℝ) : Set ℂ := Complex.ofReal '' Set.Ioi a

/-- Paper §3 `sec:geometry` — `I_{Q,r} = (a,∞) ⊂ (0,∞)` for `a ≥ 0`; the `r > 1`
companion of `ftInterval_subset_posRay`. -/
theorem ftRay_subset_posRay {a : ℝ} (ha : 0 ≤ a) : ftRay a ⊆ posRay := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, lt_of_le_of_lt ha hx, rfl⟩

end ForgacsTran
