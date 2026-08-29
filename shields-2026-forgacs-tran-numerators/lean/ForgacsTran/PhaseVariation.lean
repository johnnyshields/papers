/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.ViewingAngle
import ForgacsTran.LaurentReduction

/-!
# Linear phase variation, and the numerator-uniform defect

A continuous branch of `arg W` splits, along `eq:W-on-g`, into the branch belonging to the
denominator factor `(γ^r g'(γ))^{-1}` and one branch per zero of `B`.  Radon's bound
(`lem:viewing-angle`, `ViewingAngle.viewing_angle_bound_regular`) caps each of the latter by
`𝒦_γ + π`, a constant of the principal arc alone.  Adding them is what turns that per-root
cap into `eq:linear-phase-variation`, and the constants `κ₀`, `κ₁` it produces do not see
`B` — which is the uniformity separating `thm:main` clause 3 from clause 2.

The per-root bound is **discharged**, not hypothesized: the branches are
`ViewingAngle.polarAngle γ γ' β a`, one per zero of `B`, each built by the lift and each
capped by `viewing_angle_bound_regular` from the arc's regularity alone.

## Which form to use

Eight statements below bound the same quantity, and they are not interchangeable.
**`linear_phase_variation_components_regular` is the canonical one**: it is the
manuscript's own left-hand side — summed over the components of
`(0, π/r) ∖ {W = 0}` — it hypothesizes nothing about any argument branch, and it
allows a zero of `B` to lie **on** the arc, which the principal arc's zeros do.  A
caller with the arc's `C²` package and an ordered family of components wants that one.

The other seven are the rungs it is built from, and each is reachable on its own:

* `linear_phase_variation` — the branches are given and the per-root Radon bound is
  already in hand.
* `linear_phase_variation_multiset` — the same, with the count as a multiset
  cardinality rather than an abstract `K`.
* `linear_phase_variation_of_arc` — one branch over one set, per-root bound
  discharged, and **no zero of `B` on the arc**.
* `linear_phase_variation_regular` — the same asking only for a regular arc, with
  nothing about any branch.
* `linear_phase_variation_components` — the summed form at abstract branches, the
  per-root bound still a hypothesis.
* `phase_variation_le_laurentWeight` and `…_of_arc` — the count is `deg B_N` of
  `eq:canonical-Laurent-factorization` rather than a free `K`.

None is superseded: a bound stated at a free `K` is strictly more general than the
same bound at `deg B`, and the two `_of_arc` forms are the only ones that name the
reduced weight.

## Main statements

* `eVariationOn_add_le`, `eVariationOn_finsetSum_le`, `eVariationOn_multisetSum_le` —
  subadditivity of the variation, which Mathlib does not carry.
* `linear_phase_variation`, `linear_phase_variation_multiset` — `eq:linear-phase-variation`:
  `κ₀ + κ₁ K` with `κ₁ = 𝒦_γ + π`, over a per-root bound.
* `linear_phase_variation_of_arc`, `linear_phase_variation_regular` — the same with that
  per-root bound discharged, the zeros of `B` supplying the index multiset; the second asks
  only for a regular arc.
* `phase_variation_le_laurentWeight`, `phase_variation_le_laurentWeight_of_arc` — the bound
  at `K = deg B_N`, the reduced weight of `eq:canonical-Laurent-factorization`.
* `NumeratorUniform` / `numeratorUniform_of_le` — the `ℕ`-valued clause-3 shape and its
  production from a real linear bound.
* `numeratorUniform_natDegree_le` — the shape composed with `eq:reduced-degree-complexity`,
  so a clause-3 constant is also linear in the raw numerator data.
* `linear_phase_variation_components`, `linear_phase_variation_components_regular` —
  `eq:linear-phase-variation` over the components of `(0,π/r) ∖ {W = 0}`, the manuscript's own
  left-hand side, with the zeros of `B` allowed to lie **on** the arc.

## Implementation notes

`linear_phase_variation_of_arc` and `linear_phase_variation_regular` bound the variation of one
branch over one set, so they ask that no zero of `B` lie **on** the arc — there is no branch at
such a parameter.  `linear_phase_variation_components_regular` drops that: it sums over an
ordered family of components, each root of `B` is taken in whichever of the two states it is in,
and `ViewingAngle.viewing_angle_bound_on_arc` supplies the met case.  What the caller supplies
is the family and, per root, which branch each component carries; the constants are the same
`κ₀` and `κ₁ = 𝒦_γ + π`, and neither sees `B`.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues, and
the principal amplitude» (`sec:geometry`, `cor:linear-phase-variation`), and states the
numerator-uniform shape that `thm:main` clause 3 asks for.

## Tags

linear phase variation, numerator-uniform defect, weight polynomial
-/

namespace ForgacsTran

open Real Set Finset

/-! ### Subadditivity of the variation -/

private theorem edist_add_add_le_real (a b c d : ℝ) :
    edist (a + b) (c + d) ≤ edist a c + edist b d := by
  rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [Real.dist_eq]
  calc |a + b - (c + d)| = |(a - c) + (b - d)| := by ring_nf
    _ ≤ |a - c| + |b - d| := abs_add_le _ _

theorem eVariationOn_add_le (f g : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i))
      ≤ ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => edist_add_add_le_real _ _ _ _
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))
          + ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le hu us) (eVariationOn.sum_le hu us)

theorem eVariationOn_zero (s : Set ℝ) : eVariationOn (fun _ : ℝ => (0:ℝ)) s = 0 := by
  refine eVariationOn.constant_on ?_
  rintro x ⟨a, -, rfl⟩ y ⟨b, -, rfl⟩
  rfl

theorem eVariationOn_finsetSum_le {ι : Type*} (t : Finset ι) (ψ : ι → ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => ∑ ℓ ∈ t, ψ ℓ x) s ≤ ∑ ℓ ∈ t, eVariationOn (ψ ℓ) s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [eVariationOn_zero]
  | insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      exact le_trans (eVariationOn_add_le _ _ _) (by gcongr)

/-! ### `cor:linear-phase-variation` -/

/-- Paper `cor:linear-phase-variation`, `eq:linear-phase-variation`.  A continuous branch of
`arg W` is the denominator factor's branch `ψ₀` plus one branch `ψ ℓ` per zero of `B`.  Each
`ψ ℓ` obeys Radon's bound against the same tangent-angle variation `𝒦_γ`, so the total is at
most `κ₀ + κ₁ K` with `κ₁ = 𝒦_γ + π` and `K = deg B`.

Neither constant mentions `B`: `κ₀` is the variation of the denominator factor and `κ₁` is a
constant of the principal arc.  That is the content of the corollary — the bound is linear in
`deg B` *uniformly over numerators of a given degree*.

**Differs from the paper's route.**  `eq:linear-phase-variation` bounds the summed variations
over the components of `(0, π/r)` with the zeros of `W` deleted; here the bound is on the
variation of one branch over one set, and `ClauseThree.sum_abs_sub_le_of_eVariationOn`
recovers the component increments from it.  `eVariationOn` is defined on a set, so the summed
form is the derived one.

**Differs from the paper's route.**  Second difference, and an independent one — this is about
what the regularity hypothesis costs, not about how the variation is summed.  The manuscript
*derives* finite total variation: `W` differs near each endpoint from a real-analytic nonvanishing
function by the positive factor `δ^p` alone, which contributes nothing to the argument, so
a continuous branch is real-analytic on the closed interval and hence of finite variation.
Here that conclusion is taken outright, as `h0 : eVariationOn ψ_0 s ≤ κ_0` — bounded
variation, which is strictly weaker than analyticity, sufficient for everything downstream, and
never discharged from analyticity anywhere in the tree.  So `κ_0` is the paper's own
conclusion assumed, not an unmet analytic input: `lem:amplitude-divisor`'s `V` needs bounded
variation here, not the real-analyticity that lemma asserts. -/
theorem linear_phase_variation
    {ϑ ψ₀ : ℝ → ℝ} {s : Set ℝ} {K : ℕ} {ψ : Fin K → ℝ → ℝ} {κ₀ Kγ : ℝ}
    (hκ₀ : 0 ≤ κ₀) (hKγ : 0 ≤ Kγ)
    (hϑ : eVariationOn ϑ s ≤ ENNReal.ofReal Kγ)
    (h0 : eVariationOn ψ₀ s ≤ ENNReal.ofReal κ₀)
    (hroots : ∀ ℓ, eVariationOn (ψ ℓ) s ≤ eVariationOn ϑ s + ENNReal.ofReal π) :
    eVariationOn (fun x => ψ₀ x + ∑ ℓ, ψ ℓ x) s
      ≤ ENNReal.ofReal (κ₀ + (Kγ + π) * K) := by
  have hstep : ∀ ℓ, eVariationOn (ψ ℓ) s ≤ ENNReal.ofReal (Kγ + π) := by
    intro ℓ
    refine (hroots ℓ).trans ?_
    rw [ENNReal.ofReal_add hKγ Real.pi_pos.le]
    gcongr
  have hsum : eVariationOn (fun x => ∑ ℓ, ψ ℓ x) s
      ≤ ENNReal.ofReal ((Kγ + π) * K) := by
    refine (eVariationOn_finsetSum_le Finset.univ ψ s).trans ?_
    calc ∑ ℓ : Fin K, eVariationOn (ψ ℓ) s
        ≤ ∑ _ℓ : Fin K, ENNReal.ofReal (Kγ + π) := Finset.sum_le_sum fun ℓ _ => hstep ℓ
      _ = (K : ℕ) • ENNReal.ofReal (Kγ + π) := by simp
      _ = ENNReal.ofReal ((Kγ + π) * K) := by
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast K,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg K)]
          ring_nf
  calc eVariationOn (fun x => ψ₀ x + ∑ ℓ, ψ ℓ x) s
      ≤ eVariationOn ψ₀ s + eVariationOn (fun x => ∑ ℓ, ψ ℓ x) s :=
        eVariationOn_add_le _ _ _
    _ ≤ ENNReal.ofReal κ₀ + ENNReal.ofReal ((Kγ + π) * K) := add_le_add h0 hsum
    _ = ENNReal.ofReal (κ₀ + (Kγ + π) * K) :=
        (ENNReal.ofReal_add hκ₀ (by positivity)).symm

/-- Paper `cor:linear-phase-variation` at the reduced numerator of
`eq:canonical-Laurent-factorization`: the summed phase variation of `W` is at most
`κ₀ + κ₁ deg B_N`, with `κ₀` and `κ₁ = 𝒦_γ + π` independent of `N`. -/
theorem phase_variation_le_laurentWeight
    {Q : Polynomial ℝ} {r : ℕ} {N : Polynomial (Polynomial ℝ)} {ϑ ψ₀ : ℝ → ℝ} {s : Set ℝ}
    {ψ : Fin (laurentWeight Q r N).natDegree → ℝ → ℝ} {κ₀ Kγ : ℝ}
    (hκ₀ : 0 ≤ κ₀) (hKγ : 0 ≤ Kγ)
    (hϑ : eVariationOn ϑ s ≤ ENNReal.ofReal Kγ)
    (h0 : eVariationOn ψ₀ s ≤ ENNReal.ofReal κ₀)
    (hroots : ∀ ℓ, eVariationOn (ψ ℓ) s ≤ eVariationOn ϑ s + ENNReal.ofReal π) :
    eVariationOn (fun x => ψ₀ x + ∑ ℓ, ψ ℓ x) s
      ≤ ENNReal.ofReal (κ₀ + (Kγ + π) * (laurentWeight Q r N).natDegree) :=
  linear_phase_variation hκ₀ hKγ hϑ h0 hroots

/-! ### The numerator-uniform shape of `thm:main` clause 3 -/

/-- Paper `thm:main` clause 3.  A defect constant is *numerator-uniform* when it is bounded
by `C₀ + C₁ deg B_N` with `C₀`, `C₁` fixed before `N`.  `eq:angular-distinct-lower`,
`eq:angular-discrepancy` and `eq:angular-clock` all assert a bound of this shape. -/
def NumeratorUniform (Q : Polynomial ℝ) (r : ℕ) (F : Polynomial (Polynomial ℝ) → ℕ) : Prop :=
  ∃ C₀ C₁ : ℕ, ∀ N, F N ≤ C₀ + C₁ * (laurentWeight Q r N).natDegree

/-- A real linear bound with numerator-independent constants gives the `ℕ`-valued shape, at
`C₀ = ⌈κ₀⌉₊` and `C₁ = ⌈κ₁⌉₊`.  This is the step that turns `eq:linear-phase-variation` into
a defect constant `main_bound_interval` can consume. -/
theorem numeratorUniform_of_le {Q : Polynomial ℝ} {r : ℕ} {F : Polynomial (Polynomial ℝ) → ℕ}
    {κ₀ κ₁ : ℝ}
    (h : ∀ N, (F N : ℝ) ≤ κ₀ + κ₁ * ((laurentWeight Q r N).natDegree : ℝ)) :
    NumeratorUniform Q r F := by
  refine ⟨⌈κ₀⌉₊, ⌈κ₁⌉₊, fun N => ?_⟩
  have hd : (0:ℝ) ≤ ((laurentWeight Q r N).natDegree : ℝ) := Nat.cast_nonneg _
  have h1 : (F N : ℝ)
      ≤ (⌈κ₀⌉₊ : ℝ) + (⌈κ₁⌉₊ : ℝ) * ((laurentWeight Q r N).natDegree : ℝ) := by
    refine (h N).trans ?_
    gcongr
    · exact Nat.le_ceil _
    · exact Nat.le_ceil _
  exact_mod_cast h1

/-- Composed with `eq:reduced-degree-complexity`, a numerator-uniform constant is also linear
in the raw numerator data: `deg B_N ≤ p_N + E_N max{q, r}`. -/
theorem numeratorUniform_natDegree_le {Q : Polynomial ℝ} {r : ℕ} {F : Polynomial (Polynomial ℝ) → ℕ}
    (hF : NumeratorUniform Q r F) (hr : 1 ≤ r) (hQ0 : Q.coeff 0 ≠ 0) :
    ∃ C₀ C₁ : ℕ, ∀ (N : Polynomial (Polynomial ℝ)), N ≠ 0 →
      (∀ β, (N.coeff β).degree < ((max Q.natDegree r : ℕ) : WithBot ℕ)) →
      ∀ p E : ℕ, (∀ β, (N.coeff β).natDegree ≤ p) → N.natDegree ≤ E →
      F N ≤ C₀ + C₁ * (p + E * max Q.natDegree r) := by
  obtain ⟨C₀, C₁, hC⟩ := hF
  refine ⟨C₀, C₁, fun N hN hproper p E hp hE => ?_⟩
  refine (hC N).trans ?_
  have := natDegree_laurentWeight_le Q hr hQ0 hN hproper hp hE
  exact Nat.add_le_add_left (Nat.mul_le_mul_left C₁ this) C₀


/-! ### The corollary with no per-root hypothesis

`linear_phase_variation` takes a per-root Radon bound as a hypothesis.  It need not: the
branches are `ViewingAngle.polarAngle`, one per zero of `B`, and `viewing_angle_bound_arc`
bounds each of them from the arc's regularity alone.  Below, `hroots` is discharged. -/

private theorem multiset_sum_map_le {ι : Type*} (m : Multiset ι) (f : ι → ENNReal) (C : ENNReal)
    (h : ∀ ℓ ∈ m, f ℓ ≤ C) : (m.map f).sum ≤ Multiset.card m • C := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      calc f a + (t.map f).sum
          ≤ C + Multiset.card t • C :=
            add_le_add (h a (Multiset.mem_cons_self a t))
              (ih fun ℓ hℓ => h ℓ (Multiset.mem_cons_of_mem hℓ))
        _ = (Multiset.card t + 1) • C := by rw [add_smul, one_smul, add_comm]

theorem eVariationOn_multisetSum_le {ι : Type*} (m : Multiset ι) (ψ : ι → ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => (m.map (fun ℓ => ψ ℓ x)).sum) s
      ≤ (m.map (fun ℓ => eVariationOn (ψ ℓ) s)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp [eVariationOn_zero]
  | cons a t ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact le_trans (eVariationOn_add_le _ _ _) (by gcongr)

/-- `eq:linear-phase-variation` over a multiset of zeros, so the count on the right is the
multiset's cardinality rather than an abstract `K`. -/
theorem linear_phase_variation_multiset
    {ϑ ψ₀ : ℝ → ℝ} {s : Set ℝ} {ι : Type*} {m : Multiset ι} {ψ : ι → ℝ → ℝ} {κ₀ Kγ : ℝ}
    (hκ₀ : 0 ≤ κ₀) (hKγ : 0 ≤ Kγ)
    (hϑ : eVariationOn ϑ s ≤ ENNReal.ofReal Kγ)
    (h0 : eVariationOn ψ₀ s ≤ ENNReal.ofReal κ₀)
    (hroots : ∀ ℓ ∈ m, eVariationOn (ψ ℓ) s ≤ eVariationOn ϑ s + ENNReal.ofReal π) :
    eVariationOn (fun x => ψ₀ x + (m.map (fun ℓ => ψ ℓ x)).sum) s
      ≤ ENNReal.ofReal (κ₀ + (Kγ + π) * Multiset.card m) := by
  have hstep : ∀ ℓ ∈ m, eVariationOn (ψ ℓ) s ≤ ENNReal.ofReal (Kγ + π) := by
    intro ℓ hℓ
    refine (hroots ℓ hℓ).trans ?_
    rw [ENNReal.ofReal_add hKγ Real.pi_pos.le]
    gcongr
  have hsum : eVariationOn (fun x => (m.map (fun ℓ => ψ ℓ x)).sum) s
      ≤ ENNReal.ofReal ((Kγ + π) * Multiset.card m) := by
    refine (eVariationOn_multisetSum_le m ψ s).trans ?_
    refine (multiset_sum_map_le m _ _ hstep).trans ?_
    rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast (Multiset.card m),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact le_of_eq (by rw [mul_comm])
  calc eVariationOn (fun x => ψ₀ x + (m.map (fun ℓ => ψ ℓ x)).sum) s
      ≤ eVariationOn ψ₀ s + eVariationOn (fun x => (m.map (fun ℓ => ψ ℓ x)).sum) s :=
        eVariationOn_add_le _ _ _
    _ ≤ ENNReal.ofReal κ₀ + ENNReal.ofReal ((Kγ + π) * Multiset.card m) := add_le_add h0 hsum
    _ = ENNReal.ofReal (κ₀ + (Kγ + π) * Multiset.card m) :=
        (ENNReal.ofReal_add hκ₀ (by positivity)).symm

/-- Paper `cor:linear-phase-variation`, `eq:linear-phase-variation`, with the per-root bound
discharged.  `arg B(γ)` is the sum, over the zeros of `B` with multiplicity, of the branches
`polarAngle γ dγ β a`; `viewing_angle_bound_arc` caps each at `𝒦_γ + π`, so the total phase
variation is at most `κ₀ + (𝒦_γ + π) deg B`, with both constants independent of `B`.

Nothing about the branches is hypothesized.  What is asked is the arc's regularity, that no
zero of `B` lies **on** the arc, and that each viewing angle has finitely many critical points
— the package the manuscript takes from `thm:FT-geometry` and
`lem:principal-endpoint-regularity` rather than proving. -/
theorem linear_phase_variation_of_arc
    {γ dγ : ℝ → ℂ} {ν ϑ ψ₀ : ℝ → ℝ} {U : Set ℝ} {a b : ℝ} {κ₀ Kγ : ℝ}
    {B : Polynomial ℂ}
    (hab : a ≤ b) (hU : IsOpen U) (hsub : Set.Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hc : ContinuousOn dγ U)
    (hϑc : ContinuousOn ϑ (Set.Icc a b)) (hνpos : ∀ s ∈ Set.Icc a b, 0 ≤ ν s)
    (htan : ∀ s ∈ Set.Icc a b, dγ s = (ν s : ℂ) * Complex.exp ((ϑ s : ℂ) * Complex.I))
    (hoff : ∀ β ∈ B.roots, ∀ s ∈ Set.Icc a b, γ s ≠ β)
    (hκ₀ : 0 ≤ κ₀) (hKγ : 0 ≤ Kγ)
    (hϑ : eVariationOn ϑ (Set.Icc a b) ≤ ENNReal.ofReal Kγ)
    (h0 : eVariationOn ψ₀ (Set.Icc a b) ≤ ENNReal.ofReal κ₀)
    (S : ℂ → Finset ℝ) (hSsub : ∀ β, ∀ x ∈ S β, x ∈ Set.Icc a b)
    (hS : ∀ β ∈ B.roots, ∀ x ∈ Set.Ioo a b, ∀ m : ℤ,
        ϑ x - polarAngle γ dγ β a x = (m : ℝ) * π → x ∈ S β) :
    eVariationOn (fun x => ψ₀ x + (B.roots.map (fun β => polarAngle γ dγ β a x)).sum)
        (Set.Icc a b)
      ≤ ENNReal.ofReal (κ₀ + (Kγ + π) * B.natDegree) := by
  have hcard : Multiset.card B.roots = B.natDegree :=
    ((_root_.IsAlgClosed.splits B).natDegree_eq_card_roots).symm
  have hroots : ∀ β ∈ B.roots,
      eVariationOn (polarAngle γ dγ β a) (Set.Icc a b)
        ≤ eVariationOn ϑ (Set.Icc a b) + ENNReal.ofReal π := fun β hβ =>
    viewing_angle_bound_arc hab hU hsub hd hc (hoff β hβ) hϑc hνpos htan
      (S β) (hSsub β) (hS β hβ)
  have := linear_phase_variation_multiset (ψ := fun β => polarAngle γ dγ β a)
    hκ₀ hKγ hϑ h0 hroots
  rwa [hcard] at this


/-- Paper `cor:linear-phase-variation` at the reduced numerator of
`eq:canonical-Laurent-factorization`, with every per-root hypothesis discharged: the total
phase variation is at most `κ₀ + (𝒦_γ + π) deg B_N`.

This is the linearity `thm:main` clause 3 needs.  `κ₀` is the variation of the denominator
factor of `eq:W-on-g` and `κ₁ = 𝒦_γ + π` is a constant of the principal arc; neither mentions
`N`.  What is still hypothesized is the arc — `thm:FT-geometry` and
`lem:principal-endpoint-regularity`, which the manuscript cites rather than proves — and that
no zero of `B_N` lies on the arc. -/
theorem phase_variation_le_laurentWeight_of_arc
    {γ dγ : ℝ → ℂ} {ν ϑ ψ₀ : ℝ → ℝ} {U : Set ℝ} {a b : ℝ} {κ₀ Kγ : ℝ}
    {Q : Polynomial ℝ} {r : ℕ} {N : Polynomial (Polynomial ℝ)}
    (hab : a ≤ b) (hU : IsOpen U) (hsub : Set.Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s) (hc : ContinuousOn dγ U)
    (hϑc : ContinuousOn ϑ (Set.Icc a b)) (hνpos : ∀ s ∈ Set.Icc a b, 0 ≤ ν s)
    (htan : ∀ s ∈ Set.Icc a b, dγ s = (ν s : ℂ) * Complex.exp ((ϑ s : ℂ) * Complex.I))
    (hoff : ∀ β ∈ ((laurentWeight Q r N).map (algebraMap ℝ ℂ)).roots,
        ∀ s ∈ Set.Icc a b, γ s ≠ β)
    (hκ₀ : 0 ≤ κ₀) (hKγ : 0 ≤ Kγ)
    (hϑ : eVariationOn ϑ (Set.Icc a b) ≤ ENNReal.ofReal Kγ)
    (h0 : eVariationOn ψ₀ (Set.Icc a b) ≤ ENNReal.ofReal κ₀)
    (S : ℂ → Finset ℝ) (hSsub : ∀ β, ∀ x ∈ S β, x ∈ Set.Icc a b)
    (hS : ∀ β ∈ ((laurentWeight Q r N).map (algebraMap ℝ ℂ)).roots,
        ∀ x ∈ Set.Ioo a b, ∀ m : ℤ,
        ϑ x - polarAngle γ dγ β a x = (m : ℝ) * π → x ∈ S β) :
    eVariationOn (fun x => ψ₀ x
        + ((((laurentWeight Q r N).map (algebraMap ℝ ℂ)).roots).map
            (fun β => polarAngle γ dγ β a x)).sum) (Set.Icc a b)
      ≤ ENNReal.ofReal (κ₀ + (Kγ + π) * (laurentWeight Q r N).natDegree) := by
  have hdeg : (((laurentWeight Q r N).map (algebraMap ℝ ℂ))).natDegree
      = (laurentWeight Q r N).natDegree :=
    Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective _
  have := linear_phase_variation_of_arc (B := (laurentWeight Q r N).map (algebraMap ℝ ℂ))
    hab hU hsub hd hc hϑc hνpos htan hoff hκ₀ hKγ hϑ h0 S hSsub hS
  rwa [hdeg] at this


/-- Paper `cor:linear-phase-variation` for a regular arc, with nothing about any argument
branch hypothesized.  Every branch — the tangent angle and one viewing angle per zero of `B`
— is built by `ViewingAngle.logLift`, and each is capped by `viewing_angle_bound_regular`.

The hypotheses left are the arc's (`γ ∈ C²` on an open set carrying the interval, `γ' ≠ 0`),
that no zero of `B` lies **on** the arc, the finiteness of each viewing angle's critical set,
and the two constants: `Kγ` bounding the tangent-angle variation, `κ₀` bounding the
denominator factor's.  Those are `thm:FT-geometry` and `lem:principal-endpoint-regularity`,
which the manuscript takes from `Forgacs2017RationalDenominator` rather than proving. -/
theorem linear_phase_variation_regular
    {γ dγ d2γ : ℝ → ℂ} {ψ₀ : ℝ → ℝ} {U : Set ℝ} {a b : ℝ} {κ₀ Kγ : ℝ}
    {B : Polynomial ℂ}
    (hab : a ≤ b) (hU : IsOpen U) (hsub : Set.Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Set.Icc a b, dγ s ≠ 0)
    (hoff : ∀ β ∈ B.roots, ∀ s ∈ Set.Icc a b, γ s ≠ β)
    (hκ₀ : 0 ≤ κ₀) (hKγ : 0 ≤ Kγ)
    (hKvar : eVariationOn (polarAngle dγ d2γ 0 a) (Set.Icc a b) ≤ ENNReal.ofReal Kγ)
    (h0 : eVariationOn ψ₀ (Set.Icc a b) ≤ ENNReal.ofReal κ₀)
    (S : ℂ → Finset ℝ) (hSsub : ∀ β, ∀ x ∈ S β, x ∈ Set.Icc a b)
    (hS : ∀ β ∈ B.roots, ∀ x ∈ Set.Ioo a b, ∀ m : ℤ,
        polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = (m : ℝ) * π → x ∈ S β) :
    eVariationOn (fun x => ψ₀ x + (B.roots.map (fun β => polarAngle γ dγ β a x)).sum)
        (Set.Icc a b)
      ≤ ENNReal.ofReal (κ₀ + (Kγ + π) * B.natDegree) := by
  have hcard : Multiset.card B.roots = B.natDegree :=
    ((_root_.IsAlgClosed.splits B).natDegree_eq_card_roots).symm
  have hroots : ∀ β ∈ B.roots,
      eVariationOn (polarAngle γ dγ β a) (Set.Icc a b)
        ≤ eVariationOn (polarAngle dγ d2γ 0 a) (Set.Icc a b) + ENNReal.ofReal π := fun β hβ =>
    viewing_angle_bound_regular hab hU hsub hd hd2 hc2 hreg (hoff β hβ)
      (S β) (hSsub β) (hS β hβ)
  have hmain := linear_phase_variation_multiset (ψ := fun β => polarAngle γ dγ β a)
    hκ₀ hKγ hKvar h0 hroots
  rwa [hcard] at hmain


/-! ### `eq:linear-phase-variation` over the components, the manuscript's own form

`cor:linear-phase-variation` sums over the components of `(0,π/r) ∖ {W = 0}`, which
`lem:amplitude-divisor` identifies with the parameters where `B ∘ γ` vanishes.  A zero of `B`
that the arc *meets* has no argument branch at that parameter, so the corollary above — which
asks that no zero lie on the arc — does not reach that case.  Here it does: the components are
carried as an ordered family, each root's summed contribution is capped by
`eq:viewing-angle-bound`, and `Shields.eVariationOn_finsetSum_le` is what makes a family finer
than one root's own components cost no more than those. -/

private theorem finset_multiset_sum_comm {ι κ : Type*} (m : Multiset κ) (t : Finset ι)
    (f : κ → ι → ENNReal) :
    ∑ i ∈ t, (m.map (fun β => f β i)).sum = (m.map (fun β => ∑ i ∈ t, f β i)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ← ih, Finset.sum_add_distrib]

/-- Paper `cor:linear-phase-variation`, `eq:linear-phase-variation`, summed over an ordered
family of components — the manuscript's own left-hand side.  The branch of `arg W` on the
`i`-th component is `ψ₀` plus one branch `ψ β i` per zero of `B`, and the branch may differ
from component to component, which is exactly what a zero met by the arc forces.

Neither constant mentions `B`.  `κ₀` bounds the denominator factor's variation over the whole
parameter interval, so the components share it rather than each paying it; `κ₁ = 𝒦_γ + π`
comes from the per-root hypothesis, which is `eq:viewing-angle-bound` summed over the same
family.

**Containment.**  No hypothesis mentions both a component's variation of the full branch and
the bound `κ₀ + κ₁ deg B`: `h0` sees only `ψ₀`, `hroots` only one root's family, and `hJ`,
`hord` only the sets. -/
theorem linear_phase_variation_components
    {ψ₀ : ℝ → ℝ} {J : ℕ → Set ℝ} {ψ : ℂ → ℕ → ℝ → ℝ} {κ₀ Kγ : ℝ} {B : Polynomial ℂ}
    {s : Set ℝ} (t : Finset ℕ)
    (hκ₀ : 0 ≤ κ₀) (hKγ : 0 ≤ Kγ)
    (hJ : ∀ i ∈ t, J i ⊆ s)
    (hord : ∀ i ∈ t, ∀ j ∈ t, i < j → ∀ x ∈ J i, ∀ y ∈ J j, x ≤ y)
    (h0 : eVariationOn ψ₀ s ≤ ENNReal.ofReal κ₀)
    (hroots : ∀ β ∈ B.roots,
      ∑ i ∈ t, eVariationOn (ψ β i) (J i) ≤ ENNReal.ofReal (Kγ + π)) :
    ∑ i ∈ t, eVariationOn (fun x => ψ₀ x + (B.roots.map (fun β => ψ β i x)).sum) (J i)
      ≤ ENNReal.ofReal (κ₀ + (Kγ + π) * B.natDegree) := by
  have hcard : Multiset.card B.roots = B.natDegree :=
    ((_root_.IsAlgClosed.splits B).natDegree_eq_card_roots).symm
  have hKπ : (0 : ℝ) ≤ Kγ + π := by linarith [Real.pi_pos]
  have hstep : ∀ i ∈ t,
      eVariationOn (fun x => ψ₀ x + (B.roots.map (fun β => ψ β i x)).sum) (J i)
        ≤ eVariationOn ψ₀ (J i)
          + (B.roots.map (fun β => eVariationOn (ψ β i) (J i))).sum := by
    intro i _
    exact le_trans (eVariationOn_add_le ψ₀ (fun x => (B.roots.map (fun β => ψ β i x)).sum) (J i))
      (add_le_add le_rfl (eVariationOn_multisetSum_le B.roots (fun β => ψ β i) (J i)))
  have hA : (∑ i ∈ t, eVariationOn ψ₀ (J i)) ≤ ENNReal.ofReal κ₀ :=
    le_trans (eVariationOn_sum_le t s hJ hord) h0
  have hB : (∑ i ∈ t, (B.roots.map (fun β => eVariationOn (ψ β i) (J i))).sum)
      ≤ ENNReal.ofReal ((Kγ + π) * B.natDegree) := by
    rw [finset_multiset_sum_comm]
    refine le_trans (multiset_sum_map_le B.roots
      (fun β => ∑ i ∈ t, eVariationOn (ψ β i) (J i)) (ENNReal.ofReal (Kγ + π)) hroots) ?_
    rw [nsmul_eq_mul, hcard, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact le_of_eq (by rw [mul_comm])
  have hsum : ∑ i ∈ t, eVariationOn (fun x => ψ₀ x + (B.roots.map (fun β => ψ β i x)).sum) (J i)
      ≤ (∑ i ∈ t, eVariationOn ψ₀ (J i))
        + ∑ i ∈ t, (B.roots.map (fun β => eVariationOn (ψ β i) (J i))).sum := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hstep
  refine le_trans hsum (le_trans (add_le_add hA hB) (le_of_eq ?_))
  rw [← ENNReal.ofReal_add hκ₀ (by positivity)]

/-- Paper `cor:linear-phase-variation` for a regular arc, over the components, with every
per-root hypothesis discharged and **no assumption that the zeros of `B` miss the arc**.

Each zero is handled in whichever of the two states it is in.  A zero the arc misses keeps one
branch across every component and costs `𝒦_γ + π`.  A zero the arc meets at `m` carries the
branch based at `a` on the components left of `m` and the branch based at `b` on those right of
it — the two components of `[a,b] ∖ γ⁻¹({β})` — and costs `𝒦_γ`, which is below the same cap.
An injective arc has at most one such `m` per zero, which is why the second state names a
single parameter. -/
theorem linear_phase_variation_components_regular
    {γ dγ d2γ : ℝ → ℂ} {ψ₀ : ℝ → ℝ} {U : Set ℝ} {a b : ℝ} {κ₀ Kγ : ℝ}
    {B : Polynomial ℂ} {J : ℕ → Set ℝ} {ψ : ℂ → ℕ → ℝ → ℝ} (t : Finset ℕ)
    (hab : a ≤ b) (hU : IsOpen U) (hsub : Set.Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Set.Icc a b, dγ s ≠ 0)
    (hκ₀ : 0 ≤ κ₀) (hKγ : 0 ≤ Kγ)
    (hKvar : eVariationOn (polarAngle dγ d2γ 0 a) (Set.Icc a b) ≤ ENNReal.ofReal Kγ)
    (h0 : eVariationOn ψ₀ (Set.Icc a b) ≤ ENNReal.ofReal κ₀)
    (hJ : ∀ i ∈ t, J i ⊆ Set.Icc a b)
    (hord : ∀ i ∈ t, ∀ j ∈ t, i < j → ∀ x ∈ J i, ∀ y ∈ J j, x ≤ y)
    (hbranch : ∀ β ∈ B.roots,
      (∃ S : Finset ℝ, (∀ x ∈ Set.Icc a b, γ x ≠ β) ∧ (∀ x ∈ S, x ∈ Set.Icc a b)
          ∧ (∀ x ∈ Set.Ioo a b, ∀ k : ℤ,
              polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = (k : ℝ) * π → x ∈ S)
          ∧ ∀ i ∈ t, ψ β i = polarAngle γ dγ β a)
      ∨ (∃ m, a ≤ m ∧ m ≤ b ∧ ∃ S₁ S₂ : Finset ℝ, γ m = β
          ∧ (∀ x ∈ Set.Icc a b, x ≠ m → γ x ≠ β)
          ∧ (∀ x ∈ Set.Ioo a m, ∀ k : ℤ,
              polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = (k : ℝ) * π → x ∈ S₁)
          ∧ (∀ x ∈ Set.Ioo m b, ∀ k : ℤ,
              polarAngle dγ d2γ 0 a x - polarAngle γ dγ β b x = (k : ℝ) * π → x ∈ S₂)
          ∧ ∀ i ∈ t, (J i ⊆ Set.Ico a m ∧ ψ β i = polarAngle γ dγ β a)
              ∨ (J i ⊆ Set.Ioc m b ∧ ψ β i = polarAngle γ dγ β b))) :
    ∑ i ∈ t, eVariationOn (fun x => ψ₀ x + (B.roots.map (fun β => ψ β i x)).sum) (J i)
      ≤ ENNReal.ofReal (κ₀ + (Kγ + π) * B.natDegree) := by
  refine linear_phase_variation_components t hκ₀ hKγ hJ hord h0 fun β hβ => ?_
  have hKπ : ENNReal.ofReal Kγ + ENNReal.ofReal π = ENNReal.ofReal (Kγ + π) :=
    (ENNReal.ofReal_add hKγ Real.pi_pos.le).symm
  rcases hbranch β hβ with ⟨S, hne, hSsub, hS, hψ⟩ | ⟨m, ham, hmb, S₁, S₂, hm, hne, hS₁, hS₂, hside⟩
  · have heq : ∑ i ∈ t, eVariationOn (ψ β i) (J i)
        = ∑ i ∈ t, eVariationOn (polarAngle γ dγ β a) (J i) :=
      Finset.sum_congr rfl fun i hi => by rw [hψ i hi]
    rw [heq, ← hKπ]
    refine le_trans (viewing_angle_bound_components_off_arc hab hU hsub hd hd2 hc2 hreg hne
      S hSsub hS t hJ hord) ?_
    gcongr
  · refine le_trans (viewing_angle_bound_components_of_meet ham hmb hU hsub hd hd2 hc2 hreg
      hm hne S₁ S₂ hS₁ hS₂ t hside hord) ?_
    exact le_trans hKvar (ENNReal.ofReal_le_ofReal (by linarith [Real.pi_pos]))

/-! ### `FTPhaseSupply`'s own shape

`linear_phase_variation_components` above delivers the summed variation as an
`ENNReal`.  `AngularDiscrepancyFT.FTPhaseSupply` states its variation clause with
reals, so the two are one conversion apart, and that conversion is here rather
than at the consumer because the finiteness it needs is a fact about this
bound. -/

/-- **`FTPhaseSupply`'s variation clause, from the summed `eVariationOn` bound.**
The supply asks for reals `varψ i` dominating each block's phase increment and
summing under `κ₀ + κ₁·deg B`; the variation machinery delivers an `ENNReal`
bound on the summed variation.  This is the conversion, and the finiteness it
needs comes from the bound itself rather than being assumed — each term is under
a finite sum of nonnegatives.

**The per-block cap that must not be used.**  Bounding each block separately by
`κ₀ + κ₁·deg B` and summing gives `(J+1)(κ₀ + κ₁·deg B)`, quadratic in `deg B`
once `J ≤ deg B`, which destroys exactly the uniformity `cor:linear-phase-variation`
exists for.  The summed bound has to come in already summed, which is what
`linear_phase_variation_components` provides and why this takes it in that
form. -/
theorem exists_varPhase_of_sum_eVariationOn {k : ℕ} {ψ : Fin k → ℝ → ℝ}
    {Lb Rb : Fin k → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hsum : ∑ i, eVariationOn (ψ i) (Icc (Lb i) (Rb i)) ≤ ENNReal.ofReal K) :
    ∃ varψ : Fin k → ℝ, (∀ i, 0 ≤ varψ i) ∧
      (∀ i, Lb i ≤ Rb i → |ψ i (Rb i) - ψ i (Lb i)| ≤ varψ i) ∧
      ∑ i, varψ i ≤ K := by
  classical
  have hfin : ∀ i : Fin k, eVariationOn (ψ i) (Icc (Lb i) (Rb i)) ≠ ⊤ := by
    intro i
    have hle : eVariationOn (ψ i) (Icc (Lb i) (Rb i))
        ≤ ∑ j, eVariationOn (ψ j) (Icc (Lb j) (Rb j)) :=
      Finset.single_le_sum (f := fun j => eVariationOn (ψ j) (Icc (Lb j) (Rb j)))
        (fun j _ => zero_le) (Finset.mem_univ i)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans hle hsum)
  refine ⟨fun i => (eVariationOn (ψ i) (Icc (Lb i) (Rb i))).toReal,
    fun i => ENNReal.toReal_nonneg, ?_, ?_⟩
  · intro i hi
    have hmemL : Lb i ∈ Icc (Lb i) (Rb i) := ⟨le_rfl, hi⟩
    have hmemR : Rb i ∈ Icc (Lb i) (Rb i) := ⟨hi, le_rfl⟩
    have hed := eVariationOn.edist_le (ψ i) hmemR hmemL
    rw [edist_dist, Real.dist_eq] at hed
    have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (hfin i)).2 hed
    rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at this
  · rw [← ENNReal.toReal_sum (fun i _ => hfin i)]
    have := (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum) ENNReal.ofReal_ne_top).2 hsum
    rwa [ENNReal.toReal_ofReal hK] at this

end ForgacsTran
