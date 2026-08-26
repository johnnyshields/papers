/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# Quasi-orthogonality and the Shohat zero count

Nothing here mentions the pencil.  The two layers are:

## Main statements

* `card_oddOrderRoots_ge` — the actual content, and it needs no orthogonal
  system: a nonzero real polynomial orthogonal against a positive weight to
  every polynomial of degree below `n` has at least `n` odd-order zeros in
  `(a,b)`.  The proof is Durán's: multiply by the monic polynomial carrying
  those zeros, observe the product no longer changes sign, and read off that
  its weighted integral cannot vanish.
* `card_oddOrderRoots_linearCombination_ge` — the cited statement, obtained by
  supplying orthogonality to lower degrees from the system's own relations.

## Implementation notes

The supporting halves are `eval_mul_eval_nonneg_of_even_rootMultiplicity` (a
real polynomial whose zeros in an interval all have even order does not change
sign there) and `exists_repr_of_natDegree_le` (a degree-graded family spans).

Sorry-free.

## References

Formalizes the third-party input cited at `rem:quadratic-case` of
`../shields-2026-forgacs-tran-numerators.tex`: Shohat's theorem in the form
`Duran2026LinearCombinations` gives it, that a fixed combination of `K+1`
consecutive members of an orthogonal polynomial system,
`q = ∑_{j≤K} γ_j p_{n-j}` with `γ_0 ≠ 0`, vanishes to odd order at
at least `n - K` points of the convex hull of the support.

## Tags

quasi-orthogonality, Shohat zero count, three-term recurrence
-/

namespace ForgacsTran

open Polynomial MeasureTheory

/-! ### Even root order forbids a sign change -/

private theorem eval_mul_eval_nonneg_aux (a b : ℝ) :
    ∀ (N : ℕ) (f : Polynomial ℝ), f.natDegree ≤ N → f ≠ 0 →
      (∀ ζ ∈ Set.Ioo a b, Even (f.rootMultiplicity ζ)) →
      ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, 0 ≤ f.eval x * f.eval y := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro f hdeg hf heven x hx y hy
    by_cases hroot : ∃ ξ ∈ Set.Ioo a b, f.eval ξ = 0
    · obtain ⟨ξ, hξ, hξ0⟩ := hroot
      have hmpos : 0 < f.rootMultiplicity ξ := (rootMultiplicity_pos hf).2 hξ0
      have hme : Even (f.rootMultiplicity ξ) := heven ξ hξ
      set m := f.rootMultiplicity ξ with hm
      have hm2 : 2 ≤ m := by rcases hme with ⟨k, hk⟩; omega
      set g : Polynomial ℝ := f /ₘ (X - C ξ) ^ m with hgdef
      have hfac : (X - C ξ) ^ m * g = f := pow_mul_divByMonic_rootMultiplicity_eq f ξ
      have hgne : g ≠ 0 := by
        intro h; rw [h, mul_zero] at hfac; exact hf hfac.symm
      have hXne : ((X : Polynomial ℝ) - C ξ) ^ m ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero ξ)
      have hdegg : g.natDegree + m = f.natDegree := by
        conv_rhs => rw [← hfac]
        rw [natDegree_mul hXne hgne, natDegree_pow, natDegree_X_sub_C, mul_one]
        omega
      have hNge : 2 ≤ N := by omega
      have hgdeg : g.natDegree ≤ N - 2 := by omega
      have hgeven : ∀ ζ ∈ Set.Ioo a b, Even (g.rootMultiplicity ζ) := by
        intro ζ hζ
        have hsplit : f.rootMultiplicity ζ
            = ((X - C ξ) ^ m : Polynomial ℝ).rootMultiplicity ζ + g.rootMultiplicity ζ := by
          conv_lhs => rw [← hfac]
          exact rootMultiplicity_mul (by rw [hfac]; exact hf)
        by_cases hζξ : ζ = ξ
        · subst hζξ
          rw [rootMultiplicity_X_sub_C_pow] at hsplit
          have hsum := heven ζ hζ
          rw [hsplit] at hsum
          exact (Nat.even_add.mp hsum).mp hme
        · have hz : ((X - C ξ) ^ m : Polynomial ℝ).rootMultiplicity ζ = 0 := by
            refine rootMultiplicity_eq_zero ?_
            simp only [IsRoot, eval_pow, eval_sub, eval_X, eval_C]
            exact pow_ne_zero _ (sub_ne_zero.2 hζξ)
          rw [hz, zero_add] at hsplit
          rw [← hsplit]; exact heven ζ hζ
      have hIH := ih (N - 2) (by omega) g hgdeg hgne hgeven x hx y hy
      have hev : ∀ z : ℝ, f.eval z = (z - ξ) ^ m * g.eval z := by
        intro z
        conv_lhs => rw [← hfac]
        simp
      rw [hev x, hev y]
      have : (x - ξ) ^ m * g.eval x * ((y - ξ) ^ m * g.eval y)
          = ((x - ξ) * (y - ξ)) ^ m * (g.eval x * g.eval y) := by rw [mul_pow]; ring
      rw [this]
      exact mul_nonneg (hme.pow_nonneg _) hIH
    · push Not at hroot
      by_contra hlt
      push Not at hlt
      have hcont : ContinuousOn (fun z => f.eval z) (Set.uIcc x y) := f.continuous.continuousOn
      have hsub : Set.uIcc x y ⊆ Set.Ioo a b := Set.ordConnected_Ioo.uIcc_subset hx hy
      have h0 : (0 : ℝ) ∈ Set.uIcc (f.eval x) (f.eval y) := by
        rcases mul_neg_iff.1 hlt with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Set.mem_uIcc.2 (Or.inr ⟨h2.le, h1.le⟩)
        · exact Set.mem_uIcc.2 (Or.inl ⟨h1.le, h2.le⟩)
      obtain ⟨ξ, hξmem, hξ0⟩ := intermediate_value_uIcc hcont h0
      exact hroot ξ (hsub hξmem) hξ0

/-- A real polynomial whose zeros in `(a,b)` all have even order takes values of
one sign there.  This is what makes the auxiliary product of Durán's Lemma 3.1
sign-definite. -/
theorem eval_mul_eval_nonneg_of_even_rootMultiplicity {a b : ℝ} {f : Polynomial ℝ} (hf : f ≠ 0)
    (heven : ∀ ζ ∈ Set.Ioo a b, Even (f.rootMultiplicity ζ))
    {x y : ℝ} (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    0 ≤ f.eval x * f.eval y :=
  eval_mul_eval_nonneg_aux a b f.natDegree f le_rfl hf heven x hx y hy

/-! ### The odd-order zeros in an interval, and the polynomial that cancels them -/

open scoped Classical in
/-- The points of `(a,b)` at which `q` vanishes to odd order.  These are the
zeros Durán's Lemma 3.1 counts: a zero of even order is not a sign change and
the argument cannot see it. -/
noncomputable def oddOrderRoots (q : Polynomial ℝ) (a b : ℝ) : Finset ℝ :=
  q.roots.toFinset.filter fun ξ => a < ξ ∧ ξ < b ∧ Odd (q.rootMultiplicity ξ)

theorem mem_oddOrderRoots {q : Polynomial ℝ} (hq : q ≠ 0) {a b ξ : ℝ} :
    ξ ∈ oddOrderRoots q a b ↔ ξ ∈ Set.Ioo a b ∧ Odd (q.rootMultiplicity ξ) := by
  classical
  simp only [oddOrderRoots, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hq,
    Set.mem_Ioo]
  constructor
  · rintro ⟨-, h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨(rootMultiplicity_pos hq).1 h3.pos, h1, h2, h3⟩

/-- The monic polynomial whose simple zeros are exactly the odd-order zeros of
`q` in `(a,b)`.  Multiplying by it is the whole of Durán's argument: every zero
of the product inside the interval then has even order. -/
noncomputable def oddRootFactor (q : Polynomial ℝ) (a b : ℝ) : Polynomial ℝ :=
  ∏ ξ ∈ oddOrderRoots q a b, (X - C ξ)

theorem oddRootFactor_ne_zero (q : Polynomial ℝ) (a b : ℝ) : oddRootFactor q a b ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun ξ _ => X_sub_C_ne_zero ξ

theorem natDegree_oddRootFactor (q : Polynomial ℝ) (a b : ℝ) :
    (oddRootFactor q a b).natDegree = (oddOrderRoots q a b).card := by
  rw [oddRootFactor, natDegree_prod _ _ fun ξ _ => X_sub_C_ne_zero ξ]
  simp

theorem eval_oddRootFactor_ne_zero {q : Polynomial ℝ} {a b ζ : ℝ}
    (hζ : ζ ∉ oddOrderRoots q a b) : (oddRootFactor q a b).eval ζ ≠ 0 := by
  rw [oddRootFactor, eval_prod]
  refine Finset.prod_ne_zero_iff.2 fun ξ hξ => ?_
  simp only [eval_sub, eval_X, eval_C, ne_eq, sub_eq_zero]
  rintro rfl
  exact hζ hξ

theorem rootMultiplicity_oddRootFactor_of_notMem {q : Polynomial ℝ} {a b ζ : ℝ}
    (hζ : ζ ∉ oddOrderRoots q a b) : (oddRootFactor q a b).rootMultiplicity ζ = 0 :=
  rootMultiplicity_eq_zero (eval_oddRootFactor_ne_zero hζ)

theorem rootMultiplicity_oddRootFactor_of_mem {q : Polynomial ℝ} {a b ζ : ℝ}
    (hζ : ζ ∈ oddOrderRoots q a b) : (oddRootFactor q a b).rootMultiplicity ζ = 1 := by
  classical
  have hsplit : (X - C ζ) * ∏ ξ ∈ (oddOrderRoots q a b).erase ζ, (X - C ξ)
      = oddRootFactor q a b := Finset.mul_prod_erase _ _ hζ
  have hrest : (∏ ξ ∈ (oddOrderRoots q a b).erase ζ, (X - C ξ)).eval ζ ≠ 0 := by
    rw [eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun ξ hξ => ?_
    simp only [eval_sub, eval_X, eval_C, ne_eq, sub_eq_zero]
    rintro rfl
    exact (Finset.mem_erase.1 hξ).1 rfl
  have hne : (X - C ζ) * ∏ ξ ∈ (oddOrderRoots q a b).erase ζ, (X - C ξ) ≠ 0 := by
    rw [hsplit]; exact oddRootFactor_ne_zero q a b
  calc (oddRootFactor q a b).rootMultiplicity ζ
      = ((X - C ζ) * ∏ ξ ∈ (oddOrderRoots q a b).erase ζ, (X - C ξ)).rootMultiplicity ζ := by
        rw [hsplit]
    _ = ((X : Polynomial ℝ) - C ζ).rootMultiplicity ζ
          + (∏ ξ ∈ (oddOrderRoots q a b).erase ζ, (X - C ξ)).rootMultiplicity ζ :=
        rootMultiplicity_mul hne
    _ = 1 := by rw [rootMultiplicity_X_sub_C_self, rootMultiplicity_eq_zero hrest]

/-- Multiplying `q` by `oddRootFactor` leaves every zero inside `(a,b)` of even
order — the step that turns the sign lemma on. -/
theorem even_rootMultiplicity_mul_oddRootFactor {q : Polynomial ℝ} (hq : q ≠ 0) {a b : ℝ}
    {ζ : ℝ} (hζ : ζ ∈ Set.Ioo a b) :
    Even ((q * oddRootFactor q a b).rootMultiplicity ζ) := by
  classical
  have hne : q * oddRootFactor q a b ≠ 0 := mul_ne_zero hq (oddRootFactor_ne_zero q a b)
  rw [rootMultiplicity_mul hne]
  by_cases hmem : ζ ∈ oddOrderRoots q a b
  · rw [rootMultiplicity_oddRootFactor_of_mem hmem]
    obtain ⟨k, hk⟩ := ((mem_oddOrderRoots hq).1 hmem).2
    exact ⟨k + 1, by omega⟩
  · rw [rootMultiplicity_oddRootFactor_of_notMem hmem, add_zero]
    rcases Nat.even_or_odd (q.rootMultiplicity ζ) with h | h
    · exact h
    · exact absurd ((mem_oddOrderRoots hq).2 ⟨hζ, h⟩) hmem

/-! ### A weighted integral cannot vanish on a polynomial of one sign -/

/-- If a nonzero real polynomial takes values of one sign on `(a,b)` and the
weight is positive there, its weighted integral is nonzero.  This is the second
half of Durán's argument, and the only place the positivity of the measure is
used. -/
theorem integral_mul_weight_ne_zero {a b : ℝ} (hab : a < b) {w : ℝ → ℝ}
    (hwc : ContinuousOn w (Set.Icc a b)) (hwpos : ∀ x ∈ Set.Ioo a b, 0 < w x)
    {f : Polynomial ℝ} (hf : f ≠ 0)
    (hsign : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, 0 ≤ f.eval x * f.eval y) :
    (∫ x in a..b, f.eval x * w x) ≠ 0 := by
  -- a point of `(a,b)` off the (finite) zero set of `f`
  obtain ⟨x₀, hx₀, hfx₀⟩ : ∃ x₀ ∈ Set.Ioo a b, f.eval x₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf (eq_zero_of_infinite_isRoot f
      ((Set.Ioo_infinite hab).mono fun x hx => hcon x hx))
  intro hint
  set c : ℝ := f.eval x₀ with hc
  set G : ℝ → ℝ := fun x => f.eval x * w x * c with hG
  have hGc : ContinuousOn G (Set.Icc a b) :=
    ((f.continuous.continuousOn.mul hwc).mul continuousOn_const)
  have hGi : ∀ u v : ℝ, Set.uIcc u v ⊆ Set.Icc a b → IntervalIntegrable G volume u v :=
    fun u v h => (hGc.mono h).intervalIntegrable
  have hGnn : ∀ x ∈ Set.Ioo a b, 0 ≤ G x := by
    intro x hx
    have h1 : 0 ≤ f.eval x * c := hsign x hx x₀ hx₀
    have h2 : 0 < w x := hwpos x hx
    have : G x = f.eval x * c * w x := by rw [hG]; ring
    rw [this]
    exact mul_nonneg h1 h2.le
  have hc2 : 0 < c ^ 2 := by
    have hcne : c ≠ 0 := hfx₀
    positivity
  have hGx₀ : 0 < G x₀ := by
    have : G x₀ = c ^ 2 * w x₀ := by rw [hG]; ring
    rw [this]
    exact mul_pos hc2 (hwpos x₀ hx₀)
  have hGint : (∫ x in a..b, G x) = 0 := by
    have : (∫ x in a..b, f.eval x * w x * c) = (∫ x in a..b, f.eval x * w x) * c :=
      intervalIntegral.integral_mul_const c _
    rw [hG, this, hint, zero_mul]
  -- a subinterval of `(a,b)` on which `G` is positive
  have hnhds : G ⁻¹' Set.Ioi 0 ∩ Set.Ioo a b ∈ nhds x₀ := by
    refine Filter.inter_mem ?_ (Ioo_mem_nhds hx₀.1 hx₀.2)
    exact (hGc.continuousAt (Icc_mem_nhds hx₀.1 hx₀.2)) (Ioi_mem_nhds hGx₀)
  obtain ⟨l, r, hlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hnhds
  set u : ℝ := max l a with hu
  set v : ℝ := min r b with hv
  have hau : a ≤ u := le_max_right _ _
  have hvb : v ≤ b := min_le_right _ _
  have hux : u < x₀ := max_lt hlr.1 hx₀.1
  have hxv : x₀ < v := lt_min hlr.2 hx₀.2
  have huv : u < v := hux.trans hxv
  have hsub' : Set.Ioo u v ⊆ Set.Ioo l r := Set.Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  have hicc : ∀ p q : ℝ, a ≤ p → q ≤ b → p ≤ q → Set.uIcc p q ⊆ Set.Icc a b := by
    intro p q h1 h2 h3
    rw [Set.uIcc_of_le h3]
    exact Set.Icc_subset_Icc h1 h2
  have hmid : 0 < ∫ x in u..v, G x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (hGi u v (hicc u v hau hvb huv.le))
      (fun x hx => (hsub (hsub' hx)).1) huv
  have hub : u ≤ b := (hux.trans hx₀.2).le
  have hav : a ≤ v := (hx₀.1.trans hxv).le
  have hleft : 0 ≤ ∫ x in a..u, G x := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict hau ?_
    rw [← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact hGnn x ⟨hx.1, hx.2.trans_le hub⟩
  have hright : 0 ≤ ∫ x in v..b, G x := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict hvb ?_
    rw [← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact hGnn x ⟨hav.trans_lt hx.1, hx.2⟩
  have hadd1 : (∫ x in a..u, G x) + (∫ x in u..v, G x) = ∫ x in a..v, G x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hGi a u (hicc a u le_rfl hub hau)) (hGi u v (hicc u v hau hvb huv.le))
  have hadd2 : (∫ x in a..v, G x) + (∫ x in v..b, G x) = ∫ x in a..b, G x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hGi a v (hicc a v le_rfl hvb hav)) (hGi v b (hicc v b hav le_rfl hvb))
  rw [hGint] at hadd2
  linarith

/-! ### Shohat's count -/

/-- **Shohat's theorem, in the sign-change form Durán's Lemma 3.1 proves.**  A
nonzero real polynomial orthogonal, against a weight positive on `(a,b)`, to
every polynomial of degree below `n` vanishes to odd order at at least `n`
points of `(a,b)`.

No orthogonal system appears here.  The system enters only through
`card_oddOrderRoots_linearCombination_ge`, which supplies `horth` from the
system's own relations, and that separation is what lets the same count serve
`rem:quadratic-case` without carrying the OPS machinery into the count. -/
theorem card_oddOrderRoots_ge {a b : ℝ} (hab : a < b) {w : ℝ → ℝ}
    (hwc : ContinuousOn w (Set.Icc a b)) (hwpos : ∀ x ∈ Set.Ioo a b, 0 < w x)
    {q : Polynomial ℝ} (hq : q ≠ 0) {n : ℕ}
    (horth : ∀ r : Polynomial ℝ, r.natDegree < n →
      (∫ x in a..b, q.eval x * r.eval x * w x) = 0) :
    n ≤ (oddOrderRoots q a b).card := by
  by_contra hcon
  push Not at hcon
  set R := oddRootFactor q a b with hR
  have hRdeg : R.natDegree < n := by rw [hR, natDegree_oddRootFactor]; exact hcon
  have hzero := horth R hRdeg
  have hf : q * R ≠ 0 := mul_ne_zero hq (oddRootFactor_ne_zero q a b)
  refine integral_mul_weight_ne_zero hab hwc hwpos hf
    (fun x hx y hy => eval_mul_eval_nonneg_of_even_rootMultiplicity hf
      (fun ζ hζ => even_rootMultiplicity_mul_oddRootFactor hq hζ) hx hy) ?_
  have hcongr : (∫ x in a..b, (q * R).eval x * w x)
      = ∫ x in a..b, q.eval x * R.eval x * w x := by simp [eval_mul]
  rw [hcongr]
  exact hzero

/-! ### A degree-graded family spans -/

/-- Every real polynomial of degree at most `d` is a finite combination of
`p 0, …, p d` when `p m` has degree exactly `m`.  This is what upgrades pairwise
orthogonality of an OPS to orthogonality against all lower degrees. -/
theorem exists_repr_of_natDegree_le {p : ℕ → Polynomial ℝ}
    (hdeg : ∀ m, (p m).natDegree = m) (hne : ∀ m, p m ≠ 0) :
    ∀ (d : ℕ) (r : Polynomial ℝ), r.natDegree ≤ d →
      ∃ c : ℕ → ℝ, r = ∑ i ∈ Finset.range (d + 1), C (c i) * p i := by
  intro d
  induction d with
  | zero =>
    intro r hr
    obtain ⟨α, hα, hpα⟩ : ∃ α : ℝ, α ≠ 0 ∧ p 0 = C α := by
      refine ⟨(p 0).coeff 0, ?_, eq_C_of_natDegree_le_zero (le_of_eq (hdeg 0))⟩
      have h := hne 0
      rw [← leadingCoeff_ne_zero] at h
      rwa [leadingCoeff, hdeg 0] at h
    refine ⟨fun _ => r.coeff 0 / α, ?_⟩
    rw [Finset.sum_range_one, hpα]
    dsimp only
    rw [← C_mul, div_mul_cancel₀ _ hα]
    exact eq_C_of_natDegree_le_zero hr
  | succ d ih =>
    intro r hr
    have hlc : (p (d + 1)).coeff (d + 1) ≠ 0 := by
      have := hne (d + 1)
      rw [← leadingCoeff_ne_zero] at this
      rwa [leadingCoeff, hdeg (d + 1)] at this
    set κ : ℝ := r.coeff (d + 1) / (p (d + 1)).coeff (d + 1) with hκ
    set r' : Polynomial ℝ := r - C κ * p (d + 1) with hr'
    have hcoeff : r'.coeff (d + 1) = 0 := by
      rw [hr', coeff_sub, coeff_C_mul, hκ, div_mul_cancel₀ _ hlc, sub_self]
    have hdegr' : r'.natDegree ≤ d := by
      refine natDegree_le_iff_coeff_eq_zero.2 fun j hj => ?_
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt (by exact_mod_cast hj)) with h | h
      · rw [← h]; exact hcoeff
      · have hjd : (d : ℕ) + 1 < j := by exact_mod_cast h
        have h1 : r.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hr hjd)
        have h2 : (C κ * p (d + 1)).coeff j = 0 := by
          rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega), mul_zero]
        rw [hr', coeff_sub, h1, h2, sub_zero]
    obtain ⟨c', hc'⟩ := ih r' hdegr'
    refine ⟨fun i => if i = d + 1 then κ else c' i, ?_⟩
    rw [Finset.sum_range_succ]
    have hsum : ∑ i ∈ Finset.range (d + 1), C (if i = d + 1 then κ else c' i) * p i
        = ∑ i ∈ Finset.range (d + 1), C (c' i) * p i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [if_neg (by simpa using (Finset.mem_range.1 hi).ne)]
    rw [hsum, ← hc']
    dsimp only
    rw [if_pos rfl, hr']
    ring

/-! ### Durán's Lemma 3.1 -/

private theorem intervalIntegrable_of_continuousOn {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) : IntervalIntegrable f MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hab]
  exact hf

/-- Pairwise orthogonality of a degree-graded family gives orthogonality against
every polynomial of lower degree — the form Durán's proof actually consumes. -/
theorem integral_mul_weight_eq_zero_of_natDegree_lt {a b : ℝ} (hab : a ≤ b) {w : ℝ → ℝ}
    (hwc : ContinuousOn w (Set.Icc a b))
    {p : ℕ → Polynomial ℝ} (hdeg : ∀ m, (p m).natDegree = m) (hne : ∀ m, p m ≠ 0)
    (horth : ∀ m k, m ≠ k → (∫ x in a..b, (p m).eval x * (p k).eval x * w x) = 0)
    {m : ℕ} {r : Polynomial ℝ} (hr : r.natDegree < m) :
    (∫ x in a..b, (p m).eval x * r.eval x * w x) = 0 := by
  obtain ⟨c, hc⟩ := exists_repr_of_natDegree_le hdeg hne (m - 1) r (by omega)
  rw [show m - 1 + 1 = m by omega] at hc
  have hpt : ∀ x : ℝ, (p m).eval x * r.eval x * w x
      = ∑ i ∈ Finset.range m, c i * ((p m).eval x * (p i).eval x * w x) := by
    intro x
    conv_lhs => rw [hc]
    simp only [eval_finsetSum, eval_mul, eval_C, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [intervalIntegral.integral_congr (g := fun x =>
      ∑ i ∈ Finset.range m, c i * ((p m).eval x * (p i).eval x * w x)) fun x _ => hpt x,
    intervalIntegral.integral_finsetSum]
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [intervalIntegral.integral_const_mul, horth m i (Finset.mem_range.1 hi).ne', mul_zero]
  · intro i _
    exact (intervalIntegrable_of_continuousOn hab
      ((((p m).continuous.continuousOn.mul (p i).continuous.continuousOn).mul hwc))).const_mul _

/-- **Durán's Lemma 3.1**, the third-party statement `rem:quadratic-case` cites
for the quadratic pencil.  A fixed combination `q = ∑_{j≤K} γ_j p_{n-j}` of `K+1`
consecutive members of an orthogonal system, with `γ_0 ≠ 0`, vanishes to odd
order at at least `n - K` points of the open interval carrying the weight.

**Differs from the paper's route.**  The cited lemma places its zeros in the
convex hull of the support of a positive measure and states them for a general
orthogonal polynomial system.  Here the measure is a weight positive on an
interval, and the zeros are located in that open interval rather than in a
closed hull — which is what `rem:quadratic-case` then pays for by conceding two
endpoints.  The `+2` in the remark's "at most `K+2` outside `I_{Q,1}`" is
exactly that concession, and nothing else.

The hypothesis `γ_K ≠ 0` of the cited statement is not needed for the count and
is not assumed.  Its role is to pin the index: the conclusion is `n - K` for
*every* `K` bounding the support of `γ`, so it weakens as `K` grows, and
`γ_K ≠ 0` is what says the `K` in hand is the smallest such — the degree of the
weight rather than an overestimate of it.  `rem:quadratic-case` uses it that
way, to read `K = deg B`, and `quadReduced_card_oddOrderRoots_ge` gets it for
free by taking `K` to be `Polynomial.natDegree` in the first place. -/
theorem card_oddOrderRoots_linearCombination_ge {a b : ℝ} (hab : a < b) {w : ℝ → ℝ}
    (hwc : ContinuousOn w (Set.Icc a b)) (hwpos : ∀ x ∈ Set.Ioo a b, 0 < w x)
    {p : ℕ → Polynomial ℝ} (hdeg : ∀ m, (p m).natDegree = m) (hne : ∀ m, p m ≠ 0)
    (horth : ∀ m k, m ≠ k → (∫ x in a..b, (p m).eval x * (p k).eval x * w x) = 0)
    {K n : ℕ} (hKn : K ≤ n) {γ : ℕ → ℝ} (hγ0 : γ 0 ≠ 0)
    {q : Polynomial ℝ} (hqdef : q = ∑ j ∈ Finset.range (K + 1), C (γ j) * p (n - j)) :
    n - K ≤ (oddOrderRoots q a b).card := by
  have hlcn : (p n).coeff n ≠ 0 := by
    have h := hne n
    rw [← leadingCoeff_ne_zero] at h
    rwa [leadingCoeff, hdeg n] at h
  have hqcoeff : q.coeff n = γ 0 * (p n).coeff n := by
    rw [hqdef, finsetSum_coeff]
    refine (Finset.sum_eq_single 0 (fun j hj hj0 => ?_) (fun h => ?_)).trans ?_
    · have hjK : j < K + 1 := Finset.mem_range.1 hj
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega), mul_zero]
    · exact absurd (Finset.mem_range.2 (Nat.succ_pos K)) h
    · rw [coeff_C_mul, Nat.sub_zero]
  have hq : q ≠ 0 := by
    intro h
    rw [h, coeff_zero] at hqcoeff
    exact (mul_ne_zero hγ0 hlcn) hqcoeff.symm
  refine card_oddOrderRoots_ge hab hwc hwpos hq fun r hr => ?_
  have hpt : ∀ x : ℝ, q.eval x * r.eval x * w x
      = ∑ j ∈ Finset.range (K + 1), γ j * ((p (n - j)).eval x * r.eval x * w x) := by
    intro x
    conv_lhs => rw [hqdef]
    simp only [eval_finsetSum, eval_mul, eval_C, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [intervalIntegral.integral_congr (g := fun x =>
      ∑ j ∈ Finset.range (K + 1), γ j * ((p (n - j)).eval x * r.eval x * w x)) fun x _ => hpt x,
    intervalIntegral.integral_finsetSum]
  · refine Finset.sum_eq_zero fun j hj => ?_
    have hjK : j < K + 1 := Finset.mem_range.1 hj
    rw [intervalIntegral.integral_const_mul,
      integral_mul_weight_eq_zero_of_natDegree_lt hab.le hwc hdeg hne horth (by omega), mul_zero]
  · intro j _
    exact (intervalIntegrable_of_continuousOn hab.le
      ((((p (n - j)).continuous.continuousOn.mul r.continuous.continuousOn).mul hwc))).const_mul _

end ForgacsTran
