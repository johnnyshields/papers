/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonWordComposition

/-!
# Constructing ordinary factors from periodic internal cuts

The cut-word reconstruction used in the ribbon factorization input to
`lem:overlap-power-rigidity` of `shields-2026-skew-class-inflation.tex`.
Both factors are actual positive compositions constructed from finite
cut sets.  Periodicity is the explicit premise of this reconstruction
lemma, not a claim that coarsening equivalence already supplies it.
Sorry-free.
-/

namespace SkewClassInflation

/-- Construct a composition from any proposed natural cut positions, retaining both endpoints. -/
noncomputable def compositionFromCuts (N : ℕ) (C : Finset ℕ) : Composition N :=
  (compositionEquiv N).symm
    { boundaries := Finset.univ.filter (fun i : Fin (N + 1) =>
        i = 0 ∨ i = Fin.last N ∨ i.val ∈ C)
      zero_mem := by simp
      getLast_mem := by simp }

/-- At a proper position the constructor keeps exactly the prescribed cut membership. -/
theorem compositionFromCuts_internal (N : ℕ) (C : Finset ℕ) (x : ℕ)
    (hx : 0 < x) (hxN : x < N) :
    x ∈ properCuts (compositionFromCuts N C) ↔ x ∈ C := by
  classical
  rw [mem_properCuts_iff _ x hx hxN]
  let S : CompositionAsSet N :=
    { boundaries := Finset.univ.filter (fun i : Fin (N + 1) =>
        i = 0 ∨ i = Fin.last N ∨ i.val ∈ C)
      zero_mem := by simp
      getLast_mem := by simp }
  have hb := congrArg CompositionAsSet.boundaries ((compositionEquiv N).apply_symm_apply S)
  change (compositionFromCuts N C).boundaries = S.boundaries at hb
  rw [hb]
  have hz : (⟨x, by omega⟩ : Fin (N + 1)) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    change x = 0 at hv
    omega
  have hl : (⟨x, by omega⟩ : Fin (N + 1)) ≠ Fin.last N := by
    intro he
    have hv := congrArg Fin.val he
    change x = N at hv
    omega
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hz, hl, false_or]

/-- The outer factor reads exactly the cuts at whole-inner multiples. -/
noncomputable def periodicOuter {n q : ℕ} (θ : Composition (n * q)) : Composition n :=
  compositionFromCuts n ((Finset.Ioo 0 n).filter (fun j => j * q ∈ properCuts θ))

/-- The inner factor reads the original proper cuts strictly inside its first copy. -/
noncomputable def periodicInner {n q : ℕ} (θ : Composition (n * q)) : Composition q :=
  compositionFromCuts q (properCuts θ)

/-- Every nonmultiple cut supplied by the periodicity premise is realized by the actual factors. -/
theorem periodic_factorization {n q : ℕ} (θ : Composition (n * q)) (hq : 0 < q)
    (hper : ∀ x, 0 < x → x < n * q → x % q ≠ 0 →
      (x ∈ properCuts θ ↔ x % q ∈ properCuts θ)) :
    compositionProduct (periodicOuter θ) (periodicInner θ) = θ := by
  apply properCuts_injective
  ext x
  by_cases hx : 0 < x ∧ x < n * q
  · rw [compositionProduct_cuts _ _ x hx.1 hx.2]
    by_cases hmod : x % q = 0
    · rw [ite_eq_left hmod]
      have hd := Nat.div_add_mod x q
      have hquot : 0 < x / q := by
        apply Nat.pos_of_ne_zero
        intro hz
        rw [hz, hmod, mul_zero, zero_add] at hd
        exact (Nat.ne_of_gt hx.1) hd.symm
      have hquotN : x / q < n := (Nat.div_lt_iff_lt_mul hq).mpr hx.2
      rw [periodicOuter, compositionFromCuts_internal _ _ _ hquot hquotN]
      simp only [Finset.mem_filter, Finset.mem_Ioo, hquot, hquotN, and_self, true_and]
      have he : x / q * q = x := by nlinarith
      rw [he]
    · rw [ite_eq_right hmod]
      have hm0 : 0 < x % q := by omega
      have hmq : x % q < q := Nat.mod_lt _ hq
      rw [periodicInner, compositionFromCuts_internal _ _ _ hm0 hmq]
      exact (hper x hx.1 hx.2 hmod).symm
  · constructor <;> intro hm <;> exact (hx (properCuts_bounds _ x hm)).elim

/-- Any genuine first-copy internal cut makes the constructed inner factor multipart. -/
theorem periodicInner_multipart {n q : ℕ} (θ : Composition (n * q))
    (x : ℕ) (hx : 0 < x) (hxq : x < q) (hc : x ∈ properCuts θ) :
    2 ≤ (periodicInner θ).length := by
  have hm : x ∈ properCuts (periodicInner θ) :=
    (compositionFromCuts_internal q (properCuts θ) x hx hxq).mpr hc
  have hq : 0 < q := by omega
  have hcard := suffixSet_card (periodicInner θ).reverse hq
  rw [← properCuts_eq_suffixSet] at hcard
  have hh : 0 < (properCuts (periodicInner θ)).card := Finset.card_pos.mpr ⟨x, hm⟩
  have hlen : (periodicInner θ).reverse.length = (periodicInner θ).length := by
    simp only [Composition.length, Composition.reverse_blocks, List.length_reverse]
  omega

/-- Every actual ordinary product produces its own nonmultiple cut periodicity. -/
theorem compositionProduct_cut_periodic {n q : ℕ} (γ : Composition n)
    (β : Composition q) (hq : 0 < q) (x : ℕ)
    (hx : 0 < x) (hxN : x < n * q) (hmod : x % q ≠ 0) :
    x ∈ properCuts (compositionProduct γ β) ↔
      x % q ∈ properCuts (compositionProduct γ β) := by
  have hn : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro he
    rw [he, zero_mul] at hxN
    omega
  have hm0 : 0 < x % q := Nat.pos_of_ne_zero hmod
  have hmq : x % q < q := Nat.mod_lt _ hq
  have hmN : x % q < n * q := by nlinarith
  rw [compositionProduct_internal γ β x hx hxN hmod,
    compositionProduct_internal γ β (x % q) hm0 hmN
      (by rw [Nat.mod_eq_of_lt hmq]; exact hmod), Nat.mod_eq_of_lt hmq]

/-- Nonmultiple periodicity is exactly ordinary factorization at the specified inner weight. -/
theorem periodic_factorization_iff {n q : ℕ} (θ : Composition (n * q)) (hq : 0 < q) :
    (∃ γ : Composition n, ∃ β : Composition q, compositionProduct γ β = θ) ↔
      ∀ x, 0 < x → x < n * q → x % q ≠ 0 →
        (x ∈ properCuts θ ↔ x % q ∈ properCuts θ) := by
  constructor
  · rintro ⟨γ, β, rfl⟩ x hx hxN hmod
    exact compositionProduct_cut_periodic γ β hq x hx hxN hmod
  · intro hp
    exact ⟨periodicOuter θ, periodicInner θ, periodic_factorization θ hq hp⟩

/-- Sampling whole-inner cut positions recovers the original outer factor exactly. -/
theorem periodicOuter_compositionProduct {n q : ℕ} (γ : Composition n)
    (β : Composition q) (hq : 0 < q) :
    periodicOuter (compositionProduct γ β) = γ := by
  apply properCuts_injective
  ext x
  by_cases hx : 0 < x ∧ x < n
  · rw [periodicOuter, compositionFromCuts_internal _ _ x hx.1 hx.2]
    simp only [Finset.mem_filter, Finset.mem_Ioo, hx.1, hx.2, and_self, true_and]
    rw [compositionProduct_cuts γ β (x * q) (Nat.mul_pos hx.1 hq)
      (Nat.mul_lt_mul_of_pos_right hx.2 hq), Nat.mul_mod_left,
      ite_eq_left rfl, Nat.mul_div_cancel _ hq]
  · constructor <;> intro hm <;> exact (hx (properCuts_bounds _ x hm)).elim

/-- The first proper inner interval recovers the original inner factor when a copy is present. -/
theorem periodicInner_compositionProduct {n q : ℕ} (γ : Composition n)
    (β : Composition q) (hn : 0 < n) :
    periodicInner (compositionProduct γ β) = β := by
  apply properCuts_injective
  ext x
  by_cases hx : 0 < x ∧ x < q
  · rw [periodicInner, compositionFromCuts_internal _ _ x hx.1 hx.2]
    have hxN : x < n * q := by nlinarith
    rw [compositionProduct_internal γ β x hx.1 hxN
      (by rw [Nat.mod_eq_of_lt hx.2]; exact Nat.ne_of_gt hx.1),
      Nat.mod_eq_of_lt hx.2]
  · constructor <;> intro hm <;> exact (hx (properCuts_bounds _ x hm)).elim

end SkewClassInflation
