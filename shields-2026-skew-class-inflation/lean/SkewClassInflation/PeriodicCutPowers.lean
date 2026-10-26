/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.CompositionCuts
import SkewClassInflation.OverlapCutObstruction

/-!
# Periodic cut powers have no proper multipart right factor

The cut-set obstruction in `lem:overlap-power-rigidity` of
`shields-2026-skew-class-inflation.tex`.  The source is an actual
composition built from a periodic internal cut set.  Every proposed
composition product supplies its own repeated internal word, which the
finite gcd argument forces to be empty.  Sorry-free.
-/

namespace SkewClassInflation

/-- The actual composition whose internal cuts repeat with period `Q` and total `mQ+δ`. -/
noncomputable def periodicCutPower (m Q δ : ℕ) (C : Finset ℕ) :
    Composition (m * Q + δ) :=
  (compositionEquiv (m * Q + δ)).symm
    { boundaries := Finset.univ.filter (fun i : Fin (m * Q + δ + 1) =>
        i = 0 ∨ i = Fin.last (m * Q + δ) ∨ i.val % Q ∈ C)
      zero_mem := by simp
      getLast_mem := by simp }

/-- Internal proper cuts of the constructed composition are exactly the periodic cut word. -/
theorem periodicCutPower_internal (m Q δ : ℕ) (C : Finset ℕ) (x : ℕ)
    (hx : 0 < x) (hxT : x < m * Q + δ) :
    x ∈ properCuts (periodicCutPower m Q δ C) ↔ x % Q ∈ C := by
  classical
  rw [mem_properCuts_iff _ x hx hxT]
  let S : CompositionAsSet (m * Q + δ) :=
    { boundaries := Finset.univ.filter (fun i : Fin (m * Q + δ + 1) =>
        i = 0 ∨ i = Fin.last (m * Q + δ) ∨ i.val % Q ∈ C)
      zero_mem := by simp
      getLast_mem := by simp }
  have hb := congrArg CompositionAsSet.boundaries
    ((compositionEquiv (m * Q + δ)).apply_symm_apply S)
  change (periodicCutPower m Q δ C).boundaries = S.boundaries at hb
  rw [hb]
  have hz : (⟨x, by omega⟩ : Fin (m * Q + δ + 1)) ≠ 0 := by
    intro he
    have hh := congrArg Fin.val he
    change x = 0 at hh
    omega
  have hl : (⟨x, by omega⟩ : Fin (m * Q + δ + 1)) ≠ Fin.last (m * Q + δ) := by
    intro he
    have hh := congrArg Fin.val he
    change x = m * Q + δ at hh
    omega
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hz, hl, false_or]

/-- The arithmetic source obstruction excludes every actual multipart right cut-product factor. -/
theorem periodicCutPower_no_right_factor (m Q δ : ℕ) (hm : 2 ≤ m) (hδ : 0 < δ)
    (hδQ : δ < Q) (C : Finset ℕ) (hC : ∀ x ∈ C, δ < x ∧ x < Q)
    {n q : ℕ} (γ : Composition n) (β : Composition q) (hγ : 2 ≤ n) (hβ : 2 ≤ β.length) :
    (⟨n * q, compositionProduct γ β⟩ : (N : ℕ) × Composition N) ≠
      ⟨m * Q + δ, periodicCutPower m Q δ C⟩ := by
  classical
  intro he
  have hq : 0 < q := by have := β.length_le; omega
  let _ : NeZero q := ⟨by omega⟩
  have hsize := congrArg Sigma.fst he
  change n * q = m * Q + δ at hsize
  have hcuts := congrArg (fun D : (N : ℕ) × Composition N => properCuts D.2) he
  change properCuts (compositionProduct γ β) = properCuts (periodicCutPower m Q δ C) at hcuts
  let f : ℕ → ℤ := fun x => if x % Q ∈ C then 1 else 0
  let t : ZMod q → ℤ := fun x => if x.val ∈ properCuts β then 1 else 0
  have hall := overlap_cut_obstruction m Q δ (m * Q + δ) q rfl hδ hq
    (by nlinarith) (by nlinarith) ⟨n, hsize.symm.trans (Nat.mul_comm n q)⟩ f t
    (by intro x _; simp only [f, Nat.add_mod_right])
    (by
      intro x hx
      have hnot : x % Q ∉ C := by
        rw [Nat.mod_eq_of_lt (by omega)]
        intro hc
        have hh := (hC x hc).1
        omega
      simp only [f, ite_eq_right hnot])
    (by
      intro x hx hxq
      have hx0 : 0 < x := by
        by_contra hn
        have he0 : x = 0 := by omega
        exact hxq (by rw [he0, Nat.cast_zero])
      have hxT : x < m * Q + δ := by
        by_contra hn
        have heT : x = m * Q + δ := by omega
        apply hxq
        rw [heT, ← hsize]
        exact (ZMod.natCast_eq_zero_iff _ q).mpr ⟨n, Nat.mul_comm n q⟩
      have hmod : x % q ≠ 0 := by
        intro hz
        exact hxq ((ZMod.natCast_eq_zero_iff x q).mpr (Nat.dvd_of_mod_eq_zero hz))
      have hmemb := compositionProduct_internal γ β x hx0 (by omega) hmod
      rw [hcuts, periodicCutPower_internal m Q δ C x hx0 hxT] at hmemb
      change (if x % Q ∈ C then (1 : ℤ) else 0) =
        if (x : ZMod q).val ∈ properCuts β then 1 else 0
      rw [ZMod.val_natCast]
      simp only [hmemb])
  obtain ⟨r, hr⟩ := properCuts_nonempty β hq hβ
  have hb := properCuts_bounds β r hr
  have hrq : (r : ZMod q) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff r q).mp hz
    have hh := Nat.le_of_dvd hb.1 hd
    omega
  have hh := hall (r : ZMod q) hrq
  simp only [t, ZMod.val_natCast_of_lt hb.2, hr, ite_true] at hh
  omega

end SkewClassInflation
