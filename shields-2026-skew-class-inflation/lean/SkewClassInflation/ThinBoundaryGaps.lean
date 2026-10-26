/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ThinComponentRecovery
import SkewClassInflation.UnitCutCoefficients

/-!
# Positive exterior gaps are produced by the source block product

The ordered boundary producer for `thm:two-row-thin-class` in
`shields-2026-skew-class-inflation.tex`.  A one-row zero-cut component
would divide a genuine source thin power and hence have its row count,
which is impossible.  Neither exterior-gap condition is carried as a
hypothesis of the arbitrary-mate result.  Sorry-free.
-/

namespace SkewClassInflation.ThinParameters

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg

variable (B : ThinParameters)

/-- An actual polynomial of a positive thin power, rather than an assumed factor surrogate. -/
def IsPowerFunction (p : CompleteRing) : Prop :=
  ∃ (m : ℕ) (hm : 0 < m), p = (B.innerPower m hm).toBetaDiagram.schur

/-- Every entry of the literal source-word inventory has an actual positive-power producer. -/
theorem powerFunctions_are_actual (l : List ℕ) (hl : ∀ m ∈ l, 0 < m) :
    ∀ p ∈ B.powerFunctions l hl, B.IsPowerFunction p := by
  intro p hp
  obtain ⟨m, _, hm⟩ := List.mem_map.mp hp
  exact ⟨m.val, hl _ m.property, hm.symm⟩

/-- A connected divisor of a genuine thin-power product equals one of its actual factors. -/
theorem connected_factor_of_power_product {n : ℕ} (D : BetaDiagram n) (hD : D.Connected)
    (fs : List CompleteRing) (hfs : ∀ p ∈ fs, B.IsPowerFunction p)
    (hd : D.schur ∣ fs.prod) :
    ∃ (m : ℕ) (hm : 0 < m), D.schur = (B.innerPower m hm).toBetaDiagram.schur ∧ D.schur ∈ fs := by
  have hp := (D.schur_irreducible hD).prime
  have hd' : D.schur ∣ (fs : Multiset CompleteRing).prod := by
    simpa only [Multiset.prod_coe] using hd
  obtain ⟨p, hpl, hdp⟩ := hp.exists_mem_multiset_dvd hd'
  have hpl' : p ∈ fs := by simpa only [Multiset.mem_coe] using hpl
  obtain ⟨m, hm, hpm⟩ := hfs p hpl'
  have hs : D.schur = (B.innerPower m hm).toBetaDiagram.schur := by
    apply D.schur_eq_of_associated
    exact (D.schur_irreducible hD).associated_of_dvd
      ((B.innerPower m hm).toBetaDiagram.schur_irreducible
        (B.innerPower m hm).toBetaDiagram_connected) (by simpa only [hpm] using hdp)
  refine ⟨m, hm, hs, ?_⟩
  rw [hs, ← hpm]
  exact hpl'

/-- The first zero cut cannot isolate a one-row factor of the source block product. -/
theorem first_gap_positive_of_product {n : ℕ} (Q : Profile n)
    (fs : List CompleteRing) (hfs : ∀ p ∈ fs, B.IsPowerFunction p)
    (he : (unitSchur Q).coeff 0 = fs.prod) :
    ∀ j : Fin n, j.val = 0 → 0 < Q.g j := by
  intro j hj
  cases n with
  | zero => exact Fin.elim0 j
  | succ n =>
    have hj0 : j = (0 : Fin (n + 1)) := Fin.ext hj
    by_contra hn
    have hc : Q.g (0 : Fin (n + 1)) = 0 := by rw [← hj0]; omega
    let L : Profile 0 := leftOfSeam Q (0 : Fin (n + 1))
    have hL : (unitSchur (leftOfSeam Q 0)).coeff 0 = L.toBetaDiagram.schur :=
      unit_single_row_constant L
    have hd : L.toBetaDiagram.schur ∣ fs.prod := by
      rw [← he, unit_zero_cut_constant Q 0 hc, hL]
      exact dvd_mul_right _ _
    obtain ⟨m, hm, hs, _⟩ := B.connected_factor_of_power_product L.toBetaDiagram
      L.toBetaDiagram_connected fs hfs hd
    have hrows := L.toBetaDiagram.row_count_of_schur_eq (B.innerPower m hm).toBetaDiagram hs
    change 1 = m + 1 at hrows
    omega

/-- Rotation preserves every produced retained-unit product observation. -/
theorem rotated_source_constant {n : ℕ} (Q : Profile n) (fs : List CompleteRing)
    (he : (unitSchur Q).coeff 0 = fs.prod) : (unitSchur Q.rotate).coeff 0 = fs.prod := by
  have hs : Q.rotate.toBetaDiagram.schur = Q.toBetaDiagram.schur := by
    rw [SkewJacobiNegative.Gluing.Profile.toBetaDiagram_schur,
      SkewJacobiNegative.Gluing.Profile.schur_rotate,
      SkewJacobiNegative.Gluing.Profile.toBetaDiagram_schur]
  rw [unitSchur_eq_of_schur_eq Q.rotate Q hs, he]

/-- The last exterior gap is positive for the same source-product reason. -/
theorem last_gap_positive_of_product {n : ℕ} (Q : Profile n)
    (fs : List CompleteRing) (hfs : ∀ p ∈ fs, B.IsPowerFunction p)
    (he : (unitSchur Q).coeff 0 = fs.prod) :
    ∀ j : Fin n, j.val + 1 = n → 0 < Q.g j := by
  intro j hj
  have hr : j.rev.val = 0 := by simp only [Fin.val_rev]; omega
  have h := B.first_gap_positive_of_product Q.rotate fs hfs
    (rotated_source_constant Q fs he) j.rev hr
  change 0 < Q.g j.rev.rev at h
  simpa only [Fin.rev_rev] using h

end SkewClassInflation.ThinParameters
