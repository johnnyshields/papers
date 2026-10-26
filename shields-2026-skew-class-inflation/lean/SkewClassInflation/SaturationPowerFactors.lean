/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SaturationCutCoefficients

/-!
# Connected factors of actual repeated-inner power products

The irreducibility input to `lem:total-contraction-inverse` of
`shields-2026-skew-class-inflation.tex`.  Each factor is an actual full
power polynomial.  No conclusion about a one-copy mate's geometry is
assumed.  Sorry-free.
-/

namespace SkewClassInflation.SaturationInner

open SkewJacobiNegative

variable (A : SaturationInner)

/-- A polynomial supplied by a positive actual power of this given inner. -/
def IsPowerFunction (p : CompleteRing) : Prop :=
  ∃ (m : ℕ) (hm : 0 < m), p = (A.power m hm).toBetaDiagram.schur

/-- The literal source factor list supplies an actual positive power for every entry. -/
theorem powerFunctions_are_actual (l : List ℕ) (hl : ∀ m ∈ l, 0 < m) :
    ∀ p ∈ A.powerFunctions l hl, A.IsPowerFunction p := by
  intro p hp
  obtain ⟨m, _, hm⟩ := List.mem_map.mp hp
  exact ⟨m.val, hl _ m.property, hm.symm⟩

/-- A connected divisor of the actual factor product equals a supplied actual power. -/
theorem connected_factor_of_power_product {n : ℕ} (D : BetaDiagram n) (hD : D.Connected)
    (fs : List CompleteRing) (hfs : ∀ p ∈ fs, A.IsPowerFunction p)
    (hd : D.schur ∣ fs.prod) :
    ∃ (m : ℕ) (hm : 0 < m), D.schur = (A.power m hm).toBetaDiagram.schur ∧ D.schur ∈ fs := by
  have hp := (D.schur_irreducible hD).prime
  have hd' : D.schur ∣ (fs : Multiset CompleteRing).prod := by
    simpa only [Multiset.prod_coe] using hd
  obtain ⟨p, hpl, hdp⟩ := hp.exists_mem_multiset_dvd hd'
  have hpl' : p ∈ fs := by simpa only [Multiset.mem_coe] using hpl
  obtain ⟨m, hm, hpm⟩ := hfs p hpl'
  have hs : D.schur = (A.power m hm).toBetaDiagram.schur := by
    apply D.schur_eq_of_associated
    exact (D.schur_irreducible hD).associated_of_dvd
      ((A.power m hm).toBetaDiagram.schur_irreducible
        (A.power m hm).toBetaDiagram_connected) (by simpa only [hpm] using hdp)
  refine ⟨m, hm, hs, ?_⟩
  rw [hs, ← hpm]
  exact hpl'

end SkewClassInflation.SaturationInner
