/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.PeriodicCutEncoding
import Mathlib.Data.Nat.ModEq

/-!
# Actual negative witnesses in the even-discrepancy frontier

The negative-generator input to signed-period refinement for
`thm:sharp-inflation` of `shields-2026-skew-class-inflation.tex`.
Reflecting the translated endpoint gives another actual discrepancy
with the same frontier witness and the opposite residue modulo the
old candidate period.  Sorry-free.
-/

namespace SkewClassInflation

/-- The actual reflected cut type is unchanged throughout the true weight interval. -/
theorem compositionCutType_reflect {N : ℕ} (α : Composition N) (x : ℕ) (hx : x ≤ N) :
    compositionCutType α (N - x) = compositionCutType α x := by
  unfold compositionCutType
  rw [Nat.sub_sub_self hx]
  exact Nat.add_comm _ _

/-- Every actual new frontier generator has an actual negative partner modulo the old period.

**No consumer here:** Signed refinement uses actual zero endpoints rather than
this opposite-residue frontier property.
-/
theorem evenCutDisagreements_negative {N : ℕ} (α : Composition N) (p : ℕ) (T : Finset ℕ)
    (hpN : p ∣ N) (hT : ∀ t ∈ T, p ∣ t)
    (x : ℕ) (hx : x ∈ evenCutDisagreements α p T) :
    ∃ y ∈ evenCutDisagreements α p T, p ∣ x + y := by
  classical
  obtain ⟨hx0, hxN, hnpx⟩ := evenCutDisagreements_bounds α p T x hx
  obtain ⟨_, t, ht, hevenx, hevenr, hdisagree⟩ := (Finset.mem_filter.mp hx).2
  let r := (x + t) % N
  have hrN : r < N := Nat.mod_lt _ (by omega)
  have hrp : ¬ p ∣ r := by
    intro hr
    have hdecomp := Nat.mod_add_div (x + t) N
    have hmul : p ∣ N * ((x + t) / N) := dvd_mul_of_dvd_left hpN _
    have hsum : p ∣ r + N * ((x + t) / N) := dvd_add hr hmul
    rw [hdecomp] at hsum
    exact hnpx ((Nat.dvd_add_iff_left (hT t ht)).mpr hsum)
  have hr0 : 0 < r := by
    by_contra hh
    have he : r = 0 := by omega
    exact hrp (by rw [he]; exact dvd_zero p)
  let y := N - r
  have hy0 : 0 < y := by dsimp only [y]; omega
  have hyN : y < N := by dsimp only [y]; omega
  have hsumr : r + y = N := by dsimp only [y]; omega
  have hsumxy : x + y + t = N * (((x + t) / N) + 1) := by
    have hd := Nat.mod_add_div (x + t) N
    change r + N * ((x + t) / N) = x + t at hd
    nlinarith
  have hdxy : p ∣ x + y := by
    have hh : p ∣ x + y + t := by
      rw [hsumxy]
      exact dvd_mul_of_dvd_left hpN _
    exact (Nat.dvd_add_iff_left (hT t ht)).mpr hh
  have hyp : ¬ p ∣ y := by
    intro hh
    exact hnpx ((Nat.dvd_add_iff_left hh).mpr hdxy)
  have hshift : (y + t) % N = N - x := by
    have hadd : x + (y + t) ≡ x + (N - x) [MOD N] := by
      change (x + (y + t)) % N = (x + (N - x)) % N
      rw [← Nat.add_assoc, hsumxy, Nat.mul_mod_right,
        Nat.add_sub_of_le hxN.le, Nat.mod_self]
    have hc := Nat.ModEq.add_left_cancel' x hadd
    change (y + t) % N = (N - x) % N at hc
    rwa [Nat.mod_eq_of_lt (by omega : N - x < N)] at hc
  have hytype : compositionCutType α y = compositionCutType α r :=
    compositionCutType_reflect α r hrN.le
  have hnext : compositionCutType α ((y + t) % N) = compositionCutType α x := by
    rw [hshift, compositionCutType_reflect α x hxN.le]
  refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hy0, hyN⟩,
    hyp, t, ht, ?_, ?_, ?_⟩, hdxy⟩
  · rwa [hytype]
  · rwa [hnext]
  · rw [hytype, hnext]
    exact Ne.symm hdisagree

end SkewClassInflation
