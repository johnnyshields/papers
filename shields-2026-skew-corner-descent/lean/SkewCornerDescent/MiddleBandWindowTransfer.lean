/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.FullWindowRoot

/-!
# Complete source-window periods from an actual two-copy middle band

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Every source cell is lifted into one of its two complete literal copies.
The strict true-cap margin puts both compared cells inside the genuine
middle band of the doubled diagram. Forward and inverse physical periods
therefore give full translated source windows, not partial or
function-equivalent substitutes. Sorry-free.
-/

namespace SkewCornerDescent
open SkewGluing

/-- A complete two-copy middle period with true-cap room supplies the full
translated source windows at that period. -/
theorem twoCopy_middle_period_full_windows (D E : Diagram) (L δ lo hi : ℤ)
    (a b v : ℤ × ℤ) (hδ : 0 < δ) (hlo : 0 ≤ lo) (hsmall : lo + δ < L)
    (hroom : L + lo + δ < hi) (ha : content a = 0) (hb : content b = L)
    (hv : content v = -δ)
    (hlower : E.filter (fun x => 0 ≤ content x ∧ content x < L) = translate a D)
    (hupper : E.filter (fun x => L ≤ content x ∧ content x < 2 * L) = translate b D)
    (hforward : ∀ x ∈ E, lo + δ ≤ content x → content x < hi → x + v ∈ E)
    (hbackward : ∀ x ∈ E, lo ≤ content x → content x < hi - δ → x - v ∈ E) :
    D.filter (fun x => δ ≤ content x ∧ content x < L) =
      translate (-v) (D.filter fun x => 0 ≤ content x ∧ content x < L - δ) := by
  have hperiod (x : ℤ × ℤ) (hc : δ ≤ content x ∧ content x < L) :
      x ∈ D ↔ x+v ∈ D := by
    let off := if content x < lo+δ then b else a
    let s := if content x < lo+δ then L else 0
    have hoff : content off = s := by
      dsimp only [off,s]
      split_ifs <;> assumption
    have hcopy : E.filter (fun y => s ≤ content y ∧ content y < s+L) = translate off D := by
      dsimp only [off,s]
      split_ifs
      · simpa only [two_mul] using hupper
      · simpa only [zero_add] using hlower
    have hband : lo+δ ≤ content x+s ∧ content x+s < hi := by
      dsimp only [s]
      split_ifs <;> omega
    have hcopyIff (y : ℤ × ℤ) (hy : 0 ≤ content y ∧ content y < L) :
        y ∈ D ↔ y+off ∈ E := by
      have he : y+off ∈ E.filter (fun q => s ≤ content q ∧ content q < s+L) ↔ y+off ∈ E := by
        rw [Finset.mem_filter]
        have hbounds : s ≤ content (y+off) ∧ content (y+off) < s+L := by
          rw [content_add, hoff]
          omega
        exact ⟨fun h => h.1, fun h => ⟨h, hbounds⟩⟩
      rw [hcopy, mem_translate, add_sub_cancel_right] at he
      exact he
    have hsource : 0 ≤ content x ∧ content x < L := by omega
    have htarget : 0 ≤ content (x+v) ∧ content (x+v) < L := by
      rw [content_add, hv]
      omega
    have hq : content (x+off) = content x+s := by rw [content_add, hoff]
    have ht : content ((x+v)+off) = content x+s-δ := by
      rw [content_add, content_add, hv, hoff]
      ring
    have hE : x+off ∈ E ↔ (x+v)+off ∈ E := by
      constructor
      · intro hx
        have hh := hforward (x+off) hx (by rw [hq]; exact hband.1) (by rw [hq]; exact hband.2)
        have he : (x+off)+v = (x+v)+off := by abel
        rw [he] at hh
        exact hh
      · intro hx
        have hh := hbackward ((x+v)+off) hx (by rw [ht]; omega) (by rw [ht]; omega)
        have he : ((x+v)+off)-v = x+off := by abel
        rw [he] at hh
        exact hh
    exact (hcopyIff x hsource).trans (hE.trans (hcopyIff (x+v) htarget).symm)
  apply Finset.ext
  intro x
  rw [Finset.mem_filter, mem_translate, sub_neg_eq_add, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hlow, hhigh⟩
    refine ⟨(hperiod x ⟨hlow,hhigh⟩).mp hx, ?_, ?_⟩ <;> rw [content_add, hv] <;> omega
  · rintro ⟨hx, hlow, hhigh⟩
    have hc : δ ≤ content x ∧ content x < L := by
      rw [content_add, hv] at hlow hhigh
      omega
    exact ⟨(hperiod x hc).mpr hx, hc⟩

end SkewCornerDescent
