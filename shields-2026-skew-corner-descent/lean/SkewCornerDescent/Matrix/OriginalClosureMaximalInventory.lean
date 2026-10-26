/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPositiveInventories
import SkewCornerDescent.Matrix.OriginalClosureBoundedFrontier

/-!
# Attaining source windows in the actual closure inventory

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). Every
complete source gap window of at most one cycle is an internal interval of its
two-copy closure. An attaining source start therefore supplies a nonempty actual
filtered inventory, whose nonvanishing uses one constructed positive chamber.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- An attaining source gap start produces an attaining actual closure interval.
Its two endpoints and contraction cost are constructed from that start. -/
theorem originalHorizontalClosure_filtered_interval_exists {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (j : ℕ) (hj : 0 < j) (hjB : j ≤ originalSelectedCount (hD := hD) P)
    (M : ℤ)
    (hretain : ∃ z : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun s => c.originalCompletedGap P ((ZMod.finEquiv _).symm s)) 1 j z = M)
    (K : ℕ+) (hKeq : (K : ℤ) = (c.top : ℤ) + M) :
    ∃ i k : Fin (originalSelectedCount (hD := hD) Q + 1),
      i.val ≤ k.val ∧ k.val - i.val = j - 1 ∧
        originalHessenbergDistance (hD := hD) Q i k = (K : ℤ) := by
  obtain ⟨z, hz⟩ := hretain
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by omega
  let : NeZero (originalSelectedCount (hD := hD) Q) := ⟨by omega⟩
  have hzlt := ZMod.val_lt z
  let i : Fin (originalSelectedCount (hD := hD) Q) := ⟨z.val, by omega⟩
  let k : Fin (originalSelectedCount (hD := hD) Q) := ⟨z.val + j - 1, by omega⟩
  have hik : i ≤ k := by change z.val ≤ z.val + j - 1; omega
  have hk : k.val + 1 < originalSelectedCount (hD := hD) Q := by dsimp only [k]; omega
  have he := c.originalCompletedGap_cyclic_internal_window Q i k hik hk
  have hlen : k.val - i.val + 1 = j := by dsimp only [i, k]; omega
  rw [hlen, c.originalHorizontalClosure_completed_gap_window_at P Q v hQ] at he
  have hcast : (ZMod.castHom (show originalSelectedCount (hD := hD) P ∣
      originalSelectedCount (hD := hD) Q by rw [hc]; exact dvd_mul_left _ _)
      (ZMod (originalSelectedCount (hD := hD) P)))
      (i.val : ZMod (originalSelectedCount (hD := hD) Q)) = z := by
    simp only [map_natCast, i, ZMod.natCast_zmod_val]
  rw [hcast, hz, ← hKeq] at he
  refine ⟨i.succ, k.succ, ?_, ?_, he⟩
  · change i.val + 1 ≤ k.val + 1
    change i.val ≤ k.val at hik
    omega
  · change k.val + 1 - (i.val + 1) = j - 1
    omega

/-- The actual full closure filtered context is nonzero at every attained source
span bin; positivity and regularity are supplied by complete original elimination. -/
theorem originalHorizontalClosure_filtered_inventory_ne_zero {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (j : ℕ) (hj : 0 < j) (hjB : j ≤ originalSelectedCount (hD := hD) P)
    (M : ℤ)
    (hretain : ∃ z : ZMod (originalSelectedCount (hD := hD) P),
      windowSum (fun s => c.originalCompletedGap P ((ZMod.finEquiv _).symm s)) 1 j z = M)
    (K : ℕ+) (hKeq : (K : ℤ) = (c.top : ℤ) + M) :
    c.originalFilteredIntervalInventory Q j K ≠ 0 := by
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by omega
  exact c.originalFilteredIntervalInventory_ne_zero Q hBQ
    (c.originalHorizontalClosure_profile_component_span P Q v hQ hmax) j K
    (c.originalHorizontalClosure_filtered_interval_exists P Q v hQ hB j hj hjB M hretain K hKeq)

end SkewCornerDescent.Matrix.SelectedCoordinate
