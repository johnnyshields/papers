/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrivateEndpointSeparation
import SkewCornerDescent.Matrix.OriginalWindowExteriorContainment

/-!
# Complete private-window membership from original remaining coordinates

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Whole block containment is equivalent to strict coordinate containment at
private boundaries. Empty unit pivots use the same strict bounds; no full
nonrow block can cross either cut. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

private theorem empty_content_diagonal_eq (D : Diagram) (k : ℤ)
    (hk : k ∉ contents D) : diagLo D k = diagHi D k := by
  have hne : ¬ (diagRows D k).Nonempty := by
    intro h
    exact hk (mem_contents.mpr h)
  simp [diagLo, diagHi, hne]

/-- Both actual lower normalized boundary diagonals are private: content zero
is the extreme singleton, and content minus one is empty. -/
theorem profile_normalized_lower_private_boundaries {n : ℕ} (P : Profile n) :
    diagLo P.cells 0 = diagHi P.cells 0 ∧
      diagLo P.cells (-1) = diagHi P.cells (-1) := by
  have hs := isConnectedSkew_iff_diagonal.mp P.isConnectedSkew_cells
  constructor
  · have h := hs.2.2.2.2 (minContent P.cells) (minContent_mem hs.1)
      (Or.inl (fun hk => by have hb := minContent_le hk; omega))
    simpa only [Profile.minContent_cells] using h
  · apply empty_content_diagonal_eq
    intro hk
    have h := minContent_le hk
    rw [Profile.minContent_cells] at h
    omega

/-- Both actual upper normalized boundary diagonals are private: the exclusive
top is empty and the immediately preceding content is the extreme singleton. -/
theorem profile_normalized_upper_private_boundaries {n : ℕ} (P : Profile n) :
    diagLo P.cells (P.xi 0) = diagHi P.cells (P.xi 0) ∧
      diagLo P.cells (P.xi 0 - 1) = diagHi P.cells (P.xi 0 - 1) := by
  have hs := isConnectedSkew_iff_diagonal.mp P.isConnectedSkew_cells
  constructor
  · apply empty_content_diagonal_eq
    intro hk
    have h := le_maxContent hk
    rw [Profile.maxContent_cells] at h
    omega
  · have h := hs.2.2.2.2 (maxContent P.cells) (maxContent_mem hs.1)
      (Or.inr (fun hk => by have hb := le_maxContent hk; omega))
    simpa only [Profile.maxContent_cells] using h

/-- At two ordinary private boundaries, one actual retained row/column pair
locates its entire original block, not merely the selected or diagonal entries. -/
theorem originalRemaining_private_window_iff_bounds {n : ℕ} (P : Profile n) (lo hi : ℤ)
    (hlo : diagLo P.cells lo = diagHi P.cells lo)
    (hloprev : diagLo P.cells (lo - 1) = diagHi P.cells (lo - 1))
    (hhi : diagLo P.cells hi = diagHi P.cells hi)
    (hhiprev : diagLo P.cells (hi - 1) = diagHi P.cells (hi - 1))
    (j : OriginalRemainingIndices (hD := hD) P) :
    originalBlockInWindow P lo hi j.1 ↔
      lo < originalResponseCols P j ∧ originalResponseRows P j < hi := by
  let a := j.1
  let r := originalRemovedRow (hD := hD) P j.1 j.2
  let s := originalRemovedCol (hD := hD) P j.1 j.2
  have hlabels : interiorBlock P a.val = interiorBlock P s := by
    rw [originalRemovedCol_block]
  have hlabelr : interiorBlock P r = interiorBlock P (interiorBlockLast P a.val) := by
    rw [originalRemovedRow_block, interiorBlockLast_label]
  have hlabel0 : interiorBlock P r = interiorBlock P a.val := originalRemovedRow_block P j.1 j.2
  constructor
  · intro hb
    have hbound := originalBlockInWindow_bounds P lo hi a hb
    have hlow : lo < P.zeta (interiorBlockLast P a.val).castSucc := by
      rcases hb with ⟨hne, _⟩ | ⟨he, hl, _⟩
      · change P.zeta a.val.castSucc < P.xi a.val.succ at hne
        have hlast := interior_block_row_nonempty P hne (interiorBlockLast_label P a.val)
        by_contra h
        have heq : P.zeta (interiorBlockLast P a.val).castSucc = lo := by omega
        have hx : ((interiorBlockLast P a.val : ℤ),
            (interiorBlockLast P a.val : ℤ) + lo) ∈ diagramInterior P.cells := by
          rw [P.mem_interior_cells]
          exact ⟨_, rfl, by omega, by omega⟩
        exact private_diagonal_no_interior hlo _ hx (by simp [content])
      · have hlasteq := interior_empty_row_isolated P a.val he
          (interiorBlockLast P a.val) (interiorBlockLast_label P a.val)
        rwa [hlasteq]
    have hhigh : P.xi a.val.succ < hi := by
      rcases hb with ⟨hne, _⟩ | ⟨_, _, hh⟩
      · change P.zeta a.val.castSucc < P.xi a.val.succ at hne
        by_contra h
        have heq : P.xi a.val.succ = hi := by omega
        have hx : ((a.val : ℤ), (a.val : ℤ) + hi - 1) ∈ diagramInterior P.cells := by
          rw [P.mem_interior_cells]
          exact ⟨_, rfl, by omega, by omega⟩
        exact private_diagonal_no_interior hhiprev _ hx (by dsimp only [content]; omega)
      · exact hh
    have htlo := profile_private_same_block_endpoints_trichotomy P lo hlo hloprev
      (interiorBlockLast P a.val) r hlabelr
    have hthi := profile_private_same_block_endpoints_trichotomy P hi hhi hhiprev s a.val hlabels
    have hlo' := originalRemaining_private_cut_trichotomy P lo hlo hloprev j
    have hhi' := originalRemaining_private_cut_trichotomy P hi hhi hhiprev j
    change lo < P.zeta s.castSucc ∧ P.xi r.succ < hi
    change (P.xi r.succ < lo ∧ P.zeta s.castSucc < lo) ∨
      (lo < P.xi r.succ ∧ lo < P.zeta s.castSucc) ∨
      (P.xi r.succ = lo ∧ P.zeta s.castSucc = lo) at hlo'
    change (P.xi r.succ < hi ∧ P.zeta s.castSucc < hi) ∨
      (hi < P.xi r.succ ∧ hi < P.zeta s.castSucc) ∨
      (P.xi r.succ = hi ∧ P.zeta s.castSucc = hi) at hhi'
    omega
  · rintro ⟨hcol, hrow⟩
    change lo < P.zeta s.castSucc at hcol
    change P.xi r.succ < hi at hrow
    have htlo := profile_private_same_block_endpoints_trichotomy P lo hlo hloprev
      (interiorBlockLast P a.val) r hlabelr
    have hthi := profile_private_same_block_endpoints_trichotomy P hi hhi hhiprev s a.val hlabels
    have h0 := originalRemaining_private_cut_trichotomy P lo hlo hloprev j
    change (P.xi r.succ < lo ∧ P.zeta s.castSucc < lo) ∨
      (lo < P.xi r.succ ∧ lo < P.zeta s.castSucc) ∨
      (P.xi r.succ = lo ∧ P.zeta s.castSucc = lo) at h0
    have h1 := originalRemaining_private_cut_trichotomy P hi hhi hhiprev j
    change (P.xi r.succ < hi ∧ P.zeta s.castSucc < hi) ∨
      (hi < P.xi r.succ ∧ hi < P.zeta s.castSucc) ∨
      (P.xi r.succ = hi ∧ P.zeta s.castSucc = hi) at h1
    have hlow : lo < P.zeta (interiorBlockLast P a.val).castSucc := by omega
    have hhigh : P.xi a.val.succ < hi := by omega
    have htfirst := profile_private_same_block_endpoints_trichotomy P lo hlo hloprev a.val r hlabel0
    have hfirst : lo < P.zeta a.val.castSucc := by omega
    exact originalBlockInWindow_of_endpoint_bounds P lo hi a hlow.le hhigh.le
      (fun _ => ⟨hfirst, hhigh⟩)

end SkewCornerDescent.Matrix.SelectedCoordinate
