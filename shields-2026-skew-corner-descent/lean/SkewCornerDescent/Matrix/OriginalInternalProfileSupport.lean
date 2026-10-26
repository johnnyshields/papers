/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalProfileGeneratorSupport
import SkewCornerDescent.Matrix.OriginalInternalSelfJet

/-!
# Actual short-period support of complete endpoint profiles

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The source gap period supplies the strict generator bound for every genuine
internal interval. Both full profile coefficient families are controlled,
without freezing any normal inverse jets. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing CyclicWindows
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual short-period geometry supplies simultaneous lower-field support of
both complete internal endpoint profiles, including every inverse coefficient. -/
theorem originalInternal_profiles_mem_lower {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (H : ℕ+) (hNH : c.top < H)
    (hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ))
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) (k : ℕ) :
    (c.originalInternalEndpointProfiles P i).1.coeff k ∈ residueLowerField c.top H ∧
      (c.originalInternalEndpointProfiles P i).2.coeff k ∈ residueLowerField c.top H := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val + 1, by have := i.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  have hspan : P.xi (originalRowSplitEquiv P (.inl (some (E a)))) -
      P.zeta (originalColSplitEquiv P (.inl (some (E b)))) < (H : ℤ) := by
    have h := (c.originalInternalDistance_short_period P r d hp i i le_rfl (by omega)).trans hheight
    change P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P a.succ))) -
      P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P b.castSucc))) < _ at h
    rwa [originalHessenbergRows_succ, originalHessenbergCols_castSucc] at h
  exact (c.originalLocalResponse_profiles_mem_lower P (some (E a)) (some (E b)) H hNH hspan).2 k

/-- No later protected generator occurs in either actual full internal profile. -/
theorem originalInternal_profile_coeff_high_zero {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)] (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (H : ℕ+) (hNH : c.top < H)
    (hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ))
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) (k : ℕ) :
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hNH⟩
        ((c.originalInternalEndpointProfiles P i).1.coeff k) = 0 ∧
      residueGeneratorDeriv c.top ⟨H, ne_of_gt hNH⟩
        ((c.originalInternalEndpointProfiles P i).2.coeff k) = 0 := by
  have hs := c.originalInternal_profiles_mem_lower P r d hn hp H hNH hheight i k
  exact ⟨residueGeneratorDeriv_lower _ _ hs.1, residueGeneratorDeriv_lower _ _ hs.2⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
