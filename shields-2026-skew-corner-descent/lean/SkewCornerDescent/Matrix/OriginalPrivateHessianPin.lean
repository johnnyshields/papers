/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosurePhaseHessian
import SkewCornerDescent.Matrix.OriginalPrivatePeriodComparison
import SkewCornerDescent.Matrix.OriginalCapProductHessian

/-!
# The actual private mixed Hessian pins the closure correction

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Produced period-boundary coordinates, actual phase-core equality, and the
complete literal cap comparison supply the mixed jet, including its doubled
value at a coincident square. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- When the upper true cap is longer, the produced lower private interval's
mixed jet differs from its actual horizontal reference only by the ordinary
vertical cut unit. All phase, coordinate, and inverse matches are derived. -/
theorem originalPrivate_lower_hessian_pin {n m : ℕ}
    (P : Profile n) [NeZero (originalSelectedCount (hD := hD) P)]
    (Q : Profile m) (v w : ℤ × ℤ) (q : ℤ) (hv : content v = q)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hprefix : IsSkew (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hprevcut : diagLo P.cells (P.xi 0 - q - 1) = diagHi P.cells (P.xi 0 - q - 1))
    (a b r : ℕ) [NeZero r] (ha : 0 < a) (hab : a < b)
    (hcount : originalSelectedCount (hD := hD) P = r * b)
    (hcard : Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)) = r * a)
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hstep : ∀ i j : Fin (originalSelectedCount (hD := hD) P), j.val = i.val + r →
      ∀ k, k < (c.top : ℕ) →
        (c.originalSelectedCoreLeft P j).coeff k = (c.originalSelectedCoreLeft P i).coeff k ∧
        (c.originalSelectedCoreRight P j).coeff k =
          (c.originalSelectedCoreRight P i).coeff k)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (cur prev : ℤ × ℤ) (hcur : cur ∈ P.cells) (hprev : prev ∈ P.cells)
    (hc : content cur = P.xi 0 - q) (hp : content prev = P.xi 0 - q - 1)
    (hlong : originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) ≤
      originalHessenbergDistance (hD := hD) P 0 0) :
    let hB := NeZero.pos (originalSelectedCount (hD := hD) P)
    let i : Fin (originalSelectedCount (hD := hD) P) := ⟨r * (b - a) - 1, by
      have hlt := Nat.mul_lt_mul_of_pos_left (show b - a < b by omega) (NeZero.pos r)
      omega⟩
    let j : Fin (originalSelectedCount (hD := hD) P) := ⟨r * (b - a), by
      have hlt := Nat.mul_lt_mul_of_pos_left (show b - a < b by omega) (NeZero.pos r)
      omega⟩
    let first : Fin (originalSelectedCount (hD := hD) P) := ⟨0, hB⟩
    let last : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
    let E := originalSelectedEnumeration (hD := hD) P
    let p := c.originalHessenbergTop P hB 0 0 le_rfl
    let t := c.originalHessenbergTop P hB (Fin.last _) (Fin.last _) le_rfl
    let hp' := c.originalHessenbergTop_gt_selected P hB 0 0 le_rfl
    let ht' := c.originalHessenbergTop_gt_selected P hB (Fin.last _) (Fin.last _) le_rfl
    residueGeneratorDeriv c.top ⟨p, ne_of_gt hp'⟩
      (residueGeneratorDeriv c.top ⟨t, ne_of_gt ht'⟩
        (c.regularResidue (c.originalLocalResponse P (some (E i)) (some (E j))) -
          c.regularResidue (c.originalLocalResponse Q
            (some (originalHorizontalClosureSelectedCopy P Q w hQ true (E last)))
            (some (originalHorizontalClosureSelectedCopy P Q w hQ false (E first)))))) =
      if cur.2 = prev.2 then -(if p = t then 2 else 1) else 0 := by
  intro hB i j first last E p t hp' ht'
  have hr := NeZero.pos r
  have hpos : 0 < r * (b - a) := Nat.mul_pos hr (by omega)
  have hij : i < j := by change i.val < j.val; dsimp only [i, j]; omega
  have hpc : (p : ℤ) = originalHessenbergDistance (hD := hD) P 0 0 :=
    c.originalHessenbergTop_coe P hB 0 0 le_rfl
  have htc : (t : ℤ) = originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) :=
    c.originalHessenbergTop_coe P hB (Fin.last _) (Fin.last _) le_rfl
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E i))))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E j))))
  let xr := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E last)))) + P.xi 0
  let A := (c.originalSelectedCoreLeft P i).toLaurent
  let T := (c.originalSelectedCoreRight P j).toLaurent
  have hcoords := c.originalPrivateLower_cap_coordinates P a b r ha hab q v hv
    hprefix hwindow hcutq hcutLq hcount hcard hgap
  dsimp only at hcoords
  change y = P.xi 0 - q - _ ∧ x = P.xi 0 - q + _ at hcoords
  have hsum : (p : ℤ) + (t : ℤ) = x - y := by omega
  have hfirst := originalHessenbergDistance_first (hD := hD) P hB
  have hlast := originalHessenbergDistance_last (hD := hD) P hB
  unfold originalFirstCapDistance at hfirst
  unfold originalLastCapDistance at hlast
  rw [P.zeta_last] at hlast
  simp only [sub_zero] at hlast
  have hxr : xr = x + q := by
    dsimp only [xr]
    rw [originalRowSplitEquiv_selected]
    dsimp only [E, last] at *
    omega
  have hsumRef : (p : ℤ) + (t : ℤ) =
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E last)))) + P.xi 0 -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E first)))) := by
    rw [originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
    dsimp only [E, first, last] at *
    omega
  have hphase := c.originalSelectedCore_private_boundary P r b (b - a) hr
    (by omega) (by omega) hcount hstep i j first last rfl rfl rfl rfl
  have hsource := c.originalLocalResponse_phase_hessian P i j hij hmax p t hp' ht' hsum
  have href := c.originalHorizontalClosure_phase_hessian P Q w hQ last first hmax
    p t hp' ht' hsumRef
  dsimp only at hsource href
  rw [← hphase.1, ← hphase.2] at href
  change _ = -c.originalIntervalInverseProjection Q _ _ A T (xr - (t : ℤ)) -
    c.originalIntervalInverseProjection Q _ _ A T (xr - (p : ℤ)) at href
  have hnorm := c.originalSelectedCore_laurent_normalized P i j
  have compare (z : ℤ) (hz : z ≤ P.xi 0 - q) :=
    c.originalPrivatePeriod_comparison_lower P Q v w q hv hQ hprefix hwindow hcutq hcutLq
      hprevcut a b r ha hab hcount hcard hgap cur prev hcur hprev hc hp
      A T z hz hnorm.1 hnorm.2.1 hnorm.2.2.1 hnorm.2.2.2
  have hzt : x - (t : ℤ) = P.xi 0 - q := by omega
  have hzp : x - (p : ℤ) ≤ P.xi 0 - q := by omega
  have hc1 := compare (x - (t : ℤ)) (by omega)
  have hc2 := compare (x - (p : ℤ)) hzp
  dsimp only at hc1 hc2
  rw [hxr, show x + q - (t : ℤ) = (x - (t : ℤ)) + q by omega,
    show x + q - (p : ℤ) = (x - (p : ℤ)) + q by omega] at href
  rw [map_sub, map_sub, hsource, href, hc1, hc2]
  by_cases hV : cur.2 = prev.2
  · by_cases he : p = t
    · simp only [hzt, hV, he, and_self, ↓reduceIte]
      ring
    · have he' : (p : ℤ) ≠ (t : ℤ) := by exact_mod_cast he
      have hz : x - (p : ℤ) ≠ P.xi 0 - q := by omega
      simp only [hzt, hz, hV, he, and_true, ↓reduceIte]
      ring
  · simp only [hV, and_false, ↓reduceIte, add_zero]
    ring

/-- When the lower true cap is longer, the complementary upper private
interval gives the same mixed jet, with all reference weights and coordinates
produced from the actual period and literal windows. -/
theorem originalPrivate_upper_hessian_pin {n m : ℕ}
    (P : Profile n) [NeZero (originalSelectedCount (hD := hD) P)]
    (Q : Profile m) (v w : ℤ × ℤ) (q : ℤ) (hv : content v = q)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hprefix : IsSkew (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hprevcut : diagLo P.cells (q - 1) = diagHi P.cells (q - 1))
    (a b r : ℕ) [NeZero r] (ha : 0 < a) (hab : a < b)
    (hcount : originalSelectedCount (hD := hD) P = r * b)
    (hcard : Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)) = r * a)
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hstep : ∀ i j : Fin (originalSelectedCount (hD := hD) P), j.val = i.val + r →
      ∀ k, k < (c.top : ℕ) →
        (c.originalSelectedCoreLeft P j).coeff k = (c.originalSelectedCoreLeft P i).coeff k ∧
        (c.originalSelectedCoreRight P j).coeff k =
          (c.originalSelectedCoreRight P i).coeff k)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (cur prev : ℤ × ℤ) (hcur : cur ∈ P.cells) (hprev : prev ∈ P.cells)
    (hc : content cur = q) (hp : content prev = q - 1)
    (hlong : originalHessenbergDistance (hD := hD) P 0 0 ≤
      originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _)) :
    let hB := NeZero.pos (originalSelectedCount (hD := hD) P)
    let i : Fin (originalSelectedCount (hD := hD) P) := ⟨r * a - 1, by
      have hlt := Nat.mul_lt_mul_of_pos_left hab (NeZero.pos r)
      omega⟩
    let j : Fin (originalSelectedCount (hD := hD) P) := ⟨r * a, by
      have hlt := Nat.mul_lt_mul_of_pos_left hab (NeZero.pos r)
      omega⟩
    let first : Fin (originalSelectedCount (hD := hD) P) := ⟨0, hB⟩
    let last : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
    let E := originalSelectedEnumeration (hD := hD) P
    let p := c.originalHessenbergTop P hB 0 0 le_rfl
    let t := c.originalHessenbergTop P hB (Fin.last _) (Fin.last _) le_rfl
    let hp' := c.originalHessenbergTop_gt_selected P hB 0 0 le_rfl
    let ht' := c.originalHessenbergTop_gt_selected P hB (Fin.last _) (Fin.last _) le_rfl
    residueGeneratorDeriv c.top ⟨p, ne_of_gt hp'⟩
      (residueGeneratorDeriv c.top ⟨t, ne_of_gt ht'⟩
        (c.regularResidue (c.originalLocalResponse P (some (E i)) (some (E j))) -
          c.regularResidue (c.originalLocalResponse Q
            (some (originalHorizontalClosureSelectedCopy P Q w hQ true (E last)))
            (some (originalHorizontalClosureSelectedCopy P Q w hQ false (E first)))))) =
      if cur.2 = prev.2 then -(if p = t then 2 else 1) else 0 := by
  intro hB i j first last E p t hp' ht'
  have hr := NeZero.pos r
  have hpos : 0 < r * a := Nat.mul_pos hr ha
  have hij : i < j := by change i.val < j.val; dsimp only [i, j]; omega
  have hpc : (p : ℤ) = originalHessenbergDistance (hD := hD) P 0 0 :=
    c.originalHessenbergTop_coe P hB 0 0 le_rfl
  have htc : (t : ℤ) = originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) :=
    c.originalHessenbergTop_coe P hB (Fin.last _) (Fin.last _) le_rfl
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E i))))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E j))))
  let xr := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E last)))) + P.xi 0
  let A := (c.originalSelectedCoreLeft P i).toLaurent
  let T := (c.originalSelectedCoreRight P j).toLaurent
  have hcoords := c.originalPrivateUpper_cap_coordinates P a b r ha hab q v hv
    hprefix hwindow hcutq hcutLq hcount hcard hgap
  dsimp only at hcoords
  change x = q + _ ∧ y = q - _ at hcoords
  have hsum : (p : ℤ) + (t : ℤ) = x - y := by omega
  have hfirst := originalHessenbergDistance_first (hD := hD) P hB
  have hlast := originalHessenbergDistance_last (hD := hD) P hB
  unfold originalFirstCapDistance at hfirst
  unfold originalLastCapDistance at hlast
  rw [P.zeta_last] at hlast
  simp only [sub_zero] at hlast
  have hxr : xr = x + P.xi 0 - q := by
    dsimp only [xr]
    rw [originalRowSplitEquiv_selected]
    dsimp only [E, last] at *
    omega
  have hsumRef : (p : ℤ) + (t : ℤ) =
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E last)))) + P.xi 0 -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E first)))) := by
    rw [originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
    dsimp only [E, first, last] at *
    omega
  have hphase := c.originalSelectedCore_private_boundary P r b a hr ha hab
    hcount hstep i j first last rfl rfl rfl rfl
  have hsource := c.originalLocalResponse_phase_hessian P i j hij hmax p t hp' ht' hsum
  have href := c.originalHorizontalClosure_phase_hessian P Q w hQ last first hmax
    p t hp' ht' hsumRef
  dsimp only at hsource href
  rw [← hphase.1, ← hphase.2] at href
  change _ = -c.originalIntervalInverseProjection Q _ _ A T (xr - (t : ℤ)) -
    c.originalIntervalInverseProjection Q _ _ A T (xr - (p : ℤ)) at href
  have hnorm := c.originalSelectedCore_laurent_normalized P i j
  have compare (z : ℤ) (hz : q ≤ z) :=
    c.originalPrivatePeriod_comparison_upper P Q v w q hv hQ hprefix hwindow hcutq hcutLq
      hprevcut a b r ha hab hcount hcard hgap cur prev hcur hprev hc hp
      A T z hz hnorm.1 hnorm.2.1 hnorm.2.2.1 hnorm.2.2.2
  have hzt : x - (t : ℤ) = q := by omega
  have hzp : q ≤ x - (p : ℤ) := by omega
  have hc1 := compare (x - (t : ℤ)) (by omega)
  have hc2 := compare (x - (p : ℤ)) hzp
  dsimp only at hc1 hc2
  rw [hxr, show x + P.xi 0 - q - (t : ℤ) = (x - (t : ℤ)) + P.xi 0 - q by omega,
    show x + P.xi 0 - q - (p : ℤ) = (x - (p : ℤ)) + P.xi 0 - q by omega] at href
  rw [map_sub, map_sub, hsource, href, hc1, hc2]
  by_cases hV : cur.2 = prev.2
  · by_cases he : p = t
    · simp only [hzt, hV, he, and_self, ↓reduceIte]
      ring
    · have he' : (p : ℤ) ≠ (t : ℤ) := by exact_mod_cast he
      have hz : x - (p : ℤ) ≠ q := by omega
      simp only [hzt, hz, hV, he, and_true, ↓reduceIte]
      ring
  · simp only [hV, and_false, ↓reduceIte, add_zero]
    ring

end SkewCornerDescent.Matrix.SelectedCoordinate
