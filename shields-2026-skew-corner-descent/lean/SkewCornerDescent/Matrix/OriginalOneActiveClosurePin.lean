/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPrivateHessianPin
import SkewCornerDescent.Matrix.OriginalPrivateActivePhase
import SkewCornerDescent.Matrix.OriginalWindowActiveClasses
import SkewCornerDescent.Matrix.OriginalResponseClassDefects
import SkewCornerDescent.Matrix.ResidueAffineHessian
import SkewCornerDescent.Matrix.OriginalAmalgamationSpan

/-!
# Actual one-active nullspace closure-plane pin

Formalizes `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Corner powers produce occurrence counts. Literal equal windows identify the
omitted phase, and the complete mixed-Hessian comparison pins its rational
label to the actual ordinary cut direction. Selected rows, columns, and full
nonrow unit components are retained. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
attribute [local instance] Classical.propDecidable

noncomputable local instance oneActiveClosureRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual affine label of the omitted periodic phase is zero at a
horizontal private cut and one at a vertical private cut. Counts, cap jets,
full inverse matches, phase weights, and both representative identifications
are supplied by the original source and its literal windows. -/
theorem originalOneActive_closure_plane_pin {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (Q : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hprevq : diagLo P.cells (q - 1) = diagHi P.cells (q - 1))
    (hprevLq : diagLo P.cells (P.xi 0 - q - 1) = diagHi P.cells (P.xi 0 - q - 1))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hr : 0 < r)
    (hprime : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (r * (b - a))] [NeZero (r * b)]
    (p₀ p₁ : Polynomial ℚ) (hcoprime : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁)
    (active : c.OriginalResponseClass P)
    (hactive : c.originalResponseClassExponent P W a b active ≠ 0)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hgap : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (hperiod : r * (b - a) ≤ originalSelectedCount (hD := hD) P - 1)
    (hresponse : Function.Periodic
      (closureWord (finiteWordCycle (n := r * (b - a)) (c.originalInternalResidue P) hperiod)
        active.val (r * b)) (r : ZMod (r * b)))
    (hstep : ∀ i j : Fin (originalSelectedCount (hD := hD) P), j.val = i.val + r →
      ∀ k, k < (c.top : ℕ) →
        (c.originalSelectedCoreLeft P j).coeff k = (c.originalSelectedCoreLeft P i).coeff k ∧
        (c.originalSelectedCoreRight P j).coeff k =
          (c.originalSelectedCoreRight P i).coeff k)
    (lo prevlo hi prevhi : ℤ × ℤ)
    (hlo : lo ∈ P.cells) (hprevlo : prevlo ∈ P.cells)
    (hhi : hi ∈ P.cells) (hprevhi : prevhi ∈ P.cells)
    (hclo : content lo = P.xi 0 - q) (hcprevlo : content prevlo = P.xi 0 - q - 1)
    (hchi : content hi = q) (hcprevhi : content prevhi = q - 1)
    (hdir : lo.2 = prevlo.2 ↔ hi.2 = prevhi.2) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q w hQ]
        omega⟩
    active.val = c.regularResidue (c.originalHessenbergResponse Q middle middle) -
      (if lo.2 = prevlo.2 then 1 else 0) * c.originalTrueCapProduct P := by
  intro middle
  let : NeZero r := ⟨Nat.ne_of_gt hr⟩
  have hcount : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hprime, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hprime, Nat.mul_comm]
  have hB := NeZero.pos (originalSelectedCount (hD := hD) P)
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos hr ha
  have hnlo := profile_normalized_lower_private_boundaries P
  have hcard : Fintype.card (OriginalWindowSelected (hD := hD) P 0 (P.xi 0 - q)) = r * a := by
    rw [originalWindow_selected_count P W 0 (P.xi 0 - q) z hW.symm
      (private_diagonal_no_interior hnlo.1) (private_diagonal_no_interior hcutLq)]
    exact hcountW
  have hprefix : IsSkew (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) := by
    rw [← hW]
    exact isSkew_translate z W.isConnectedSkew_cells.1
  have hmaxW := originalWindow_component_span P W A q v u z hv hwindow hW hA
    (c.top : ℕ) hmax
  obtain ⟨label, hlabels⟩ := (c.originalWindow_active_classes P W Q q v z w hwindow hW hQ
    (private_diagonal_no_interior hcutq) (private_diagonal_no_interior hcutLq) hC hmax hmaxW
    Λ b a (b - a) (by omega) hKU hKW p₀ p₁ hcoprime hdep).1
  let rep := c.originalResponseClassIndex P active
  have hrep := c.originalResponseClassIndex_spec P active
  change c.regularResidue (c.originalHessenbergResponse P rep rep) = active.val at hrep
  have hneq : a * (Finset.univ.filter fun i => active.val = c.originalInternalResidue P i).card ≠
      b * (Finset.univ.filter fun i => active.val = c.originalInternalResidue W i).card := by
    intro he
    have hcast := congrArg (fun k : ℕ => (k : ℤ)) he
    simp only [Nat.cast_mul] at hcast
    have hflipP : (Finset.univ.filter fun i => active.val = c.originalInternalResidue P i).card =
        (Finset.univ.filter fun i => c.originalInternalResidue P i = active.val).card := by
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact eq_comm
    have hflipW : (Finset.univ.filter fun i => active.val = c.originalInternalResidue W i).card =
        (Finset.univ.filter fun i => c.originalInternalResidue W i = active.val).card := by
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact eq_comm
    rw [hflipP, hflipW] at hcast
    exact hactive (sub_eq_zero.mpr hcast)
  have hlabel := (hlabels rep (by simpa only [hrep] using hneq)).2
  rw [hrep] at hlabel
  let α := label rep
  let S₀ := c.regularResidue (c.originalHessenbergResponse Q middle middle)
  change active.val = S₀ - (α : OtherField c.top) * c.originalTrueCapProduct P at hlabel
  let p := c.originalHessenbergTop P hB 0 0 le_rfl
  let t := c.originalHessenbergTop P hB (Fin.last _) (Fin.last _) le_rfl
  let hp := c.originalHessenbergTop_gt_selected P hB 0 0 le_rfl
  let ht := c.originalHessenbergTop_gt_selected P hB (Fin.last _) (Fin.last _) le_rfl
  let jgen : {k : ℕ+ // k ≠ c.top} := ⟨p, ne_of_gt hp⟩
  let kgen : {k : ℕ+ // k ≠ c.top} := ⟨t, ne_of_gt ht⟩
  let weight : OtherField c.top := if p = t then 2 else 1
  have hw : weight ≠ 0 := by
    dsimp only [weight]
    split_ifs <;> norm_num
  have hcap := c.originalTrueCapProduct_hessian_source_order P hB hmax
  have hRef := c.originalHorizontalClosure_middle_local_response P Q w hQ hB
  have point (m : ℕ) (hm : 0 < m) (hmb : m < b) :
      let i : Fin (originalSelectedCount (hD := hD) P) := ⟨r * m - 1, by
        have hlt := Nat.mul_lt_mul_of_pos_left hmb hr
        omega⟩
      let j : Fin (originalSelectedCount (hD := hD) P) := ⟨r * m, by
        have hlt := Nat.mul_lt_mul_of_pos_left hmb hr
        omega⟩
      c.regularResidue (c.originalLocalResponse P
        (some (originalSelectedEnumeration (hD := hD) P i))
        (some (originalSelectedEnumeration (hD := hD) P j))) = active.val := by
    intro i j
    have hlt := Nat.mul_lt_mul_of_pos_left hmb hr
    have hpoint := c.originalPrivate_boundary_active P W q z v hv hW.symm hwindow
      hcutq hcutLq r b a m hr ha hm hmb hcount hcountW active hperiod hresponse
    dsimp only at hpoint
    unfold originalInternalResidue originalHessenbergResponse at hpoint
    have hpos : 0 < r * m := Nat.mul_pos hr hm
    have hrow : (⟨r * m - 1 + 1, by omega⟩ :
        Fin (originalSelectedCount (hD := hD) P + 1)) = i.succ := rfl
    have hcol : (⟨r * m - 1 + 1, by omega⟩ :
        Fin (originalSelectedCount (hD := hD) P + 1)) = j.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp only [j]
      omega
    change c.regularResidue (c.originalLocalResponse P
      (originalHessenbergRows (hD := hD) P ⟨r * m - 1 + 1, by omega⟩)
      (originalHessenbergCols (hD := hD) P ⟨r * m - 1 + 1, by omega⟩)) = active.val at hpoint
    rw [hrow, originalHessenbergRows_succ, ← hrow, hcol,
      originalHessenbergCols_castSucc] at hpoint
    exact hpoint
  have finish (e : ℚ)
      (hdiff : residueGeneratorDeriv c.top jgen
        (residueGeneratorDeriv c.top kgen (active.val - S₀)) = -(e : OtherField c.top) * weight) :
      α = e := by
    exact residue_affine_label_of_mixed_difference c.top jgen kgen α e
      active.val S₀ (c.originalTrueCapProduct P) weight hw hlabel hdiff hcap
  have he : α = if lo.2 = prevlo.2 then 1 else 0 := by
    by_cases hlong : originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) ≤
        originalHessenbergDistance (hD := hD) P 0 0
    · have hpin := c.originalPrivate_lower_hessian_pin P Q v w q hv hQ hprefix hwindow
        hcutq hcutLq hprevLq a b r ha (by omega) hcount hcard hgap hstep hmax
        lo prevlo hlo hprevlo hclo hcprevlo hlong
      have hpoint := point (b - a) (by omega) (by omega)
      dsimp only at hpin hpoint hRef
      rw [hpoint, ← hRef] at hpin
      apply finish
      by_cases hV : lo.2 = prevlo.2 <;>
        simpa only [hV, ↓reduceIte, Rat.cast_one, Rat.cast_zero, neg_zero, zero_mul,
          neg_mul, one_mul, weight, jgen, kgen, p, t, hp, ht, S₀] using hpin
    · have hlong' : originalHessenbergDistance (hD := hD) P 0 0 ≤
          originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) := le_of_not_ge hlong
      have hpin := c.originalPrivate_upper_hessian_pin P Q v w q hv hQ hprefix hwindow
        hcutq hcutLq hprevq a b r ha (by omega) hcount hcard hgap hstep hmax
        hi prevhi hhi hprevhi hchi hcprevhi hlong'
      have hpoint := point a ha (by omega)
      dsimp only at hpin hpoint hRef
      rw [hpoint, ← hRef] at hpin
      apply finish
      by_cases hV : lo.2 = prevlo.2
      · have hV' := hdir.mp hV
        simpa only [hV, hV', ↓reduceIte, Rat.cast_one, neg_mul, one_mul,
          weight, jgen, kgen, p, t, hp, ht, S₀] using hpin
      · have hV' : hi.2 ≠ prevhi.2 := fun h => hV (hdir.mpr h)
        simpa only [hV, hV', ↓reduceIte, Rat.cast_zero, neg_zero, zero_mul,
          weight, jgen, kgen, p, t, hp, ht, S₀] using hpin
  rw [he] at hlabel
  by_cases hV : lo.2 = prevlo.2 <;>
    simpa only [hV, ↓reduceIte, Rat.cast_one, Rat.cast_zero, S₀] using hlabel

end SkewCornerDescent.Matrix.SelectedCoordinate
