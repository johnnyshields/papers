/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClassDefects
import SkewCornerDescent.Matrix.OriginalWindowActiveClasses
import SkewCornerDescent.Matrix.OriginalAmalgamationSpan

/-!
# Actual active-class tops and rational labels

Supports `shields-2026-skew-corner-descent.tex` (`lem:exposure`, `lem:dual-identities`).
Complete literal occurrence counts supply the reduced class defects. The original
residue classifier supplies every active class's actual closure top and rational
label. Distinct active labels and an inhabited active set are then derived, not
assumed as properties of an abstract response family. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows PhaseInventory
open scoped BigOperators

noncomputable local instance responseClassActiveRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual matched chart produces all active-class model premises from its
literal source and window inventories, with a positive reduced remainder. -/
theorem originalWindow_responseClass_active_labels {n m s t : ℕ}
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
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hrpos : 0 < r)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (r * (b - a))]
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁) :
    let d := b - a
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
    ∃ hB : 0 < originalSelectedCount (hD := hD) P, ∃ K : ℕ+,
      (K : ℤ) = originalHessenbergDistance (hD := hD) Q middle middle ∧ c.top < K ∧
      ∃ k s : ℕ, 0 < k ∧ 0 < s ∧ s ≤ d ∧ b = k * d + s ∧
      ∃ hperiod : r * d ≤ originalSelectedCount (hD := hD) P - 1,
      ∃ label : c.OriginalResponseClass P → ℚ,
      (∀ X, classDefect (c.originalResponseClassWord P (r * d) hperiod) 1 d s
          (r * s - 1) 0 X ≠ 0 →
        c.originalResponseClassTop P hB X = K ∧ X.val =
          c.regularResidue (c.originalHessenbergResponse Q middle middle) -
            (label X : OtherField c.top) * c.originalTrueCapProduct P) ∧
      (∀ X Y, classDefect (c.originalResponseClassWord P (r * d) hperiod) 1 d s
          (r * s - 1) 0 X ≠ 0 →
        classDefect (c.originalResponseClassWord P (r * d) hperiod) 1 d s
          (r * s - 1) 0 Y ≠ 0 → label X = label Y → X = Y) ∧
      (∃ X, classDefect (c.originalResponseClassWord P (r * d) hperiod) 1 d s
          (r * s - 1) 0 X ≠ 0) ∧
      (∑ X, classDefect (c.originalResponseClassWord P (r * d) hperiod) 1 d s
          (r * s - 1) 0 X) = (d : ℤ) := by
  classical
  let d := b - a
  have hd : 0 < d := by dsimp only [d]; omega
  have hdb : d < b := by dsimp only [d]; omega
  have had : a + d = b := by dsimp only [d]; omega
  obtain ⟨k, s, hk, hs, hsd, hbshape, _⟩ := positive_remainder_exists hd hdb
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hB : 0 < originalSelectedCount (hD := hD) P := by
    rw [hcountP]; exact Nat.mul_pos hrpos (by omega)
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]; exact Nat.mul_pos hrpos ha
  have hcQ := originalHorizontalClosure_profile_selected_count (hD := hD) P Q w hQ
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by
    rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega
  let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
    ⟨originalSelectedCount (hD := hD) P, by omega⟩
  let K := c.originalHessenbergTop Q hBQ middle middle le_rfl
  have hKeq : (K : ℤ) = originalHessenbergDistance (hD := hD) Q middle middle :=
    c.originalHessenbergTop_coe Q hBQ middle middle le_rfl
  have hNK : c.top < K := by
    have ht := c.originalHessenbergDistance_gt_top Q hBQ middle middle le_rfl
    exact_mod_cast (show (c.top : ℤ) < (K : ℤ) by omega)
  have hmaxW := originalWindow_component_span P W A q v u z hv hwindow hW hA
    (c.top : ℕ) hmax
  have hcutq' : ∀ x ∈ diagramInterior P.cells, content x ≠ q :=
    fun _ hx => privateDiagonal_avoids_interior hcutq hx
  have hcutLq' : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q :=
    fun _ hx => privateDiagonal_avoids_interior hcutLq hx
  obtain ⟨hperiod, hcounts, hsum⟩ := c.originalWindow_responseClass_defects P W q z v hv
    hW.symm hwindow hcutq hcutLq hC r d s k b a hrpos hs hk hbshape had hcountP hcountW
  obtain ⟨oldlabel, hlabels⟩ := (c.originalWindow_active_classes P W Q q v z w hwindow
    hW hQ hcutq' hcutLq' hC hmax hmaxW Λ b a d (by omega) hKU hKW p₀ p₁ hpq hdep).1
  let label := fun X : c.OriginalResponseClass P => oldlabel (c.originalResponseClassIndex P X)
  have hactive (X : c.OriginalResponseClass P)
      (hne : classDefect (c.originalResponseClassWord P (r * d) hperiod) 1 d s
        (r * s - 1) 0 X ≠ 0) :
      c.originalResponseClassTop P hB X = K ∧ X.val =
        c.regularResidue (c.originalHessenbergResponse Q middle middle) -
          (label X : OtherField c.top) * c.originalTrueCapProduct P := by
    have hflipP : (Finset.univ.filter fun i => X.val = c.originalInternalResidue P i).card =
        (Finset.univ.filter fun i => c.originalInternalResidue P i = X.val).card := by
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact eq_comm
    have hflipW : (Finset.univ.filter fun i => X.val = c.originalInternalResidue W i).card =
        (Finset.univ.filter fun i => c.originalInternalResidue W i = X.val).card := by
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact eq_comm
    have hneN : a * (Finset.univ.filter fun i => X.val = c.originalInternalResidue P i).card ≠
        b * (Finset.univ.filter fun i => X.val = c.originalInternalResidue W i).card := by
      intro he
      have heZ := congrArg (fun x : ℕ => (x : ℤ)) he
      simp only [Nat.cast_mul, hflipP, hflipW] at heZ
      exact hne ((hcounts X).symm.trans (sub_eq_zero.mpr heZ))
    have hold := hlabels (c.originalResponseClassIndex P X)
      (by rw [c.originalResponseClassIndex_spec P X]; exact hneN)
    constructor
    · apply Subtype.ext
      change (originalHessenbergDistance (hD := hD) P (c.originalResponseClassIndex P X)
        (c.originalResponseClassIndex P X)).toNat =
        (originalHessenbergDistance (hD := hD) Q middle middle).toNat
      rw [hold.1]
    · rw [c.originalResponseClassIndex_spec P X] at hold
      exact hold.2
  have hexists : ∃ X, classDefect (c.originalResponseClassWord P (r * d) hperiod) 1 d s
      (r * s - 1) 0 X ≠ 0 := by
    by_contra hn
    push Not at hn
    have hz := Finset.sum_eq_zero (fun X (_ : X ∈ Finset.univ) => hn X)
    rw [hz] at hsum
    exact (Nat.cast_ne_zero.mpr hd.ne') hsum.symm
  dsimp only
  refine ⟨hB, K, hKeq, hNK, k, s, hk, hs, hsd, hbshape, hperiod, label, hactive, ?_, hexists, hsum⟩
  intro X Y hX hY he
  apply Subtype.ext
  rw [(hactive X hX).2, (hactive Y hY).2, he]

end SkewCornerDescent.Matrix.SelectedCoordinate
