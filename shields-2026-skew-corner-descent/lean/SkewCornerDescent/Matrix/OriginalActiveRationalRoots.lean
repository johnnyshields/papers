/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ActualPlaneRootSupport
import SkewCornerDescent.Matrix.OriginalWindowRationalFactors
import SkewCornerDescent.Matrix.OriginalClosureNormalQuotient

/-!
# Actual active plane labels and the reduced rational roots

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The full original chart produces the signed representation, coprime root
support, complete window class inclusion, and both directions of the active
class/root correspondence. No support or labeling premise is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

noncomputable local instance actualRationalRootsRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every active original class produces a root of the actual coprime rational
pair, and every such root produces an active original class. The only coordinate
change is the produced closure-orientation sign. -/
theorem originalWindow_active_rational_roots {n m s t : ℕ}
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
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
    ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ ∃ label : c.OriginalResponseClass P → ℚ,
      (∀ X, c.originalResponseClassExponent P W a b X ≠ 0 →
        X.val = c.regularResidue (c.originalHessenbergResponse Q middle middle) -
          (label X : OtherField c.top) * c.originalTrueCapProduct P) ∧
      (∀ X Y, c.originalResponseClassExponent P W a b X ≠ 0 →
        c.originalResponseClassExponent P W a b Y ≠ 0 → label X = label Y → X = Y) ∧
      (∀ X, c.originalResponseClassExponent P W a b X ≠ 0 →
        p₀.eval ((δ : ℚ) * label X) = 0 ∨ p₁.eval ((δ : ℚ) * label X) = 0) ∧
      (∀ α : ℚ, p₀.eval α = 0 ∨ p₁.eval α = 0 →
        ∃ X : c.OriginalResponseClass P, c.originalResponseClassExponent P W a b X ≠ 0 ∧
          α = (δ : ℚ) * label X) := by
  classical
  obtain ⟨label, hlabels, hinj⟩ := c.originalWindow_plane_labels P W A Q q v u z w hv hwindow
    hW hA hQ hcutq hcutLq hmax Λ b a r ha hab hrpos hr hKU hKW p₀ p₁ hpq hdep
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hB : 0 < originalSelectedCount (hD := hD) P := by
    rw [hcountP]
    exact Nat.mul_pos hrpos (by omega)
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos hrpos ha
  have hmaxW := originalWindow_component_span P W A q v u z hv hwindow hW hA (c.top : ℕ) hmax
  have hcutq' : ∀ x ∈ diagramInterior P.cells, content x ≠ q :=
    fun _ hx => privateDiagonal_avoids_interior hcutq hx
  have hcutLq' : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q :=
    fun _ hx => privateDiagonal_avoids_interior hcutLq hx
  obtain ⟨hu, _, ε, δ, s, e, hδ, hε, he, _, hs, hcounts, _, hfactor⟩ :=
    c.originalWindow_rational_factorization P W Q q v z w hwindow hW hQ hcutq' hcutLq'
      hC hmax hmaxW Λ b a (b - a) (by omega) hKU hKW p₀ p₁ hpq hdep
  have hPne := c.originalSchur_residue_ne_zero P hB hmax
  have hWne := c.originalSchur_residue_ne_zero W hC hmaxW
  have hratio : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b ≠ 0 :=
    div_ne_zero (pow_ne_zero a hPne) (pow_ne_zero b hWne)
  have hp₁ : p₁ ≠ 0 := by
    intro hz
    rw [hz, map_zero, div_zero] at hdep
    exact hratio hdep
  have hcross : p₀ * signedRationalDenominator s e = signedRationalNumerator ε s e * p₁ :=
    transcendental_rational_representation_unique hu p₀ p₁
      (signedRationalNumerator ε s e) (signedRationalDenominator s e) hp₁
      (signedRationalDenominator_ne_zero s e)
      (hdep.symm.trans (hfactor.trans (signedRational_aeval _ ε s e).symm))
  have hεQ : (ε : ℚ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hWcells : W.cells = translate (-z)
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) := by
    rw [← hW, SkewGluing.translate_translate, neg_add_cancel, translate_zero]
  dsimp only at hlabels hinj hcounts ⊢
  refine ⟨δ, hδ, label, hlabels, hinj, ?_, ?_⟩
  · intro X hX
    have hm := c.original_active_class_label_mem_support P W Q _ a b δ hδ label s e hs
      hcounts X hX (hlabels X hX)
    exact (signedRational_root_support p₀ p₁ hpq ε s e hεQ he hcross _).mp hm
  · intro α hα
    have hm := (signedRational_root_support p₀ p₁ hpq ε s e hεQ he hcross α).mpr hα
    exact c.original_signed_support_label_exists P W Q _ q (-z) hWcells hcutLq hB hmax
      a b δ hδ label s e hs hcounts hlabels α hm

end SkewCornerDescent.Matrix.SelectedCoordinate
