/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TransposeFrameInventory
import SkewCornerDescent.Matrix.OriginalRowRationalRoots
import SkewCornerDescent.Matrix.SelectedCapTranspose

/-!
# Consecutive integral labels on the complete actual column chart

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Whole-diagram transpose produces a complete row chart, and complementary
closures reflect its coprime rational pair. The actual class/root factory
then bounds the original column labels without identifying individual inverse
responses under transpose. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

noncomputable local instance columnPlaneRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The original active labels of a whole all-column inventory lie in three
consecutive integers, reduced to two at coincident actual source cap tops.
Every transposed chart, residue match, root correspondence, cap correspondence,
and orientation sign is produced from the actual original data. -/
theorem originalWindow_column_plane_labels {n m s t : ℕ}
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
    (hcutqBefore : diagLo P.cells (q - 1) = diagHi P.cells (q - 1))
    (hcutLqBefore : diagLo P.cells (P.xi 0 - q - 1) = diagHi P.cells (P.xi 0 - q - 1))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hcol : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.snd).card = 1)
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hrpos : 0 < r)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁) :
    let sourceLimit := if originalHessenbergDistance (hD := hD) P 0 0 =
      originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) then 1 else 2
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q w hQ]; omega⟩
    ∃ label : c.OriginalResponseClass P → ℚ, ∃ start : ℤ,
      (∀ X, c.originalResponseClassExponent P W a b X ≠ 0 →
        (∃ j : ℕ, j ≤ sourceLimit ∧ label X = (start : ℚ) + (j : ℚ)) ∧
        X.val = c.regularResidue (c.originalHessenbergResponse Q middle middle) -
          (label X : OtherField c.top) * c.originalTrueCapProduct P) ∧
      (∀ X Y, c.originalResponseClassExponent P W a b X ≠ 0 →
        c.originalResponseClassExponent P W a b Y ≠ 0 → label X = label Y → X = Y) := by
  classical
  have hdpos : 0 < b - a := by omega
  let : NeZero (r * (b - a)) := ⟨Nat.ne_of_gt (Nat.mul_pos hrpos hdpos)⟩
  obtain ⟨δc, hδc, label, hlabels, hinj, hroots, _⟩ := c.originalWindow_active_rational_roots
    P W A Q q v u z w hv hwindow hW hA hQ hcutq hcutLq hmax Λ b a r ha hab hrpos hr
      hKU hKW p₀ p₁ hpq hdep
  obtain ⟨d, hdtop⟩ := exists_transposed_selectedCoordinate c
  obtain ⟨nt, T, vt, hT⟩ := (isConnectedSkew_transpose P.isConnectedSkew_cells).exists_profile_cells
  obtain ⟨ns, S, vs, hS⟩ := (isConnectedSkew_transpose W.isConnectedSkew_cells).exists_profile_cells
  obtain ⟨nb, B, vb, hAT⟩ :=
    (isConnectedSkew_transpose A.isConnectedSkew_cells).exists_profile_cells
  obtain ⟨nh, H, vh, hHT⟩ := (originalHorizontalClosure_connected T).exists_profile_cells
  have hvT : content (-v.swap) = q := (content_neg_swap v).trans hv
  have hwindowT := complete_profile_window_transpose P T v vt q hT hwindow
  have hWT := complete_transposed_shared_window P T W S vt v z vs q hT hS hwindow hW
  have hAB := complete_overlap_union_transpose P T A v vt u hT hA
  rw [hAT, SkewGluing.translate_translate] at hAB
  obtain ⟨hcutT, hcutLT⟩ := complete_transpose_private_cuts P T vt hT q hcutqBefore hcutLqBefore
  have hrowsT := transpose_profile_all_columns_rows P T vt hT hcol
  have hmaxT := transpose_profile_component_span P T vt hT (c.top : ℕ) hmax
  rw [← hdtop] at hmaxT
  have hKUT := transpose_profile_corner_power P T vt hT Λ b hKU
  have hKWT := transpose_profile_corner_power W S vs hS Λ a hKW
  have hrT : primeOrder (cellSchur (transpose D) (isSkew_transpose hD.1)) (schurInvolution Λ) = r :=
    (transposed_selected_primeOrder (hD := hD) Λ).trans hr
  have hB : 0 < originalSelectedCount (hD := hD) P := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
    exact Nat.mul_pos hrpos (by omega)
  have hdepH : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap (cellSchur (originalHorizontalClosure P)
        (originalHorizontalClosure_connected P).1) / c.residueMap P.schur ^ 2) p₀ /
      Polynomial.aeval (c.residueMap (cellSchur (originalHorizontalClosure P)
        (originalHorizontalClosure_connected P).1) / c.residueMap P.schur ^ 2) p₁ := by
    rw [cellSchur_eq_profile (originalHorizontalClosure_connected P) Q w hQ]
    exact hdep
  obtain ⟨hpT, hdepT⟩ := c.original_rational_match_transpose_horizontal d P W T S H vt vs vh
    hT hS hHT hB hmax a b p₀ p₁ hpq hdepH
  obtain ⟨δt, hδt, origin, horigin, hrowroots⟩ := d.originalWindow_row_rational_roots
    T S B H q (-v.swap) (-vt - v.swap + u.swap + vb)
      (-vt + v.swap + z.swap + vs) vh hvT hwindowT hWT hAB hHT hcutT hcutLT hmaxT hrowsT
      (schurInvolution Λ) b a r ha hab hrpos hrT hKUT hKWT
      (rationalReflection p₀) (rationalReflection p₁) hpT hdepT
  let limit := if originalHessenbergDistance (hD := isConnectedSkew_transpose hD) T 0 0 =
    originalHessenbergDistance (hD := isConnectedSkew_transpose hD) T
      (Fin.last _) (Fin.last _) then 1 else 2
  have hlimits : limit =
      (if originalHessenbergDistance (hD := hD) P 0 0 =
        originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) then 1 else 2 : ℕ) := by
    unfold limit
    simp only [original_cap_coincidence_transpose P T vt hT hB]
  dsimp only at hrowroots horigin hlabels hroots ⊢
  obtain ⟨start, hinterval⟩ := signed_complement_integer_interval δc δt hδc hδt origin limit
  refine ⟨label, start, ?_, hinj⟩
  intro X hX
  have hroot := hroots X hX
  have hdouble : (1 : ℚ) - (1 - (δc : ℚ) * label X) = (δc : ℚ) * label X := by ring
  have hrootT : (rationalReflection p₀).eval (1 - (δc : ℚ) * label X) = 0 ∨
      (rationalReflection p₁).eval (1 - (δc : ℚ) * label X) = 0 := by
    apply (rationalReflection_root_union p₀ p₁ _).mpr
    rwa [hdouble]
  obtain ⟨k, hk, hpoint⟩ := hrowroots _ hrootT
  have hlinear : (δc : ℚ) * label X = 1 - (δt : ℚ) * ((k : ℚ) - (origin : ℚ)) := by
    linarith only [hpoint]
  have hδsquare : (δc : ℚ) * (δc : ℚ) = 1 := by
    rcases hδc with rfl | rfl <;> norm_num
  have hl := congrArg ((δc : ℚ) * ·) hlinear
  rw [← mul_assoc, hδsquare, one_mul] at hl
  obtain ⟨j, hj, hjlabel⟩ := hinterval k hk
  rw [hlimits] at hj
  exact ⟨⟨j, hj, hl.trans hjlabel⟩, hlabels X hX⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
