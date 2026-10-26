/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalRowPlaneLabels
import SkewCornerDescent.Matrix.OriginalResponseClassActiveLabels

/-!
# Complete actual all-row chart has consecutive integral plane labels

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The original residue classifier supplies each actual active class and its
protected top and rational affine label. Literal cofactor powers and windows
supply complete class counts. Actual closure, cap and source mixed jets then
place every active label in three consecutive integers, or two at equal cap
tops. No response, count or integer-jet premise is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows PhaseInventory

noncomputable local instance rowPencilRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- All active actual row-plane labels lie in one produced interval of three
consecutive integers, reduced to two when the original true-cap tops agree.
Every class, count, top, affine relation and integer origin is produced from
the same complete original chart. -/
theorem originalWindow_row_plane_labels {n m s t : ℕ}
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
    (hrows : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.fst).card = 1)
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
    let limit := if originalHessenbergDistance (hD := hD) P 0 0 =
      originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) then 1 else 2
    ∃ label : c.OriginalResponseClass P → ℚ, ∃ origin : ℕ, origin ≤ limit ∧
      (∀ X, c.originalResponseClassExponent P W a b X ≠ 0 →
        (∃ k : ℕ, k ≤ limit ∧ label X = (k : ℚ) - (origin : ℚ)) ∧
        X.val = c.regularResidue (c.originalHessenbergResponse Q middle middle) -
          (label X : OtherField c.top) * c.originalTrueCapProduct P) ∧
      (∀ X Y, c.originalResponseClassExponent P W a b X ≠ 0 →
        c.originalResponseClassExponent P W a b Y ≠ 0 → label X = label Y → X = Y) := by
  classical
  obtain ⟨hB, K, hKeq, hNK, k, s, hk, hs, _, hbshape, capacity, label, hlabels, hinj, _, _⟩ :=
    c.originalWindow_responseClass_active_labels P W A Q q v u z w hv hwindow hW hA hQ
      hcutq hcutLq hmax Λ b a r ha hab hrpos hr hKU hKW p₀ p₁ hpq hdep
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]
    exact Nat.mul_pos hrpos ha
  obtain ⟨_, hcounts, _⟩ := c.originalWindow_responseClass_defects P W q z v hv hW.symm
    hwindow hcutq hcutLq hC r (b - a) s k b a hrpos hs hk hbshape (by omega) hcountP hcountW
  have heq : c.originalResponseClassExponent P W a b =
      classDefect (c.originalResponseClassWord P (r * (b - a)) capacity) 1 (b - a) s
        (r * s - 1) 0 := by
    funext X
    exact hcounts X
  let p := c.originalHessenbergTop P hB 0 0 le_rfl
  let q' := c.originalHessenbergTop P hB (Fin.last _) (Fin.last _) le_rfl
  have hp := c.originalHessenbergTop_gt_selected P hB 0 0 le_rfl
  have hq := c.originalHessenbergTop_gt_selected P hB (Fin.last _) (Fin.last _) le_rfl
  have hpTop : originalHessenbergDistance (hD := hD) P 0 0 = (p : ℤ) :=
    (c.originalHessenbergTop_coe P hB 0 0 le_rfl).symm
  have hqTop : originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) = (q' : ℤ) :=
    (c.originalHessenbergTop_coe P hB (Fin.last _) (Fin.last _) le_rfl).symm
  have hcapSum := c.originalHorizontalClosure_central_cap_sum P Q w hQ hB
  dsimp only at hcapSum hKeq hlabels hinj
  have hsum : (p : ℤ) + (q' : ℤ) = (K : ℤ) := by
    rw [hpTop, hqTop] at hcapSum
    exact hcapSum.symm.trans hKeq.symm
  obtain ⟨origin, horigin, hquantize⟩ := c.original_row_plane_integer_origin P Q w hQ hB
    hmax hrows p q' hp hq hpTop hqTop
  have hlimit : (if p = q' then 1 else 2 : ℕ) =
      (if originalHessenbergDistance (hD := hD) P 0 0 =
        originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) then 1 else 2) := by
    have he : p = q' ↔ (p : ℤ) = (q' : ℤ) :=
      ⟨fun h => congrArg (fun x : ℕ+ => (x : ℤ)) h, fun h => by exact_mod_cast h⟩
    simp only [hpTop, hqTop, ← he]
  dsimp only
  rw [← hlimit]
  refine ⟨label, origin, horigin, ?_, ?_⟩
  · intro X hX
    have hX' : classDefect (c.originalResponseClassWord P (r * (b - a)) capacity)
        1 (b - a) s (r * s - 1) 0 X ≠ 0 := by rwa [← heq]
    obtain ⟨hTop, haffine⟩ := hlabels X hX'
    refine ⟨hquantize X (label X) ?_ haffine, haffine⟩
    rw [hTop]
    exact hsum
  · intro X Y hX hY he
    apply hinj X Y
    · rwa [← heq]
    · rwa [← heq]
    · exact he

end SkewCornerDescent.Matrix.SelectedCoordinate
