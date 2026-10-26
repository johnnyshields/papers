/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.DerivCoframe
import SkewCoframeRigidity.Stationary.TopSupport
import SkewCoframeRigidity.Stationary.TerminalExample

/-!
# The derivative of the coframe along the highest strict component

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `sc:component-column`.  If the first proper
row sits at `M - 1`, the derivative `∂_{H_{M-1}}` of the complete native coefficients is
`-k⁻¹ (g, 1)` on the first strict component and zero elsewhere, where `g` is the component's
own right coframe and `k = [Hg]_L` its top quotient (`g = 1`, `k = ϑ` for a unit).
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- The first proper row has position `M - 1`. -/
def TopRow (D : BetaDiagram (n + 1)) (hn : 0 < n) : Prop := rowPos D ⟨0, hn⟩ = span D - 1

theorem rowPos_ne_top_of_pos (D : BetaDiagram (n + 1)) (i : Fin n) (hi : 0 < i.val) :
    rowPos D i < rowPos D ⟨0, by omega⟩ := rowPos_strictAnti D (by rw [Fin.lt_def]; simpa using hi)

/-- The derivative of the native coefficients vanishes or is supported on the first row. -/
theorem properMatrix_mulVec_dvec_top {D : BetaDiagram (n + 1)} (hD : D.Connected) (hn : 0 < n)
    (htop : TopRow D hn) :
    properMatrixOf cohLetters D *ᵥ (fun j => dRaw (span D - 1) (coframeVecOf cohLetters D j)) =
      -(Pi.single ⟨0, hn⟩ (1 : CohField)) := by
  rw [properMatrix_mulVec_dvec hD]
  ext i
  by_cases hi : i = ⟨0, hn⟩
  · subst hi; unfold TopRow at htop; simp [htop]
  · rw [Pi.neg_apply, Pi.single_eq_of_ne hi, if_neg]
    · have h0 : 0 < i.val := by
        rcases Nat.eq_zero_or_pos i.val with h | h
        · exact absurd (Fin.ext h) hi
        · exact h
      have := rowPos_ne_top_of_pos D i h0
      unfold TopRow at htop; omega


/-- The positivity of the diagonal of the first `t + 1` proper indices. -/
def BlockPos (D : BetaDiagram (n + 1)) (t : ℕ) (ht : t + 1 ≤ n) : Prop :=
  ∀ i : Fin (t + 1), D.col (blockEmb 0 (t + 1) (by omega) i).castSucc <
    D.row (blockEmb 0 (t + 1) (by omega) i).succ

/-- The first `t + 1` proper indices as a diagram. -/
def firstBlock (D : BetaDiagram (n + 1)) (t : ℕ) (ht : t + 1 ≤ n) (hpos : BlockPos D t ht) :
    BetaDiagram (t + 1) :=
  blockDiagram D 0 (t + 1) (by omega) hpos

/-- The first strict component and the solution of the first inverse column on it. -/
theorem top_component_solution {D : BetaDiagram (n + 1)} (hD : D.Connected) (hn : 0 < n) :
    ∃ (t : ℕ) (ht : t + 1 ≤ n) (W : Fin n → CohField) (k : CohField),
      (∀ j : Fin n, W j ≠ 0 → j.val ≤ t) ∧ k ≠ 0 ∧
      properMatrixOf cohLetters D *ᵥ W = Pi.single ⟨0, hn⟩ k ∧
      (∀ j : Fin n, blockIdx D j = blockIdx D ⟨0, hn⟩ ↔ j.val ≤ t) ∧
      ((t = 0 ∧ (∀ i : Fin n, i.val = 0 → IsUnit' D i) ∧ k = cohLetters 0 ∧
          W = Pi.single ⟨0, hn⟩ 1) ∨
       ∃ hpos : BlockPos D t ht, (firstBlock D t ht hpos).Connected ∧
         k = topQuotient (firstBlock D t ht hpos) ∧
         ∀ j : Fin n, ∀ hj : j.val < t + 1, W j =
           (Fin.snoc (α := fun _ => CohField)
             (coframeVecOf cohLetters (firstBlock D t ht hpos)) 1 :
             Fin (t + 1) → CohField) ⟨j.val, hj⟩) := by
  classical
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  obtain ⟨s0, m, hsm, hm, hfib, hcase⟩ :=
    strict_component cohLetters hD (k := blockIdx D i0) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hs0 : s0 = 0 := by
    have := (hfib i0).1 rfl
    simpa [hi0] using this.1
  subst hs0
  have hblk : ∀ i : Fin n, blockIdx D i = blockIdx D i0 ↔ i.val < m := fun i => by
    rw [hfib]; omega
  have hvan : ∀ (W : Fin n → CohField), (∀ j, W j ≠ 0 → j.val < m) →
      ∀ i : Fin n, m ≤ i.val → (properMatrixOf cohLetters D *ᵥ W) i = 0 := by
    intro W hW i hi
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hwj : W j = 0
    · rw [hwj, mul_zero]
    · have hj := hW j hwj
      have hlt : blockIdx D j < blockIdx D i := by
        have h1 : blockIdx D j = blockIdx D i0 := (hblk j).2 hj
        have h2 : blockIdx D i0 ≤ blockIdx D i := blockIdx_mono D (by rw [Fin.le_iff_val_le_val]; simp [hi0])
        have h3 : blockIdx D i ≠ blockIdx D i0 := fun h => by have := (hblk i).1 h; omega
        omega
      rw [properMatrixOf_eq_zero cohLetters D hlt, zero_mul]
  have hinv : IsUnit (properMatrixOf cohLetters D).det := (properDet_cohLetters_ne_zero hD).isUnit
  have hkne : ∀ (W : Fin n → CohField) (k : CohField) (j0 : Fin n), W j0 = 1 →
      properMatrixOf cohLetters D *ᵥ W = Pi.single i0 k → k ≠ 0 := by
    intro W k j0 hj0 hTW hk
    rw [hk, Pi.single_zero] at hTW
    have : W = 0 := by
      have h1 := congrArg ((properMatrixOf cohLetters D)⁻¹ *ᵥ ·) hTW
      simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hinv, Matrix.one_mulVec,
        Matrix.mulVec_zero] at h1
      exact h1
    rw [this] at hj0; simp at hj0
  rcases hcase with ⟨hm1, hu, hdet⟩ | ⟨hpos, hconn, hdet⟩
  · subst hm1
    refine ⟨0, by omega, Pi.single i0 1, cohLetters 0, ?_, cohLetters_zero_ne_zero, ?_, fun j => by rw [hblk]; omega, Or.inl ⟨rfl, hu, rfl, rfl⟩⟩
    · intro j hj
      by_contra hne
      have : j = i0 := by
        by_contra hji; rw [Pi.single_eq_of_ne hji] at hj; exact hj rfl
      exact hne (by simp [this, hi0])
    · ext i
      by_cases hi : i = i0
      · subst hi
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        have := hu i0 (by simp [hi0])
        unfold IsUnit' at this
        simp [properMatrixOf, letterOf, this]
      · rw [Pi.single_eq_of_ne hi]
        refine hvan _ (fun j hj => ?_) i (by
          have : i.val ≠ 0 := fun h => hi (Fin.ext h)
          omega)
        have : j = i0 := by
          by_contra hji; rw [Pi.single_eq_of_ne hji] at hj; exact hj rfl
        simp [this, hi0]
  · obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
    have ht : t + 1 ≤ n := by omega
    have hpos' : BlockPos D t ht := hpos
    set E := firstBlock D t ht hpos' with hE
    have hEc : E.Connected := hconn
    let W : Fin n → CohField := fun j =>
      if h : j.val < t + 1 then
        (Fin.snoc (α := fun _ => CohField) (coframeVecOf cohLetters E) 1 :
          Fin (t + 1) → CohField) ⟨j.val, h⟩ else 0
    have hWsupp : ∀ j, W j ≠ 0 → j.val < t + 1 := fun j hj => by
      by_contra h; exact hj (by simp only [W]; rw [dif_neg h])
    have hsumE : ∀ (f : Fin n → CohField), (∀ j, t + 1 ≤ j.val → f j = 0) →
        ∑ j, f j = ∑ j' : Fin (t + 1), f (blockEmb 0 (t + 1) (by omega) j') := by
      intro f hf
      rw [← Finset.sum_image (f := f) (g := blockEmb 0 (t + 1) (by omega)) (fun a _ b _ h => by
        have := congrArg Fin.val h; simp [blockEmb] at this; exact Fin.ext this)]
      refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
      by_contra hlt
      exact hj (Finset.mem_image.2 ⟨⟨j.val, by omega⟩, Finset.mem_univ _, by
        ext; simp [blockEmb]⟩)
    have hrows := full_rows hEc
    have hsol : properMatrixOf cohLetters D *ᵥ W = Pi.single i0 (topQuotient E) := by
      ext i
      by_cases hi : i.val < t + 1
      · have hrow : (properMatrixOf cohLetters D *ᵥ W) i =
            ∑ j' : Fin (t + 1), fullMatrixOf cohLetters E ⟨i.val, hi⟩ j' *
              (Fin.snoc (α := fun _ => CohField) (coframeVecOf cohLetters E) 1 :
                Fin (t + 1) → CohField) j' := by
          simp only [Matrix.mulVec, dotProduct]
          rw [hsumE _ (fun j hj => by
            have : W j = 0 := by simp only [W]; rw [dif_neg (by omega)]
            rw [this, mul_zero])]
          refine Finset.sum_congr rfl fun j' _ => ?_
          have : W (blockEmb 0 (t + 1) (by omega) j') = (Fin.snoc (α := fun _ => CohField)
              (coframeVecOf cohLetters E) 1 : Fin (t + 1) → CohField) j' := by
            simp only [W, blockEmb]; rw [dif_pos (by simpa [Nat.lt_succ_iff] using Nat.lt_succ_iff.mp j'.isLt)]
            exact congrArg _ (Fin.ext (by simp))
          rw [this]
          have e : fullMatrixOf cohLetters E ⟨i.val, hi⟩ j' =
              properMatrixOf cohLetters D i (blockEmb 0 (t + 1) (by omega) j') := by
            have := congrFun (congrFun (fullMatrixOf_blockDiagram cohLetters D 0 (t + 1) hsm hpos)
              ⟨i.val, hi⟩) j'
            simp only [Matrix.submatrix_apply] at this
            refine this.trans ?_
            congr 1
            exact Fin.ext (by simp [blockEmb])
          rw [e]
        rw [hrow]
        rcases Nat.eq_zero_or_pos i.val with h0 | h0
        · have hi0' : i = i0 := Fin.ext h0
          have : (⟨i.val, hi⟩ : Fin (t + 1)) = 0 := Fin.ext h0
          rw [this, hrows.2, hi0', Pi.single_eq_same]
        · obtain ⟨i'', hi''⟩ : ∃ i'' : Fin t, i''.val + 1 = i.val := ⟨⟨i.val - 1, by omega⟩, by simp; omega⟩
          have : (⟨i.val, hi⟩ : Fin (t + 1)) = i''.succ := Fin.ext (by simp [hi''])
          rw [this, hrows.1 i'', Pi.single_eq_of_ne]
          intro h; have := congrArg Fin.val h; simp [hi0] at this; omega
      · rw [hvan W hWsupp i (by omega), Pi.single_eq_of_ne]
        intro h; have := congrArg Fin.val h; simp [hi0] at this; omega
    refine ⟨t, ht, W, topQuotient E, fun j hj => ?_, ?_, hsol, fun j => by rw [hblk]; omega, Or.inr ⟨hpos', hEc, rfl, ?_⟩⟩
    · have := hWsupp j hj; omega
    · exact hkne W _ ⟨t, by omega⟩ (by
        simp only [W]; rw [dif_pos (by simp)]; exact Fin.snoc_last _ _) hsol
    · intro j hj; simp only [W]; rw [dif_pos hj]


/-- The derivative of the native coefficients is `-k⁻¹ W`. -/
theorem dvec_eq_of_solution {D : BetaDiagram (n + 1)} (hD : D.Connected) (hn : 0 < n)
    (htop : TopRow D hn) {W : Fin n → CohField} {k : CohField} (hk : k ≠ 0)
    (hW : properMatrixOf cohLetters D *ᵥ W = Pi.single ⟨0, hn⟩ k) :
    (fun j => dRaw (span D - 1) (coframeVecOf cohLetters D j)) = -(k⁻¹ • W) := by
  have hinv : IsUnit (properMatrixOf cohLetters D).det :=
    (properDet_cohLetters_ne_zero hD).isUnit
  have h1 := properMatrix_mulVec_dvec_top hD hn htop
  have h2 : properMatrixOf cohLetters D *ᵥ (-(k⁻¹ • W)) = -(Pi.single ⟨0, hn⟩ (1 : CohField)) := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_smul, hW]
    congr 1
    ext i
    by_cases hi : i = ⟨0, hn⟩
    · subst hi; simp [hk]
    · simp [Pi.single_eq_of_ne hi]
  have := h1.trans h2.symm
  have h3 := congrArg ((properMatrixOf cohLetters D)⁻¹ *ᵥ ·) this
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hinv, Matrix.one_mulVec] using h3


theorem sum_fin_of_supp {α : Type*} [AddCommMonoid α] {n t : ℕ} (ht : t + 1 ≤ n) (f : Fin n → α)
    (hf : ∀ j : Fin n, t + 1 ≤ j.val → f j = 0) :
    ∑ j, f j = ∑ j' : Fin (t + 1), f (blockEmb 0 (t + 1) (by omega) j') := by
  classical
  rw [← Finset.sum_image (f := f) (g := blockEmb 0 (t + 1) (by omega)) (fun a _ b _ h => by
    have := congrArg Fin.val h; simp [blockEmb] at this; exact Fin.ext this)]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
  by_contra hlt
  exact hj (Finset.mem_image.2 ⟨⟨j.val, by omega⟩, Finset.mem_univ _, by
    ext; simp [blockEmb]⟩)

end SkewCoframeRigidity.Coframe
