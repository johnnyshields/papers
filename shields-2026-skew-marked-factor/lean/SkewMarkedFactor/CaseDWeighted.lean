/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
import SkewMarkedFactor.JtRotation
import SkewMarkedFactor.CaseDNorthwest

/-!
# The weighted derivative of a case-(d) row power

«Mixed weighted covariance» (`rt:mixed-covariance`) of `shields-2026-skew-marked-factor.tex`.
When no ribbon is removable on the right from `λ / μ`, the row-move terms of `V_r s_{λ/μ}` sum to
zero: the rotated beta pair is the pair of a skew Young diagram with no removable ribbon on the
left.  Combined with the classification of the northwest-removable ribbons of
`F_m = Row_m ∘_η E` this evaluates `V_{k p} s_{F_m}` in terms of one signed cofactor.
-/

noncomputable section
namespace SkewMarkedFactor
open Gluing Gluing.Plan Gluing.Plan.MN MvPolynomial

variable {η : MarkedInner} {m : ℕ}

/-- The Young diagram with prescribed antitone row lengths, vanishing from row `M` on. -/
def youngOfRows (M : ℕ) (f : ℕ → ℕ) (hf : Antitone f) (_hM : ∀ i, M ≤ i → f i = 0) :
    YoungDiagram where
  cells := ((Finset.range M) ×ˢ (Finset.range (f 0))).filter fun c => c.2 < f c.1
  isLowerSet := by
    intro a b hba ha
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_range] at ha
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_range]
    have h1 : b.1 ≤ a.1 := hba.1
    have h2 : b.2 ≤ a.2 := hba.2
    have h3 : f a.1 ≤ f b.1 := hf h1
    have h4 : f a.1 ≤ f 0 := hf (Nat.zero_le _)
    refine ⟨⟨by omega, by omega⟩, by omega⟩

theorem mem_youngOfRows {M : ℕ} {f : ℕ → ℕ} {hf : Antitone f} {hM : ∀ i, M ≤ i → f i = 0}
    {i j : ℕ} : (i, j) ∈ youngOfRows M f hf hM ↔ j < f i := by
  change (i, j) ∈ (((Finset.range M) ×ˢ (Finset.range (f 0))).filter fun c => c.2 < f c.1) ↔
    j < f i
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    have h0 : f i ≤ f 0 := hf (Nat.zero_le _)
    have hi : i < M := by
      by_contra hc
      have := hM i (by omega)
      omega
    exact ⟨⟨hi, by omega⟩, h⟩

theorem rowLen_youngOfRows {M : ℕ} {f : ℕ → ℕ} {hf : Antitone f}
    {hM : ∀ i, M ≤ i → f i = 0} (i : ℕ) : (youngOfRows M f hf hM).rowLen i = f i := by
  apply le_antisymm
  · by_contra hc
    push Not at hc
    have h1 : (i, f i) ∈ youngOfRows M f hf hM := YoungDiagram.mem_iff_lt_rowLen.mpr hc
    rw [mem_youngOfRows] at h1
    omega
  · by_contra hc
    push Not at hc
    have : (i, (youngOfRows M f hf hM).rowLen i) ∈ youngOfRows M f hf hM :=
      mem_youngOfRows.mpr hc
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp this) (lt_irrefl _)

/-- Translation preserves the upset property. -/
theorem isUpsetIn_translate (v : ℤ × ℤ) {X Y : Diagram} (h : IsUpsetIn X Y) :
    IsUpsetIn (translate v X) (translate v Y) := by
  refine ⟨Finset.image_subset_image h.1, ?_⟩
  intro x hx y hy h1 h2
  rw [mem_translate] at hx hy ⊢
  exact h.2 _ hx _ hy (by simp only [Prod.fst_sub] at *; omega)
    (by simp only [Prod.snd_sub] at *; omega)

theorem rightRibbons_eq_empty_of_translate (v : ℤ × ℤ) {X : Diagram} {n : ℕ}
    (h : rightRibbons (translate v X) n = ∅) : rightRibbons X n = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun Y hY => ?_
  obtain ⟨h1, h2, h3, h4⟩ := mem_rightRibbons.mp hY
  have : translate v Y ∈ rightRibbons (translate v X) n :=
    mem_rightRibbons.mpr ⟨Finset.image_subset_image h1, by rw [card_translate, h2],
      (isRibbon_translate v).mpr h3, isUpsetIn_translate v h4⟩
  rw [h] at this
  exact absurd this (Finset.notMem_empty _)

/-- The column-move sum for a beta pair presented over an index type of the right size. -/
theorem sum_column_moves_weighted_cast {lam mu : YoungDiagram} (hmu : mu ≤ lam) {m : ℕ}
    (hm : 0 < m) (g : ℤ → Lambda) {M : ℕ} (hM : lam.colLen 0 = M) (a b : Fin M → ℤ)
    (ha : ∀ i : Fin M, a i = (lam.rowLen i : ℤ) - i)
    (hb : ∀ i : Fin M, b i = (mu.rowLen i : ℤ) - i) :
    ∑ j : Fin M, g (b j) * jtDet a (Function.update b j (b j + m)) =
      ∑ Y ∈ leftRibbons (skewDiagram lam mu) m,
        (ribbonSign Y : Lambda) * g (minContent Y) * cellSchur (skewDiagram lam mu \ Y) := by
  subst hM
  have ha' : a = fun i : Fin (lam.colLen 0) => (lam.rowLen i : ℤ) - i := funext ha
  have hb' : b = fun i : Fin (lam.colLen 0) => (mu.rowLen i : ℤ) - i := funext hb
  subst ha' hb'
  exact sum_column_moves_weighted hmu hm g

/-- **The rotated skew diagram.**  For `μ ≤ λ`, every diagram `λ' / μ'` with row lengths
`λ'_i = N - μ_{M-1-i}` and `μ'_i = N - λ_{M-1-i}` (`M = λ.colLen 0`, `N > λ_0`, padded by empty
rows) is a translate of the rotation of `λ / μ`, and its beta pair is the rotated beta pair. -/
theorem exists_rotated_pair {lam mu : YoungDiagram} (hmu : mu ≤ lam) :
    ∃ (lam' mu' : YoungDiagram) (w : ℤ × ℤ) (c : ℤ), mu' ≤ lam' ∧
      lam'.colLen 0 = lam.colLen 0 ∧
      skewDiagram lam' mu' = translate w (rotate (skewDiagram lam mu)) ∧
      (∀ i : Fin (lam.colLen 0), c - ((mu.rowLen i.rev : ℤ) - (i.rev : ℕ)) =
        (lam'.rowLen i : ℤ) - i) ∧
      (∀ i : Fin (lam.colLen 0), c - ((lam.rowLen i.rev : ℤ) - (i.rev : ℕ)) =
        (mu'.rowLen i : ℤ) - i) ∧ c = content w + 1 := by
  set M := lam.colLen 0 with hMdef
  have hM : ∀ i, M ≤ i → lam.rowLen i = 0 := rowLen_eq_zero_of_colLen_le lam
  have hMmu : ∀ i, M ≤ i → mu.rowLen i = 0 := fun i hi => by
    have := rowLen_le_of_le hmu i
    have := hM i hi
    omega
  set N : ℕ := lam.rowLen 0 + 1 with hN
  have hlamN : ∀ i, lam.rowLen i < N := fun i => by
    have := lam.rowLen_anti 0 i (Nat.zero_le _)
    omega
  have hmuN : ∀ i, mu.rowLen i < N := fun i => by
    have := rowLen_le_of_le hmu i
    have := hlamN i
    omega
  let fL : ℕ → ℕ := fun i => if i < M then N - mu.rowLen (M - 1 - i) else 0
  let fM : ℕ → ℕ := fun i => if i < M then N - lam.rowLen (M - 1 - i) else 0
  have hfL : Antitone fL := fun i i' h => by
    simp only [fL]
    have := mu.rowLen_anti (M - 1 - i') (M - 1 - i) (by omega)
    split_ifs <;> omega
  have hfM : Antitone fM := fun i i' h => by
    simp only [fM]
    have := lam.rowLen_anti (M - 1 - i') (M - 1 - i) (by omega)
    split_ifs <;> omega
  have hfL0 : ∀ i, M ≤ i → fL i = 0 := fun i hi => by
    simp only [fL]; simp only [show ¬ i < M from by omega, ite_false]
  have hfM0 : ∀ i, M ≤ i → fM i = 0 := fun i hi => by
    simp only [fM]; simp only [show ¬ i < M from by omega, ite_false]
  set lam' := youngOfRows M fL hfL hfL0 with hlam'
  set mu' := youngOfRows M fM hfM hfM0 with hmu'
  have hrl : ∀ i, lam'.rowLen i = fL i := fun i => rowLen_youngOfRows i
  have hrm : ∀ i, mu'.rowLen i = fM i := fun i => rowLen_youngOfRows i
  have hle : mu' ≤ lam' := by
    refine le_of_rowLen_le fun i => ?_
    rw [hrl, hrm]
    simp only [fL, fM]
    have := rowLen_le_of_le hmu (M - 1 - i)
    split_ifs <;> omega
  have hcol : lam'.colLen 0 = M := by
    have key : ∀ i, i < lam'.colLen 0 ↔ i < M := fun i => by
      rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen, hrl]
      simp only [fL]
      have := hmuN (M - 1 - i)
      split_ifs with h
      · simp only [h, iff_true]; omega
      · simp [h]
    apply le_antisymm
    · by_contra hc
      push Not at hc
      have := (key M).mp hc
      omega
    · by_contra hc
      push Not at hc
      have := (key (lam'.colLen 0)).mpr hc
      omega
  refine ⟨lam', mu', ((M : ℤ) - 1, (N : ℤ) - 1), (N : ℤ) - M + 1, hle, hcol, ?_, ?_, ?_, ?_⟩
  · ext ⟨x, y⟩
    rw [mem_translate, mem_rotate]
    constructor
    · intro h
      obtain ⟨i, j, rfl, rfl, h1, h2⟩ := mem_skewDiagram_iff.mp h
      rw [hrl, hrm] at *
      simp only [fL, fM] at h1 h2
      have hiM : i < M := by
        by_contra hc
        simp only [hc, ite_false] at h2
        omega
      simp only [hiM, ite_true] at h1 h2
      have := hmuN (M - 1 - i)
      have := hlamN (M - 1 - i)
      refine mem_skewDiagram_iff.mpr ⟨M - 1 - i, N - 1 - j, ?_, ?_, ?_, ?_⟩
      · simp only [Prod.fst_sub]; omega
      · simp only [Prod.snd_sub]; omega
      · omega
      · omega
    · intro h
      obtain ⟨i, j, h1, h2, h3, h4⟩ := mem_skewDiagram_iff.mp h
      simp only [Prod.fst_sub] at h1
      simp only [Prod.snd_sub] at h2
      have hiM : i < M := by
        by_contra hc
        have := hM i (by omega)
        omega
      have := hmuN i
      have := hlamN i
      refine mem_skewDiagram_iff.mpr ⟨M - 1 - i, N - 1 - j, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · rw [hrm]
        simp only [fM, show M - 1 - i < M from by omega, ite_true]
        have e : M - 1 - (M - 1 - i) = i := by omega
        rw [e]; omega
      · rw [hrl]
        simp only [fL, show M - 1 - i < M from by omega, ite_true]
        have e : M - 1 - (M - 1 - i) = i := by omega
        rw [e]; omega
  · intro i
    rw [hrl]
    simp only [fL, Fin.val_rev, i.isLt, ite_true]
    have e : M - ((i : ℕ) + 1) = M - 1 - i := by omega
    simp only [e]
    have := hmuN (M - 1 - i)
    omega
  · intro i
    rw [hrm]
    simp only [fM, Fin.val_rev, i.isLt, ite_true]
    have e : M - ((i : ℕ) + 1) = M - 1 - i := by omega
    simp only [e]
    have := hlamN (M - 1 - i)
    omega
  · simp only [content]
    omega

/-- **Vanishing row moves.**  If no ribbon of `r` cells is removable on the right from
`λ / μ`, the row-move terms of `V_r s_{λ/μ}` sum to zero. -/
theorem rowMoveSum_eq_zero_of_rightRibbons {lam mu : YoungDiagram} (hmu : mu ≤ lam) {r : ℕ}
    (hr : 0 < r) (h : rightRibbons (skewDiagram lam mu) r = ∅) : rowMoveSum lam mu r = 0 := by
  obtain ⟨lam', mu', w, c, hle, hcol, hcells, hA, hB, -⟩ := exists_rotated_pair hmu
  have hempty : leftRibbons (skewDiagram lam' mu') r = ∅ := by
    rw [hcells, leftRibbons_translate, Corner.leftRibbons_rotate_eq_empty h]
    simp
  unfold rowMoveSum
  simp only
  rw [rowMove_sum_rotate c]
  refine (sum_column_moves_weighted_cast hle hr (fun y => ((c - y - r : ℤ) : Lambda)) hcol
    (rotA c _) (rotB c _) (fun i => ?_) (fun i => ?_)).trans ?_
  · exact hA i
  · exact hB i
  · rw [hempty]
    simp

/-- The weighted derivative of a translate of `λ / μ` with vanishing row moves, with the
weights measured from the least content of the translate. -/
theorem wDeriv_cellSchur_translate {lam mu : YoungDiagram} (hmu : mu ≤ lam) (v : ℤ × ℤ)
    {r : ℕ} (hr : 0 < r) (hrow : rowMoveSum lam mu r = 0) :
    wDeriv r (cellSchur (translate v (skewDiagram lam mu))) =
      -∑ Y ∈ leftRibbons (translate v (skewDiagram lam mu)) r,
        (ribbonSign Y : Lambda) * ((minContent Y - content v : ℤ) : Lambda) *
          cellSchur (translate v (skewDiagram lam mu) \ Y) := by
  rw [cellSchur_translate, wDeriv_cellSchur_of_rowMoveSum_eq_zero hmu hr hrow,
    leftRibbons_translate, Finset.sum_image (fun A _ B _ h => translate_injective' v h)]
  congr 1
  refine Finset.sum_congr rfl fun Y hY => ?_
  obtain ⟨-, hcard, -, -⟩ := mem_leftRibbons.mp hY
  have hne : Y.Nonempty := Finset.card_pos.mp (by omega)
  have e : translate v (skewDiagram lam mu) \ translate v Y =
      translate v (skewDiagram lam mu \ Y) := by
    unfold Gluing.translate
    rw [Finset.image_sdiff _ _ (add_left_injective _)]
  rw [ribbonSign_translate, minContent_translate hne, e, cellSchur_translate]
  simp

/-- **The weighted derivative of a case-(d) row power.**  For `1 ≤ k ≤ m`,
`V_{k p} s_{F_m} = - ((m - k) p + s - t) (-1)^{ht R} s_{F_m \ R}`, where `R` is the northwest
border segment of `k p` cells at the content `(m - k) p + s` above the least content, the
cofactor being zero unless `R` is removable on the left. -/
theorem wDeriv_rowPower (h : η.IsLegalNonempty) (hd : η.case = .d) {s t : ℤ}
    (hph : η.IsPhases s t) (hlt : t < s) (hm : 1 ≤ m) {k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    wDeriv (k * η.period.toNat) (cellSchur (η.compose (rowCells 0 m))) =
      -((((m : ℤ) - k) * η.period + s - t : ℤ) : Lambda) *
        (if Plan.segment (η.compose (rowCells 0 m))
              (minContent η.E + (((m : ℤ) - k) * η.period + s)) (k * η.period.toNat) ∈
            leftRibbons (η.compose (rowCells 0 m)) (k * η.period.toNat) then
          (ribbonSign (Plan.segment (η.compose (rowCells 0 m))
              (minContent η.E + (((m : ℤ) - k) * η.period + s)) (k * η.period.toNat)) :
              Lambda) *
            cellSchur (η.compose (rowCells 0 m) \ Plan.segment (η.compose (rowCells 0 m))
              (minContent η.E + (((m : ℤ) - k) * η.period + s)) (k * η.period.toNat))
         else 0) := by
  have hmz : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hD := isConnectedSkew_rowCells (s := 0) (e := (m : ℤ)) (by omega)
  have hF := (h.1.isConnectedSkew_compose hD).1
  have hpp : 0 < η.period.toNat := by have := h.1.period_pos; omega
  have hr : 0 < k * η.period.toNat := Nat.mul_pos hk hpp
  obtain ⟨v, lam, mu, hmu, hv⟩ := KernelAux.exists_translate_skewDiagram hF
  have hright : rightRibbons (η.compose (rowCells 0 m)) (k * η.period.toNat) = ∅ :=
    Corner.corner_no_rightRibbons_d h.1 hd hD hk
  rw [hv] at hright
  have hrow := rowMoveSum_eq_zero_of_rightRibbons hmu hr
    (rightRibbons_eq_empty_of_translate v hright)
  have h1 := wDeriv_cellSchur_translate hmu v hr hrow
  rw [← hv] at h1
  rw [h1]
  have h2 := rowPower_weighted_ribbonSum h hd hph hlt hm hk hkm
    (fun y => ((y - content v : ℤ) : Lambda))
  rw [h2]
  push_cast
  ring

end SkewMarkedFactor
