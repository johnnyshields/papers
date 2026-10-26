/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.ExteriorGaps

/-!
# Nonnegative-index rigidity

The full strong induction for `thm:nonnegative-rigidity`, including its
one-row and two-row boundary cases.  The unknown mate is never assumed to
have nonnegative indices.  Padded corner readings and connected
irreducibility produce the unknown core; the actual exterior coefficients
place its two margins and close the induction.
-/

namespace SkewCofactorIndependence

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false in
/-- Complete indices are recoverable on the nonnegative domain, including the unit at zero. -/
theorem complete_injective_nonnegative {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : complete a = complete b) : a = b := by
  by_cases hp : 0 < a
  · let v : ℕ+ := ⟨a.toNat, by omega⟩
    have hv : v ∈ (complete a).vars := by
      rw [mem_vars_complete_iff]
      dsimp [v]
      omega
    rw [he, mem_vars_complete_iff] at hv
    dsimp [v] at hv
    omega
  · have haz : a = 0 := by omega
    subst a
    by_cases hp : 0 < b
    · let v : ℕ+ := ⟨b.toNat, by omega⟩
      have hv : v ∈ (complete b).vars := by
        rw [mem_vars_complete_iff]
        dsimp [v]
        omega
      rw [← he] at hv
      have hfalse : False := by simp at hv
      exact hfalse.elim
    · omega

set_option backward.isDefEq.respectTransparency false in
/-- Faithful complete-generator products recover the unordered positive row lengths. -/
theorem complete_two_product_reading {a b c d : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : complete a * complete b = complete c * complete d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have heI : Base.complete a * Base.complete b = Base.complete c * Base.complete d := by
    apply integerLift_injective
    rw [map_mul, map_mul]
    exact he
  have hnat : (Base.complete (a.toNat : ℤ) * Base.complete (b.toNat : ℤ)) =
      Base.complete (c.toNat : ℤ) * Base.complete (d.toNat : ℤ) := by
    have h₁ : (a.toNat : ℤ) = a := by omega
    have h₂ : (b.toNat : ℤ) = b := by omega
    have h₃ : (c.toNat : ℤ) = c := by omega
    have h₄ : (d.toNat : ℤ) = d := by omega
    simpa [h₁, h₂, h₃, h₄] using heI
  have hm : (([a.toNat, b.toNat] : List ℕ) : Multiset ℕ) =
      (([c.toNat, d.toNat] : List ℕ) : Multiset ℕ) := by
    apply (Base.prod_complete_eq_iff_of_pos [a.toNat, b.toNat] [c.toNat, d.toNat]
      (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega)
      (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega)).mp
    simpa using hnat
  have hmemb : a.toNat = c.toNat ∨ a.toNat = d.toNat := by
    have hmema : a.toNat ∈ (([a.toNat, b.toNat] : List ℕ) : Multiset ℕ) := by simp
    rw [hm] at hmema
    simpa using hmema
  rcases hmemb with h | h
  · have hb' : b.toNat = d.toNat := by
      rw [h] at hm
      simpa using hm
    exact Or.inl ⟨by omega, by omega⟩
  · have hb' : b.toNat = c.toNat := by
      rw [h] at hm
      have hs : (([c.toNat, d.toNat] : List ℕ) : Multiset ℕ) =
          (([d.toNat, c.toNat] : List ℕ) : Multiset ℕ) :=
        Multiset.pair_comm _ _
      rw [hs] at hm
      simpa using hm
    exact Or.inr ⟨by omega, by omega⟩

/-- Exact degree of a weakly feasible diagonal product, retaining the zero-index convention. -/
theorem weak_diagonal_product_degree {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, complete (f i)).totalDegree = ∑ i ∈ s, if 0 < f i then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hn : (∏ j ∈ s, complete (f j)) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro j hj
        exact (complete_ne_zero_iff _).mpr (hf j (Finset.mem_insert_of_mem hj))
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        MvPolynomial.totalDegree_mul_of_isDomain
          ((complete_ne_zero_iff _).mpr (hf i (Finset.mem_insert_self _ _))) hn,
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]
      by_cases hp : 0 < f i
      · let v : ℕ+ := ⟨(f i).toNat, by omega⟩
        have he : complete (f i) = (MvPolynomial.X v : CompleteRing) := complete_of_pos hp
        rw [he, MvPolynomial.totalDegree_X v, ite_eq_left hp]
      · have hz : f i = 0 := by have := hf i (Finset.mem_insert_self _ _); omega
        simp [hz]

/-- A full degree reading of a padded diagonal forces every padded entry to be positive. -/
theorem positive_diagonal_of_product_degree {n : ℕ} (f : Fin n → ℤ)
    (hf : ∀ i, 0 ≤ f i)
    (hdeg : (∏ i, complete (f i)).totalDegree = n) : ∀ i, 0 < f i := by
  classical
  have he := weak_diagonal_product_degree Finset.univ f (fun i _ => hf i)
  rw [hdeg] at he
  intro i
  by_contra hp
  have hlt : (∑ j : Fin n, if 0 < f j then 1 else 0) < ∑ _j : Fin n, 1 := by
    apply Finset.sum_lt_sum
    · intro j _
      split_ifs <;> omega
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      simp [hp]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one] at hlt
  omega

namespace BetaDiagram

variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- Recovery of the unknown corner's positive rows from the actual padded initial monomial. -/
theorem positiveCorner_of_cornerPolynomial_eq (D E : BetaDiagram (n + 1))
    (hD : D.Connected) (hE : E.Connected) (hP : D.PositiveCorner)
    (he : D.cornerPolynomial = E.cornerPolynomial) : E.PositiveCorner := by
  have hinit := congrArg (Base.initialForm Base.squareWeight.generatorWeight) he
  rw [D.corner_square_initialForm hD, E.corner_square_initialForm hE] at hinit
  have hd : (∏ i : Fin n, complete (D.row i.succ - D.col i.castSucc)).totalDegree = n := by
    rw [weak_diagonal_product_degree Finset.univ _
      (fun i _ => (sub_pos.mpr (hP i)).le)]
    have hpos : ∀ i : Fin n, 0 < D.row i.succ - D.col i.castSucc :=
      fun i => sub_pos.mpr (hP i)
    simp only [hpos, ite_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have hedeg : (∏ i : Fin n, complete (E.row i.succ - E.col i.castSucc)).totalDegree = n := by
    rw [← hinit]
    exact hd
  have hp := positive_diagonal_of_product_degree
    (fun i : Fin n => E.row i.succ - E.col i.castSucc)
    (fun i => sub_nonneg.mpr (E.corner_diagonal_nonnegative hE i)) hedeg
  intro i
  exact sub_pos.mp (hp i)

/-- Irreducibility of the source core produces connectedness of the unknown recovered core. -/
theorem recovered_corner_connected (D E : BetaDiagram (n + 3))
    (hD : D.Connected) (hE : E.Connected) (hN : D.Nonnegative)
    (he : D.schur = E.schur) :
    let hP := D.positiveCorner_of_cornerPolynomial_eq E hD hE
      (D.positiveCorner_of_nonnegative hN)
      (D.cornerPolynomial_eq_of_schur_eq E hD hE he)
    (E.cornerDiagram hP).Connected := by
  dsimp only
  let hP := D.positiveCorner_of_cornerPolynomial_eq E hD hE
    (D.positiveCorner_of_nonnegative hN)
    (D.cornerPolynomial_eq_of_schur_eq E hD hE he)
  apply (E.cornerDiagram hP).connected_of_schur_irreducible (by omega)
  rw [cornerDiagram_schur,
    ← D.cornerPolynomial_eq_of_schur_eq E hD hE he,
    ← D.cornerDiagram_schur (D.positiveCorner_of_nonnegative hN)]
  exact (D.cornerDiagram (D.positiveCorner_of_nonnegative hN)).schur_irreducible
    (D.cornerDiagram_connected hN _ (by omega))

/-- One-row polynomial equality determines the common translation. -/
theorem rigidity_one (D E : BetaDiagram 1) (he : D.schur = E.schur) :
    D.TranslationEquivalent E := by
  have hindex : D.row 0 - D.col 0 = E.row 0 - E.col 0 := by
    apply complete_injective_nonnegative
      (sub_pos.mpr (D.row_nonempty 0)).le (sub_pos.mpr (E.row_nonempty 0)).le
    simpa [schur, matrix, Matrix.det_unique] using he
  refine ⟨D.col 0 - E.col 0, ?_, ?_⟩
  · intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    omega
  · intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    ring

set_option backward.isDefEq.respectTransparency false in
/-- Two rows are rigid without any nonnegative-index condition. -/
theorem rigidity_two (D E : BetaDiagram 2) (hD : D.Connected) (hE : E.Connected)
    (he : D.schur = E.schur) :
    D.TranslationEquivalent E ∨ D.RotationEquivalent E := by
  have hcorner := D.cornerPolynomial_eq_of_schur_eq E hD hE he
  have hoverlap : D.row 1 - D.col 0 = E.row 1 - E.col 0 := by
    apply complete_injective_nonnegative
      (sub_nonneg.mpr (hD.2 0 (by decide)))
      (sub_nonneg.mpr (hE.2 0 (by decide)))
    simpa [cornerPolynomial, cornerBoard, betaBoard, Matrix.det_unique] using hcorner
  have hinit := congrArg (Base.initialForm Base.squareWeight.generatorWeight) he
  rw [D.square_initialForm, E.square_initialForm] at hinit
  have hprod : complete (D.rowLength 0) * complete (D.rowLength 1) =
      complete (E.rowLength 0) * complete (E.rowLength 1) := by
    simpa [Fin.prod_univ_two, rowLength] using hinit
  rcases complete_two_product_reading (D.rowLength_pos 0) (D.rowLength_pos 1)
    (E.rowLength_pos 0) (E.rowLength_pos 1) hprod with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  · left
    change D.row 0 - D.col 0 = E.row 0 - E.col 0 at h₀
    change D.row 1 - D.col 1 = E.row 1 - E.col 1 at h₁
    refine ⟨D.col 1 - E.col 1, ?_, ?_⟩
    · intro i
      fin_cases i
      · change D.row 0 = E.row 0 + (D.col 1 - E.col 1)
        omega
      · change D.row 1 = E.row 1 + (D.col 1 - E.col 1)
        omega
    · intro i
      fin_cases i
      · change D.col 0 = E.col 0 + (D.col 1 - E.col 1)
        omega
      · change D.col 1 = E.col 1 + (D.col 1 - E.col 1)
        ring
  · right
    change D.row 0 - D.col 0 = E.row 1 - E.col 1 at h₀
    change D.row 1 - D.col 1 = E.row 0 - E.col 0 at h₁
    refine ⟨D.row 0 + E.col 1, ?_, ?_⟩
    · intro i
      fin_cases i
      · change D.row 0 = D.row 0 + E.col 1 - E.col 1
        ring
      · change D.row 1 = D.row 0 + E.col 1 - E.col 0
        omega
    · intro i
      fin_cases i
      · change D.col 0 = D.row 0 + E.col 1 - E.row 1
        omega
      · change D.col 1 = D.row 0 + E.col 1 - E.row 0
        omega

/-- A translated recovered core forces the unknown parent into the nonnegative-index class. -/
theorem nonnegative_of_corner_translation (D E : BetaDiagram (n + 3))
    (hND : D.Nonnegative) (hPD : D.PositiveCorner) (hPE : E.PositiveCorner)
    (h : (D.cornerDiagram hPD).TranslationEquivalent (E.cornerDiagram hPE)) :
    E.Nonnegative := by
  obtain ⟨c, hr, hc⟩ := h
  have hrl := hr (Fin.last (n + 1))
  have hcf := hc 0
  have hn := hND (Fin.last (n + 2)) 0
  change D.row (Fin.last (n + 2)) = E.row (Fin.last (n + 2)) + c at hrl
  change D.col 0 = E.col 0 + c at hcf
  intro i j
  have hri := E.row_strictAnti.antitone (Fin.le_last i)
  have hcj := E.col_strictAnti.antitone (Fin.zero_le j)
  omega

/-- The common maximal label determines the sum of the two exterior margins. -/
theorem marginSum_eq_of_corner_translation (D E : BetaDiagram (n + 3))
    (hPD : D.PositiveCorner) (hPE : E.PositiveCorner)
    (h : (D.cornerDiagram hPD).TranslationEquivalent (E.cornerDiagram hPE))
    (hl : D.largestLabel = E.largestLabel) :
    D.topMargin + D.bottomMargin = E.topMargin + E.bottomMargin := by
  obtain ⟨c, hr, hc⟩ := h
  have hr₀ := hr 0
  have hcL := hc (Fin.last (n + 1))
  change D.row (0 : Fin (n + 2)).succ = E.row (0 : Fin (n + 2)).succ + c at hr₀
  change D.col (Fin.last (n + 1)).castSucc =
    E.col (Fin.last (n + 1)).castSucc + c at hcL
  change D.row 0 - D.col (Fin.last (n + 2)) =
    E.row 0 - E.col (Fin.last (n + 2)) at hl
  change (D.row 0 - D.row (0 : Fin (n + 2)).succ) +
      (D.col (Fin.last (n + 1)).castSucc - D.col (Fin.last (n + 2))) =
    (E.row 0 - E.row (0 : Fin (n + 2)).succ) +
      (E.col (Fin.last (n + 1)).castSucc - E.col (Fin.last (n + 2)))
  omega

/-- Equal oriented margins lift a core translation to the two full parents. -/
theorem translation_of_corner_translation_of_margins (D E : BetaDiagram (n + 3))
    (hPD : D.PositiveCorner) (hPE : E.PositiveCorner)
    (h : (D.cornerDiagram hPD).TranslationEquivalent (E.cornerDiagram hPE))
    (ht : D.topMargin = E.topMargin) (hb : D.bottomMargin = E.bottomMargin) :
    D.TranslationEquivalent E := by
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨c, ?_, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero =>
        have hr₀ := hr 0
        dsimp [cornerDiagram] at hr₀
        dsimp [topMargin] at ht
        omega
    | succ i => exact hr i
  · intro i
    cases i using Fin.lastCases with
    | last =>
        have hcL := hc (Fin.last (n + 1))
        change D.col (Fin.last (n + 1)).castSucc =
          E.col (Fin.last (n + 1)).castSucc + c at hcL
        change D.col (Fin.last (n + 1)).castSucc - D.col (Fin.last (n + 2)) =
          E.col (Fin.last (n + 1)).castSucc - E.col (Fin.last (n + 2)) at hb
        change D.col (Fin.last (n + 2)) = E.col (Fin.last (n + 2)) + c
        omega
    | cast i => exact hc i

/-- A symmetric core lifts an interchange of its two margins to a rotation of the parents. -/
theorem rotation_of_corner_translation_of_swapped_margins (D E : BetaDiagram (n + 3))
    (hPD : D.PositiveCorner) (hPE : E.PositiveCorner)
    (h : (D.cornerDiagram hPD).TranslationEquivalent (E.cornerDiagram hPE))
    (ht : D.topMargin = E.bottomMargin) (hb : D.bottomMargin = E.topMargin)
    (hs : (D.cornerDiagram hPD).Symmetric) : D.RotationEquivalent E := by
  obtain ⟨c, hr, hc⟩ := h
  obtain ⟨k, hsr, hsc⟩ := hs
  refine ⟨k - c, ?_, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero =>
        have hs₀ := hsr 0
        have hcL := hc (Fin.last (n + 1))
        simp only [cornerDiagram, Fin.rev_zero] at hs₀ hcL
        change D.row (0 : Fin (n + 2)).succ =
          k - D.col (Fin.last (n + 1)).castSucc at hs₀
        change D.col (Fin.last (n + 1)).castSucc =
          E.col (Fin.last (n + 1)).castSucc + c at hcL
        change D.row 0 - D.row (0 : Fin (n + 2)).succ =
          E.col (Fin.last (n + 1)).castSucc - E.col (Fin.last (n + 2)) at ht
        change D.row 0 = (k - c) - E.col (Fin.last (n + 2))
        omega
    | succ i =>
        have hsi := hsr i
        have hci := hc i.rev
        change D.row i.succ = k - D.col i.rev.castSucc at hsi
        change D.col i.rev.castSucc = E.col i.rev.castSucc + c at hci
        rw [Fin.rev_succ]
        omega
  · intro i
    cases i using Fin.lastCases with
    | last =>
        have hsL := hsc (Fin.last (n + 1))
        have hr₀ := hr 0
        simp only [cornerDiagram, Fin.rev_last] at hsL hr₀
        change D.col (Fin.last (n + 1)).castSucc =
          k - D.row (0 : Fin (n + 2)).succ at hsL
        change D.row (0 : Fin (n + 2)).succ =
          E.row (0 : Fin (n + 2)).succ + c at hr₀
        change D.col (Fin.last (n + 1)).castSucc - D.col (Fin.last (n + 2)) =
          E.row 0 - E.row (0 : Fin (n + 2)).succ at hb
        simp only [Fin.rev_last]
        change D.col (Fin.last (n + 2)) = (k - c) - E.row 0
        omega
    | cast i =>
        have hsi := hsc i
        have hri := hr i.rev
        change D.col i.castSucc = k - D.row i.rev.succ at hsi
        change D.row i.rev.succ = E.row i.rev.succ + c at hri
        rw [Fin.rev_castSucc]
        omega

/-- Core translations also translate each corresponding actual endpoint extension. -/
theorem extendBottom_schur_eq_of_translation (T U : BetaDiagram (n + 1))
    (h : T.TranslationEquivalent U) (d : ℤ) (hd : 0 < d) :
    (T.extendBottom d hd).schur = (U.extendBottom d hd).schur := by
  apply TranslationEquivalent.schur_eq
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨c, hr, ?_⟩
  intro i
  change (if i = Fin.last n then T.col i - d else T.col i) =
    (if i = Fin.last n then U.col i - d else U.col i) + c
  have hi := hc i
  split_ifs <;> omega

/-- The first endpoint extension behaves identically under a core translation. -/
theorem extendTop_schur_eq_of_translation (T U : BetaDiagram (n + 1))
    (h : T.TranslationEquivalent U) (d : ℤ) (hd : 0 < d) :
    (T.extendTop d hd).schur = (U.extendTop d hd).schur := by
  apply TranslationEquivalent.schur_eq
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨c, ?_, hc⟩
  intro i
  change (if i = 0 then T.row i + d else T.row i) =
    (if i = 0 then U.row i + d else U.row i) + c
  have hi := hr i
  split_ifs <;> omega

set_option backward.isDefEq.respectTransparency false in
/-- Actual private coefficients make a nontrivial margin interchange
compare the two core extensions. -/
theorem extensions_schur_eq_of_swapped_margins (D E : BetaDiagram (n + 3))
    (hD : D.Connected) (hE : E.Connected) (hND : D.Nonnegative)
    (hPD : D.PositiveCorner) (hPE : E.PositiveCorner)
    (hcore : (D.cornerDiagram hPD).TranslationEquivalent (E.cornerDiagram hPE))
    (ht : D.topMargin = E.bottomMargin) (hb : D.bottomMargin = E.topMargin)
    (hne : D.topMargin ≠ D.bottomMargin) (he : D.schur = E.schur) :
    let d := min D.topMargin D.bottomMargin
    let hd : 0 < d := lt_min D.topMargin_pos D.bottomMargin_pos
    ((D.cornerDiagram hPD).extendTop d hd).schur =
      ((D.cornerDiagram hPD).extendBottom d hd).schur := by
  classical
  have hNE := D.nonnegative_of_corner_translation E hND hPD hPE hcore
  have hl := D.largestLabel_eq_of_schur_eq E hD hE he
  let ND : ℕ+ := ⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩
  let NE : ℕ+ := ⟨E.largestLabel.toNat, by have := E.largestLabel_pos; omega⟩
  have hNDE : ND = NE := by
    apply Subtype.ext
    exact congrArg Int.toNat hl
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hEt : E.bottomMargin < E.topMargin := by omega
    have hEp : 0 < E.largestLabel - E.bottomMargin := by
      have hp := E.rotate.exterior_top_label_pos
      rw [E.rotate_largestLabel, E.rotate_topMargin] at hp
      exact hp
    let MD : ℕ+ := ⟨(D.largestLabel - D.topMargin).toNat,
      by have := D.exterior_top_label_pos; omega⟩
    let ME : ℕ+ := ⟨(E.largestLabel - E.bottomMargin).toNat, by omega⟩
    have hMDE : MD = ME := by
      apply Subtype.ext
      change (D.largestLabel - D.topMargin).toNat = (E.largestLabel - E.bottomMargin).toNat
      rw [hl, ht]
    have hDcoef : MvPolynomial.pderiv MD (eraseGenerator ND D.schur) =
        (-1) ^ (n + 3) * ((D.cornerDiagram hPD).extendTop D.topMargin D.topMargin_pos).schur :=
      D.exterior_top_coefficient hND hlt
    have hEcoef : MvPolynomial.pderiv ME (eraseGenerator NE E.schur) =
        (-1) ^ (n + 3) *
          ((E.cornerDiagram hPE).extendBottom E.bottomMargin E.bottomMargin_pos).schur :=
      E.exterior_bottom_coefficient hNE hEt
    have hcoeff : (-1 : CompleteRing) ^ (n + 3) *
        ((D.cornerDiagram hPD).extendTop D.topMargin D.topMargin_pos).schur =
        (-1 : CompleteRing) ^ (n + 3) *
        ((E.cornerDiagram hPE).extendBottom E.bottomMargin E.bottomMargin_pos).schur := by
      calc
        _ = MvPolynomial.pderiv MD (eraseGenerator ND D.schur) := hDcoef.symm
        _ = MvPolynomial.pderiv MD (eraseGenerator ND E.schur) :=
          congrArg (fun p : CompleteRing => MvPolynomial.pderiv MD (eraseGenerator ND p)) he
        _ = MvPolynomial.pderiv ME (eraseGenerator NE E.schur) := by rw [hMDE, hNDE]
        _ = _ := hEcoef
    have heExt := mul_left_cancel₀
      (pow_ne_zero (n + 3) (neg_ne_zero.mpr (one_ne_zero : (1 : CompleteRing) ≠ 0))) hcoeff
    have hBot := extendBottom_schur_eq_of_translation
      (D.cornerDiagram hPD) (E.cornerDiagram hPE) hcore
      E.bottomMargin E.bottomMargin_pos
    dsimp only
    simpa only [min_eq_left hlt.le, ← ht] using heExt.trans hBot.symm
  · have hEt : E.topMargin < E.bottomMargin := by omega
    have hDp : 0 < D.largestLabel - D.bottomMargin := by
      have hp := D.rotate.exterior_top_label_pos
      rw [D.rotate_largestLabel, D.rotate_topMargin] at hp
      exact hp
    let MD : ℕ+ := ⟨(D.largestLabel - D.bottomMargin).toNat, by omega⟩
    let ME : ℕ+ := ⟨(E.largestLabel - E.topMargin).toNat,
      by have := E.exterior_top_label_pos; omega⟩
    have hMDE : MD = ME := by
      apply Subtype.ext
      change (D.largestLabel - D.bottomMargin).toNat = (E.largestLabel - E.topMargin).toNat
      rw [hl, hb]
    have hDcoef : MvPolynomial.pderiv MD (eraseGenerator ND D.schur) =
        (-1) ^ (n + 3) *
          ((D.cornerDiagram hPD).extendBottom D.bottomMargin D.bottomMargin_pos).schur :=
      D.exterior_bottom_coefficient hND hgt
    have hEcoef : MvPolynomial.pderiv ME (eraseGenerator NE E.schur) =
        (-1) ^ (n + 3) * ((E.cornerDiagram hPE).extendTop E.topMargin E.topMargin_pos).schur :=
      E.exterior_top_coefficient hNE hEt
    have hcoeff : (-1 : CompleteRing) ^ (n + 3) *
        ((D.cornerDiagram hPD).extendBottom D.bottomMargin D.bottomMargin_pos).schur =
        (-1 : CompleteRing) ^ (n + 3) *
        ((E.cornerDiagram hPE).extendTop E.topMargin E.topMargin_pos).schur := by
      calc
        _ = MvPolynomial.pderiv MD (eraseGenerator ND D.schur) := hDcoef.symm
        _ = MvPolynomial.pderiv MD (eraseGenerator ND E.schur) :=
          congrArg (fun p : CompleteRing => MvPolynomial.pderiv MD (eraseGenerator ND p)) he
        _ = MvPolynomial.pderiv ME (eraseGenerator NE E.schur) := by rw [hMDE, hNDE]
        _ = _ := hEcoef
    have heExt := mul_left_cancel₀
      (pow_ne_zero (n + 3) (neg_ne_zero.mpr (one_ne_zero : (1 : CompleteRing) ≠ 0))) hcoeff
    have hTop := extendTop_schur_eq_of_translation
      (D.cornerDiagram hPD) (E.cornerDiagram hPE) hcore
      E.topMargin E.topMargin_pos
    dsimp only
    simpa only [min_eq_right hgt.le, ← hb] using hTop.trans heExt.symm

/-- The border step consumes the actual smaller-order induction theorem twice. -/
theorem rigidity_of_corner_translation (D E : BetaDiagram (n + 3))
    (hD : D.Connected) (hE : E.Connected) (hND : D.Nonnegative)
    (hPD : D.PositiveCorner) (hPE : E.PositiveCorner)
    (hcore : (D.cornerDiagram hPD).TranslationEquivalent (E.cornerDiagram hPE))
    (he : D.schur = E.schur)
    (ih : ∀ T U : BetaDiagram (n + 2), T.Connected → U.Connected →
      T.Nonnegative → T.schur = U.schur →
      T.TranslationEquivalent U ∨ T.RotationEquivalent U) :
    D.TranslationEquivalent E ∨ D.RotationEquivalent E := by
  have hNE := D.nonnegative_of_corner_translation E hND hPD hPE hcore
  have hsum := D.marginSum_eq_of_corner_translation E hPD hPE hcore
    (D.largestLabel_eq_of_schur_eq E hD hE he)
  have hmin := D.minMargin_eq_of_schur_eq E hD hE hND hNE he
  have hmargins :
      (D.topMargin = E.topMargin ∧ D.bottomMargin = E.bottomMargin) ∨
      (D.topMargin = E.bottomMargin ∧ D.bottomMargin = E.topMargin) := by
    omega
  rcases hmargins with ⟨ht, hb⟩ | ⟨ht, hb⟩
  · exact Or.inl (D.translation_of_corner_translation_of_margins E hPD hPE hcore ht hb)
  · by_cases hne : D.topMargin = D.bottomMargin
    · left
      apply D.translation_of_corner_translation_of_margins E hPD hPE hcore <;> omega
    · let T := D.cornerDiagram hPD
      let d := min D.topMargin D.bottomMargin
      have hd : 0 < d := lt_min D.topMargin_pos D.bottomMargin_pos
      have hTC := D.cornerDiagram_connected hND hPD (by omega)
      have hTN := D.cornerDiagram_nonnegative hND hPD
      have hExt := D.extensions_schur_eq_of_swapped_margins E hD hE hND hPD hPE
        hcore ht hb hne he
      rcases ih (T.extendTop d hd) (T.extendBottom d hd)
        (T.extendTop_connected hTC d hd) (T.extendBottom_connected hTC d hd)
        (T.extendTop_nonnegative hTN d hd) hExt with htr | hrot
      · exact False.elim (T.extendTop_not_translation_extendBottom d hd htr)
      · right
        exact D.rotation_of_corner_translation_of_swapped_margins E hPD hPE hcore ht hb
          (T.symmetric_of_extendTop_rotation_extendBottom d hd hrot)

/-- Positive corner rows are preserved by the half-turn
even before nonnegative indices are known. -/
theorem rotate_positiveCorner (D : BetaDiagram (n + 1)) (hP : D.PositiveCorner) :
    D.rotate.PositiveCorner := by
  intro i
  have hp := hP i.rev
  change -D.row i.castSucc.rev < -D.col i.succ.rev
  rw [Fin.rev_castSucc, Fin.rev_succ]
  omega

/-- A recovered core rotation is a core translation after rotating the unknown parent. -/
theorem corner_translation_of_rotation (D E : BetaDiagram (n + 1))
    (hPD : D.PositiveCorner) (hPE : E.PositiveCorner)
    (h : (D.cornerDiagram hPD).RotationEquivalent (E.cornerDiagram hPE)) :
    (D.cornerDiagram hPD).TranslationEquivalent
      (E.rotate.cornerDiagram (E.rotate_positiveCorner hPE)) := by
  obtain ⟨c, hr, hc⟩ := h
  refine ⟨c, ?_, ?_⟩
  · intro i
    have ht := hr i
    change D.row i.succ = c - E.col i.rev.castSucc at ht
    change D.row i.succ = -E.col i.succ.rev + c
    rw [Fin.rev_succ]
    omega
  · intro i
    have ht := hc i
    change D.col i.castSucc = c - E.row i.rev.succ at ht
    change D.col i.castSucc = -E.row i.castSucc.rev + c
    rw [Fin.rev_castSucc]
    omega

/-- Translating the half-turn of a parent is the same geometric conclusion as rotating it. -/
theorem translation_rotate_iff_rotation (D E : BetaDiagram n) :
    D.TranslationEquivalent E.rotate ↔ D.RotationEquivalent E := by
  constructor
  · rintro ⟨c, hr, hc⟩
    refine ⟨c, ?_, ?_⟩
    · intro i; have := hr i; change D.row i = -E.col i.rev + c at this; omega
    · intro i; have := hc i; change D.col i = -E.row i.rev + c at this; omega
  · rintro ⟨c, hr, hc⟩
    refine ⟨c, ?_, ?_⟩
    · intro i; have := hr i; change D.row i = -E.col i.rev + c; omega
    · intro i; have := hc i; change D.col i = -E.row i.rev + c; omega

/-- A rotation of a half-turn is a translation of the original parent. -/
theorem rotation_rotate_iff_translation (D E : BetaDiagram n) :
    D.RotationEquivalent E.rotate ↔ D.TranslationEquivalent E := by
  constructor
  · rintro ⟨c, hr, hc⟩
    refine ⟨c, ?_, ?_⟩
    · intro i; have := hr i; simp only [rotate, Fin.rev_rev] at this; omega
    · intro i; have := hc i; simp only [rotate, Fin.rev_rev] at this; omega
  · rintro ⟨c, hr, hc⟩
    refine ⟨c, ?_, ?_⟩
    · intro i; have := hr i; simp only [rotate, Fin.rev_rev]; omega
    · intro i; have := hc i; simp only [rotate, Fin.rev_rev]; omega

/-- Full nonnegative-index rigidity; no index condition is imposed on the unknown mate. -/
theorem nonnegative_rigidity_same_order (D E : BetaDiagram n)
    (hD : D.Connected) (hE : E.Connected) (hN : D.Nonnegative)
    (hEq : D.schur = E.schur) :
    D.TranslationEquivalent E ∨ D.RotationEquivalent E := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => exact False.elim (by simpa [Connected] using hD.1)
      | succ n =>
          cases n with
          | zero => exact Or.inl (D.rigidity_one E hEq)
          | succ n =>
              cases n with
              | zero => exact D.rigidity_two E hD hE hEq
              | succ n =>
                  let hPD := D.positiveCorner_of_nonnegative hN
                  have hCornerEq := D.cornerPolynomial_eq_of_schur_eq E hD hE hEq
                  let hPE := D.positiveCorner_of_cornerPolynomial_eq E hD hE hPD hCornerEq
                  have hTC := D.cornerDiagram_connected hN hPD (by omega)
                  have hTN := D.cornerDiagram_nonnegative hN hPD
                  have hUC : (E.cornerDiagram hPE).Connected :=
                    D.recovered_corner_connected E hD hE hN hEq
                  have hsmall := ih (n + 2) (by omega)
                  have hsmallEq : (D.cornerDiagram hPD).schur =
                      (E.cornerDiagram hPE).schur := hCornerEq
                  rcases hsmall (D.cornerDiagram hPD) (E.cornerDiagram hPE)
                    hTC hUC hTN hsmallEq with htr | hrot
                  · exact D.rigidity_of_corner_translation E hD hE hN hPD hPE htr hEq
                      (fun T U hT hU hNT he => hsmall T U hT hU hNT he)
                  · have htr := D.corner_translation_of_rotation E hPD hPE hrot
                    have hrEq : D.schur = E.rotate.schur := hEq.trans E.rotate_schur.symm
                    rcases D.rigidity_of_corner_translation E.rotate hD (E.rotate_connected hE)
                      hN hPD (E.rotate_positiveCorner hPE) htr hrEq
                      (fun T U hT hU hNT he => hsmall T U hT hU hNT he) with h | h
                    · exact Or.inr ((D.translation_rotate_iff_rotation E).mp h)
                    · exact Or.inl ((D.rotation_rotate_iff_translation E).mp h)

/-- `thm:nonnegative-rigidity`: arbitrary-order assembly first produces
row-count equality from the actual observations. -/
theorem nonnegative_rigidity {m : ℕ} (D : BetaDiagram n) (E : BetaDiagram m)
    (hD : D.Connected) (hE : E.Connected) (hN : D.Nonnegative)
    (hEq : D.schur = E.schur) :
    ∃ hnm : n = m,
      D.TranslationEquivalent (hnm.symm ▸ E) ∨ D.RotationEquivalent (hnm.symm ▸ E) := by
  have hnm := D.row_count_of_schur_eq E hEq
  subst m
  exact ⟨rfl, D.nonnegative_rigidity_same_order E hD hE hN hEq⟩

end BetaDiagram
end SkewCofactorIndependence
