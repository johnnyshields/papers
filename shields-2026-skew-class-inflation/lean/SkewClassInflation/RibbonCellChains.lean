/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ProfileJoinCells
import SkewClassInflation.HorizontalCells
import SkewClassInflation.RibbonDeterminants
import SkewClassInflation.ThinCompositions

/-!
# Literal outer ribbons assembled from their rows

The actual outer ribbons in `lem:subthreshold-transport` of
`shields-2026-skew-class-inflation.tex`.  Their complete row word,
zero-gap profile, and Schur determinant are identified explicitly.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- The full joined row word is the concatenation of the two full row words. -/
theorem join_row_word {n m : ℕ} (P : Profile n) (Q : Profile m) (d : ℕ)
    (hP : d < P.r (Fin.last n)) (hQ : d < Q.r 0) :
    List.ofFn (Profile.join P Q d hP hQ).r = List.ofFn P.r ++ List.ofFn Q.r := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
    change Profile.joinRows P Q ⟨i, by simpa only [List.length_ofFn] using hi⟩ = _
    unfold Profile.joinRows
    split_ifs <;> rfl

/-- The normalized profile of a single horizontal ribbon row. -/
def ribbonRow (a : ℕ) (ha : 0 < a) : Profile 0 := ribbonRows a ha [] (by simp)

/-- The actual single-row cell set has its standard origin. -/
theorem profileCells_ribbonRow (a : ℕ) (ha : 0 < a) :
    profileCells (ribbonRow a ha) = rowCells 0 a := by
  ext x
  rcases x with ⟨i, j⟩
  rw [mem_profileCells, mem_rowCells]
  have hx : (ribbonRow a ha).xi 0 = a := by
    have he := (ribbonRow a ha).xi_sub_zeta 0
    have hz := (ribbonRow a ha).zeta_last
    change (ribbonRow a ha).zeta 0 = 0 at hz
    rw [hz, sub_zero] at he
    exact he
  have hz : (ribbonRow a ha).zeta 0 = 0 := (ribbonRow a ha).zeta_last
  constructor
  · rintro ⟨k, hk, hlo, hhi⟩
    have he : k = 0 := Fin.ext (by have := k.isLt; simp only [Fin.val_zero]; omega)
    subst k
    simp only [hz, hx, Fin.val_zero, Nat.cast_zero, add_zero] at hk hlo hhi
    exact ⟨hk.symm, hlo, hhi⟩
  · rintro ⟨rfl, hlo, hhi⟩
    exact ⟨0, rfl, by simpa only [hz, Fin.val_zero, Nat.cast_zero, add_zero] using hlo,
      by simpa only [hx, Fin.val_zero, Nat.cast_zero, add_zero] using hhi⟩

/-- Assemble a nonempty positive outer word using literal zero joins. -/
def ribbonChain (a : ℕ) (ha : 0 < a) :
    (l : List ℕ) → (∀ k ∈ l, 0 < k) → ConnectedProfile
  | [], _ => ⟨0, ribbonRow a ha⟩
  | b :: l, hl => ConnectedProfile.zeroJoin ⟨0, ribbonRow a ha⟩
      (ribbonChain b (hl b List.mem_cons_self) l
        (fun k hk => hl k (List.mem_cons_of_mem _ hk)))

/-- Every original row survives in its original order, including repeated equal parts. -/
theorem ribbonChain_word (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
    List.ofFn (ribbonChain a ha l hl).2.r = a :: l := by
  induction l generalizing a with
  | nil => exact ribbonRows_word a ha [] (by simp)
  | cons b l ih =>
    change List.ofFn (Profile.zeroJoin (ribbonRow a ha)
      (ribbonChain b (hl b List.mem_cons_self) l _).2).r = _
    rw [Profile.zeroJoin, join_row_word, ih, ribbonRow, ribbonRows_word]
    rfl

/-- No positive gap is introduced into an ordinary outer ribbon. -/
theorem ribbonChain_gaps (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
    ∀ j, (ribbonChain a ha l hl).2.g j = 0 := by
  induction l generalizing a with
  | nil => intro j; exact Fin.elim0 j
  | cons b l ih =>
    intro j
    change Profile.joinGaps (ribbonRow a ha) (ribbonChain b _ l _).2 0 j = 0
    unfold Profile.joinGaps
    split_ifs
    · omega
    · rfl
    · exact ih b _ _ _

/-- The literal outer ribbon has exactly the canonical independent-generator ribbon function. -/
theorem ribbonChain_schur (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
    (ribbonChain a ha l hl).2.toBetaDiagram.schur = ribbonWord (a :: l) := by
  rw [zero_gaps_ribbon_polynomial _ (ribbonChain_gaps a ha l hl), ribbonChain_word]

/-- The content span of the actual outer ribbon is its total number of cells. -/
theorem ribbonChain_span (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
    (ribbonChain a ha l hl).2.xi 0 = (a + l.sum : ℕ) := by
  rw [profile_span_sum]
  simp only [ribbonChain_gaps, Nat.cast_zero, Finset.sum_const_zero, sub_zero]
  have he := congrArg (fun s : List ℕ => s.sum) (ribbonChain_word a ha l hl)
  simp only [List.sum_ofFn, List.sum_cons] at he
  exact_mod_cast he

/-- The recursive literal ribbon is exactly the standard full row-and-gap profile. -/
theorem ribbonChain_eq_ribbonRows (a : ℕ) (ha : 0 < a) (l : List ℕ)
    (hl : ∀ k ∈ l, 0 < k) :
    ribbonChain a ha l hl = ⟨l.length, ribbonRows a ha l hl⟩ := by
  apply profileSigma_eq_of_words
  · exact (ribbonChain_word a ha l hl).trans (ribbonRows_word a ha l hl).symm
  · have hn := congrArg List.length (ribbonChain_word a ha l hl)
    simp only [List.length_ofFn, List.length_cons] at hn
    apply List.ext_getElem
    · simp only [List.length_ofFn]
      omega
    · intro i hi hj
      simp only [List.getElem_ofFn]
      exact ribbonChain_gaps a ha l hl _

/-- The outer ribbon of a composition in its literal normalized cell coordinates. -/
def outerRibbon {M : ℕ} (α : Composition M) (hM : 0 < M) : ConnectedProfile :=
  match he : α.blocks with
  | [] => False.elim (by
      have hs := α.blocks_sum
      rw [he] at hs
      simp only [List.sum_nil] at hs
      omega)
  | a :: l => ribbonChain a
      (α.blocks_pos (by rw [he]; exact List.mem_cons_self)) l
      (fun _ hk => α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hk))

/-- Every outer composition retains its complete original ribbon word. -/
theorem outerRibbon_word {M : ℕ} (α : Composition M) (hM : 0 < M) :
    List.ofFn (outerRibbon α hM).2.r = α.blocks := by
  unfold outerRibbon
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · rename_i a l he
    exact (ribbonChain_word a _ l _).trans he.symm

/-- The actual normalized outer has the Schur function of the original composition. -/
theorem outerRibbon_schur {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (outerRibbon α hM).2.toBetaDiagram.schur = ribbonWord α.blocks := by
  unfold outerRibbon
  split
  · rename_i he
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  · rename_i a l he
    exact (ribbonChain_schur a _ l _).trans (congrArg ribbonWord he.symm)

/-- A proved nonempty outer word identifies the actual canonical ribbon with its literal chain. -/
theorem outerRibbon_eq_chain {M : ℕ} (α : Composition M) (hM : 0 < M)
    (a : ℕ) (ha : 0 < a) (l : List ℕ) (hl : ∀ b ∈ l, 0 < b)
    (he : α.blocks = a :: l) : outerRibbon α hM = ribbonChain a ha l hl := by
  unfold outerRibbon
  split
  · rename_i hnil
    rw [he] at hnil
    cases hnil
  · rename_i b q hbq
    obtain ⟨rfl, rfl⟩ := List.cons.inj (he.symm.trans hbq)
    rfl

end SkewClassInflation
