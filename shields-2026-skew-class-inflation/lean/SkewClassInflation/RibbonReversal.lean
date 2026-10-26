/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonDeterminants

/-!
# Literal reversal preserves ribbon functions

The global reversal input to the ribbon classification used in
`thm:repeated-block-saturation` and `thm:sharp-inflation` of
`shields-2026-skew-class-inflation.tex`.  Reversing the complete positive
row word is the actual global rotation of its zero-gap full profile.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- Reversing a finite natural row vector reverses its literal word. -/
theorem word_ofFn_rev {n : ℕ} (r : Fin n → ℕ) :
    List.ofFn (fun i => r i.rev) = (List.ofFn r).reverse := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_reverse]
  · intro i hi hj
    rw [List.getElem_ofFn, List.getElem_reverse]
    simp only [List.length_ofFn, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

/-- Reversing the full positive ribbon row word leaves its Schur function unchanged. -/
theorem ribbonWord_ofFn_reverse {n : ℕ} (r : Fin (n + 1) → ℕ) (hr : ∀ i, 0 < r i) :
    ribbonWord (List.ofFn r).reverse = ribbonWord (List.ofFn r) := by
  let P : Profile n :=
    { r := r, g := fun _ => 0, r_pos := hr,
      g_lt_castSucc := fun j => hr j.castSucc, g_lt_succ := fun j => hr j.succ }
  have he : P.rotate.toBetaDiagram.schur = P.toBetaDiagram.schur := by
    simpa only [Gluing.Profile.toBetaDiagram_schur] using P.schur_rotate
  rw [zero_gaps_ribbon_polynomial _ (fun _ => rfl),
    zero_gaps_ribbon_polynomial _ (fun _ => rfl)] at he
  change ribbonWord (List.ofFn (fun i : Fin (n + 1) => r i.rev)) = ribbonWord (List.ofFn r) at he
  rw [word_ofFn_rev] at he
  exact he

/-- Global reversal preserves every actual positive composition's ribbon function. -/
theorem ribbonWord_reverse {M : ℕ} (α : Composition M) (hM : 0 < M) :
    ribbonWord α.reverse.blocks = ribbonWord α.blocks := by
  cases he : α.blocks with
  | nil =>
    have hs := α.blocks_sum
    rw [he] at hs
    simp only [List.sum_nil] at hs
    omega
  | cons a l =>
    have ha := α.blocks_pos (by rw [he]; exact List.mem_cons_self)
    have hl : ∀ m ∈ l, 0 < m := fun m hm =>
      α.blocks_pos (by rw [he]; exact List.mem_cons_of_mem _ hm)
    have hh := ribbonWord_ofFn_reverse (ribbonRows a ha l hl).r (ribbonRows a ha l hl).r_pos
    rw [ribbonRows_word] at hh
    simpa only [Composition.reverse_blocks, he] using hh

/-- The literal positive word version includes the empty unit word. -/
theorem ribbonWord_reverse_word (w : List ℕ) (hw : ∀ a ∈ w, 0 < a) :
    ribbonWord w.reverse = ribbonWord w := by
  cases w with
  | nil => rfl
  | cons a l =>
    let α : Composition (a + l.sum) := ⟨a :: l, fun {b} hb => hw b hb, rfl⟩
    have ha := hw a List.mem_cons_self
    exact ribbonWord_reverse α (by omega)

end SkewClassInflation
