-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/MurnaghanNakayama/Raise.lean
import GluingCore.OlsonHarris.Plan.MurnaghanNakayama.RowMove
import GluingCore.SchurBridge

/-!
# Raising one β-number of a Young diagram

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis §5.1.3 (`OlsonHarris2024HopfApplications`).

For a Young diagram `μ` with the β-numbers `b_i = μ_i - i`, raising `b_j` by `m` to a value not
among the other `b_k` and sorting yields a Young diagram `ν` with `ν / μ` a ribbon of `m` cells:
`exists_rowMove_of_injective` constructs `ν` together with its `RowMove`.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace MN

/-- **Raising a β-number gives a row move.** -/
theorem exists_rowMove_of_injective {mu : YoungDiagram} {M j m : ℕ}
    (hM : ∀ i, M ≤ i → mu.rowLen i = 0) (hj : j < M) (hm : 0 < m)
    (hinj : ∀ k, k < M → k ≠ j → (mu.rowLen k : ℤ) - k ≠ mu.rowLen j - j + m) :
    ∃ nu i1, RowMove mu nu j i1 m := by
  classical
  have hP : ∃ i, i ≤ j ∧ (mu.rowLen i : ℤ) - i < mu.rowLen j - j + m := ⟨j, le_rfl, by omega⟩
  obtain ⟨i1, hi1j, hi1b, hmin⟩ : ∃ i1, i1 ≤ j ∧ (mu.rowLen i1 : ℤ) - i1 < mu.rowLen j - j + m ∧
      ∀ i < i1, (mu.rowLen j : ℤ) - j + m < mu.rowLen i - i := by
    refine ⟨Nat.find hP, (Nat.find_spec hP).1, (Nat.find_spec hP).2, fun i hi => ?_⟩
    have h1 := Nat.find_min hP hi
    have h2 : i ≤ j := le_trans hi.le (Nat.find_spec hP).1
    have h3 : ¬ ((mu.rowLen i : ℤ) - i < mu.rowLen j - j + m) := fun h => h1 ⟨h2, h⟩
    have h4 := hinj i (by omega) (by have := (Nat.find_spec hP).1; omega)
    omega
  let f : ℕ → ℕ := fun i =>
    if i < i1 ∨ j < i then mu.rowLen i
    else if i = i1 then mu.rowLen j + m + i1 - j else mu.rowLen (i - 1) + 1
  have hf : ∀ i, f (i + 1) ≤ f i := by
    intro i
    have a1 := mu.rowLen_anti i (i + 1) (by omega)
    have a2 := mu.rowLen_anti (i - 1) i (by omega)
    have a3 := mu.rowLen_anti (i - 1) (i + 1) (by omega)
    have a4 : i + 1 = i1 → (mu.rowLen j : ℤ) - j + m < mu.rowLen i - i :=
      fun h => hmin i (by omega)
    by_cases h1 : i = j
    · subst h1
      by_cases h2 : i = i1
      · subst h2
        simp only [f]
        split_ifs <;> omega
      · simp only [f]
        split_ifs <;> (try simp only [Nat.add_sub_cancel] at *) <;> omega
    · by_cases h2 : i = i1
      · subst h2
        simp only [f]
        split_ifs <;> (try simp only [Nat.add_sub_cancel] at *) <;> omega
      · simp only [f]
        split_ifs <;> (try simp only [Nat.add_sub_cancel] at *) <;> omega
  have hz : ∀ i, M ≤ i → f i = 0 := by
    intro i hi
    simp only [f]
    split_ifs with h1 h2
    · exact hM i hi
    · omega
    · omega
  have hanti : Antitone (fun i : Fin (M + 1) => f i) := by
    intro a b hab
    have : ∀ n, a.val + n ≤ M → f (a.val + n) ≤ f a.val := by
      intro n
      induction n with
      | zero => intro _; exact le_rfl
      | succ n ih => intro h; exact (hf _).trans (ih (by omega))
    have := this (b.val - a.val) (by have := b.isLt; omega)
    rwa [show a.val + (b.val - a.val) = b.val by have := Fin.le_def.mp hab; omega] at this
  let nu := youngOfRows (fun i : Fin (M + 1) => f i) hanti
  have hnu : ∀ i, nu.rowLen i = f i := by
    intro i
    by_cases hi : i < M + 1
    · exact rowLen_youngOfRows (fun i : Fin (M + 1) => f i) hanti ⟨i, hi⟩
    · rw [rowLen_youngOfRows_of_le _ hanti (by omega), hz i (by omega)]
  refine ⟨nu, i1, hi1j, ?_, ?_, ?_⟩
  · intro i hi
    rw [hnu]
    simp only [f]
    split_ifs
    rfl
  · rw [hnu]
    simp only [f]
    split_ifs <;> omega
  · intro i hi1 hi2
    rw [hnu]
    simp only [f]
    split_ifs <;> first | rfl | omega

end MN

end Plan

end GluingCore
