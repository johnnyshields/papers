/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ZeroFreeTransport

/-!
# Membership words of the beta lists under inflation

Formalizes the word formulas in the proof of `lem:inflate-chart` in
`shields-2026-skew-class-inflation.tex`.  The full membership words are
\(A(j)=\mathbf 1_{j\in Y}\) and \(B(j)=\mathbf 1_{j\in X}\), with height
\(H(j)=\#\{y\in Y:y\le j\}-\#\{x\in X:x\le j\}\).  One inflation step acts by
\(A_{\mathcal I}(j)=A(j)\), \(B_{\mathcal I}(j)=B(j-1)\), \(H_{\mathcal I}(j)=H(j)+B(j)\),
and the inflated board is zero-free exactly when \(B(j)A(j+1)=0\) for every \(j\).
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

namespace Profile

variable {n : ℕ}

/-- The lower word: `1` exactly at the members of the column beta list. -/
noncomputable def wordA (P : Profile n) (j : ℤ) : ℤ :=
  open Classical in if ∃ k, P.zeta k = j then 1 else 0

/-- The upper word: `1` exactly at the members of the row beta list. -/
noncomputable def wordB (P : Profile n) (j : ℤ) : ℤ :=
  open Classical in if ∃ i, P.xi i = j then 1 else 0

/-- The height `#{y ≤ j} - #{x ≤ j}`. -/
noncomputable def wordH (P : Profile n) (j : ℤ) : ℤ :=
  open Classical in
  ((Finset.univ.filter fun k => P.zeta k ≤ j).card : ℤ) -
    (Finset.univ.filter fun i => P.xi i ≤ j).card

theorem wordA_inflate (t : ℕ) (P : Profile n) (j : ℤ) :
    wordA (inflate t P) j = wordA P j := by
  unfold wordA
  simp only [zeta_inflate]

theorem wordB_inflate_one (P : Profile n) (j : ℤ) :
    wordB (inflate 1 P) j = wordB P (j - 1) := by
  unfold wordB
  simp only [xi_inflate]
  have : (∃ i, P.xi i + ((1 : ℕ) : ℤ) = j) ↔ ∃ i, P.xi i = j - 1 := by
    constructor <;> rintro ⟨i, hi⟩ <;> exact ⟨i, by push_cast at *; omega⟩
  simp only [this]

theorem wordH_inflate_one (P : Profile n) (j : ℤ) :
    wordH (inflate 1 P) j = wordH P j + wordB P j := by
  classical
  unfold wordH wordB
  simp only [zeta_inflate, xi_inflate]
  have hfil : (Finset.univ.filter fun i : Fin (n + 1) => P.xi i + ((1 : ℕ) : ℤ) ≤ j) =
      Finset.univ.filter fun i : Fin (n + 1) => P.xi i ≤ j - 1 := by
    apply Finset.filter_congr
    intro i _
    push_cast
    omega
  have hsplit : (Finset.univ.filter fun i : Fin (n + 1) => P.xi i ≤ j) =
      (Finset.univ.filter fun i : Fin (n + 1) => P.xi i ≤ j - 1) ∪
        Finset.univ.filter fun i : Fin (n + 1) => P.xi i = j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.univ.filter fun i : Fin (n + 1) => P.xi i ≤ j - 1)
      (Finset.univ.filter fun i : Fin (n + 1) => P.xi i = j) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega
  have hone : (Finset.univ.filter fun i : Fin (n + 1) => P.xi i = j).card =
      if ∃ i, P.xi i = j then 1 else 0 := by
    split_ifs with h
    · obtain ⟨i, hi⟩ := h
      rw [Finset.card_eq_one]
      refine ⟨i, ?_⟩
      ext i'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h' => P.xi_strictAnti.injective (h'.trans hi.symm), fun h' => h' ▸ hi⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hi
      exact h ⟨i, hi⟩
  rw [hfil, hsplit, Finset.card_union_of_disjoint hdisj, hone]
  push_cast
  ring

/-- Index minus one occurs exactly when a row beta is one below a column beta. -/
theorem exists_index_neg_one_iff (P : Profile n) :
    (∃ i j, P.xi i - P.zeta j = -1) ↔ ∃ m : ℤ, wordB P m = 1 ∧ wordA P (m + 1) = 1 := by
  classical
  unfold wordA wordB
  constructor
  · rintro ⟨i, j, h⟩
    refine ⟨P.xi i, by simp, ?_⟩
    rw [ite_eq_left ⟨j, by omega⟩]
  · rintro ⟨m, h1, h2⟩
    have e1 : ∃ i, P.xi i = m := by
      by_contra hc; rw [ite_eq_right hc] at h1; exact zero_ne_one h1
    have e2 : ∃ k, P.zeta k = m + 1 := by
      by_contra hc; rw [ite_eq_right hc] at h2; exact zero_ne_one h2
    obtain ⟨i, hi⟩ := e1
    obtain ⟨k, hk⟩ := e2
    exact ⟨i, k, by omega⟩

/-- The inflated board is zero-free exactly when `B(j) A(j + 1) = 0` for every `j`. -/
theorem zeroFree_inflate_one_iff (P : Profile n) :
    (inflate 1 P).ZeroFree ↔ ∀ m : ℤ, wordB P m * wordA P (m + 1) = 0 := by
  have h1 : (inflate 1 P).ZeroFree ↔ ¬ ∃ i j, P.xi i - P.zeta j = -1 := by
    unfold ZeroFree
    simp only [xi_inflate, zeta_inflate, not_exists]
    constructor
    · intro h i j hij
      exact h i j (by push_cast at *; omega)
    · intro h i j hij
      exact h i j (by push_cast at *; omega)
  rw [h1, exists_index_neg_one_iff]
  have hB01 : ∀ m, wordB P m = 0 ∨ wordB P m = 1 := by
    intro m; unfold wordB; split_ifs <;> simp
  have hA01 : ∀ m, wordA P m = 0 ∨ wordA P m = 1 := by
    intro m; unfold wordA; split_ifs <;> simp
  constructor
  · intro h m
    by_contra hm
    apply h
    refine ⟨m, ?_, ?_⟩
    · rcases hB01 m with h1 | h1 <;> rcases hA01 (m + 1) with h2 | h2 <;>
        simp_all
    · rcases hB01 m with h1 | h1 <;> rcases hA01 (m + 1) with h2 | h2 <;>
        simp_all
  · rintro h ⟨m, hb, ha⟩
    have := h m
    rw [hb, ha] at this
    simp at this

end Profile
end SkewClassInflation
