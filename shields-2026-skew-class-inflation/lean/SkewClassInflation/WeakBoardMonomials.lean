/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.MonomialBoards
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Monomial classification for weakly feasible beta boards

Formalizes the arbitrary-cofactor step of `lem:hessenberg-membership` in
`shields-2026-skew-class-inflation.tex`.  Diagonal indices may vanish;
connected blocks of order at least two are the only obstruction.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative
open scoped BigOperators

/-- A nonnegative complete-generator index is a single nonzero monomial. -/
theorem isMonomial_complete (k : ℤ) (hk : 0 ≤ k) : IsMonomial (complete k) := by
  rcases eq_or_lt_of_le hk with hk | hk
  · rw [← hk, complete_zero]
    exact ⟨0, 1, one_ne_zero, by simp⟩
  · let j : ℕ+ := ⟨k.toNat, by omega⟩
    refine ⟨Finsupp.single j 1, 1, one_ne_zero, ?_⟩
    exact complete_of_pos hk

/-- A finite product of single nonzero monomials is a single nonzero monomial. -/
theorem isMonomial_prod {ι : Type*} (s : Finset ι) (f : ι → CompleteRing)
    (h : ∀ i ∈ s, IsMonomial (f i)) : IsMonomial (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, one_ne_zero, by simp⟩
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (isMonomial_mul_iff _ _).mpr
      ⟨h i (Finset.mem_insert_self _ _), ih (fun j hj => h j (Finset.mem_insert_of_mem hj))⟩

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/ConnectedIrreducibility.lean,
-- schur_factor_at_cut, adapted to retain weak diagonal feasibility.
/-- A negative adjacent index splits the genuine determinant into its two principal boards. -/
theorem weak_board_factor_at_cut {a b : ℕ} (u v : Fin (a + b) → ℤ)
    (hu : StrictAnti u) (hv : StrictAnti v) (ha : 0 < a) (hb : 0 < b)
    (hcut : u ⟨a, by omega⟩ < v ⟨a - 1, by omega⟩) :
    (betaBoard u v).det =
      (betaBoard (fun i => u (i.castAdd b)) (fun i => v (i.castAdd b))).det *
      (betaBoard (fun i => u (i.natAdd a)) (fun i => v (i.natAdd a))).det := by
  classical
  let e : Fin a ⊕ Fin b ≃ Fin (a + b) := finSumFinEquiv
  let B : Matrix (Fin a) (Fin b) CompleteRing :=
    (betaBoard u v).submatrix (Fin.castAdd b) (Fin.natAdd a)
  have hm : (betaBoard u v).submatrix e e = Matrix.fromBlocks
      (betaBoard (fun i => u (i.castAdd b)) (fun i => v (i.castAdd b))) B 0
      (betaBoard (fun i => u (i.natAdd a)) (fun i => v (i.natAdd a))) := by
    apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · change complete (u (i.natAdd a) - v (j.castAdd b)) = 0
      apply complete_of_neg
      have hr := hu.antitone
        (show (⟨a, by omega⟩ : Fin (a + b)) ≤ i.natAdd a by change a ≤ a + i.val; omega)
      have hc := hv.antitone
        (show j.castAdd b ≤ (⟨a - 1, by omega⟩ : Fin (a + b)) by
          change j.val ≤ a - 1; omega)
      omega
    · rfl
  have hd := Matrix.det_submatrix_equiv_self e (betaBoard u v)
  rw [hm, Matrix.det_fromBlocks_zero₂₁] at hd
  exact hd.symm

/-- Full weak beta boards are monomials precisely when every adjacent lower index is negative. -/
theorem weak_board_monomial_iff (n : ℕ) (u v : Fin n → ℤ)
    (hu : StrictAnti u) (hv : StrictAnti v) (hdiag : ∀ i, v i ≤ u i) :
    IsMonomial (betaBoard u v).det ↔
      ∀ (i : Fin n) (hi : i.val + 1 < n), u ⟨i.val + 1, hi⟩ < v i := by
  classical
  constructor
  · intro hm
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n ≤ 1
      · intro i hi
        have := i.isLt
        omega
      have hn2 : 2 ≤ n := by omega
      by_cases hcut : ∃ (i : Fin n) (hi : i.val + 1 < n), u ⟨i.val + 1, hi⟩ < v i
      · obtain ⟨i, hi, hcut⟩ := hcut
        let a := i.val + 1
        let b := n - a
        have ha : 0 < a := by dsimp [a]; omega
        have hb : 0 < b := by dsimp [a, b]; omega
        have hab : a + b = n := by dsimp [a, b]; omega
        let U : Fin (a + b) → ℤ := fun j => u (Fin.cast hab j)
        let V : Fin (a + b) → ℤ := fun j => v (Fin.cast hab j)
        have hU : StrictAnti U := hu.comp_strictMono (Fin.cast_strictMono hab)
        have hV : StrictAnti V := hv.comp_strictMono (Fin.cast_strictMono hab)
        have hc : U ⟨a, by omega⟩ < V ⟨a - 1, by omega⟩ := by
          have he1 : Fin.cast hab (⟨a, by omega⟩ : Fin (a + b)) = ⟨i.val + 1, hi⟩ :=
            Fin.ext (by rfl)
          have he2 : Fin.cast hab (⟨a - 1, by omega⟩ : Fin (a + b)) = i :=
            Fin.ext (by change i.val + 1 - 1 = i.val; omega)
          simpa only [U, V, he1, he2] using hcut
        have hd : (betaBoard U V).det = (betaBoard u v).det := by
          exact Matrix.det_submatrix_equiv_self (finCongr hab) (betaBoard u v)
        have hm' := hd ▸ hm
        rw [weak_board_factor_at_cut U V hU hV ha hb hc,
          isMonomial_mul_iff] at hm'
        have hl := ih a (by dsimp [a]; omega)
          (fun j => U (j.castAdd b)) (fun j => V (j.castAdd b))
          (hU.comp_strictMono (Fin.strictMono_castAdd b))
          (hV.comp_strictMono (Fin.strictMono_castAdd b))
          (fun j => hdiag _) hm'.1
        have hr := ih b (by dsimp [a, b]; omega)
          (fun j => U (j.natAdd a)) (fun j => V (j.natAdd a))
          (hU.comp_strictMono (Fin.strictMono_natAdd a))
          (hV.comp_strictMono (Fin.strictMono_natAdd a))
          (fun j => hdiag _) hm'.2
        intro j hj
        by_cases hja : j.val + 1 < a
        · have hh := hl ⟨j.val, by omega⟩ hja
          simpa only [U, V, Fin.cast_mk, Fin.castAdd_mk] using hh
        · by_cases hje : j.val + 1 = a
          · have he : j = i := Fin.ext (by dsimp [a] at hje; omega)
            subst j
            exact hcut
          · have hjb : j.val - a < b := by dsimp [b]; omega
            have hh := hr ⟨j.val - a, hjb⟩ (by dsimp [b]; omega)
            have he1 : Fin.cast hab ((⟨j.val - a + 1, by dsimp [b]; omega⟩ : Fin b).natAdd a) =
                (⟨j.val + 1, hj⟩ : Fin n) := Fin.ext (by simp; omega)
            have he2 : Fin.cast hab ((⟨j.val - a, hjb⟩ : Fin b).natAdd a) = j :=
              Fin.ext (by simp; omega)
            simpa only [U, V, he1, he2] using hh
      · have hconn : ∀ (i : Fin n) (hi : i.val + 1 < n), v i ≤ u ⟨i.val + 1, hi⟩ := by
          intro i hi
          by_contra h
          exact hcut ⟨i, hi, by omega⟩
        have hpos : ∀ i : Fin n, v i < u i := by
          intro i
          by_cases hi : i.val + 1 < n
          · have hu' := hu (show i < (⟨i.val + 1, hi⟩ : Fin n) by
              change i.val < i.val + 1; omega)
            have ho := hconn i hi
            omega
          · let j : Fin n := ⟨i.val - 1, by omega⟩
            have hj : j.val + 1 < n := by dsimp [j]; omega
            have he : (⟨j.val + 1, hj⟩ : Fin n) = i := Fin.ext (by dsimp [j]; omega)
            have ho := hconn j hj
            rw [he] at ho
            have hv' := hv (show j < i by dsimp [j]; omega)
            omega
        let D : BetaDiagram n := ⟨u, v, hu, hv, hpos⟩
        exact (connected_schur_not_monomial D ⟨by omega, hconn⟩ hn2 hm).elim
  · intro h
    have htri : (betaBoard u v).IsUpperTriangular := by
      intro i j hij
      change j.val < i.val at hij
      change complete (u i - v j) = 0
      have hj : j.val + 1 < n := by have := i.isLt; omega
      have ho := h j hj
      have hui := hu.antitone
        (show (⟨j.val + 1, hj⟩ : Fin n) ≤ i by change j.val + 1 ≤ i.val; omega)
      exact complete_of_neg (by omega)
    rw [Matrix.det_of_isUpperTriangular htri]
    exact isMonomial_prod Finset.univ _ (fun i _ => isMonomial_complete _ (by
      have := hdiag i
      omega))

end SkewClassInflation
