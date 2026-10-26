/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-!
# Signs of permutations preserving two ordered blocks

The permutation-parity input for `eq:boundary-lowest-degree` in
`shields-2026-skew-class-inflation.tex`.  An order-preserving shuffle
has no inversions inside either block; its sign is the product over
the actual cross-block comparisons.  Sorry-free.
-/

namespace SkewClassInflation

open scoped BigOperators

/-- The sign of an increasing two-block shuffle is exactly its cross-block inversion product. -/
theorem sign_ordered_blocks {k z : ℕ} (σ : Equiv.Perm (Fin (k + z)))
    (hl : StrictMono (fun i : Fin k => σ (i.castAdd z)))
    (hr : StrictMono (fun j : Fin z => σ (j.natAdd k))) :
    σ.sign = ∏ i : Fin k, ∏ j : Fin z,
      if σ (i.castAdd z) < σ (j.natAdd k) then (1 : ℤˣ) else -1 := by
  classical
  let w (i j : Fin (k + z)) : ℤˣ :=
    if i < j then (if σ i < σ j then 1 else -1) else 1
  have hσ : σ.sign = ∏ i : Fin (k + z), ∏ j : Fin (k + z), w i j := by
    rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
    apply Finset.prod_congr rfl
    intro i _
    have hi : Finset.Ioi i = Finset.univ.filter (fun j : Fin (k + z) => i < j) := by
      ext j
      simp
    rw [hi, Finset.prod_filter]
  have hleft (i : Fin k) : (∏ j : Fin (k + z), w (i.castAdd z) j) =
      ∏ j : Fin z, if σ (i.castAdd z) < σ (j.natAdd k) then (1 : ℤˣ) else -1 := by
    rw [Fin.prod_univ_add]
    have hll : (∏ j : Fin k, w (i.castAdd z) (j.castAdd z)) = 1 := by
      apply Finset.prod_eq_one
      intro j _
      by_cases hij : i < j
      · have ho : i.castAdd z < j.castAdd z := hij
        simp only [w, ite_eq_left ho, ite_eq_left (hl hij)]
      · have ho : ¬ i.castAdd z < j.castAdd z := hij
        simp only [w, ite_eq_right ho]
    rw [hll, one_mul]
    apply Finset.prod_congr rfl
    intro j _
    have ho : i.castAdd z < j.natAdd k := by
      change i.val < k + j.val
      have := i.isLt
      omega
    simp only [w, ite_eq_left ho]
  have hright (i : Fin z) : (∏ j : Fin (k + z), w (i.natAdd k) j) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    refine Fin.addCases (fun j : Fin k => ?_) (fun j : Fin z => ?_) j
    · have ho : ¬ i.natAdd k < j.castAdd z := by
        change ¬ k + i.val < j.val
        have := j.isLt
        omega
      simp only [w, ite_eq_right ho]
    · by_cases hij : i < j
      · have ho : i.natAdd k < j.natAdd k := by
          change k + i.val < k + j.val
          exact Nat.add_lt_add_left hij k
        simp only [w, ite_eq_left ho, ite_eq_left (hr hij)]
      · have ho : ¬ i.natAdd k < j.natAdd k := by
          change ¬ k + i.val < k + j.val
          omega
        simp only [w, ite_eq_right ho]
  rw [hσ, Fin.prod_univ_add]
  simp_rw [hleft, hright]
  rw [Finset.prod_const_one, mul_one]

end SkewClassInflation
