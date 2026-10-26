-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/Kernel/Homogeneity.lean
import GluingCore.OlsonHarris.Plan.Defs

/-!
# Homogeneity of the power sums

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): the grading of `Λ = ℚ[h₁, h₂, …]` by `deg h_k = k` is
respected by the power sums `p_m` and their products `p_ν`; these facts feed the degreewise
linear independence of the Ferrers Schur functions.

Sorry-free.
-/

namespace GluingCore

namespace Plan

namespace KernelAux

open MvPolynomial

theorem isWeightedHomogeneous_hPos (k : ℕ) : IsWeightedHomogeneous degWeight (hPos k) k := by
  have := isWeightedHomogeneous_hh (j := (k : ℤ)) (Int.natCast_nonneg k)
  rwa [hh_natCast, Int.toNat_natCast] at this

theorem isWeightedHomogeneous_pPoly (m : ℕ) : IsWeightedHomogeneous degWeight (pPoly m) m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases m with _ | n
  · rw [pPoly]; exact isWeightedHomogeneous_zero _ _ _
  · rw [pPoly]
    refine IsWeightedHomogeneous.sub ?_ ?_
    · simpa using (isWeightedHomogeneous_C degWeight ((n + 1 : ℕ) : ℚ)).mul
        (isWeightedHomogeneous_hPos (n + 1))
    · refine IsWeightedHomogeneous.sum _ _ _ fun i _ => ?_
      have h1 := ih (i + 1) (by have := i.isLt; omega)
      have h2 := isWeightedHomogeneous_hPos (n - i)
      have := h1.mul h2
      have hi := i.isLt
      rwa [show (i : ℕ) + 1 + (n - i) = n + 1 by omega] at this

theorem isWeightedHomogeneous_pProd (ν : List ℕ) :
    IsWeightedHomogeneous degWeight (pProd ν) ν.sum := by
  induction ν with
  | nil => simpa [pProd] using isWeightedHomogeneous_one ℚ degWeight
  | cons m ν ih =>
    have := (isWeightedHomogeneous_pPoly m).mul ih
    simpa [pProd] using this

end KernelAux

end Plan

end GluingCore
