/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVisibleProfileCoefficients

/-!
# Full original inverse values from visible profile jets

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
Matched actual endpoint distances and equal visible polynomial coefficients
produce the corresponding complete incoming and outgoing inverse values.
No retained row, column or inverse coupling is omitted.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Equal visible profile coefficients at matched actual row distances give
the complete incoming inverse values, without discarding any retained index. -/
theorem original_incoming_value_of_profile_jet {n m : ℕ} (P : Profile n) (Q : Profile m)
    (a : OriginalSelectedBlocks (hD := hD) P)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (a' : OriginalSelectedBlocks (hD := hD) Q)
    (b' : Option (OriginalSelectedBlocks (hD := hD) Q))
    (p : OriginalResponseInterval (hD := hD) P (some a) b)
    (q : OriginalResponseInterval (hD := hD) Q (some a') b') (K : ℤ)
    (hcoeff : ∀ w : ℕ, 2 * (w : ℤ) < K →
      (c.originalResidueLeftEndpointPolynomial P (some a) b).coeff w =
        (c.originalResidueLeftEndpointPolynomial Q (some a') b').coeff w)
    (hdist : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
        originalResponseRows P p.1.1 =
      Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
        originalResponseRows Q q.1.1)
    (hvisible : 2 * (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
      originalResponseRows P p.1.1) < K) :
    let rowP := fun k : OriginalResponseInterval (hD := hD) P (some a) b =>
      originalResponseRows P k.1.1
    let colP := fun k : OriginalResponseInterval (hD := hD) P (some a) b =>
      originalResponseCols P k.1.1
    let rowQ := fun k : OriginalResponseInterval (hD := hD) Q (some a') b' =>
      originalResponseRows Q k.1.1
    let colQ := fun k : OriginalResponseInterval (hD := hD) Q (some a') b' =>
      originalResponseCols Q k.1.1
    (vertexOutgoing c.residueMap colP
        (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))) *
      (vertexBetaMatrix c.residueMap rowP colP)⁻¹) () p =
    (vertexOutgoing c.residueMap colQ
        (Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a')))) *
      (vertexBetaMatrix c.residueMap rowQ colQ)⁻¹) () q := by
  have hp := originalResponse_row_lt P (some a) p.1.1 p.2
  change originalResponseRows P p.1.1 <
    P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) at hp
  have hw : 0 ≤ P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
      originalResponseRows P p.1.1 := by omega
  have h := hcoeff (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
    originalResponseRows P p.1.1).toNat (by rw [Int.toNat_of_nonneg hw]; exact hvisible)
  have hqDegree := congrArg Int.toNat hdist
  rw [hqDegree] at h
  have hpc := c.original_left_profile_coeff_at_row P (some a) b p
  have hqc := c.original_left_profile_coeff_at_row Q (some a') b' q
  rw [← hqDegree, hpc, hqDegree, hqc] at h
  exact neg_inj.mp h

/-- The outgoing version retains the full genuine interval inverse as well. -/
theorem original_outgoing_value_of_profile_jet {n m : ℕ} (P : Profile n) (Q : Profile m)
    (a : Option (OriginalSelectedBlocks (hD := hD) P))
    (b : OriginalSelectedBlocks (hD := hD) P)
    (a' : Option (OriginalSelectedBlocks (hD := hD) Q))
    (b' : OriginalSelectedBlocks (hD := hD) Q)
    (p : OriginalResponseInterval (hD := hD) P a (some b))
    (q : OriginalResponseInterval (hD := hD) Q a' (some b')) (K : ℤ)
    (hcoeff : ∀ w : ℕ, 2 * (w : ℤ) < K →
      (c.originalResidueRightEndpointPolynomial P a (some b)).coeff w =
        (c.originalResidueRightEndpointPolynomial Q a' (some b')).coeff w)
    (hdist : originalResponseCols P p.1.1 -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) =
      originalResponseCols Q q.1.1 -
        Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b'))))
    (hvisible : 2 * (originalResponseCols P p.1.1 -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))) < K) :
    let rowP := fun k : OriginalResponseInterval (hD := hD) P a (some b) =>
      originalResponseRows P k.1.1
    let colP := fun k : OriginalResponseInterval (hD := hD) P a (some b) =>
      originalResponseCols P k.1.1
    let rowQ := fun k : OriginalResponseInterval (hD := hD) Q a' (some b') =>
      originalResponseRows Q k.1.1
    let colQ := fun k : OriginalResponseInterval (hD := hD) Q a' (some b') =>
      originalResponseCols Q k.1.1
    ((vertexBetaMatrix c.residueMap rowP colP)⁻¹ * vertexIncoming c.residueMap rowP
      (P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))))) p () =
    ((vertexBetaMatrix c.residueMap rowQ colQ)⁻¹ * vertexIncoming c.residueMap rowQ
      (Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b'))))) q () := by
  have hp := originalResponse_col_gt P (some b) p.1.1 p.1.2
  change P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) <
    originalResponseCols P p.1.1 at hp
  have hw : 0 ≤ originalResponseCols P p.1.1 -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) := by omega
  have h := hcoeff (originalResponseCols P p.1.1 -
    P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))).toNat
    (by rw [Int.toNat_of_nonneg hw]; exact hvisible)
  have hqDegree := congrArg Int.toNat hdist
  rw [hqDegree] at h
  have hpc := c.original_right_profile_coeff_at_col P a (some b) p
  have hqc := c.original_right_profile_coeff_at_col Q a' (some b') q
  rw [← hqDegree, hpc, hqDegree, hqc] at h
  exact neg_inj.mp h

end SkewCornerDescent.Matrix.SelectedCoordinate
