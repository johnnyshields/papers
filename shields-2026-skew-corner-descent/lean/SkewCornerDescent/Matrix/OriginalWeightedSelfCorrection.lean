/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalSelfJet

/-!
# Exact weighted self-profile correction on actual internal cycles

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
The full raw/chart identity supplies each self coefficient. A shared
actual residue response makes the raw chart terms cancel between the two
complete cycles, leaving the selected-function derivative times the full
weighted onsite normal jet. No self coefficient is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing MvPolynomial
open scoped BigOperators
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Natural-offset form of the complete actual self-profile correction. -/
theorem originalInternal_self_polynomial_correction {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) (j : ℕ+) (k : ℕ)
    (hdegree : originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i) - (j : ℤ) = (k : ℤ)) :
    let p := c.originalInternalEndpointProfiles P i
    (p.1*p.2).coeff k = residueChartDeriv c.top j (c.originalInternalResidue P i) +
      c.residueMap (pderiv j (cellSchur D hD.1)) *
        PowerSeries.coeff 1 (c.normalSeries (c.originalInternalResponseMatrix P i i)) := by
  have he := c.originalInternal_self_chart_correction P i j
  dsimp only at he ⊢
  rw [hdegree] at he
  have hcoeff (f : Polynomial (OtherField c.top)) : f.toLaurent.coeff (k : ℤ) = f.coeff k := by
    change (Finsupp.mapDomain (fun z : ℕ => (z : ℤ)) f.toFinsupp.coeff) (k : ℤ) = _
    exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ k
  rwa [hcoeff] at he

/-- Complete weighted actual self coefficients equal the selected-function
raw derivative times the complete weighted first onsite normal jet. The
common chart derivative cancels by the actual cardinalities of both cycles. -/
theorem originalInternal_weighted_self_correction {pn qn b d : ℕ} [NeZero b] [NeZero d]
    (P : Profile pn) (Q : Profile qn)
    (ip : ZMod d → Fin (originalSelectedCount (hD := hD) P - 1))
    (iq : ZMod b → Fin (originalSelectedCount (hD := hD) Q - 1))
    (S : OtherField c.top) (j : ℕ+) (k : ℕ)
    (hP : ∀ i, c.originalInternalResidue P (ip i) = S)
    (hQ : ∀ i, c.originalInternalResidue Q (iq i) = S)
    (hdegreeP : ∀ i, originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P (ip i)) (originalInternalStateIndex P (ip i)) - (j : ℤ) =
        (k : ℤ))
    (hdegreeQ : ∀ i, originalHessenbergDistance (hD := hD) Q
      (originalInternalStateIndex Q (iq i)) (originalInternalStateIndex Q (iq i)) - (j : ℤ) =
        (k : ℤ)) :
    (b : OtherField c.top) * (∑ i,
      ((c.originalInternalEndpointProfiles P (ip i)).1 *
        (c.originalInternalEndpointProfiles P (ip i)).2).coeff k) -
    (d : OtherField c.top) * (∑ i,
      ((c.originalInternalEndpointProfiles Q (iq i)).1 *
        (c.originalInternalEndpointProfiles Q (iq i)).2).coeff k) =
    c.residueMap (pderiv j (cellSchur D hD.1)) *
      ((b : OtherField c.top) * (∑ i, PowerSeries.coeff 1
        (c.normalSeries (c.originalInternalResponseMatrix P (ip i) (ip i)))) -
      (d : OtherField c.top) * (∑ i, PowerSeries.coeff 1
        (c.normalSeries (c.originalInternalResponseMatrix Q (iq i) (iq i))))) := by
  have hp (i : ZMod d) := c.originalInternal_self_polynomial_correction P (ip i) j k (hdegreeP i)
  have hq (i : ZMod b) := c.originalInternal_self_polynomial_correction Q (iq i) j k (hdegreeQ i)
  dsimp only at hp hq
  simp_rw [hp, hq, hP, hQ]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, ← Finset.mul_sum]
  ring

end SkewCornerDescent.Matrix.SelectedCoordinate
