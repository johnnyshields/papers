import SkewGluing.DiagramSchur
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Int.Basic

/-!
# Integral skew Schur functions and primitivity

Supports `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `lem:cofactor`). The integral Jacobi--Trudi determinant has the same
coefficient-one diagonal monomial as its rational realization. Reduction modulo each
prime proves primitivity of the product over actual connected components. Sorry-free.
-/

namespace SkewGluing

open MvPolynomial

noncomputable section

/-- Integral complete homogeneous generator, with the usual zero and negative conventions. -/
def integralHH (x : ℤ) : MvPolynomial ℕ+ ℤ :=
  if x < 0 then 0 else monomial (hExp x.toNat) 1

/-- Jacobi--Trudi determinant over the integers. -/
def integralBetaDet {k : ℕ} (ξ ζ : Fin k → ℤ) : MvPolynomial ℕ+ ℤ :=
  (Matrix.of fun i j => integralHH (ξ i - ζ j)).det

@[simp]
theorem map_integralHH (x : ℤ) :
    map (Int.castRingHom ℚ) (integralHH x) = hh x := by
  by_cases hx : x < 0
  · simp [integralHH, hx]
  · simp only [integralHH, hx, ite_false, map_monomial]
    exact (hh_eq_monomial (by omega)).symm

@[simp]
theorem map_integralBetaDet {k : ℕ} (ξ ζ : Fin k → ℤ) :
    map (Int.castRingHom ℚ) (integralBetaDet ξ ζ) = betaDet ξ ζ := by
  rw [integralBetaDet, RingHom.map_det]
  congr 1
  funext i j
  exact map_integralHH _

/-- The diagonal monomial has coefficient one integrally, not merely over the rationals. -/
theorem coeff_integralBetaDet {k : ℕ} {ξ ζ : Fin k → ℤ}
    (hξ : StrictAnti ξ) (hζ : StrictAnti ζ) (hle : ∀ i, ζ i ≤ ξ i) :
    (integralBetaDet ξ ζ).coeff (betaMon ξ ζ) = 1 := by
  have h := (betaDet_extremal hξ hζ hle).1
  rw [← map_integralBetaDet, coeff_map] at h
  change ((integralBetaDet ξ ζ).coeff (betaMon ξ ζ) : ℚ) = 1 at h
  exact_mod_cast h

/-- Every field specialization of a genuine skew Jacobi--Trudi determinant is nonzero. -/
theorem map_integralBetaDet_ne_zero {R : Type*} [CommRing R] [Nontrivial R]
    {k : ℕ} {ξ ζ : Fin k → ℤ}
    (hξ : StrictAnti ξ) (hζ : StrictAnti ζ) (hle : ∀ i, ζ i ≤ ξ i) :
    map (Int.castRingHom R) (integralBetaDet ξ ζ) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : MvPolynomial ℕ+ R => f.coeff (betaMon ξ ζ)) h
  simp [coeff_map, coeff_integralBetaDet hξ hζ hle] at hc

/-- Integral determinant of a connected profile. -/
def Profile.integralSchur {n : ℕ} (P : Profile n) : MvPolynomial ℕ+ ℤ :=
  integralBetaDet P.xi P.zeta

@[simp]
theorem Profile.map_integralSchur {n : ℕ} (P : Profile n) :
    map (Int.castRingHom ℚ) P.integralSchur = P.schur :=
  map_integralBetaDet _ _

/-- Integral function of a connected cell diagram, using its unique profile. -/
def integralConnectedSchur (D : Diagram) (hD : IsConnectedSkew D) : MvPolynomial ℕ+ ℤ :=
  (diagramProfile D hD).2.integralSchur

@[simp]
theorem map_integralConnectedSchur (D : Diagram) (hD : IsConnectedSkew D) :
    map (Int.castRingHom ℚ) (integralConnectedSchur D hD) = connectedSchur D hD :=
  Profile.map_integralSchur _

/-- Integral product over the actual nonempty edge components. -/
def integralCellSchur (D : Diagram) (hs : IsSkew D) : MvPolynomial ℕ+ ℤ :=
  ∏ C ∈ (edgeComponents D).attach,
    integralConnectedSchur C.1 (isConnectedSkew_component hs C.2)

@[simp]
theorem map_integralCellSchur (D : Diagram) (hs : IsSkew D) :
    map (Int.castRingHom ℚ) (integralCellSchur D hs) = cellSchur D hs := by
  simp [integralCellSchur, cellSchur]

/-- No prime-characteristic specialization annihilates a skew Schur function. -/
theorem map_integralCellSchur_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    (D : Diagram) (hs : IsSkew D) :
    map (Int.castRingHom R) (integralCellSchur D hs) ≠ 0 := by
  simp only [integralCellSchur, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro C _
  let P := (diagramProfile C.1 (isConnectedSkew_component hs C.2)).2
  apply map_integralBetaDet_ne_zero P.xi_strictAnti P.zeta_strictAnti
  intro i
  have := P.xi_sub_zeta i
  have := P.r_pos i
  omega

/-- Every common integer divisor of the coefficients is a unit: skew Schur functions
are primitive, including the empty diagram. -/
theorem integralCellSchur_primitive (D : Diagram) (hs : IsSkew D) (a : ℤ)
    (ha : ∀ m, a ∣ (integralCellSchur D hs).coeff m) : IsUnit a := by
  by_contra hu
  have habs : a.natAbs ≠ 1 := by
    simpa only [Int.isUnit_iff_natAbs_eq] using hu
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd habs
  have : Fact p.Prime := ⟨hp⟩
  have hzero : map (Int.castRingHom (ZMod p)) (integralCellSchur D hs) = 0 := by
    ext m
    rw [coeff_map]
    change ((integralCellSchur D hs).coeff m : ZMod p) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
      ((Int.natCast_dvd.mpr hpa).trans (ha m))
  exact map_integralCellSchur_ne_zero D hs hzero

end

end SkewGluing
