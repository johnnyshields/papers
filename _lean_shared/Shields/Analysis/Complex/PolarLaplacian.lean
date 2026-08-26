/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# The Laplacian in polar coordinates

Green's identity on an annulus is not available from Mathlib's divergence theorem, which is
stated on a box.  What that identity rests on is the polar form of the Laplacian, and this module
proves it.

For `u` of class `C²` and a point `c + re^{iθ}` with `r > 0`,
\[
  \partial_r^2 u + \tfrac1r\partial_r u + \tfrac1{r^2}\partial_\theta^2 u = \Delta u .
\]

Two facts do the work, and neither is special to the plane:

* **`{e^{iθ}, ie^{iθ}}` is an orthonormal basis**, being the standard one rotated, and Mathlib
  computes the Laplacian from *any* orthonormal basis.  So `Δu = D²u[e,e] + D²u[ie,ie]` at every
  angle, not just at the axes.
* **The first-order terms cancel.**  Differentiating the angular direction `ire^{iθ}` in `θ`
  returns `-re^{iθ}`, so `∂_θ²u = r²D²u[ie,ie] - rD u[e]`; the `-r^{-1}Du[e]` this contributes is
  exactly what the `r^{-1}∂_r u` term supplies.  That cancellation is the whole reason the polar
  Laplacian has the shape it does.

The identity is the classical one and is stated for an arbitrary `C²` function on `ℂ`.

## Main results

* `circleDir`, `hasDerivAt_circleDir` — the unit vector at angle `θ` and its derivative `ie^{iθ}`.
* `laplacian_apply_rotated` — **the Laplacian from the rotated basis**, at every angle.
* `hasDerivAt_radial`, `hasDerivAt_radial_fderiv` — the radial first and second derivatives.
* `hasDerivAt_angular`, `hasDerivAt_angular_fderiv` — the angular ones, the second carrying the
  first-order term that cancels.
* `polar_laplacian` — **the identity**.

## Tags

laplacian, polar coordinates, orthonormal basis, second derivative
-/

open InnerProductSpace Complex Laplacian

namespace Shields

/-! ### The unit vector at an angle -/

/-- The unit vector `e^{iθ}`. -/
noncomputable def circleDir (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem circleDir_ne_zero (θ : ℝ) : circleDir θ ≠ 0 := Complex.exp_ne_zero _

@[simp] theorem norm_circleDir (θ : ℝ) : ‖circleDir θ‖ = 1 := by
  rw [circleDir, Complex.norm_exp]
  simp

@[simp] theorem coe_circleExp (θ : ℝ) : ((Circle.exp θ : Circle) : ℂ) = circleDir θ :=
  Circle.coe_exp θ

/-- `d/dθ e^{iθ} = ie^{iθ}`, which is the rotation by a right angle that makes the angular
direction orthogonal to the radial one. -/
theorem hasDerivAt_circleDir (θ : ℝ) : HasDerivAt circleDir (circleDir θ * Complex.I) θ := by
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 θ := by
    simpa using (hasDerivAt_id θ).ofReal_comp
  have h : HasDerivAt (fun t : ℝ => ((t : ℂ) * Complex.I)) Complex.I θ := by
    simpa using HasDerivAt.mul_const h0 Complex.I
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) θ := HasDerivAt.cexp h
  exact h2

/-! ### The Laplacian from the rotated basis -/

/-- **The Laplacian is computed by the basis at any angle.**  `{e^{iθ}, ie^{iθ}}` is the standard
orthonormal basis rotated, and rotations are linear isometries, so Mathlib's any-basis formula
applies verbatim. -/
theorem laplacian_apply_rotated (u : ℂ → ℝ) (θ : ℝ) (p : ℂ) :
    Δ u p = fderiv ℝ (fderiv ℝ u) p (circleDir θ) (circleDir θ)
      + fderiv ℝ (fderiv ℝ u) p (circleDir θ * Complex.I) (circleDir θ * Complex.I) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (Complex.orthonormalBasisOneI.map (rotation (Circle.exp θ)))]
  simp [Fin.sum_univ_two, iteratedFDeriv_two_apply, rotation_apply, circleDir]

/-! ### The radial derivatives -/

theorem hasDerivAt_ray (c e : ℂ) (r : ℝ) :
    HasDerivAt (fun s : ℝ => c + (s : ℂ) * e) e r := by
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 r := by
    simpa using (hasDerivAt_id r).ofReal_comp
  simpa using HasDerivAt.const_add c (HasDerivAt.mul_const h0 e)

theorem hasDerivAt_radial {u : ℂ → ℝ} (hu : Differentiable ℝ u) (c e : ℂ) (r : ℝ) :
    HasDerivAt (fun s : ℝ => u (c + (s : ℂ) * e)) (fderiv ℝ u (c + (r : ℂ) * e) e) r :=
  (hu (c + (r : ℂ) * e)).hasFDerivAt.comp_hasDerivAt r (hasDerivAt_ray c e r)

/-- The second radial derivative is the second differential along the ray. -/
theorem hasDerivAt_radial_fderiv {u : ℂ → ℝ} (hu : Differentiable ℝ (fderiv ℝ u)) (c e : ℂ)
    (r : ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ u (c + (s : ℂ) * e) e)
      (fderiv ℝ (fderiv ℝ u) (c + (r : ℂ) * e) e e) r := by
  have hbase : HasDerivAt (fun s : ℝ => fderiv ℝ u (c + (s : ℂ) * e))
      (fderiv ℝ (fderiv ℝ u) (c + (r : ℂ) * e) e) r :=
    (hu _).hasFDerivAt.comp_hasDerivAt r (hasDerivAt_ray c e r)
  simpa using HasDerivAt.clm_apply hbase (hasDerivAt_const r e)

/-! ### The angular derivatives -/

theorem hasDerivAt_arc (c : ℂ) (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => c + (r : ℂ) * circleDir t) ((r : ℂ) * (circleDir θ * Complex.I)) θ :=
  HasDerivAt.const_add c (HasDerivAt.const_mul (r : ℂ) (hasDerivAt_circleDir θ))

theorem hasDerivAt_angular {u : ℂ → ℝ} (hu : Differentiable ℝ u) (c : ℂ) (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => u (c + (r : ℂ) * circleDir t))
      (fderiv ℝ u (c + (r : ℂ) * circleDir θ) ((r : ℂ) * (circleDir θ * Complex.I))) θ :=
  (hu _).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_arc c r θ)

/-- **The second angular derivative carries a first-order term.**  The direction itself turns with
`θ`, and its derivative `-re^{iθ}` is radial — that term is what the `r^{-1}∂_r` of the polar
Laplacian cancels. -/
theorem hasDerivAt_angular_fderiv {u : ℂ → ℝ}
    (hu2 : Differentiable ℝ (fderiv ℝ u)) (c : ℂ) (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => fderiv ℝ u (c + (r : ℂ) * circleDir t)
        ((r : ℂ) * (circleDir t * Complex.I)))
      (fderiv ℝ (fderiv ℝ u) (c + (r : ℂ) * circleDir θ) ((r : ℂ) * (circleDir θ * Complex.I))
          ((r : ℂ) * (circleDir θ * Complex.I))
        + fderiv ℝ u (c + (r : ℂ) * circleDir θ) (-((r : ℂ) * circleDir θ))) θ := by
  have hbase : HasDerivAt (fun t : ℝ => fderiv ℝ u (c + (r : ℂ) * circleDir t))
      (fderiv ℝ (fderiv ℝ u) (c + (r : ℂ) * circleDir θ)
        ((r : ℂ) * (circleDir θ * Complex.I))) θ :=
    (hu2 _).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_arc c r θ)
  have hdir : HasDerivAt (fun t : ℝ => (r : ℂ) * (circleDir t * Complex.I))
      (-((r : ℂ) * circleDir θ)) θ := by
    have h := HasDerivAt.const_mul (r : ℂ)
      (HasDerivAt.mul_const (hasDerivAt_circleDir θ) Complex.I)
    have hI : (r : ℂ) * (circleDir θ * Complex.I * Complex.I) = -((r : ℂ) * circleDir θ) := by
      rw [mul_assoc, Complex.I_mul_I]
      ring
    rwa [hI] at h
  exact HasDerivAt.clm_apply hbase hdir

/-! ### The identity -/

/-- **The Laplacian in polar coordinates.**  For `r > 0`,
`∂_r²u + r^{-1}∂_r u + r^{-2}∂_θ²u = Δu` at `c + re^{iθ}`.

The radial second derivative supplies `D²u[e,e]`, the angular one supplies `r²D²u[ie,ie]` together
with a stray `-rDu[e]`, and `r^{-1}∂_ru` is exactly `r^{-1}Du[e]`.  The strays cancel and the two
second differentials add to the Laplacian, `{e, ie}` being orthonormal. -/
theorem polar_laplacian {u : ℂ → ℝ} (hu : Differentiable ℝ u)
    (hu2 : Differentiable ℝ (fderiv ℝ u)) (c : ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    deriv (deriv fun s : ℝ => u (c + (s : ℂ) * circleDir θ)) r
        + r⁻¹ * deriv (fun s : ℝ => u (c + (s : ℂ) * circleDir θ)) r
        + (r ^ 2)⁻¹ * deriv (deriv fun t : ℝ => u (c + (r : ℂ) * circleDir t)) θ
      = Δ u (c + (r : ℂ) * circleDir θ) := by
  set e : ℂ := circleDir θ with he
  set P : ℂ := c + (r : ℂ) * e with hP
  -- The radial derivative, as a function, and its own derivative.
  have hrad : (deriv fun s : ℝ => u (c + (s : ℂ) * e))
      = fun s : ℝ => fderiv ℝ u (c + (s : ℂ) * e) e :=
    funext fun s => (hasDerivAt_radial hu c e s).deriv
  have hrad1 : deriv (fun s : ℝ => u (c + (s : ℂ) * e)) r = fderiv ℝ u P e := by
    rw [hrad]
  have hrad2 : deriv (deriv fun s : ℝ => u (c + (s : ℂ) * e)) r
      = fderiv ℝ (fderiv ℝ u) P e e := by
    rw [hrad]
    exact (hasDerivAt_radial_fderiv hu2 c e r).deriv
  -- The angular derivative, as a function, and its own derivative.
  have hang : (deriv fun t : ℝ => u (c + (r : ℂ) * circleDir t))
      = fun t : ℝ => fderiv ℝ u (c + (r : ℂ) * circleDir t)
          ((r : ℂ) * (circleDir t * Complex.I)) :=
    funext fun t => (hasDerivAt_angular hu c r t).deriv
  have hang2 : deriv (deriv fun t : ℝ => u (c + (r : ℂ) * circleDir t)) θ
      = fderiv ℝ (fderiv ℝ u) P ((r : ℂ) * (e * Complex.I)) ((r : ℂ) * (e * Complex.I))
        + fderiv ℝ u P (-((r : ℂ) * e)) := by
    rw [hang]
    exact (hasDerivAt_angular_fderiv hu2 c r θ).deriv
  -- Pull the radius out of both slots of the second differential, and out of the first.
  have hsmul : ∀ z : ℂ, (r : ℂ) * z = (r : ℝ) • z := fun z => Complex.real_smul.symm
  have hbil : fderiv ℝ (fderiv ℝ u) P ((r : ℂ) * (e * Complex.I)) ((r : ℂ) * (e * Complex.I))
      = r ^ 2 * fderiv ℝ (fderiv ℝ u) P (e * Complex.I) (e * Complex.I) := by
    simp only [hsmul, map_smul, smul_apply, smul_eq_mul]
    ring
  have hlin : fderiv ℝ u P (-((r : ℂ) * e)) = -(r * fderiv ℝ u P e) := by
    simp only [hsmul, ← smul_neg, map_smul, smul_eq_mul, map_neg]
    ring
  rw [hrad1, hrad2, hang2, hbil, hlin, laplacian_apply_rotated u θ P, ← he]
  field

end Shields
