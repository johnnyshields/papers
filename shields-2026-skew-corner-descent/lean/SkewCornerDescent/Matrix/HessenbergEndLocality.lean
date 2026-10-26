/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergBoundaryLog

/-!
# Finite prefix and suffix locality of the normalized endpoint logarithms

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).

The family `A : ℕ → ℕ → PowerSeries F` is upper-Hessenberg (`hA`), has the constant
first subdiagonal `C a * X` (`hsub`), and has nonzero diagonal residues (`hdiag`). Diagonal
residues are arbitrary nonzero series; no row normalization is performed.

Every interval block `intervalDet A s m` is the determinant of the states `s, …, s+m-1`.
Its constant term is nonzero, derived from `mapped_hessenberg_det` and the nonzero
diagonal residues. Every cap is built from the normalized logarithm
`normLog A s m := logOf (C (constantCoeff (intervalDet A s m))⁻¹ * intervalDet A s m)`.

The four-minor identity `hessenberg_boundary_log_coeff` supplies the telescoping step.
Left and right caps are then stable under moving the interval one state inward, and the
right cap is iterated to a finite window. Cap entries outside the window and their normal
jets, including any chosen higher generator, are arbitrary.

Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix

variable {F : Type*} [Field F] [Algebra ℚ F]

/-- Determinant of the contiguous block on states `s, …, s+m-1`. -/
def intervalDet (A : ℕ → ℕ → PowerSeries F) (s m : ℕ) : PowerSeries F :=
  Matrix.det (Matrix.of fun x y : Fin m => A (s + (x : ℕ)) (s + (y : ℕ)))

/-- The normalized logarithm of the interval block on `s, …, s+m-1`. -/
def normLog (A : ℕ → ℕ → PowerSeries F) (s m : ℕ) : PowerSeries F :=
  PowerSeries.logOf
    (PowerSeries.C (PowerSeries.constantCoeff (intervalDet A s m))⁻¹ * intervalDet A s m)

/-- The left cap at length `m`: normalized log of `[0, m]` minus that of `[1, m]`. -/
def leftCap (A : ℕ → ℕ → PowerSeries F) (m : ℕ) : PowerSeries F :=
  normLog A 0 (m + 1) - normLog A 1 m

/-- The right cap at start `s` and length `m`: normalized log of length `m+1` minus length `m`. -/
def rightCap (A : ℕ → ℕ → PowerSeries F) (s m : ℕ) : PowerSeries F :=
  normLog A s (m + 1) - normLog A s m

omit [Algebra ℚ F] in
/-- The determinant of a block, written as the named interval. -/
theorem intervalDet_def (A : ℕ → ℕ → PowerSeries F) (s m : ℕ) :
    Matrix.det (Matrix.of fun x y : Fin m => A (s + (x : ℕ)) (s + (y : ℕ))) =
      intervalDet A s m :=
  rfl

omit [Algebra ℚ F] in
/-- An interval block of an upper-Hessenberg family is upper-Hessenberg. -/
theorem intervalDet_hessenberg (A : ℕ → ℕ → PowerSeries F)
    (hA : ∀ i j : ℕ, j + 1 < i → A i j = 0) (s m : ℕ) :
    IsUpperHessenberg (Matrix.of fun x y : Fin m => A (s + (x : ℕ)) (s + (y : ℕ))) := by
  intro i j hij
  change A _ _ = 0
  exact hA _ _ (by omega)

omit [Algebra ℚ F] in
/-- The constant first subdiagonal survives restriction to a block of length `m+2`. -/
theorem intervalDet_subdiag (A : ℕ → ℕ → PowerSeries F) (a : F)
    (hsub : ∀ i : ℕ, A (i + 1) i = PowerSeries.C a * PowerSeries.X) (s m : ℕ) :
    ∀ i : Fin (m + 1),
      (Matrix.of fun x y : Fin (m + 2) => A (s + (x : ℕ)) (s + (y : ℕ))) i.succ
        i.castSucc = PowerSeries.C a * PowerSeries.X := by
  intro i
  simp only [Matrix.of_apply, Fin.val_succ, Fin.val_castSucc]
  rw [show s + ((i : ℕ) + 1) = s + (i : ℕ) + 1 by omega]
  exact hsub _

omit [Algebra ℚ F] in
/-- Deleting the first state of a block of length `m+2` gives the shifted block of length `m+1`. -/
theorem intervalDet_succ_eq (A : ℕ → ℕ → PowerSeries F) (s m : ℕ) :
    ((Matrix.of fun x y : Fin (m + 2) => A (s + (x : ℕ)) (s + (y : ℕ))).submatrix
        Fin.succ Fin.succ).det = intervalDet A (s + 1) (m + 1) := by
  unfold intervalDet
  congr 1
  ext x y : 1
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.val_succ]
  rw [show s + ((x : ℕ) + 1) = s + 1 + (x : ℕ) by omega,
    show s + ((y : ℕ) + 1) = s + 1 + (y : ℕ) by omega]

omit [Algebra ℚ F] in
/-- Deleting both end states of a block of length `m+2` gives the shifted block of length `m`. -/
theorem intervalDet_mid_eq (A : ℕ → ℕ → PowerSeries F) (s m : ℕ) :
    ((Matrix.of fun x y : Fin (m + 2) => A (s + (x : ℕ)) (s + (y : ℕ))).submatrix
        (fun i : Fin m => i.castSucc.succ) (fun j : Fin m => j.castSucc.succ)).det =
      intervalDet A (s + 1) m := by
  unfold intervalDet
  congr 1
  ext x y : 1
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.val_succ, Fin.val_castSucc]
  rw [show s + ((x : ℕ) + 1) = s + 1 + (x : ℕ) by omega,
    show s + ((y : ℕ) + 1) = s + 1 + (y : ℕ) by omega]

omit [Algebra ℚ F] in
/-- Deleting the last state of a block of length `m+2` gives the initial block of length `m+1`. -/
theorem intervalDet_castSucc_eq (A : ℕ → ℕ → PowerSeries F) (s m : ℕ) :
    ((Matrix.of fun x y : Fin (m + 2) => A (s + (x : ℕ)) (s + (y : ℕ))).submatrix
        Fin.castSucc Fin.castSucc).det = intervalDet A s (m + 1) := by
  rfl

omit [Algebra ℚ F] in
/-- Every interval block has nonzero constant term. The determinant of an upper-Hessenberg
block maps to the product of its diagonal residues under the constant-term map, because the
constant subdiagonal `C a * X` has zero constant term. -/
theorem intervalDet_regular (A : ℕ → ℕ → PowerSeries F) (a : F)
    (hA : ∀ i j : ℕ, j + 1 < i → A i j = 0)
    (hsub : ∀ i : ℕ, A (i + 1) i = PowerSeries.C a * PowerSeries.X)
    (hdiag : ∀ i : ℕ, PowerSeries.constantCoeff (A i i) ≠ 0) (s m : ℕ) :
    PowerSeries.constantCoeff (intervalDet A s m) ≠ 0 := by
  cases m with
  | zero => simp [intervalDet]
  | succ k =>
    have hφ : ∀ i : Fin k,
        PowerSeries.constantCoeff
          ((Matrix.of fun x y : Fin (k + 1) => A (s + (x : ℕ)) (s + (y : ℕ))) i.succ
            i.castSucc) = 0 := by
      intro i
      simp only [Matrix.of_apply, Fin.val_succ, Fin.val_castSucc]
      rw [show s + ((i : ℕ) + 1) = s + (i : ℕ) + 1 by omega, hsub]
      simp
    unfold intervalDet
    rw [mapped_hessenberg_det PowerSeries.constantCoeff _
      (intervalDet_hessenberg A hA s (k + 1)) hφ]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by
      simpa only [Matrix.of_apply] using hdiag (s + (i : ℕ))

/-- Four-minor normalized-log identity on the block `[s, s+m+1]`, through order `k ≤ m`. -/
theorem intervalDet_four_log (A : ℕ → ℕ → PowerSeries F) (a : F)
    (hA : ∀ i j : ℕ, j + 1 < i → A i j = 0)
    (hsub : ∀ i : ℕ, A (i + 1) i = PowerSeries.C a * PowerSeries.X)
    (hdiag : ∀ i : ℕ, PowerSeries.constantCoeff (A i i) ≠ 0) (s m k : ℕ) (hk : k ≤ m) :
    PowerSeries.coeff k (normLog A s (m + 2)) + PowerSeries.coeff k (normLog A (s + 1) m) =
      PowerSeries.coeff k (normLog A (s + 1) (m + 1)) +
        PowerSeries.coeff k (normLog A s (m + 1)) := by
  have hM := intervalDet_hessenberg A hA s (m + 2)
  have hsubM := intervalDet_subdiag A a hsub s m
  have hfull : PowerSeries.constantCoeff (intervalDet A s (m + 2)) ≠ 0 :=
    intervalDet_regular A a hA hsub hdiag s (m + 2)
  have hmid : PowerSeries.constantCoeff
      ((Matrix.of fun x y : Fin (m + 2) => A (s + (x : ℕ)) (s + (y : ℕ))).submatrix
        (fun i : Fin m => i.castSucc.succ) (fun j : Fin m => j.castSucc.succ)).det ≠ 0 := by
    rw [intervalDet_mid_eq]
    exact intervalDet_regular A a hA hsub hdiag (s + 1) m
  have hright : PowerSeries.constantCoeff
      ((Matrix.of fun x y : Fin (m + 2) => A (s + (x : ℕ)) (s + (y : ℕ))).submatrix
        Fin.succ Fin.succ).det ≠ 0 := by
    rw [intervalDet_succ_eq]
    exact intervalDet_regular A a hA hsub hdiag (s + 1) (m + 1)
  have hleft : PowerSeries.constantCoeff
      ((Matrix.of fun x y : Fin (m + 2) => A (s + (x : ℕ)) (s + (y : ℕ))).submatrix
        Fin.castSucc Fin.castSucc).det ≠ 0 := by
    rw [intervalDet_castSucc_eq]
    exact intervalDet_regular A a hA hsub hdiag s (m + 1)
  have key := hessenberg_boundary_log_coeff
    (Matrix.of fun x y : Fin (m + 2) => A (s + (x : ℕ)) (s + (y : ℕ))) hM a hsubM
    hfull hmid hright hleft k (by omega)
  simp only [intervalDet_def, intervalDet_mid_eq, intervalDet_succ_eq,
    intervalDet_castSucc_eq] at key
  exact key

/-- Left cap is stable one length step inward when `k ≤ m`. -/
theorem leftCap_coeff_succ (A : ℕ → ℕ → PowerSeries F) (a : F)
    (hA : ∀ i j : ℕ, j + 1 < i → A i j = 0)
    (hsub : ∀ i : ℕ, A (i + 1) i = PowerSeries.C a * PowerSeries.X)
    (hdiag : ∀ i : ℕ, PowerSeries.constantCoeff (A i i) ≠ 0) (k m : ℕ) (hk : k ≤ m) :
    PowerSeries.coeff k (leftCap A (m + 1)) = PowerSeries.coeff k (leftCap A m) := by
  have key := intervalDet_four_log A a hA hsub hdiag 0 m k hk
  simp only [zero_add] at key
  change PowerSeries.coeff k (normLog A 0 (m + 2) - normLog A 1 (m + 1)) =
    PowerSeries.coeff k (normLog A 0 (m + 1) - normLog A 1 m)
  rw [map_sub, map_sub]
  linear_combination key

/-- Right cap is stable under moving its start one state right, through order `k ≤ m`. -/
theorem rightCap_coeff_step (A : ℕ → ℕ → PowerSeries F) (a : F)
    (hA : ∀ i j : ℕ, j + 1 < i → A i j = 0)
    (hsub : ∀ i : ℕ, A (i + 1) i = PowerSeries.C a * PowerSeries.X)
    (hdiag : ∀ i : ℕ, PowerSeries.constantCoeff (A i i) ≠ 0) (s m k : ℕ) (hk : k ≤ m) :
    PowerSeries.coeff k (rightCap A s (m + 1)) =
      PowerSeries.coeff k (rightCap A (s + 1) m) := by
  have key := intervalDet_four_log A a hA hsub hdiag s m k hk
  change PowerSeries.coeff k (normLog A s (m + 2) - normLog A s (m + 1)) =
    PowerSeries.coeff k (normLog A (s + 1) (m + 1) - normLog A (s + 1) m)
  rw [map_sub, map_sub]
  linear_combination key

/-- Through order `k`, the left cap is constant for every length at least `k`. -/
theorem leftCap_coeff_eq_of_le (A : ℕ → ℕ → PowerSeries F) (a : F)
    (hA : ∀ i j : ℕ, j + 1 < i → A i j = 0)
    (hsub : ∀ i : ℕ, A (i + 1) i = PowerSeries.C a * PowerSeries.X)
    (hdiag : ∀ i : ℕ, PowerSeries.constantCoeff (A i i) ≠ 0)
    (k m m' : ℕ) (hm : k ≤ m) (hmm : m ≤ m') :
    PowerSeries.coeff k (leftCap A m') = PowerSeries.coeff k (leftCap A m) := by
  induction m', hmm using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [leftCap_coeff_succ A a hA hsub hdiag k n (hm.trans hn), ih]

/-- Iterated right-cap shift: through order `k`, the right cap at start `s` and length
`k + d` equals the right cap at start `s + d` and length `k`. -/
theorem rightCap_shift (A : ℕ → ℕ → PowerSeries F) (a : F)
    (hA : ∀ i j : ℕ, j + 1 < i → A i j = 0)
    (hsub : ∀ i : ℕ, A (i + 1) i = PowerSeries.C a * PowerSeries.X)
    (hdiag : ∀ i : ℕ, PowerSeries.constantCoeff (A i i) ≠ 0) (k : ℕ) :
    ∀ d s : ℕ,
      PowerSeries.coeff k (rightCap A s (k + d)) =
        PowerSeries.coeff k (rightCap A (s + d) k) := by
  intro d
  induction d with
  | zero => intro s; simp
  | succ d ih =>
    intro s
    rw [show k + (d + 1) = (k + d) + 1 by omega,
      rightCap_coeff_step A a hA hsub hdiag s (k + d) k (by omega), ih (s + 1),
      show s + (d + 1) = s + 1 + d by omega]

omit [Algebra ℚ F] in
/-- Interval blocks depend only on the entries in their window `[s, s+m)`. -/
theorem intervalDet_congr (A B : ℕ → ℕ → PowerSeries F) (s m : ℕ)
    (h : ∀ i j : ℕ, s ≤ i → s ≤ j → i < s + m → j < s + m → A i j = B i j) :
    intervalDet A s m = intervalDet B s m := by
  unfold intervalDet
  congr 1
  ext x y : 1
  simp only [Matrix.of_apply]
  exact h (s + x.val) (s + y.val) (by omega) (by omega)
    (by have := x.isLt; omega) (by have := y.isLt; omega)

/-- The left cap at length `m` depends only on the entries with both indices at most `m`. -/
theorem leftCap_congr (A B : ℕ → ℕ → PowerSeries F) (m : ℕ)
    (h : ∀ i j : ℕ, i ≤ m → j ≤ m → A i j = B i j) :
    leftCap A m = leftCap B m := by
  unfold leftCap normLog
  rw [intervalDet_congr A B 0 (m + 1) (fun i j _ _ r t => h i j (by omega) (by omega)),
    intervalDet_congr A B 1 m (fun i j _ _ r t => h i j (by omega) (by omega))]

/-- The right cap at start `s` and length `m` depends only on the entries in `[s, s+m+1)`. -/
theorem rightCap_congr (A B : ℕ → ℕ → PowerSeries F) (s m : ℕ)
    (h : ∀ i j : ℕ, s ≤ i → s ≤ j → i < s + m + 1 → j < s + m + 1 → A i j = B i j) :
    rightCap A s m = rightCap B s m := by
  unfold rightCap normLog
  rw [intervalDet_congr A B s (m + 1) (fun i j p q r t => h i j p q (by omega) (by omega)),
    intervalDet_congr A B s m (fun i j p q r t => h i j p q (by omega) (by omega))]

/-- **Left-cap prefix locality.** Through order `k`, the left cap at any length `m' ≥ k`
equals the left cap at length `k` of any family `B` agreeing with `A` on indices at most `k`.
Entries outside that prefix, including cap entries and the normal jets inside them, play no role. -/
theorem leftCap_prefix_locality (A B : ℕ → ℕ → PowerSeries F) (a : F)
    (hA : ∀ i j : ℕ, j + 1 < i → A i j = 0)
    (hsub : ∀ i : ℕ, A (i + 1) i = PowerSeries.C a * PowerSeries.X)
    (hdiag : ∀ i : ℕ, PowerSeries.constantCoeff (A i i) ≠ 0)
    (k m' : ℕ) (hm : k ≤ m') (hB : ∀ i j : ℕ, i ≤ k → j ≤ k → A i j = B i j) :
    PowerSeries.coeff k (leftCap A m') = PowerSeries.coeff k (leftCap B k) := by
  rw [leftCap_coeff_eq_of_le A a hA hsub hdiag k k m' le_rfl hm, leftCap_congr A B k hB]

/-- **Right-cap window locality.** Through order `k`, the right cap at start `s` and length
`k + d` equals the right cap at start `s + d` and length `k` of any family `B` agreeing with
`A` on the window `[s+d, s+d+k]`. Entries outside that window, and the normal jets inside them,
play no role. -/
theorem rightCap_locality (A B : ℕ → ℕ → PowerSeries F) (a : F)
    (hA : ∀ i j : ℕ, j + 1 < i → A i j = 0)
    (hsub : ∀ i : ℕ, A (i + 1) i = PowerSeries.C a * PowerSeries.X)
    (hdiag : ∀ i : ℕ, PowerSeries.constantCoeff (A i i) ≠ 0) (k d s : ℕ)
    (h : ∀ i j : ℕ, s + d ≤ i → s + d ≤ j → i < s + d + k + 1 → j < s + d + k + 1 →
      A i j = B i j) :
    PowerSeries.coeff k (rightCap A s (k + d)) =
      PowerSeries.coeff k (rightCap B (s + d) k) := by
  rw [rightCap_shift A a hA hsub hdiag k d s, rightCap_congr A B (s + d) k h]

/-- Matching complete interval entries at different source offsets identifies the
whole normalized logarithm, not only a truncated or constant-diagonal version. -/
theorem normLog_offsets_congr (A B : ℕ → ℕ → PowerSeries F) (s t m : ℕ)
    (h : ∀ i j : ℕ, i < m → j < m → A (s + i) (s + j) = B (t + i) (t + j)) :
    normLog A s m = normLog B t m := by
  have he : intervalDet A s m = intervalDet B t m := by
    unfold intervalDet
    congr 1
    ext i j : 1
    exact h i.val j.val i.isLt j.isLt
  unfold normLog
  rw [he]

/-- Complete right-cap logarithms agree under literal matching of their finite
windows, even when those windows occupy different original source offsets. -/
theorem rightCap_offsets_congr (A B : ℕ → ℕ → PowerSeries F) (s t m : ℕ)
    (h : ∀ i j : ℕ, i ≤ m → j ≤ m → A (s + i) (s + j) = B (t + i) (t + j)) :
    rightCap A s m = rightCap B t m := by
  unfold rightCap
  rw [normLog_offsets_congr A B s t (m + 1) (fun i j hi hj => h i j (by omega) (by omega)),
    normLog_offsets_congr A B s t m (fun i j hi hj => h i j (by omega) (by omega))]

/-- Below the full selected cost, the complete logarithm splits into its actual
internal logarithm and both full endpoint logarithms. No boundary jet is discarded. -/
theorem normLog_internal_caps (A : ℕ → ℕ → PowerSeries F) (a : F)
    (hA : ∀ i j : ℕ, j + 1 < i → A i j = 0)
    (hsub : ∀ i : ℕ, A (i + 1) i = PowerSeries.C a * PowerSeries.X)
    (hdiag : ∀ i : ℕ, PowerSeries.constantCoeff (A i i) ≠ 0)
    (B k : ℕ) (hk : k < B) :
    PowerSeries.coeff k (normLog A 0 (B + 1)) =
      PowerSeries.coeff k (normLog A 1 (B - 1)) +
        PowerSeries.coeff k (leftCap A B) + PowerSeries.coeff k (rightCap A 0 B) := by
  have h := intervalDet_four_log A a hA hsub hdiag 0 (B - 1) k (by omega)
  have h1 : B - 1 + 1 = B := by omega
  have h2 : B - 1 + 2 = B + 1 := by omega
  simp only [zero_add, h1, h2] at h
  simp only [leftCap, rightCap, map_sub]
  linear_combination -h

end SkewCornerDescent.Matrix
