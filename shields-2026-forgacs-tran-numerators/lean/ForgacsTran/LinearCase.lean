/-
# The linear case

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, §5 «Proof of the
fixed-numerator theorem», `prop:linear-case`: the excluded elementary case
`deg Q = r = 1`.  With `Q(t) = q₀ + q₁ t` (`q₀ > 0`, `q₁ < 0`) the properness
condition `deg_t N < 1` forces `N(t,z) = R(z)`, and the geometric expansion of
`R/(q₀ + (q₁+z)t)` gives the closed form
`P_m(z) = (-1)^m q₀^{-(m+1)} R(z) (z + q₁)^m`.

The single moving zero `-q₁ > 0` is positive, so every exceptional zero belongs
to the fixed factor `R`.  The exceptional-zero count is therefore constant in
`m`, bounded by `deg R`.

Worked over `ℂ`, so the count is the genuine complex one of `thm:main`.
Sorry-free.
-/
import ForgacsTran.ZeroCount
import ForgacsTran.Reduction

open Classical Polynomial

namespace ForgacsTran

/-- Paper §5 `sec:proof`, `prop:linear-case` — the linear-case coefficient
polynomial `P_m(z) = (-1)^m q₀^{-(m+1)} R(z) (z+q₁)^m`, as an element of `ℂ[X]`. -/
noncomputable def Plin (R : ℂ[X]) (q0 q1 : ℝ) (m : ℕ) : ℂ[X] :=
  C ((-1) ^ m / (q0 : ℂ) ^ (m + 1)) * R * (X + C (q1 : ℂ)) ^ m

/-- **Paper §5 `sec:proof`, `prop:linear-case` — the generating relation.**
`(q₀ + (q₁+z)t) ∑ P_m t^m = R` in coefficient
form: `q₀ P_{m+1} + (z+q₁) P_m = 0`.  This is exactly the denominator recurrence
that defines the sequence, verified for the closed form. -/
theorem Plin_recurrence (R : ℂ[X]) {q0 : ℝ} (hq0 : q0 ≠ 0) (q1 : ℝ) (m : ℕ) :
    C (q0 : ℂ) * Plin R q0 q1 (m + 1) + (X + C (q1 : ℂ)) * Plin R q0 q1 m = 0 := by
  have hq0c : (q0 : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hpow : (q0 : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ hq0c
  -- The scalar coefficients cancel.
  have hscalar : (q0 : ℂ) * ((-1) ^ (m + 1) / (q0 : ℂ) ^ (m + 1 + 1))
      + (-1) ^ m / (q0 : ℂ) ^ (m + 1) = 0 := by
    rw [pow_succ ((-1 : ℂ)) m, pow_succ (q0 : ℂ) (m + 1)]
    field_simp
    ring
  have hkey : C (q0 : ℂ) * C ((-1) ^ (m + 1) / (q0 : ℂ) ^ (m + 1 + 1))
      + C ((-1) ^ m / (q0 : ℂ) ^ (m + 1)) = 0 := by
    have hC0 : C ((q0 : ℂ) * ((-1) ^ (m + 1) / (q0 : ℂ) ^ (m + 1 + 1))
        + (-1) ^ m / (q0 : ℂ) ^ (m + 1)) = (0 : ℂ[X]) := by
      rw [hscalar]; simp
    simpa [map_mul, map_add] using hC0
  unfold Plin
  have expand : C (q0 : ℂ) * (C ((-1) ^ (m + 1) / (q0 : ℂ) ^ (m + 1 + 1)) * R
        * (X + C (q1 : ℂ)) ^ (m + 1))
      + (X + C (q1 : ℂ)) * (C ((-1) ^ m / (q0 : ℂ) ^ (m + 1)) * R
        * (X + C (q1 : ℂ)) ^ m)
      = (C (q0 : ℂ) * C ((-1) ^ (m + 1) / (q0 : ℂ) ^ (m + 1 + 1))
          + C ((-1) ^ m / (q0 : ℂ) ^ (m + 1)))
        * (R * (X + C (q1 : ℂ)) ^ (m + 1)) := by
    ring
  rw [expand, hkey, zero_mul]

/-- Paper §5 `sec:proof`, `prop:linear-case` (supporting) — `P_m ≠ 0` when
`R ≠ 0` and `q₀ ≠ 0`. -/
theorem Plin_ne_zero {R : ℂ[X]} (hR : R ≠ 0) {q0 : ℝ} (hq0 : q0 ≠ 0) (q1 : ℝ) (m : ℕ) :
    Plin R q0 q1 m ≠ 0 := by
  have hq0c : (q0 : ℂ) ≠ 0 := by exact_mod_cast hq0
  unfold Plin
  exact mul_ne_zero (mul_ne_zero
    (C_ne_zero.mpr (div_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hq0c))) hR)
    (pow_ne_zero _ (X_add_C_ne_zero _))

/-- Paper §5 `sec:proof`, `prop:linear-case` (supporting) — the root multiset of
`P_m` is that of `R` together with `m` copies of the moving zero `-q₁`. -/
theorem Plin_roots {R : ℂ[X]} (hR : R ≠ 0) {q0 : ℝ} (hq0 : q0 ≠ 0) (q1 : ℝ) (m : ℕ) :
    (Plin R q0 q1 m).roots = R.roots + m • ({-(q1 : ℂ)} : Multiset ℂ) := by
  have hq0c : (q0 : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hCc : C ((-1 : ℂ) ^ m / (q0 : ℂ) ^ (m + 1)) ≠ 0 :=
    C_ne_zero.mpr (div_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hq0c))
  have hApow : (X + C (q1 : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (X_add_C_ne_zero _)
  have hRA : R * (X + C (q1 : ℂ)) ^ m ≠ 0 := mul_ne_zero hR hApow
  have hAroots : (X + C (q1 : ℂ)).roots = {-(q1 : ℂ)} := by
    rw [show (X + C (q1 : ℂ)) = X - C (-(q1 : ℂ)) by rw [map_neg, sub_neg_eq_add]]
    exact roots_X_sub_C _
  show (C ((-1 : ℂ) ^ m / (q0 : ℂ) ^ (m + 1)) * R * (X + C (q1 : ℂ)) ^ m).roots = _
  rw [mul_assoc, roots_mul (mul_ne_zero hCc hRA), roots_C, zero_add,
    roots_mul hRA, roots_pow, hAroots]

/-- **`prop:linear-case`, zero structure.**  The exceptional zeros of `P_m` are
exactly those of the fixed numerator `R`, independent of `m`: the `m` copies of
the moving zero `-q₁ > 0` all lie on the positive ray. -/
theorem Plin_exceptional_eq {R : ℂ[X]} (hR : R ≠ 0) {q0 : ℝ} (hq0 : q0 ≠ 0)
    {q1 : ℝ} (hq1 : q1 < 0) (m : ℕ) :
    exceptionalRoots (Plin R q0 q1 m) posRay = exceptionalRoots R posRay := by
  have hmem : -(q1 : ℂ) ∈ posRay := by
    refine ⟨-q1, ?_, ?_⟩
    · exact neg_pos.mpr hq1
    · push_cast; ring
  have hnil : (m • ({-(q1 : ℂ)} : Multiset ℂ)).filter (fun x => x ∉ posRay) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro a ha
    have ha' : a ∈ ({-(q1 : ℂ)} : Multiset ℂ) := (Multiset.mem_nsmul.mp ha).2
    rw [Multiset.mem_singleton] at ha'
    rw [ha']
    exact not_not.mpr hmem
  unfold exceptionalRoots
  rw [Plin_roots hR hq0 q1 m, Multiset.filter_add, hnil, add_zero]

/-- **`prop:linear-case`, uniform bound.**  Every `P_m` has at most `deg R`
exceptional zeros — a bound independent of `m`. -/
theorem Plin_exceptional_card_le {R : ℂ[X]} (hR : R ≠ 0) {q0 : ℝ} (hq0 : q0 ≠ 0)
    {q1 : ℝ} (hq1 : q1 < 0) (m : ℕ) :
    (exceptionalRoots (Plin R q0 q1 m) posRay).card ≤ R.natDegree := by
  rw [Plin_exceptional_eq hR hq0 hq1 m]
  calc (exceptionalRoots R posRay).card
      ≤ R.roots.card := Multiset.card_le_card (Multiset.filter_le _ _)
    _ ≤ R.natDegree := R.card_roots'

/-! ### Identification with the coefficient sequence

`Plin` is a *defined* closed form.  What `prop:linear-case` asserts is that the
coefficient sequence of `R/(q₀+(q₁+z)t)` **equals** it, and that is a uniqueness
statement: the §2 denominator recurrence plus the initial datum pins the sequence.
`Reduction.initial_data_unique` supplies exactly that, with `d₀ = C q₀` a unit. -/

/-- The linear-case denominator sequence `d₀ = C q₀`, `d₁ = X + C q₁`, `dⱼ = 0`
for `j ≥ 2` — the `ftDenom` of §2 specialised to `deg Q = r = 1`. -/
noncomputable def dlin (q0 q1 : ℝ) : ℕ → ℂ[X] :=
  fun j => if j = 0 then C (q0 : ℂ) else if j = 1 then X + C (q1 : ℂ) else 0

/-- The two-term collapse: only `j = 0, 1` contribute to the convolution. -/
theorem denomConv_dlin_succ (P : ℕ → ℂ[X]) (q0 q1 : ℝ) (m : ℕ) :
    denomConv (dlin q0 q1) P (m + 1)
      = (X + C (q1 : ℂ)) * P m + C (q0 : ℂ) * P (m + 1) := by
  unfold denomConv
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have htail : ∀ i ∈ Finset.range m,
      dlin q0 q1 (i + 1 + 1) * P (m + 1 - (i + 1 + 1)) = 0 := by
    intro i _
    simp [dlin]
  rw [Finset.sum_eq_zero htail]
  simp [dlin]

/-- `denomConv` of the closed form: `R` at `m = 0`, zero afterwards. -/
theorem denomConv_dlin_Plin (R : ℂ[X]) {q0 : ℝ} (hq0 : q0 ≠ 0) (q1 : ℝ) (m : ℕ) :
    denomConv (dlin q0 q1) (Plin R q0 q1) m = if m = 0 then R else 0 := by
  cases m with
  | zero =>
      have hq0c : (q0 : ℂ) ≠ 0 := by exact_mod_cast hq0
      simp [denomConv, dlin, Plin, mul_comm]
      -- remaining goal: C q0 * (R * C q0⁻¹) = R
      rw [show C (q0 : ℂ) * (R * C ((q0 : ℂ))⁻¹)
            = (C (q0 : ℂ) * C ((q0 : ℂ))⁻¹) * R from by ring,
        ← C_mul, mul_inv_cancel₀ hq0c, map_one, one_mul]
  | succ n =>
      rw [denomConv_dlin_succ]
      have := Plin_recurrence R hq0 q1 n
      simp only [if_neg (Nat.succ_ne_zero n)]
      linear_combination (norm := ring_nf) this

/-- **`prop:linear-case`, identification.**  Any sequence satisfying the linear-case
denominator recurrence with numerator `R` *is* the closed form `Plin`.  Together
with `Plin_exceptional_card_le` this gives the surviving first conclusion of
`thm:main` for the excluded case `deg Q = r = 1`. -/
theorem Plin_unique (R : ℂ[X]) {q0 : ℝ} (hq0 : q0 ≠ 0) (q1 : ℝ) (P : ℕ → ℂ[X])
    (h : ∀ m, denomConv (dlin q0 q1) P m = if m = 0 then R else 0) :
    P = Plin R q0 q1 := by
  have hq0c : (q0 : ℂ) ≠ 0 := by exact_mod_cast hq0
  refine initial_data_unique (d := dlin q0 q1) ?_ ?_
  · have : dlin q0 q1 0 = C (q0 : ℂ) := by simp [dlin]
    rw [this]
    exact (Polynomial.isUnit_C).mpr (isUnit_iff_ne_zero.mpr hq0c)
  · intro m
    rw [h m, denomConv_dlin_Plin R hq0 q1 m]

end ForgacsTran
