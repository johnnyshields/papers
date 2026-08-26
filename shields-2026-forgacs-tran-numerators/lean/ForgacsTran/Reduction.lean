/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# Numerator as initial data

Writing `D(t,z) = ∑_j d_j(z) t^j` with `d_0 = Q(0) ≠ 0` a unit, the coefficients
`P_m` of `N/D` satisfy the lower-triangular convolution system
`∑_{j=0}^m d_j P_{m-j} = N_m`.  Because the diagonal `d_0` is a unit, the
sequence `(P_m)` is uniquely determined by the right-hand side, and conversely
every prescribed right-hand side is realized — the generating series
`D = ∑_j d_j t^j` is invertible in `A⟦t⟧`.  `initialDataEquivFin` packages the
two halves as the paper's bijection from proper numerators `(N_0,…,N_{d-1})`
onto initial data `(P_0,…,P_{d-1})`; `initialDataEquiv` is its sequence form.

Stated over an arbitrary commutative ring (instantiated at `R[z]`, where the
units are the nonzero real constants, so `d_0 = Q(0)` qualifies).  Sorry-free;
strong induction plus cancellation by a unit for uniqueness, inversion of a
power series with unit constant term for existence.

`eventual_natDegree_le` adds the `lem:eventual-degree` upper bound
`deg_z F_M ≤ ⌊M/r⌋` for any sequence satisfying the concrete denominator
recurrence with `d_i = C(Q.coeff i) + [i=r]·X`, by the same strong induction on
the peeled recurrence.  It is the degree half of the `subsec:proof` bulk count.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Canonical Laurent
reduction and eventual degree» (`sec:reduction`, `prop:initial-data`): the numerator of a
proper rational generating function carries the same information as the initial
data of the denominator recurrence.

## Tags

initial conditions, numerator, Laurent reduction
-/

open scoped BigOperators

namespace ForgacsTran

variable {A : Type*} [CommRing A]

/-- The denominator convolution `∑_{j=0}^m d_j P_{m-j}` of `prop:initial-data`. -/
def denomConv (d P : ℕ → A) (m : ℕ) : A := ∑ j ∈ Finset.range (m + 1), d j * P (m - j)

/-- Paper `sec:reduction` — supporting step for `prop:initial-data`.  Peeling
the `j = 0` term isolates the diagonal contribution `d_0 · P_m`. -/
theorem denomConv_eq (d P : ℕ → A) (m : ℕ) :
    denomConv d P m
      = (∑ j ∈ Finset.range m, d (j + 1) * P (m - (j + 1))) + d 0 * P m := by
  unfold denomConv
  rw [Finset.sum_range_succ']
  simp

/-- **`prop:initial-data` (uniqueness, truncated).**  If the diagonal `d_0` is a
unit, the first `n` equations of the convolution system already determine the
first `n` coefficients: the lower-triangular solve of `prop:initial-data` run for
finitely many steps. -/
theorem initial_data_unique_lt {d : ℕ → A} (hd : IsUnit (d 0)) {P P' : ℕ → A} {n : ℕ}
    (h : ∀ m, m < n → denomConv d P m = denomConv d P' m) : ∀ m, m < n → P m = P' m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hmn
    have hm := h m hmn
    rw [denomConv_eq, denomConv_eq] at hm
    -- the tail sums agree by the induction hypothesis
    have htail : (∑ j ∈ Finset.range m, d (j + 1) * P (m - (j + 1)))
        = ∑ j ∈ Finset.range m, d (j + 1) * P' (m - (j + 1)) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjm : j < m := Finset.mem_range.mp hj
      rw [ih (m - (j + 1)) (by omega) (by omega)]
    rw [htail] at hm
    exact (hd.mul_right_inj).mp (add_left_cancel hm)

/-- **`prop:initial-data` (uniqueness).**  If the diagonal `d_0` is a unit, the
convolution system `∑_{j=0}^m d_j P_{m-j} = N_m` has at most one solution `P`.
Equivalently, the numerator `N` determines the coefficient sequence, so a fixed
proper numerator is the same datum as a fixed vector of polynomial initial
conditions. -/
theorem initial_data_unique {d : ℕ → A} (hd : IsUnit (d 0)) {P P' : ℕ → A}
    (h : ∀ m, denomConv d P m = denomConv d P' m) : P = P' :=
  funext fun m =>
    initial_data_unique_lt hd (n := m + 1) (fun k _ => h k) m (Nat.lt_succ_self m)

/-- Paper `sec:reduction` — the convolution of `prop:initial-data` is coefficient
extraction from the product of the two generating series in `t`. -/
theorem denomConv_eq_coeff_mul (d P : ℕ → A) (m : ℕ) :
    denomConv d P m = PowerSeries.coeff m (PowerSeries.mk d * PowerSeries.mk P) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (PowerSeries.mk d) * PowerSeries.coeff j (PowerSeries.mk P))]
  simp [denomConv]

/-- **`prop:initial-data` (existence).**  With the diagonal `d_0` a unit, every
prescribed numerator sequence is realized: the generating series
`D = ∑_j d_j t^j` is invertible in `A⟦t⟧` because its constant term is, and the
coefficients of `N/D` solve the system. -/
theorem exists_denomConv_eq {d : ℕ → A} (hd : IsUnit (d 0)) (N : ℕ → A) :
    ∃ P : ℕ → A, ∀ m, denomConv d P m = N m := by
  obtain ⟨u, hu⟩ := hd
  have hconst : PowerSeries.constantCoeff (PowerSeries.mk d) = (u : A) := by
    simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hu]
  set Dinv := PowerSeries.invOfUnit (PowerSeries.mk d) u with hDinv
  refine ⟨fun m => PowerSeries.coeff m (Dinv * PowerSeries.mk N), fun m => ?_⟩
  have hmk : PowerSeries.mk (fun m => PowerSeries.coeff m (Dinv * PowerSeries.mk N))
      = Dinv * PowerSeries.mk N := by
    ext n; simp
  rw [denomConv_eq_coeff_mul, hmk, ← mul_assoc, PowerSeries.mul_invOfUnit _ u hconst,
    one_mul, PowerSeries.coeff_mk]

/-- **`prop:initial-data`, sequence form.**  For a denominator with unit diagonal
`d_0`, the map `P ↦ (∑_{j≤m} d_j P_{m-j})_m` from coefficient sequences to
numerator sequences is a bijection.  The paper's map `N ↦ (P_0, P_1, …)` is the
inverse, `(initialDataEquiv d hd).symm`. -/
noncomputable def initialDataEquiv (d : ℕ → A) (hd : IsUnit (d 0)) : (ℕ → A) ≃ (ℕ → A) :=
  Equiv.ofBijective (fun P => denomConv d P)
    ⟨fun _ _ h => initial_data_unique hd (fun m => congrFun h m),
     fun N => (exists_denomConv_eq hd N).imp fun _ h => funext h⟩

@[simp] theorem initialDataEquiv_apply (d : ℕ → A) (hd : IsUnit (d 0)) (P : ℕ → A) :
    initialDataEquiv d hd P = denomConv d P := rfl

/-- The truncated convolution of `prop:initial-data`: the `d` equations
`∑_{j=0}^m d_j P_{m-j} = N_m` for `0 ≤ m < d`, read as a map on `d`-tuples.  The
equations indexed by `m < n` involve only `P_0, …, P_{n-1}`, so no hypothesis on
the support of `d` is needed. -/
def denomConvFin {n : ℕ} (d : ℕ → A) (P : Fin n → A) (m : Fin n) : A :=
  ∑ j ∈ Finset.range (m.1 + 1), d j * P ⟨m.1 - j, lt_of_le_of_lt (Nat.sub_le _ _) m.2⟩

/-- Paper `sec:reduction` (supporting) — the truncated system is the restriction
of the full one. -/
theorem denomConvFin_eq_denomConv {n : ℕ} (d : ℕ → A) (P : ℕ → A) {m : ℕ} (hm : m < n) :
    denomConvFin d (fun i : Fin n => P i.1) ⟨m, hm⟩ = denomConv d P m := rfl

/-- **`prop:initial-data`.**  For a denominator with unit diagonal `d_0 = Q(0)`,
the lower-triangular system `∑_{j=0}^m d_j P_{m-j} = N_m`, `0 ≤ m < d`, is a
bijection between vectors of initial conditions `(P_0,…,P_{d-1})` and proper
numerators `(N_0,…,N_{d-1})`.  Instantiated at `A = ℝ[z]` and `n = d = deg_t D`
this is the paper's bijection from proper numerators onto `ℝ[z]^d`, its `symm`
being the paper's direction `N ↦ (P_0,…,P_{d-1})`. -/
noncomputable def initialDataEquivFin {n : ℕ} (d : ℕ → A) (hd : IsUnit (d 0)) :
    (Fin n → A) ≃ (Fin n → A) := by
  refine Equiv.ofBijective (denomConvFin d) ⟨fun P P' hPP' => ?_, fun N => ?_⟩
  · -- injective: extend by zero and apply the truncated uniqueness
    set Pe : ℕ → A := fun j => if h : j < n then P ⟨j, h⟩ else 0 with hPe
    set Pe' : ℕ → A := fun j => if h : j < n then P' ⟨j, h⟩ else 0 with hPe'
    have hres : (fun i : Fin n => Pe i.1) = P := by
      funext i; simp [hPe, i.2]
    have hres' : (fun i : Fin n => Pe' i.1) = P' := by
      funext i; simp [hPe', i.2]
    have hagree : ∀ m, m < n → denomConv d Pe m = denomConv d Pe' m := by
      intro m hm
      rw [← denomConvFin_eq_denomConv d Pe hm, ← denomConvFin_eq_denomConv d Pe' hm,
        hres, hres', hPP']
    funext i
    have := initial_data_unique_lt hd hagree i.1 i.2
    simpa [hPe, hPe', i.2] using this
  · -- surjective: solve the full system for the zero-extended numerator
    obtain ⟨P, hP⟩ := exists_denomConv_eq hd (fun j => if h : j < n then N ⟨j, h⟩ else 0)
    refine ⟨fun i : Fin n => P i.1, funext fun m => ?_⟩
    have := hP m.1
    rw [denomConvFin_eq_denomConv d P m.2]
    rw [this]
    simp [m.2]

@[simp] theorem initialDataEquivFin_apply {n : ℕ} (d : ℕ → A) (hd : IsUnit (d 0))
    (P : Fin n → A) : initialDataEquivFin d hd P = denomConvFin d P := rfl

/-! ### Eventual degree (upper bound)

The `sec:reduction` Laurent reduction (`lem:laurent-reduction`) writes coefficient extraction
from `B(t)/(Q(t)+z t^r)` as the denominator recurrence
`∑_{i=0}^M d_i F_{M-i} = C(b_M)`, where `d_i = [t^i](Q(t)+z t^r) = C(Q.coeff i)
+ [i=r]·X` (`X` the `z`-indeterminate).  The `z`-degree of `F_M` is at most `⌊M/r⌋`
(`lem:eventual-degree`, upper bound) — the half feeding the bulk count of `subsec:proof`:
combined with the phase-count lower bound `#interior ≥ ⌊M/r⌋ - C` it gives
`deg F_M - C ≤ #interior`.

The argument is purely algebraic (a peeled recurrence with an invertible diagonal),
so it is stated over an arbitrary field `𝕜`: the paper uses the coefficient field
`ℝ` in `sec:reduction`, and the analytic bridge (`Bridge.FTInputs.ofRecurrence`) instantiates it
at `ℂ`, where the zeros of the `P_m` live. -/

open Polynomial

variable {𝕜 : Type*} [Field 𝕜]

/-- Paper `sec:reduction`, `lem:eventual-degree` — the denominator coefficient
`d_i = [t^i](Q(t) + z t^r) = C(Q.coeff i) + [i=r]·X`, a polynomial in `z = X`. -/
noncomputable def ftDenom (Q : Polynomial 𝕜) (r i : ℕ) : Polynomial 𝕜 :=
  Polynomial.C (Q.coeff i) + (if i = r then Polynomial.X else 0)

/-- Paper `sec:reduction` (supporting) — `z`-degree of `d_i` is `≤ 1` at the
resonant index `i = r` and `≤ 0` elsewhere. -/
theorem ftDenom_natDegree_le_one (Q : Polynomial 𝕜) (r i : ℕ) :
    (ftDenom Q r i).natDegree ≤ (if i = r then 1 else 0) := by
  unfold ftDenom
  by_cases h : i = r
  · simp only [if_pos h]
    refine le_trans (natDegree_add_le _ _) ?_
    simp [natDegree_C, natDegree_X]
  · simp [if_neg h, natDegree_C]

/-- Paper `sec:reduction` (supporting) — the diagonal `d_0 = C(Q(0))` when
`r ≥ 1`. -/
theorem ftDenom_zero (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r) :
    ftDenom Q r 0 = C (Q.coeff 0) := by
  unfold ftDenom
  rw [if_neg (by omega : ¬ (0 : ℕ) = r), add_zero]

/-- **Paper `sec:reduction`, `lem:eventual-degree` (upper bound).**  If a
`z`-polynomial sequence `F` satisfies the denominator recurrence
`∑_{i=0}^M d_i F_{M-i} = C(b_M)` with `d_i = C(Q.coeff i) + [i=r]·X`, numerator
`b`, order `r ≥ 1`, and `Q(0) ≠ 0`, then `deg_z F_M ≤ ⌊M/r⌋`.  This is the degree
half of the bulk count: with the `subsec:proof` phase count it yields `deg F_M - C ≤ #interior`. -/
theorem eventual_natDegree_le (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.coeff 0 ≠ 0) (b : ℕ → 𝕜) (F : ℕ → Polynomial 𝕜)
    (hrec : ∀ M, denomConv (ftDenom Q r) F M = C (b M)) (M : ℕ) :
    (F M).natDegree ≤ M / r := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    -- Peel the diagonal: `C(b M) = SUM + C(Q(0))·F M`.
    have key : C (b M)
        = (∑ j ∈ Finset.range M, ftDenom Q r (j + 1) * F (M - (j + 1)))
          + C (Q.coeff 0) * F M := by
      rw [← hrec M, denomConv_eq, ftDenom_zero Q hr]
    -- Invert the constant diagonal: `F M = C(Q(0)⁻¹)·(C(b M) - SUM)`.
    have hFM : F M
        = C ((Q.coeff 0)⁻¹)
          * (C (b M) - ∑ j ∈ Finset.range M, ftDenom Q r (j + 1) * F (M - (j + 1))) := by
      have hcancel : C (Q.coeff 0) * F M
          = C (b M) - ∑ j ∈ Finset.range M, ftDenom Q r (j + 1) * F (M - (j + 1)) := by
        rw [key]; ring
      rw [← hcancel, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hQ0, C_1, one_mul]
    -- Every summand has `z`-degree `≤ ⌊M/r⌋`.
    have hSle : (∑ j ∈ Finset.range M, ftDenom Q r (j + 1) * F (M - (j + 1))).natDegree
        ≤ M / r := by
      apply natDegree_sum_le_of_forall_le
      intro j hj
      have hjM : j < M := Finset.mem_range.mp hj
      have hIH : (F (M - (j + 1))).natDegree ≤ (M - (j + 1)) / r := ih _ (by omega)
      have hmulle : (ftDenom Q r (j + 1) * F (M - (j + 1))).natDegree
          ≤ (ftDenom Q r (j + 1)).natDegree + (F (M - (j + 1))).natDegree := natDegree_mul_le
      have hden := ftDenom_natDegree_le_one Q r (j + 1)
      by_cases hjr : j + 1 = r
      · rw [if_pos hjr] at hden
        have hrM : r ≤ M := by omega
        have hdiv : 1 + (M - r) / r = M / r := by
          have hh := Nat.add_div_right (M - r) (show 0 < r by omega)
          rw [Nat.sub_add_cancel hrM] at hh
          omega
        have hMi : M - (j + 1) = M - r := by rw [hjr]
        calc (ftDenom Q r (j + 1) * F (M - (j + 1))).natDegree
            ≤ 1 + (M - (j + 1)) / r := le_trans hmulle (Nat.add_le_add hden hIH)
          _ = 1 + (M - r) / r := by rw [hMi]
          _ = M / r := hdiv
      · rw [if_neg hjr] at hden
        have h0 : (ftDenom Q r (j + 1)).natDegree = 0 := Nat.le_zero.mp hden
        have hle : (M - (j + 1)) / r ≤ M / r := Nat.div_le_div_right (by omega)
        calc (ftDenom Q r (j + 1) * F (M - (j + 1))).natDegree
            ≤ (ftDenom Q r (j + 1)).natDegree + (F (M - (j + 1))).natDegree := hmulle
          _ = (F (M - (j + 1))).natDegree := by rw [h0, zero_add]
          _ ≤ (M - (j + 1)) / r := hIH
          _ ≤ M / r := hle
    -- Assemble: `deg (C(b M) - SUM) ≤ ⌊M/r⌋`, and `C(Q(0)⁻¹)·` cannot raise degree.
    have hsub : (C (b M)
        - ∑ j ∈ Finset.range M, ftDenom Q r (j + 1) * F (M - (j + 1))).natDegree ≤ M / r := by
      refine le_trans (natDegree_sub_le _ _) (max_le ?_ hSle)
      rw [natDegree_C]; exact Nat.zero_le _
    calc (F M).natDegree
        = (C ((Q.coeff 0)⁻¹)
            * (C (b M) - ∑ j ∈ Finset.range M, ftDenom Q r (j + 1) * F (M - (j + 1)))).natDegree :=
          by rw [hFM]
      _ ≤ (C (b M)
            - ∑ j ∈ Finset.range M, ftDenom Q r (j + 1) * F (M - (j + 1))).natDegree :=
          natDegree_C_mul_le _ _
      _ ≤ M / r := hsub

end ForgacsTran
