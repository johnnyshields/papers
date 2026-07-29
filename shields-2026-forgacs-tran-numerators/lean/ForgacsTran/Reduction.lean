/-
# Numerator as initial data

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, §2 «Laurent reduction
and eventual degree» (`sec:reduction`, `prop:initial-data`): the numerator of a
proper rational generating function carries the same information as the initial
data of the denominator recurrence.

Writing `D(t,z) = ∑_j d_j(z) t^j` with `d_0 = Q(0) ≠ 0` a unit, the coefficients
`P_m` of `N/D` satisfy the lower-triangular convolution system
`∑_{j=0}^m d_j P_{m-j} = N_m`.  Because the diagonal `d_0` is a unit, the
sequence `(P_m)` is uniquely determined by the right-hand side.  This is the
injective half of the bijection `N ↦ (P_0, P_1, …)` — a fixed numerator is a
fixed choice of initial data, and conversely.

Stated over an arbitrary commutative ring (instantiated at `R[z]`, where the
units are the nonzero real constants, so `d_0 = Q(0)` qualifies).  Sorry-free;
strong induction plus cancellation by a unit.

`eventual_natDegree_le` adds the `lem:eventual-degree` upper bound
`deg_z F_M ≤ ⌊M/r⌋` for any sequence satisfying the concrete denominator
recurrence with `d_i = C(Q.coeff i) + [i=r]·X`, by the same strong induction on
the peeled recurrence.  It is the degree half of the §5 bulk count.
-/
import Mathlib

open scoped BigOperators

namespace ForgacsTran

variable {A : Type*} [CommRing A]

/-- The denominator convolution `∑_{j=0}^m d_j P_{m-j}` of `prop:initial-data`. -/
def denomConv (d P : ℕ → A) (m : ℕ) : A := ∑ j ∈ Finset.range (m + 1), d j * P (m - j)

/-- Paper §2 `sec:reduction` — supporting step for `prop:initial-data`.  Peeling
the `j = 0` term isolates the diagonal contribution `d_0 · P_m`. -/
theorem denomConv_eq (d P : ℕ → A) (m : ℕ) :
    denomConv d P m
      = (∑ j ∈ Finset.range m, d (j + 1) * P (m - (j + 1))) + d 0 * P m := by
  unfold denomConv
  rw [Finset.sum_range_succ']
  simp

/-- **`prop:initial-data` (uniqueness).**  If the diagonal `d_0` is a unit, the
convolution system `∑_{j=0}^m d_j P_{m-j} = N_m` has at most one solution `P`.
Equivalently, the numerator `N` determines the coefficient sequence, so a fixed
proper numerator is the same datum as a fixed vector of polynomial initial
conditions. -/
theorem initial_data_unique {d : ℕ → A} (hd : IsUnit (d 0)) {P P' : ℕ → A}
    (h : ∀ m, denomConv d P m = denomConv d P' m) : P = P' := by
  funext m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hm := h m
    rw [denomConv_eq, denomConv_eq] at hm
    -- the tail sums agree by the induction hypothesis
    have htail : (∑ j ∈ Finset.range m, d (j + 1) * P (m - (j + 1)))
        = ∑ j ∈ Finset.range m, d (j + 1) * P' (m - (j + 1)) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hlt : m - (j + 1) < m := by
        have : j < m := Finset.mem_range.mp hj
        omega
      rw [ih (m - (j + 1)) hlt]
    rw [htail] at hm
    have hcancel : d 0 * P m = d 0 * P' m := add_left_cancel hm
    exact (hd.mul_right_inj).mp hcancel

/-! ### Eventual degree (upper bound)

The §2 Laurent reduction (`lem:laurent-reduction`) writes coefficient extraction
from `B(t)/(Q(t)+z t^r)` as the denominator recurrence
`∑_{i=0}^M d_i F_{M-i} = C(b_M)`, where `d_i = [t^i](Q(t)+z t^r) = C(Q.coeff i)
+ [i=r]·X` (`X` the `z`-indeterminate).  The `z`-degree of `F_M` is at most `⌊M/r⌋`
(`lem:eventual-degree`, upper bound) — the half feeding the bulk count of §5:
combined with the phase-count lower bound `#interior ≥ ⌊M/r⌋ - C` it gives
`deg F_M - C ≤ #interior`.

The argument is purely algebraic (a peeled recurrence with an invertible diagonal),
so it is stated over an arbitrary field `𝕜`: the paper uses the coefficient field
`ℝ` in §2, and the analytic bridge (`Bridge.FTInputs.ofRecurrence`) instantiates it
at `ℂ`, where the zeros of the `P_m` live. -/

open Polynomial

variable {𝕜 : Type*} [Field 𝕜]

/-- Paper §2 `sec:reduction`, `lem:eventual-degree` — the denominator coefficient
`d_i = [t^i](Q(t) + z t^r) = C(Q.coeff i) + [i=r]·X`, a polynomial in `z = X`. -/
noncomputable def ftDenom (Q : Polynomial 𝕜) (r i : ℕ) : Polynomial 𝕜 :=
  Polynomial.C (Q.coeff i) + (if i = r then Polynomial.X else 0)

/-- Paper §2 `sec:reduction` (supporting) — `z`-degree of `d_i` is `≤ 1` at the
resonant index `i = r` and `≤ 0` elsewhere. -/
theorem ftDenom_natDegree_le_one (Q : Polynomial 𝕜) (r i : ℕ) :
    (ftDenom Q r i).natDegree ≤ (if i = r then 1 else 0) := by
  unfold ftDenom
  by_cases h : i = r
  · simp only [if_pos h]
    refine le_trans (natDegree_add_le _ _) ?_
    simp [natDegree_C, natDegree_X]
  · simp [if_neg h, natDegree_C]

/-- Paper §2 `sec:reduction` (supporting) — the diagonal `d_0 = C(Q(0))` when
`r ≥ 1`. -/
theorem ftDenom_zero (Q : Polynomial 𝕜) {r : ℕ} (hr : 1 ≤ r) :
    ftDenom Q r 0 = C (Q.coeff 0) := by
  unfold ftDenom
  rw [if_neg (by omega : ¬ (0 : ℕ) = r), add_zero]

/-- **Paper §2 `sec:reduction`, `lem:eventual-degree` (upper bound).**  If a
`z`-polynomial sequence `F` satisfies the denominator recurrence
`∑_{i=0}^M d_i F_{M-i} = C(b_M)` with `d_i = C(Q.coeff i) + [i=r]·X`, numerator
`b`, order `r ≥ 1`, and `Q(0) ≠ 0`, then `deg_z F_M ≤ ⌊M/r⌋`.  This is the degree
half of the bulk count: with the §5 phase count it yields `deg F_M - C ≤ #interior`. -/
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
