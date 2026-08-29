/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchEndpoint
import ForgacsTran.PencilIndex

/-!
# Identifying the endpoint limit

`FTBranchEndpoint` shows the branch radius converges as `θ → 0⁺` to *a* zero of
the critical polynomial.  Which zero is a separate question, and their Lemma 6
answers it with the angle count: `∑_k θ_k = rθ + (n-1)π` forces `τ₁ ≤ t_a ≤ τ₂`.
This module carries the half of that count the consumers need — when the
smallest zero of `Q` is repeated, the limit is that zero.

## Main statements

* `tendsto_ftAngle_nhdsGT_zero_of_lt` / `_pi_of_gt` — a branch angle collapses to
  `0` or opens to `π` according as its zero lies below or above the limit.
* `ftTau_limit_eq_of_repeated_min` — if the smallest zero has multiplicity at
  least two, the limit is that zero.

## Implementation notes

**Differs from the paper's route.**  Forgács--Tran's Figures 1--2 carry the
count; here each angle's limit is obtained from the closed form of
`FTBranchAngle`:
`cot θ_k = (cos θ - τ_k/τ)/sin θ`, whose right side runs to `±∞` as `θ → 0⁺`
according to the sign of `1 - τ_k/L`, so no figure is consulted and the two
cases are the two signs.

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

endpoint limit, branch radius, minimum modulus
-/

namespace ForgacsTran

open Real Set Filter Topology

theorem ftAngle_eq_div {a τ θ : ℝ} (hτ : τ ≠ 0) (hs : Real.sin θ ≠ 0) :
    ftAngle a τ θ = ftArccot ((Real.cos θ - a / τ) / Real.sin θ) := by
  rw [ftAngle]
  congr 1
  field_simp

/-- A zero below the limit sends its angle to `0`. -/
theorem tendsto_ftAngle_nhdsGT_zero_of_lt {a L : ℝ} {T : ℝ → ℝ} (ha : 0 < a) (hL : a < L)
    (hT : Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 L)) (hTpos : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < T θ) :
    Tendsto (fun θ => ftAngle a (T θ) θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hLpos : 0 < L := lt_trans ha hL
  set q : ℝ := (1 + a / L) / 2 with hq
  have haL : a / L < 1 := (div_lt_one hLpos).2 hL
  have haL0 : 0 < a / L := div_pos ha hLpos
  have hqlt : q < 1 := by rw [hq]; linarith
  have hqpos : a / L < q := by rw [hq]; linarith
  have hqpos' : 0 < q := by rw [hq]; linarith
  have hbig : ∀ᶠ θ in 𝓝[>] (0 : ℝ), a / q < T θ := by
    refine hT.eventually (eventually_gt_nhds ?_)
    rw [div_lt_iff₀ hqpos']
    have : a / L < q := hqpos
    rw [div_lt_iff₀ hLpos] at this
    linarith
  have hsin : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo (0 : ℝ) π := Ioo_mem_nhdsGT pi_pos
  have hub : Tendsto (fun θ : ℝ => ftArccot ((Real.cos θ - q) / Real.sin θ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_ftArccot_atTop.comp (tendsto_cos_sub_div_sin_atTop hqlt)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℝ => (0 : ℝ))
    (h := fun θ : ℝ => ftArccot ((Real.cos θ - q) / Real.sin θ)) tendsto_const_nhds hub ?_ ?_
  · filter_upwards [hTpos, hsin] with θ hTθ hθ using (ftAngle_pos a (T θ) θ).le
  · filter_upwards [hbig, hTpos, hsin] with θ hbθ hTθ hθ
    have hs : 0 < Real.sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    rw [ftAngle_eq_div (ne_of_gt hTθ) (ne_of_gt hs)]
    refine le_of_lt (ftArccot_strictAnti ?_)
    refine div_lt_div_of_pos_right ?_ hs
    have : a / T θ < q := by rw [div_lt_iff₀ hTθ, ← div_lt_iff₀' hqpos']; exact hbθ
    linarith

/-- A zero above the limit opens its angle to `π`. -/
theorem tendsto_ftAngle_nhdsGT_pi_of_gt {a L : ℝ} {T : ℝ → ℝ} (hL : 0 < L) (hgt : L < a)
    (hT : Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 L)) (hTpos : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < T θ) :
    Tendsto (fun θ => ftAngle a (T θ) θ) (𝓝[>] (0 : ℝ)) (𝓝 π) := by
  set q : ℝ := (1 + a / L) / 2 with hq
  have haL : 1 < a / L := (one_lt_div hL).2 hgt
  have hqgt : 1 < q := by rw [hq]; linarith
  have hqlt : q < a / L := by rw [hq]; linarith
  have hsmall : ∀ᶠ θ in 𝓝[>] (0 : ℝ), T θ < a / q := by
    refine hT.eventually (eventually_lt_nhds ?_)
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < q), ← lt_div_iff₀' hL]
    exact hqlt
  have hsin : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo (0 : ℝ) π := Ioo_mem_nhdsGT pi_pos
  have hlb : Tendsto (fun θ : ℝ => ftArccot ((Real.cos θ - q) / Real.sin θ))
      (𝓝[>] (0 : ℝ)) (𝓝 π) :=
    tendsto_ftArccot_atBot.comp (tendsto_cos_sub_div_sin_atBot hqgt)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun θ : ℝ =>
      ftArccot ((Real.cos θ - q) / Real.sin θ)) (h := fun _ : ℝ => π) hlb tendsto_const_nhds ?_ ?_
  · filter_upwards [hsmall, hTpos, hsin] with θ hsθ hTθ hθ
    have hs : 0 < Real.sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    rw [ftAngle_eq_div (ne_of_gt hTθ) (ne_of_gt hs)]
    refine le_of_lt (ftArccot_strictAnti ?_)
    refine div_lt_div_of_pos_right ?_ hs
    have : q < a / T θ := by rw [lt_div_iff₀ hTθ, ← lt_div_iff₀' (by linarith : (0:ℝ) < q)]
                             exact hsθ
    linarith
  · filter_upwards [hsin] with θ hθ using (ftAngle_lt_pi a (T θ) θ).le

/-- **The identification.**  If the smallest zero of `Q` is repeated then the
endpoint limit of the branch radius *is* that zero.  This is the half of the
count of `Forgacs2017RationalDenominator` Lemma 6 the consumers need: with
multiplicity `ρ ≥ 2` at `x₁` the bracket `τ₁ ≤ t_a ≤ τ₂` collapses to a point. -/
theorem ftTau_limit_eq_of_repeated_min {n r : ℕ} {a : Fin n → ℝ} {L : ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i j : Fin n} (hij : i ≠ j) (haij : a i = a j)
    (hmin : ∀ k, a i ≤ a k) (hLpos : 0 < L)
    (hb : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) θ)
    (hT : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    L = a i := by
  classical
  have hπ := pi_pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hn : 0 < n := by omega
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := cast_pred_eq_sub_one hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have harc : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo (0 : ℝ) (π / r) :=
    Ioo_mem_nhdsGT (by positivity)
  have hTpos : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < ftTau a r (n - 1) θ := by
    filter_upwards [harc] with θ hθ using ftTau_pos (hb θ hθ)
  -- the angle sum, and its limit
  have hsum : ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      (∑ k, ftAngle (a k) (ftTau a r (n - 1) θ) θ) = r * θ + ((n : ℝ) - 1) * π := by
    filter_upwards [harc] with θ hθ
    have := ftAngleSum_ftTau (hb θ hθ)
    rwa [ftAngleSum, hn1] at this
  have hsumtend : Tendsto (fun θ => ∑ k, ftAngle (a k) (ftTau a r (n - 1) θ) θ)
      (𝓝[>] (0 : ℝ)) (𝓝 (((n : ℝ) - 1) * π)) := by
    refine Tendsto.congr' (hsum.mono fun θ h => h.symm) ?_
    have : Tendsto (fun θ : ℝ => (r : ℝ) * θ + ((n : ℝ) - 1) * π) (𝓝[>] (0 : ℝ))
        (𝓝 ((r : ℝ) * 0 + ((n : ℝ) - 1) * π)) :=
      ((tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds)).add
        tendsto_const_nhds)
    simpa using this
  rcases lt_trichotomy L (a i) with hlt | heq | hgt
  · -- every zero lies above the limit, so every angle opens to `π`
    exfalso
    have hall : ∀ k, Tendsto (fun θ => ftAngle (a k) (ftTau a r (n - 1) θ) θ)
        (𝓝[>] (0 : ℝ)) (𝓝 π) := fun k =>
      tendsto_ftAngle_nhdsGT_pi_of_gt hLpos (lt_of_lt_of_le hlt (hmin k)) hT hTpos
    have hbig : Tendsto (fun θ => ∑ k, ftAngle (a k) (ftTau a r (n - 1) θ) θ)
        (𝓝[>] (0 : ℝ)) (𝓝 ((n : ℝ) * π)) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Fin n))
        (fun k (_ : k ∈ Finset.univ) => hall k)
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
    have := tendsto_nhds_unique hbig hsumtend
    nlinarith
  · exact heq
  · -- the two smallest zeros lie below the limit, so two angles collapse to `0`
    exfalso
    have hi := tendsto_ftAngle_nhdsGT_zero_of_lt (ha i) hgt hT hTpos
    have hj := tendsto_ftAngle_nhdsGT_zero_of_lt (ha j) (by rw [← haij]; exact hgt) hT hTpos
    have hle : ∀ᶠ θ in 𝓝[>] (0 : ℝ),
        (∑ k, ftAngle (a k) (ftTau a r (n - 1) θ) θ)
          ≤ ftAngle (a i) (ftTau a r (n - 1) θ) θ + ftAngle (a j) (ftTau a r (n - 1) θ) θ
            + ((n : ℝ) - 2) * π := by
      filter_upwards [harc, hTpos] with θ hθ hTθ
      set g : Fin n → ℝ := fun k => π - ftAngle (a k) (ftTau a r (n - 1) θ) θ with hg
      have hgnn : ∀ k, 0 ≤ g k := fun k => by
        simp only [hg]; linarith [ftAngle_lt_pi (a k) (ftTau a r (n - 1) θ) θ]
      have hpair : g i + g j ≤ ∑ k, g k := by
        have hsub : ({i, j} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
        have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hgnn k)
        rwa [Finset.sum_pair hij] at this
      have hgsum : ∑ k, g k
          = (n : ℝ) * π - ∑ k, ftAngle (a k) (ftTau a r (n - 1) θ) θ := by
        simp only [hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      rw [hgsum] at hpair
      simp only [hg] at hpair
      linarith
    have hrhs : Tendsto (fun θ => ftAngle (a i) (ftTau a r (n - 1) θ) θ
        + ftAngle (a j) (ftTau a r (n - 1) θ) θ + ((n : ℝ) - 2) * π) (𝓝[>] (0 : ℝ))
        (𝓝 (0 + 0 + ((n : ℝ) - 2) * π)) := (hi.add hj).add tendsto_const_nhds
    have := le_of_tendsto_of_tendsto hsumtend hrhs hle
    nlinarith

/-- **The endpoint limit, identified.**  For a pencil whose smallest zero is
repeated, the branch radius converges to that zero — no hypothesis beyond
`2 ≤ n`, positive zeros and `r ≥ 1`, and in particular none of
`Forgacs2017RationalDenominator` Lemma 3. -/
theorem tendsto_ftTau_nhdsGT_zero_of_repeated_min {n r : ℕ} {a : Fin n → ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i j : Fin n} (hij : i ≠ j) (haij : a i = a j)
    (hmin : ∀ k, a i ≤ a k) :
    Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 (a i)) := by
  have hn : 0 < n := by omega
  obtain ⟨L, hLpos, hT, -⟩ :=
    exists_tendsto_ftTau_nhdsGT_zero_of_two_le (c := (1 : ℝ)) hn2 ha hr one_pos
  have hb : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) θ := fun θ hθ =>
    ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ
  have := ftTau_limit_eq_of_repeated_min hn2 ha hr hij haij hmin hLpos hb hT
  rwa [this] at hT

/-! ### The first-order behaviour at the endpoint

The angle count fixes not only the limit but the slope.  All `ρ` angles belonging
to the repeated smallest zero are literally the same function of `θ`, so the
count `∑_k θ_k = rθ + (n-1)π` reads `ρ β(θ) + ∑_{k ∉ S} θ_k = rθ + (n-1)π`; the
`n - ρ` others open to `π`, so `β(θ) → (ρ-1)π/ρ`.  Since `cot β(θ)` *is*
`(cos θ - x₁/τ(θ))/sin θ`, that limit is exactly the statement that
`(τ(θ) - x₁)/θ → -x₁ cot(π/ρ)`. -/

theorem cot_ftAngle {a τ θ : ℝ} (hτ : τ ≠ 0) (hs : Real.sin θ ≠ 0) :
    Real.cos (ftAngle a τ θ) / Real.sin (ftAngle a τ θ) = (Real.cos θ - a / τ) / Real.sin θ := by
  rw [ftAngle_eq_div hτ hs, cos_ftArccot, mul_div_assoc,
    div_self (ne_of_gt (sin_ftArccot_pos _)), mul_one]

/-- **The radius defect, exactly.**  The distance from the branch radius to a zero
splits into the chord defect `τ(1 - cos θ)` and a cotangent term:
`τ - a = τ(1 - cos θ) + τ sin θ · cot(θ_a)`.  This is `cot_ftAngle` cleared of
denominators, and it is the identity that converts control on an angle into
control on the radius. -/
theorem sub_eq_cot_ftAngle {a τ θ : ℝ} (hτ : τ ≠ 0) (hs : Real.sin θ ≠ 0) :
    τ - a = τ * (1 - Real.cos θ)
      + τ * Real.sin θ * (Real.cos (ftAngle a τ θ) / Real.sin (ftAngle a τ θ)) := by
  rw [cot_ftAngle hτ hs]
  field

/-- **The angle count, split at the repeated zero.**  The `ρ` angles belonging to
the repeated smallest zero are the single function `β(θ) = ftBranchAngle a r
(n-1) i θ`, so on the principal arc `∑_k θ_k = rθ + (n-1)π` reads
`ρ β(θ) + ∑_{k ∉ S} θ_k = rθ + (n-1)π`.  This is the count rearranged and
contains no analysis; both the endpoint slope and the first-order bound on `β`
are read off it. -/
theorem ftBranchAngle_count {n r ρ : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ)
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (π / r)) :
    (ρ : ℝ) * ftBranchAngle a r (n - 1) i θ
        + ∑ k ∈ Sᶜ, ftAngle (a k) (ftTau a r (n - 1) θ) θ
      = (r : ℝ) * θ + ((n : ℝ) - 1) * π := by
  have hn : 0 < n := by omega
  have hbr := ftAngleSum_ftTau (ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ)
  rw [ftAngleSum, Nat.cast_sub hn, Nat.cast_one] at hbr
  have hsplit : ∑ k, ftAngle (a k) (ftTau a r (n - 1) θ) θ
      = ∑ k ∈ S, ftAngle (a k) (ftTau a r (n - 1) θ) θ
        + ∑ k ∈ Sᶜ, ftAngle (a k) (ftTau a r (n - 1) θ) θ :=
    (Finset.sum_add_sum_compl S _).symm
  have hSconst : ∑ k ∈ S, ftAngle (a k) (ftTau a r (n - 1) θ) θ
      = (ρ : ℝ) * ftBranchAngle a r (n - 1) i θ := by
    rw [Finset.sum_congr rfl fun k hk => by rw [(hS k).1 hk], Finset.sum_const, hcard,
      nsmul_eq_mul]
    rfl
  rw [hsplit, hSconst] at hbr
  linarith

/-- **The endpoint slope.**  With the smallest zero `x₁` repeated `ρ ≥ 2` times,
`(τ(θ) - x₁)/θ → -x₁ cot(π/ρ)`: the branch leaves the endpoint with the slope
`Forgacs2017RationalDenominator`'s Proposition 3 measures against. -/
theorem tendsto_ftTau_slope_nhdsGT_zero {n r ρ : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ) (hρ : 2 ≤ ρ)
    (hmin : ∀ k, a i ≤ a k) :
    Tendsto (fun θ => (ftTau a r (n - 1) θ - a i) / θ) (𝓝[>] (0 : ℝ))
      (𝓝 (-(a i) * Real.cos (π / ρ) / Real.sin (π / ρ))) := by
  classical
  have hπ := pi_pos
  have hn : 0 < n := by omega
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hρ0 : (0 : ℝ) < ρ := by positivity
  have hρR : (2 : ℝ) ≤ ρ := by exact_mod_cast hρ
  -- two indices in `S`, so the limit of `τ` is `a i`
  have hρn : ρ ≤ n := by
    have h := Finset.card_le_univ S
    rw [Fintype.card_fin] at h
    exact hcard ▸ h
  obtain ⟨j, hj⟩ : (S.erase i).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ((hS i).2 rfl), hcard]; omega
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  have hjS : j ∈ S := Finset.mem_of_mem_erase hj
  have hT : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 (a i)) :=
    tendsto_ftTau_nhdsGT_zero_of_repeated_min hn2 ha hr (Ne.symm hji) ((hS j).1 hjS).symm hmin
  have hTpos : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < ftTau a r (n - 1) θ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < π / r by positivity)] with θ hθ
    exact ftTau_pos (ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ)
  have hai : 0 < a i := ha i
  -- the angles outside `S` open to `π`
  have hout : ∀ k ∉ S, Tendsto (fun θ => ftAngle (a k) (ftTau a r (n - 1) θ) θ)
      (𝓝[>] (0 : ℝ)) (𝓝 π) := by
    intro k hk
    refine tendsto_ftAngle_nhdsGT_pi_of_gt hai ?_ hT hTpos
    exact lt_of_le_of_ne (hmin k) fun h => hk ((hS k).2 h.symm)
  have houtsum : Tendsto (fun θ => ∑ k ∈ Sᶜ, ftAngle (a k) (ftTau a r (n - 1) θ) θ)
      (𝓝[>] (0 : ℝ)) (𝓝 (((n : ℝ) - ρ) * π)) := by
    have := tendsto_finsetSum (Sᶜ : Finset (Fin n))
      (fun k (hk : k ∈ Sᶜ) => hout k (Finset.mem_compl.1 hk))
    have hcc : ((Sᶜ : Finset (Fin n)).card : ℝ) = (n : ℝ) - ρ := by
      rw [Finset.card_compl, Fintype.card_fin, hcard, Nat.cast_sub hρn]
    simpa [Finset.sum_const, nsmul_eq_mul, hcc] using this
  -- the angle count, in terms of the common angle `β`
  have hcount : ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      (ρ : ℝ) * ftAngle (a i) (ftTau a r (n - 1) θ) θ
        = r * θ + ((n : ℝ) - 1) * π - ∑ k ∈ Sᶜ, ftAngle (a k) (ftTau a r (n - 1) θ) θ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < π / r by positivity)] with θ hθ
    have h := ftBranchAngle_count hn2 ha hr hS hcard hθ
    rw [show ftBranchAngle a r (n - 1) i θ = ftAngle (a i) (ftTau a r (n - 1) θ) θ from rfl] at h
    linarith
  -- so the common angle tends to `(ρ-1)π/ρ`
  have hβ : Tendsto (fun θ => ftAngle (a i) (ftTau a r (n - 1) θ) θ) (𝓝[>] (0 : ℝ))
      (𝓝 (π - π / ρ)) := by
    have hlin : Tendsto (fun θ : ℝ => ((r : ℝ) * θ + ((n : ℝ) - 1) * π
        - ∑ k ∈ Sᶜ, ftAngle (a k) (ftTau a r (n - 1) θ) θ) / ρ) (𝓝[>] (0 : ℝ))
        (𝓝 (((r : ℝ) * 0 + ((n : ℝ) - 1) * π - ((n : ℝ) - ρ) * π) / ρ)) :=
      (((tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds)).add
        tendsto_const_nhds).sub houtsum).div_const _
    have hval : ((r : ℝ) * 0 + ((n : ℝ) - 1) * π - ((n : ℝ) - ρ) * π) / ρ = π - π / ρ := by
      field
    rw [hval] at hlin
    refine Tendsto.congr' ?_ hlin
    filter_upwards [hcount] with θ hθ
    rw [← hθ]
    field_simp
  -- `cot β(θ)` is the difference quotient in disguise
  have hβ₀ : Real.sin (π - π / ρ) ≠ 0 := by
    refine ne_of_gt (sin_pos_of_pos_of_lt_pi ?_ ?_)
    · have : π / ρ ≤ π / 2 := by
        apply div_le_div_of_nonneg_left hπ.le (by norm_num) hρR
      linarith
    · have : 0 < π / ρ := by positivity
      linarith
  have hcosβ : Tendsto (fun θ => Real.cos (ftAngle (a i) (ftTau a r (n - 1) θ) θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.cos (π - π / ρ))) := (Real.continuous_cos.tendsto _).comp hβ
  have hsinβ : Tendsto (fun θ => Real.sin (ftAngle (a i) (ftTau a r (n - 1) θ) θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sin (π - π / ρ))) := (Real.continuous_sin.tendsto _).comp hβ
  have hcot : Tendsto (fun θ => (Real.cos θ - a i / ftTau a r (n - 1) θ) / Real.sin θ)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.cos (π - π / ρ) / Real.sin (π - π / ρ))) := by
    refine Tendsto.congr' ?_ (hcosβ.div hsinβ hβ₀)
    filter_upwards [hTpos, Ioo_mem_nhdsGT hπ] with θ hτθ hθ
    exact cot_ftAngle (ne_of_gt hτθ) (ne_of_gt (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2))
  -- the two elementary limits at `0`
  have hsinq : Tendsto (fun θ : ℝ => Real.sin θ / θ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (Real.hasDerivAt_sin 0).tendsto_slope
    have h2 : Tendsto (slope Real.sin 0) (𝓝[>] (0 : ℝ)) (𝓝 (Real.cos 0)) :=
      h.mono_left (nhdsWithin_mono 0 fun x hx => ne_of_gt hx)
    simp only [Real.cos_zero] at h2
    refine Tendsto.congr' ?_ h2
    filter_upwards with θ
    rw [slope_def_field, Real.sin_zero, sub_zero, sub_zero]
  have hcosq : Tendsto (fun θ : ℝ => (Real.cos θ - 1) / θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.hasDerivAt_cos 0).tendsto_slope
    have h2 : Tendsto (slope Real.cos 0) (𝓝[>] (0 : ℝ)) (𝓝 (-Real.sin 0)) :=
      h.mono_left (nhdsWithin_mono 0 fun x hx => ne_of_gt hx)
    simp only [Real.sin_zero, neg_zero] at h2
    refine Tendsto.congr' ?_ h2
    filter_upwards with θ
    rw [slope_def_field, Real.cos_zero, sub_zero]
  have hcos1 : Tendsto (fun θ : ℝ => (Real.cos θ - 1) / Real.sin θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun θ : ℝ => ((Real.cos θ - 1) / θ) / (Real.sin θ / θ))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 / 1)) := hcosq.div hsinq one_ne_zero
    rw [zero_div] at h
    refine Tendsto.congr' ?_ h
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hπ] with θ hθ0 hθ
    have hs : Real.sin θ ≠ 0 := ne_of_gt (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
    have hθ' : θ ≠ 0 := ne_of_gt hθ0
    field_simp
  -- assemble
  have hval : (Real.cos (π - π / ρ) / Real.sin (π - π / ρ) - 0) * a i * 1
      = -(a i) * Real.cos (π / ρ) / Real.sin (π / ρ) := by
    rw [Real.cos_pi_sub, Real.sin_pi_sub, sub_zero, mul_one, neg_div]
    ring
  rw [← hval]
  refine Tendsto.congr' ?_ (((hcot.sub hcos1).mul hT).mul hsinq)
  filter_upwards [hTpos, Ioo_mem_nhdsGT hπ, self_mem_nhdsWithin] with θ hτθ hθ hθ0
  have hs : Real.sin θ ≠ 0 := ne_of_gt (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  field

/-! ### The rate at which the outer angles open to `π`

`tendsto_ftAngle_nhdsGT_pi_of_gt` gives the limit; the second-order expansion of
`τ` needs the rate, and it is first order with an explicit constant. -/

/-- **The rate.**  If `τ (1 + c) ≤ τ_k` then the angle at `τ_k` is within `θ/c`
of `π`. -/
theorem pi_sub_ftAngle_le {a τ θ c : ℝ} (hτ : 0 < τ) (hθ : θ ∈ Ioo 0 π) (hc : 0 < c)
    (hgap : τ * (1 + c) ≤ a) : π - ftAngle a τ θ ≤ θ / c := by
  have hs : 0 < Real.sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsle : Real.sin θ ≤ θ := Real.sin_le hθ.1.le
  have hdiv : (1 : ℝ) + c ≤ a / τ := by
    rw [le_div_iff₀ hτ]; linarith [hgap]
  have hnum : Real.cos θ - a / τ ≤ -c := by
    have := Real.cos_le_one θ
    linarith
  have hX : (Real.cos θ - a / τ) / Real.sin θ ≤ -(c / θ) := by
    rw [div_le_iff₀ hs]
    have h1 : c / θ * Real.sin θ ≤ c := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hθ.1]
      nlinarith [hsle, hc]
    nlinarith [hnum, h1]
  rw [ftAngle_eq_div (ne_of_gt hτ) (ne_of_gt hs)]
  exact pi_sub_ftArccot_le hc hθ.1 hX

/-- **The rate, along the branch.**  Eventually every angle outside the repeated
minimum is within `Kθ` of `π`, with `K` explicit. -/
theorem eventually_pi_sub_ftAngle_le {n r : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hmin : ∀ k, a i ≤ a k) {j : Fin n} (hj : j ∈ S) (hji : j ≠ i)
    {c : ℝ} (hc : 0 < c) (hgap : ∀ k ∉ S, a i * (1 + c) < a k) :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ k ∉ S,
      π - ftAngle (a k) (ftTau a r (n - 1) θ) θ ≤ θ / c := by
  have hn : 0 < n := by omega
  have hai : 0 < a i := ha i
  have hT : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 (a i)) :=
    tendsto_ftTau_nhdsGT_zero_of_repeated_min hn2 ha hr (Ne.symm hji) ((hS j).1 hj).symm hmin
  by_cases hSc : Sᶜ = (∅ : Finset (Fin n))
  · filter_upwards with θ k hk
    exact absurd (Finset.mem_compl.2 hk) (by rw [hSc]; exact Finset.notMem_empty k)
  · obtain ⟨k₀, hk₀, hk₀min⟩ :=
      Finset.exists_min_image (Sᶜ) a (Finset.nonempty_of_ne_empty hSc)
    set A₂ : ℝ := a k₀ with hA₂
    have hA₂gap : a i * (1 + c) < A₂ := hgap k₀ (Finset.mem_compl.1 hk₀)
    have hbd : a i < A₂ / (1 + c) := by
      rw [lt_div_iff₀ (by linarith : (0:ℝ) < 1 + c)]
      exact hA₂gap
    have hclose : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ftTau a r (n - 1) θ * (1 + c) ≤ A₂ := by
      filter_upwards [hT.eventually (eventually_lt_nhds hbd)] with θ hθ
      rw [← le_div_iff₀ (by linarith : (0:ℝ) < 1 + c)]
      exact hθ.le
    have harc : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo (0 : ℝ) (π / r) :=
      Ioo_mem_nhdsGT (by positivity)
    filter_upwards [hclose, harc] with θ hcθ hθ k hk
    have hτθ : 0 < ftTau a r (n - 1) θ :=
      ftTau_pos (ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ)
    refine pi_sub_ftAngle_le hτθ (ftArc_subset hr hθ) hc (le_trans hcθ ?_)
    exact hk₀min k (Finset.mem_compl.2 hk)

/-! ### Second order: `τ(δ) = x₁ + mδ + O(δ²)`

The identity `x₁/τ(θ) = cos θ - sin θ · cot β(θ)` is exact, so a *first-order*
bound on `β` gives a *second-order* bound on `τ`.  And `β` is governed by
`ρ β(θ) = rθ + (ρ-1)π + ∑_{k ∉ S} (π - θ_k)`, which contains no analysis at all:
the first bound below is a rearrangement of the angle count, not an estimate. -/

/-- **Step 1: the common angle is within `Kθ` of its limit.**  Pure arithmetic on
the angle count and `pi_sub_ftAngle_le`. -/
theorem eventually_abs_ftBranchAngle_sub_le {n r ρ : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ) (hρ : 2 ≤ ρ)
    (hmin : ∀ k, a i ≤ a k) {j : Fin n} (hj : j ∈ S) (hji : j ≠ i)
    {c : ℝ} (hc : 0 < c) (hgap : ∀ k ∉ S, a i * (1 + c) < a k) :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      |ftBranchAngle a r (n - 1) i θ - (π - π / ρ)|
        ≤ (((r : ℝ) + ((n : ℝ) - ρ) / c) / ρ) * θ := by
  have hn : 0 < n := by omega
  have hρ0 : (0 : ℝ) < ρ := by positivity
  have hρn : ρ ≤ n := by
    have h := Finset.card_le_univ S
    rw [Fintype.card_fin] at h
    exact hcard ▸ h
  have hcc : ((Sᶜ : Finset (Fin n)).card : ℝ) = (n : ℝ) - ρ := by
    rw [Finset.card_compl, Fintype.card_fin, hcard, Nat.cast_sub hρn]
  have harc : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo (0 : ℝ) (π / r) :=
    Ioo_mem_nhdsGT (by positivity)
  filter_upwards [eventually_pi_sub_ftAngle_le hn2 ha hr hS hmin hj hji hc hgap, harc,
    self_mem_nhdsWithin] with θ hrate hθ hθ0
  -- the count, rearranged
  have hbr := ftBranchAngle_count hn2 ha hr hS hcard hθ
  have hEdef : ∑ k ∈ Sᶜ, ftAngle (a k) (ftTau a r (n - 1) θ) θ
      = ((n : ℝ) - ρ) * π - ∑ k ∈ Sᶜ, (π - ftAngle (a k) (ftTau a r (n - 1) θ) θ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcc]
    ring
  set E : ℝ := ∑ k ∈ Sᶜ, (π - ftAngle (a k) (ftTau a r (n - 1) θ) θ) with hE
  have hE0 : 0 ≤ E := by
    refine Finset.sum_nonneg fun k _ => ?_
    linarith [ftAngle_lt_pi (a k) (ftTau a r (n - 1) θ) θ]
  have hEub : E ≤ ((n : ℝ) - ρ) * (θ / c) := by
    have := Finset.sum_le_sum (f := fun k => π - ftAngle (a k) (ftTau a r (n - 1) θ) θ)
      (g := fun _ : Fin n => θ / c)
      (fun k hk => hrate k (Finset.mem_compl.1 hk)) (s := (Sᶜ : Finset (Fin n)))
    rwa [Finset.sum_const, nsmul_eq_mul, hcc] at this
  rw [hEdef] at hbr
  have hval : ftBranchAngle a r (n - 1) i θ - (π - π / ρ) = ((r : ℝ) * θ + E) / ρ := by
    field_simp
    linarith [hbr]
  have hnn : 0 ≤ ((r : ℝ) * θ + E) / ρ := by
    refine div_nonneg ?_ hρ0.le
    have : 0 ≤ (r : ℝ) * θ := mul_nonneg (Nat.cast_nonneg r) hθ.1.le
    linarith
  rw [hval, abs_of_nonneg hnn]
  rw [div_le_iff₀ hρ0]
  have : ((r : ℝ) + ((n : ℝ) - ρ) / c) / ρ * θ * ρ = ((r : ℝ) + ((n : ℝ) - ρ) / c) * θ := by
    field_simp
  rw [this]
  have hnρ : (0 : ℝ) ≤ (n : ℝ) - ρ := by
    have : (ρ : ℝ) ≤ n := by exact_mod_cast hρn
    linarith
  calc (r : ℝ) * θ + E ≤ (r : ℝ) * θ + ((n : ℝ) - ρ) * (θ / c) := by linarith
    _ = ((r : ℝ) + ((n : ℝ) - ρ) / c) * θ := by field_simp

/-- **Step 2: the cotangent is Lipschitz where the angles live.**  An identity,
not a mean value argument. -/
theorem abs_cot_sub_cot_le {x y : ℝ} (hx : x ∈ Ioo 0 π) (hy : y ∈ Ioo 0 π) :
    |Real.cos x / Real.sin x - Real.cos y / Real.sin y|
      ≤ |x - y| / (Real.sin x * Real.sin y) := by
  have hsx : 0 < Real.sin x := sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsy : 0 < Real.sin y := sin_pos_of_pos_of_lt_pi hy.1 hy.2
  have hid : Real.cos x / Real.sin x - Real.cos y / Real.sin y
      = Real.sin (y - x) / (Real.sin x * Real.sin y) := by
    rw [Real.sin_sub]
    field_simp
  have hnum : |Real.sin (y - x)| ≤ |x - y| := by
    calc |Real.sin (y - x)| ≤ |y - x| := Real.abs_sin_le_abs
      _ = |x - y| := by rw [abs_sub_comm]
  rw [hid, abs_div, abs_of_pos (mul_pos hsx hsy),
    div_le_div_iff_of_pos_right (mul_pos hsx hsy)]
  exact hnum

/-- **Steps 1 and 2 combined.**  A function tracking a point of `(0, π)` to first
order in `θ` has its cotangent tracking that point's cotangent to the same order.
The sine in the denominator of `abs_cot_sub_cot_le` is bounded below because `B`
converges to `β₀`, where the sine is positive, so no separate hypothesis on `B`
is needed beyond staying in `(0, π)`. -/
theorem isBigO_cot_sub_cot_of_abs_sub_le {B : ℝ → ℝ} {β₀ κ : ℝ} (hβ₀ : β₀ ∈ Ioo 0 π)
    (hB : ∀ᶠ θ in 𝓝[>] (0 : ℝ), B θ ∈ Ioo 0 π)
    (hκ : ∀ᶠ θ in 𝓝[>] (0 : ℝ), |B θ - β₀| ≤ κ * θ) :
    (fun θ => Real.cos (B θ) / Real.sin (B θ) - Real.cos β₀ / Real.sin β₀)
      =O[𝓝[>] (0 : ℝ)] (fun θ : ℝ => θ) := by
  have hsβ₀ : 0 < Real.sin β₀ := sin_pos_of_pos_of_lt_pi hβ₀.1 hβ₀.2
  have hθ0 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), (0 : ℝ) < θ := self_mem_nhdsWithin
  have hidθ : Tendsto (fun θ : ℝ => θ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hBtend : Tendsto B (𝓝[>] (0 : ℝ)) (𝓝 β₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (by filter_upwards with θ using dist_nonneg) ?_
      (by simpa using hidθ.const_mul κ)
    filter_upwards [hκ] with θ h using by rwa [Real.dist_eq]
  have hsB : ∀ᶠ θ in 𝓝[>] (0 : ℝ), Real.sin β₀ / 2 ≤ Real.sin (B θ) := by
    have h := ((Real.continuous_sin.tendsto _).comp hBtend).eventually
      (eventually_gt_nhds (show Real.sin β₀ / 2 < Real.sin β₀ by linarith))
    filter_upwards [h] with θ hh using hh.le
  refine Asymptotics.IsBigO.of_bound (κ / (Real.sin β₀ / 2 * Real.sin β₀)) ?_
  filter_upwards [hκ, hB, hsB, hθ0] with θ h1 h2 h3 h4
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h4]
  have hnn : 0 ≤ κ * θ := le_trans (abs_nonneg _) h1
  have hsBpos : 0 < Real.sin (B θ) := lt_of_lt_of_le (by linarith) h3
  calc |Real.cos (B θ) / Real.sin (B θ) - Real.cos β₀ / Real.sin β₀|
      ≤ |B θ - β₀| / (Real.sin (B θ) * Real.sin β₀) := abs_cot_sub_cot_le h2 hβ₀
    _ ≤ (κ * θ) / (Real.sin (B θ) * Real.sin β₀) := by gcongr
    _ ≤ (κ * θ) / (Real.sin β₀ / 2 * Real.sin β₀) := by gcongr
    _ = κ / (Real.sin β₀ / 2 * Real.sin β₀) * θ := (div_mul_eq_mul_div _ _ _).symm

/-- **Step 3.**  The exact identity `x₁/τ(θ) = cos θ - sin θ · cot β(θ)` turns the
first-order control on `β` into second-order control on `τ`. -/
theorem isBigO_ftTau_sub_linear {n r ρ : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ) (hρ : 2 ≤ ρ)
    (hmin : ∀ k, a i ≤ a k) {j : Fin n} (hj : j ∈ S) (hji : j ≠ i)
    {c : ℝ} (hc : 0 < c) (hgap : ∀ k ∉ S, a i * (1 + c) < a k) :
    (fun θ => ftTau a r (n - 1) θ
        - (a i + a i * (Real.cos (π - π / ρ) / Real.sin (π - π / ρ)) * θ))
      =O[𝓝[>] (0 : ℝ)] (fun θ : ℝ => θ ^ 2) := by
  have hπ := pi_pos
  have hn : 0 < n := by omega
  have hai : 0 < a i := ha i
  have hρ0 : (0 : ℝ) < ρ := by positivity
  have hρR : (2 : ℝ) ≤ ρ := by exact_mod_cast hρ
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  set β₀ : ℝ := π - π / ρ with hβ₀
  set K₀ : ℝ := Real.cos β₀ / Real.sin β₀ with hK₀
  have hβ₀mem : β₀ ∈ Ioo (0 : ℝ) π := by
    constructor
    · have : π / ρ ≤ π / 2 := div_le_div_of_nonneg_left hπ.le (by norm_num) hρR
      simp only [hβ₀]; linarith
    · have : 0 < π / ρ := by positivity
      simp only [hβ₀]; linarith
  have hsβ₀ : 0 < Real.sin β₀ := sin_pos_of_pos_of_lt_pi hβ₀mem.1 hβ₀mem.2
  set B : ℝ → ℝ := fun θ => ftBranchAngle a r (n - 1) i θ with hB
  set T : ℝ → ℝ := fun θ => ftTau a r (n - 1) θ with hTdef
  set κ : ℝ := ((r : ℝ) + ((n : ℝ) - ρ) / c) / ρ with hκ
  -- step 1, and the resulting convergence of `B`
  have hstep1 : ∀ᶠ θ in l, |B θ - β₀| ≤ κ * θ :=
    eventually_abs_ftBranchAngle_sub_le hn2 ha hr hS hcard hρ hmin hj hji hc hgap
  have hθ0 : ∀ᶠ θ in l, (0 : ℝ) < θ := self_mem_nhdsWithin
  have hidθ : Tendsto (fun θ : ℝ => θ) l (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hBtend : Tendsto B l (𝓝 β₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (by filter_upwards with θ using dist_nonneg) ?_
      (by simpa using hidθ.const_mul κ)
    filter_upwards [hstep1] with θ h using by rwa [Real.dist_eq]
  have hKtend : Tendsto (fun θ => Real.cos (B θ) / Real.sin (B θ)) l (𝓝 K₀) :=
    ((Real.continuous_cos.tendsto _).comp hBtend).div
      ((Real.continuous_sin.tendsto _).comp hBtend) (ne_of_gt hsβ₀)
  have hTtend : Tendsto T l (𝓝 (a i)) :=
    tendsto_ftTau_nhdsGT_zero_of_repeated_min hn2 ha hr (Ne.symm hji) ((hS j).1 hj).symm hmin
  -- the exact identity
  have harc : ∀ᶠ θ in l, θ ∈ Ioo (0 : ℝ) (π / r) := Ioo_mem_nhdsGT (by positivity)
  have hTpos : ∀ᶠ θ in l, 0 < T θ := by
    filter_upwards [harc] with θ hθ
    exact ftTau_pos (ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθ)
  have hexact : ∀ᶠ θ in l, T θ - a i
      = T θ * (1 - Real.cos θ) + T θ * Real.sin θ * (Real.cos (B θ) / Real.sin (B θ)) := by
    filter_upwards [hTpos, harc] with θ hτθ hθ
    have hs : Real.sin θ ≠ 0 :=
      ne_of_gt (sin_pos_of_pos_of_lt_pi (ftArc_subset hr hθ).1 (ftArc_subset hr hθ).2)
    exact sub_eq_cot_ftAngle (a := a i) (ne_of_gt hτθ) hs
  -- elementary asymptotics
  have hOθ2θ : (fun θ : ℝ => θ ^ 2) =O[l] (fun θ : ℝ => θ) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hθ0, Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with θ h1 h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos h1 2), abs_of_pos h1, one_mul]
    nlinarith [h2.2]
  have hOcos : (fun θ : ℝ => 1 - Real.cos θ) =O[l] (fun θ : ℝ => θ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hθ0] with θ h1
    have h2 : (0 : ℝ) ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos h1 2), abs_of_nonneg h2, one_mul]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
  have hOsin : (fun θ : ℝ => Real.sin θ) =O[l] (fun θ : ℝ => θ) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards with θ
    simpa using Real.abs_sin_le_abs
  have hOsinsub : (fun θ : ℝ => Real.sin θ - θ) =O[l] (fun θ : ℝ => θ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hθ0, Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with θ h1 hlt1
    have h2 : Real.sin θ - θ ≤ 0 := by linarith [Real.sin_lt h1]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos h1 2), abs_of_nonpos h2, one_mul]
    nlinarith [Real.sin_gt_sub_cube h1, hlt1.2]
  have hTb : T =O[l] (fun _ : ℝ => (1 : ℝ)) := hTtend.isBigO_one ℝ
  have hKb : (fun θ => Real.cos (B θ) / Real.sin (B θ)) =O[l] (fun _ : ℝ => (1 : ℝ)) :=
    hKtend.isBigO_one ℝ
  -- `τ - x₁ = O(θ)`
  have hOA : (fun θ => T θ * (1 - Real.cos θ)) =O[l] (fun θ : ℝ => θ ^ 2) :=
    (hTb.mul hOcos).congr_right fun θ => one_mul _
  have hOB2 : (fun θ => T θ * Real.sin θ * (Real.cos (B θ) / Real.sin (B θ)))
      =O[l] (fun θ : ℝ => θ) :=
    ((hTb.mul hOsin).mul hKb).congr_right fun θ => by ring
  have hOT : (fun θ => T θ - a i) =O[l] (fun θ : ℝ => θ) := by
    refine Asymptotics.IsBigO.congr' ?_ (hexact.mono fun θ h => h.symm) EventuallyEq.rfl
    exact (hOA.trans hOθ2θ).add hOB2
  -- `cot B - K₀ = O(θ)`
  have hOK : (fun θ => Real.cos (B θ) / Real.sin (B θ) - K₀) =O[l] (fun θ : ℝ => θ) := by
    have hBmem : ∀ᶠ θ in l, B θ ∈ Ioo (0 : ℝ) π := by
      filter_upwards [hTpos, harc] with θ hτθ hθ
      exact ⟨lt_trans (ftArc_subset hr hθ).1 (ftAngle_mem_Ioo hai hτθ (ftArc_subset hr hθ)).1,
        ftAngle_lt_pi _ _ _⟩
    exact isBigO_cot_sub_cot_of_abs_sub_le hβ₀mem hBmem hstep1
  -- assemble
  have hdecomp : ∀ᶠ θ in l, T θ - (a i + a i * K₀ * θ)
      = T θ * (1 - Real.cos θ)
        + ((T θ - a i) * Real.sin θ + a i * (Real.sin θ - θ))
            * (Real.cos (B θ) / Real.sin (B θ))
        + a i * (θ * (Real.cos (B θ) / Real.sin (B θ) - K₀)) := by
    filter_upwards [hexact] with θ h
    linear_combination h
  have hmid : (fun θ => ((T θ - a i) * Real.sin θ + a i * (Real.sin θ - θ))
      * (Real.cos (B θ) / Real.sin (B θ))) =O[l] (fun θ : ℝ => θ ^ 2) := by
    have h1 : (fun θ => (T θ - a i) * Real.sin θ) =O[l] (fun θ : ℝ => θ ^ 2) :=
      (hOT.mul hOsin).congr_right fun θ => (sq θ).symm
    have h2 : (fun θ : ℝ => a i * (Real.sin θ - θ)) =O[l] (fun θ : ℝ => θ ^ 2) :=
      hOsinsub.const_mul_left (a i)
    exact ((h1.add h2).mul hKb).congr_right fun θ => by ring
  have hlast : (fun θ => a i * (θ * (Real.cos (B θ) / Real.sin (B θ) - K₀)))
      =O[l] (fun θ : ℝ => θ ^ 2) :=
    (((Asymptotics.isBigO_refl (fun θ : ℝ => θ) l).mul hOK).congr_right
      fun θ => (sq θ).symm).const_mul_left (a i)
  exact Asymptotics.IsBigO.congr' ((hOA.add hmid).add hlast)
    (hdecomp.mono fun θ h => h.symm) EventuallyEq.rfl

/-- **`Forgacs2017RationalDenominator` Proposition 3, Case 2: the analytic core.**
`|τ(δ) - (x₁ - x₁cos(π/ρ)/sin(π/ρ)·δ)| ≤ C δ²` on `(0, ε]`, in the shape the
expansion of the principal point consumes. -/
theorem exists_bound_ftTau_sub_linear {n r ρ : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ) (hρ : 2 ≤ ρ)
    (hmin : ∀ k, a i ≤ a k) {j : Fin n} (hj : j ∈ S) (hji : j ≠ i)
    {c : ℝ} (hc : 0 < c) (hgap : ∀ k ∉ S, a i * (1 + c) < a k) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      |ftTau a r (n - 1) δ
        - (a i - a i * Real.cos (π / ρ) / Real.sin (π / ρ) * δ)| ≤ C * δ ^ 2 := by
  have hO := isBigO_ftTau_sub_linear hn2 ha hr hS hcard hρ hmin hj hji hc hgap
  obtain ⟨C₀, hC₀⟩ := Asymptotics.isBigO_iff.1 hO
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hC₀
  rw [mem_Ioi] at hε₀
  refine ⟨max C₀ 1, ε₀ / 2, lt_of_lt_of_le one_pos (le_max_right _ _), by linarith, ?_⟩
  intro δ hδ0 hδε
  have hmem : δ ∈ Ioo (0 : ℝ) ε₀ := ⟨hδ0, by linarith⟩
  have h := hsub hmem
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs] at h
  rw [abs_of_pos (pow_pos hδ0 2)] at h
  have hrw : a i - a i * Real.cos (π / ρ) / Real.sin (π / ρ) * δ
      = a i + a i * (Real.cos (π - π / ρ) / Real.sin (π - π / ρ)) * δ := by
    rw [Real.cos_pi_sub, Real.sin_pi_sub]
    ring
  rw [hrw]
  exact le_trans h (by nlinarith [le_max_left C₀ 1, pow_pos hδ0 2])

/-- A concrete instance: `Q(t) = (1-t)²(3-t)`, `ρ = 2`, `r = 1`.  Compiling this
is what turns "the shapes match" into a fact. -/
example : ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε →
    |ftTau (fun k : Fin 3 => if k = 2 then (3 : ℝ) else 1) 1 (3 - 1) δ
      - ((1 : ℝ) - (1 : ℝ) * Real.cos (π / 2) / Real.sin (π / 2) * δ)| ≤ C * δ ^ 2 := by
  classical
  set a : Fin 3 → ℝ := fun k => if k = 2 then (3 : ℝ) else 1 with hadef
  have hai : a 0 = 1 := by simp [hadef]
  have hS : ∀ k, k ∈ ({0, 1} : Finset (Fin 3)) ↔ a k = a 0 := by
    intro k
    fin_cases k <;> simp [hadef]
  have hmin : ∀ k, a 0 ≤ a k := by
    intro k; fin_cases k <;> simp [hadef]
  have hgap : ∀ k ∉ ({0, 1} : Finset (Fin 3)), a 0 * (1 + (1 : ℝ)) < a k := by
    intro k hk
    fin_cases k <;> simp_all
    norm_num
  have hpos : ∀ k, 0 < a k := by
    intro k; fin_cases k <;> simp [hadef]
  have h := exists_bound_ftTau_sub_linear (n := 3) (r := 1) (ρ := 2) (a := a)
    (S := ({0, 1} : Finset (Fin 3))) (by norm_num) hpos le_rfl hS (by decide) le_rfl
    hmin (j := 1) (by decide) (by decide) (c := 1) one_pos hgap
  simpa [hai] using h

end ForgacsTran
