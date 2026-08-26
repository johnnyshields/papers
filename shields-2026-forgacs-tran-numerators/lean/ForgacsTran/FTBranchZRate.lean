/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchGap
import ForgacsTran.FTBranchProp1

/-!
# The rate of the spectral parameter along the branch

The member leg of Prop. 3 Case 2 needs each cluster member's crude size, and
`Cluster.norm_cluster_root` turns that into a rate on the spectral parameter
itself: `‖z(δ)‖ = O(δ^ρ)` where `ρ` is the multiplicity of the smallest zero.
That is a statement about the branch, so it is proved here.

## Main statements

* `isBigO_ftTau_sub_min` — the crude first-order rate `τ(θ) - x₁ = O(θ)`,
  extracted from the slope limit.
* `isBigO_ftChordProd_pow` — the chord product is `O(θ^ρ)`: the `ρ` chords at the
  repeated zero are each `O(θ)` and the rest are bounded.
* `isBigO_ftBranchZ_pow` and `exists_bound_ftBranchZ_pow` — the rate itself, and
  the `∃ C ε` form a consumer takes as a hypothesis.
* `tendsto_sqrt_chordSq_div_of_slope`, `tendsto_sqrt_chordSq_of_le`,
  `sqrt_sq_add_sq_neg_mul_cot` — the two limits a chord can have at the endpoint,
  and the closed form `x₁/sin(π/ρ)` of the first one's rate.  None mentions the
  branch.

## Implementation notes

**Differs from the paper's route.**  `Forgacs2017RationalDenominator` reads the
size of `z` off the expansion of the cluster, which is circular here: the
expansion is what the rate is wanted for.  The route taken instead uses only the
PRINCIPAL point, whose rate is already proved -- the chord to a repeated zero is
`√((x₁ - τ)² + 2x₁τ(1 - cos θ))`, and both terms are `O(θ²)` from `τ - x₁ = O(θ)`
and `1 - cos θ = O(θ²)` alone.  No cluster member enters, so nothing is assumed
that the conclusion supplies.

`tendsto_sin_div_nhdsGT_zero` and `tendsto_one_sub_cos_div_sq_nhdsGT_zero` are
Mathlib-level and carry nothing specific to this paper; either is reusable as it
stands.

Sorry-free.

## Tags

spectral parameter, rate, endpoint asymptotics
-/

namespace ForgacsTran

open Real Set Filter Topology Asymptotics

/-- **The crude first-order rate.**  `τ(θ) - x₁ = O(θ)`, which is all the chord
bound needs; the second-order form is `exists_bound_ftTau_sub_linear`. -/
theorem isBigO_ftTau_sub_min {n r ρ : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ) (hρ : 2 ≤ ρ)
    (hmin : ∀ k, a i ≤ a k) :
    (fun θ => ftTau a r (n - 1) θ - a i) =O[𝓝[>] (0 : ℝ)] (fun θ : ℝ => θ) := by
  have h := (tendsto_ftTau_slope_nhdsGT_zero hn2 ha hr hS hcard hρ hmin).isBigO_one ℝ
  have h2 := h.mul (isBigO_refl (fun θ : ℝ => θ) (𝓝[>] (0 : ℝ)))
  refine h2.congr' ?_ (by filter_upwards with θ; simp)
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have : θ ≠ 0 := ne_of_gt hθ
  field_simp

/-- **The chord product carries the multiplicity.**  Each of the `ρ` chords to
the repeated smallest zero is `O(θ)`; the remaining `n - ρ` are bounded. -/
theorem isBigO_ftChordProd_pow {n r ρ : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ) (hρ : 2 ≤ ρ)
    (hmin : ∀ k, a i ≤ a k) :
    (fun θ => ftChordProd a (ftTau a r (n - 1) θ) θ)
      =O[𝓝[>] (0 : ℝ)] (fun θ : ℝ => θ ^ ρ) := by
  have hai : 0 < a i := ha i
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  set T : ℝ → ℝ := fun θ => ftTau a r (n - 1) θ with hT
  have hiS : i ∈ S := (hS i).2 rfl
  obtain ⟨j, hj⟩ : (S.erase i).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hiS, hcard]; omega
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  have hjS : j ∈ S := Finset.mem_of_mem_erase hj
  have haij : a i = a j := ((hS j).1 hjS).symm
  obtain ⟨A, hAnn, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ θ in l, ‖T θ - a i‖ ≤ A * ‖θ‖ := by
    obtain ⟨A, hA⟩ := (isBigO_ftTau_sub_min hn2 ha hr hS hcard hρ hmin).bound
    exact ⟨max A 0, le_max_right _ _, hA.mono fun θ h =>
      le_trans h (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩
  have hTlim : Tendsto T l (𝓝 (a i)) :=
    tendsto_ftTau_nhdsGT_zero_of_repeated_min hn2 ha hr (Ne.symm hji) haij hmin
  have hTub : ∀ᶠ θ in l, T θ ≤ 2 * a i := by
    have := hTlim.eventually (eventually_lt_nhds (by linarith : a i < 2 * a i))
    filter_upwards [this] with θ h using h.le
  -- the constants
  set A₁ : ℝ := Real.sqrt (A ^ 2 + 2 * a i ^ 2) with hA₁
  have hA₁nn : 0 ≤ A₁ := Real.sqrt_nonneg _
  set B : ℝ := ∏ k ∈ Sᶜ, (a k + 2 * a i) with hB
  have hBnn : 0 ≤ B := Finset.prod_nonneg fun k _ => by linarith [ha k]
  rw [isBigO_iff]
  refine ⟨A₁ ^ ρ * B, ?_⟩
  filter_upwards [hA, hTub, self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (div_pos pi_pos (by exact_mod_cast Nat.lt_of_lt_of_le one_pos hr :
      (0 : ℝ) < r))] with θ hAθ hub hθ0 hθarc
  replace hθ0 : (0 : ℝ) < θ := hθ0
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθarc
  have hb : FTBranchAt a r (n - 1) θ :=
    ftBranchAt_of_arc_principal (by omega) ha hr (Or.inl hn2) hθarc
  have hTpos : 0 < T θ := ftTau_pos hb
  have hcos : 1 - Real.cos θ ≤ θ ^ 2 / 2 := one_sub_cos_le_sq_div_two θ
  -- the `ρ` chords at the repeated zero
  have hin : ∀ k ∈ S, Real.sqrt (a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2) ≤ A₁ * θ := by
    intro k hk
    have hak : a k = a i := (hS k).1 hk
    have hrad : a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2
        = (a i - T θ) ^ 2 + 2 * a i * T θ * (1 - Real.cos θ) := by
      rw [hak]; exact chordSq_eq_sub_sq_add (a i) (T θ) θ
    have hsq : a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2 ≤ (A₁ * θ) ^ 2 := by
      have h1 : (a i - T θ) ^ 2 ≤ A ^ 2 * θ ^ 2 := by
        have := hAθ
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hθ0] at this
        nlinarith [abs_nonneg (T θ - a i), sq_abs (T θ - a i)]
      have h2 : 2 * a i * T θ * (1 - Real.cos θ) ≤ 2 * a i ^ 2 * θ ^ 2 := by
        have hcnn : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
        calc 2 * a i * T θ * (1 - Real.cos θ)
            ≤ 2 * a i * (2 * a i) * (θ ^ 2 / 2) := by
              refine mul_le_mul ?_ hcos hcnn (by positivity)
              exact mul_le_mul_of_nonneg_left hub (by linarith)
          _ = 2 * a i ^ 2 * θ ^ 2 := by ring
      have hA₁sq : A₁ ^ 2 = A ^ 2 + 2 * a i ^ 2 :=
        Real.sq_sqrt (by positivity)
      rw [hrad]
      nlinarith
    calc Real.sqrt (a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2)
        ≤ Real.sqrt ((A₁ * θ) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = A₁ * θ := Real.sqrt_sq (by positivity)
  -- the remaining chords are bounded
  have hout : ∀ k ∈ Sᶜ, Real.sqrt (a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2)
      ≤ a k + 2 * a i := by
    intro k _
    have hsq : a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2 ≤ (a k + 2 * a i) ^ 2 := by
      have hkT : a k * T θ ≤ a k * (2 * a i) := mul_le_mul_of_nonneg_left hub (ha k).le
      have hTT : T θ * T θ ≤ 2 * a i * (2 * a i) := mul_self_le_mul_self hTpos.le hub
      nlinarith [Real.neg_one_le_cos θ, mul_pos (ha k) hTpos]
    calc Real.sqrt (a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2)
        ≤ Real.sqrt ((a k + 2 * a i) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = a k + 2 * a i := Real.sqrt_sq (by linarith [ha k])
  -- assemble
  have hsplit : ftChordProd a (T θ) θ
      = (∏ k ∈ S, Real.sqrt (a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2))
        * ∏ k ∈ Sᶜ, Real.sqrt (a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2) := by
    rw [ftChordProd, ← Finset.prod_mul_prod_compl S]
  have hSle : (∏ k ∈ S, Real.sqrt (a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2))
      ≤ A₁ ^ ρ * θ ^ ρ := by
    calc (∏ k ∈ S, Real.sqrt (a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2))
        ≤ ∏ _k ∈ S, A₁ * θ :=
          Finset.prod_le_prod (fun k _ => Real.sqrt_nonneg _) hin
      _ = A₁ ^ ρ * θ ^ ρ := by rw [Finset.prod_const, hcard, mul_pow]
  have hCle : (∏ k ∈ Sᶜ, Real.sqrt (a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2)) ≤ B := by
    exact Finset.prod_le_prod (fun k _ => Real.sqrt_nonneg _) hout
  have hpos : 0 < ftChordProd a (T θ) θ := ftChordProd_pos ha hTpos hθπ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos, abs_of_pos (by positivity)]
  have hnn1 : 0 ≤ ∏ k ∈ S, Real.sqrt (a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2) :=
    Finset.prod_nonneg fun k _ => Real.sqrt_nonneg _
  have hnn2 : 0 ≤ ∏ k ∈ Sᶜ, Real.sqrt (a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2) :=
    Finset.prod_nonneg fun k _ => Real.sqrt_nonneg _
  rw [hsplit]
  calc (∏ k ∈ S, Real.sqrt (a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2))
        * ∏ k ∈ Sᶜ, Real.sqrt (a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2)
      ≤ (A₁ ^ ρ * θ ^ ρ) * B := by
        apply mul_le_mul hSle hCle hnn2 (by positivity)
    _ = A₁ ^ ρ * B * θ ^ ρ := by ring

/-- **`‖z(δ)‖ = O(δ^ρ)`.**  The spectral parameter along the branch inherits the
multiplicity of the smallest zero. -/
theorem isBigO_ftBranchZ_pow {n r ρ : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ) (hρ : 2 ≤ ρ)
    (hmin : ∀ k, a i ≤ a k) (c : ℝ) :
    (fun θ => ftBranchZ a c r (n - 1) θ) =O[𝓝[>] (0 : ℝ)] (fun θ : ℝ => θ ^ ρ) := by
  have hai : 0 < a i := ha i
  have hiS : i ∈ S := (hS i).2 rfl
  obtain ⟨j, hj⟩ : (S.erase i).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hiS, hcard]; omega
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  have hjS : j ∈ S := Finset.mem_of_mem_erase hj
  have haij : a i = a j := ((hS j).1 hjS).symm
  obtain ⟨M, hMnn, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      ‖ftChordProd a (ftTau a r (n - 1) θ) θ‖ ≤ M * ‖θ ^ ρ‖ := by
    obtain ⟨M, hM⟩ := (isBigO_ftChordProd_pow hn2 ha hr hS hcard hρ hmin).bound
    exact ⟨max M 0, le_max_right _ _, hM.mono fun θ h =>
      le_trans h (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩
  have hTlim : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 (a i)) :=
    tendsto_ftTau_nhdsGT_zero_of_repeated_min hn2 ha hr (Ne.symm hji) haij hmin
  have hTlb : ∀ᶠ θ in 𝓝[>] (0 : ℝ), a i / 2 ≤ ftTau a r (n - 1) θ := by
    have := hTlim.eventually (eventually_gt_nhds (by linarith : a i / 2 < a i))
    filter_upwards [this] with θ h using h.le
  rw [isBigO_iff]
  refine ⟨|c| * M / (a i / 2) ^ r, ?_⟩
  filter_upwards [hM, hTlb, self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (div_pos pi_pos (by exact_mod_cast Nat.lt_of_lt_of_le one_pos hr :
      (0 : ℝ) < r))] with θ hMθ hlb hθ0 hθarc
  replace hθ0 : (0 : ℝ) < θ := hθ0
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθarc
  have hb : FTBranchAt a r (n - 1) θ :=
    ftBranchAt_of_arc_principal (by omega) ha hr (Or.inl hn2) hθarc
  have hTpos : 0 < ftTau a r (n - 1) θ := ftTau_pos hb
  have hprod : (∏ k, ftChord (a k) θ (ftBranchAngle a r (n - 1) k θ))
      = ftChordProd a (ftTau a r (n - 1) θ) θ := by
    rw [show (∏ k, ftChord (a k) θ (ftBranchAngle a r (n - 1) k θ))
        = ∏ k, ftChord (a k) θ (ftAngle (a k) (ftTau a r (n - 1) θ) θ) from
      Finset.prod_congr rfl fun k _ => by rw [ftBranchAngle]]
    exact prod_ftChord_eq_ftChordProd ha hTpos hθπ
  have hcpos : 0 < ftChordProd a (ftTau a r (n - 1) θ) θ := ftChordProd_pos ha hTpos hθπ
  have habs : ‖ftBranchZ a c r (n - 1) θ‖
      = |c| * ftChordProd a (ftTau a r (n - 1) θ) θ / ftTau a r (n - 1) θ ^ r := by
    have hτr : (0 : ℝ) < ftTau a r (n - 1) θ ^ r := pow_pos hTpos r
    rw [Real.norm_eq_abs, ftBranchZ, hprod, abs_div, abs_of_pos hτr]
    congr 1
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hcpos]
  rw [habs, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < θ ^ ρ)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hcpos,
    abs_of_pos (by positivity : (0:ℝ) < θ ^ ρ)] at hMθ
  have hden : (a i / 2) ^ r ≤ ftTau a r (n - 1) θ ^ r := by
    exact pow_le_pow_left₀ (by linarith) hlb r
  have hdpos : (0 : ℝ) < (a i / 2) ^ r := by positivity
  rw [div_le_iff₀ (by positivity : (0:ℝ) < ftTau a r (n - 1) θ ^ r)]
  calc |c| * ftChordProd a (ftTau a r (n - 1) θ) θ
      ≤ |c| * (M * θ ^ ρ) := by
        exact mul_le_mul_of_nonneg_left hMθ (abs_nonneg c)
    _ = (|c| * M / (a i / 2) ^ r * θ ^ ρ) * (a i / 2) ^ r := by field_simp
    _ ≤ (|c| * M / (a i / 2) ^ r * θ ^ ρ) * ftTau a r (n - 1) θ ^ r := by
        refine mul_le_mul_of_nonneg_left hden ?_
        positivity

/-- The `∃ C ε` form, in the shape a consumer takes as a hypothesis. -/
theorem exists_bound_ftBranchZ_pow {n r ρ : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ) (hρ : 2 ≤ ρ)
    (hmin : ∀ k, a i ≤ a k) (c : ℝ) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      |ftBranchZ a c r (n - 1) δ| ≤ C * δ ^ ρ := by
  obtain ⟨C₀, hC₀⟩ :=
    isBigO_iff.1 (isBigO_ftBranchZ_pow hn2 ha hr hS hcard hρ hmin c)
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hC₀
  rw [mem_Ioi] at hε₀
  refine ⟨max C₀ 1, ε₀ / 2, lt_of_lt_of_le one_pos (le_max_right _ _), by linarith, ?_⟩
  intro δ hδ0 hδε
  have h := hsub ⟨hδ0, by linarith⟩
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs] at h
  rw [abs_of_pos (by positivity : (0:ℝ) < δ ^ ρ)] at h
  exact le_trans h (by nlinarith [le_max_left C₀ 1, pow_pos hδ0 ρ])

/-- `sin θ / θ → 1` as `θ → 0⁺`, from the derivative of `sin` at `0`. -/
theorem tendsto_sin_div_nhdsGT_zero :
    Tendsto (fun θ : ℝ => Real.sin θ / θ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h : HasDerivAt Real.sin 1 0 := by simpa using Real.hasDerivAt_sin 0
  have h3 : Tendsto (slope Real.sin 0) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    (hasDerivAt_iff_tendsto_slope.1 h).mono_left
      (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  refine h3.congr fun θ => ?_
  simp [slope_def_field, div_eq_inv_mul]

/-- `(1 - cos θ)/θ² → 1/2`, through the half angle. -/
theorem tendsto_one_sub_cos_div_sq_nhdsGT_zero :
    Tendsto (fun θ : ℝ => (1 - Real.cos θ) / θ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2)) := by
  have hhalf : Tendsto (fun θ : ℝ => θ / 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hid : Tendsto (fun θ : ℝ => θ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using hid.div_const 2
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact mem_Ioi.2 (by linarith [mem_Ioi.1 hθ])
  have h : Tendsto (fun θ : ℝ => Real.sin (θ / 2) / (θ / 2)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa [Function.comp_def] using tendsto_sin_div_nhdsGT_zero.comp hhalf
  have h2 : Tendsto (fun θ : ℝ => (Real.sin (θ / 2) / (θ / 2)) ^ 2 / 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2)) := by simpa using (h.pow 2).div_const 2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ0 : (0 : ℝ) < θ := hθ
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have hd := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at hd
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  rw [hcos]
  field

/-! ### The two chord limits

`ftChordProd` is a product of chords, and at the endpoint they fall into two
kinds: the `ρ` at the repeated smallest zero, which collapse at a definite linear
rate, and the rest, which converge to their gaps.  Both are stated here without
any branch in them — what they take is a function converging to `x` and, for the
first, its slope. -/

/-- **A chord to the limit point grows linearly, at rate `√(m² + x²)`.**  For `T`
converging to `x` with slope `m`, the chord from `x` to `T(θ)e^{iθ}` is
`θ√(m² + x²) + o(θ)`: `chordSq_eq_sub_sq_add` splits it into the radial
displacement `mθ + o(θ)` and the angular one, whose square is
`2xT(θ)(1 - cos θ) = x²θ² + o(θ²)`, and the chord is the hypotenuse. -/
theorem tendsto_sqrt_chordSq_div_of_slope {T : ℝ → ℝ} {x m : ℝ}
    (hT : Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 x))
    (hslope : Tendsto (fun θ => (T θ - x) / θ) (𝓝[>] (0 : ℝ)) (𝓝 m)) :
    Tendsto (fun θ => Real.sqrt (x ^ 2 - 2 * x * T θ * Real.cos θ + T θ ^ 2) / θ)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt (m ^ 2 + x ^ 2))) := by
  have h1 : Tendsto (fun θ : ℝ => ((x - T θ) / θ) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (m ^ 2)) := by
    have h0 : Tendsto (fun θ : ℝ => (x - T θ) / θ) (𝓝[>] (0 : ℝ)) (𝓝 (-m)) := by
      refine hslope.neg.congr fun θ => ?_
      rw [← neg_div, neg_sub]
    simpa [neg_sq] using h0.pow 2
  have h2 : Tendsto (fun θ : ℝ => 2 * x * T θ * ((1 - Real.cos θ) / θ ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (x ^ 2)) := by
    have h0 := (hT.const_mul (2 * x)).mul tendsto_one_sub_cos_div_sq_nhdsGT_zero
    have heq : 2 * x * x * (1 / 2 : ℝ) = x ^ 2 := by ring
    rwa [heq] at h0
  have hsqrt := (Real.continuous_sqrt.tendsto (m ^ 2 + x ^ 2)).comp (h1.add h2)
  rw [Function.comp_def] at hsqrt
  refine hsqrt.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ0 : (0 : ℝ) < θ := hθ
  have hin2 : ((x - T θ) / θ) ^ 2 + 2 * x * T θ * ((1 - Real.cos θ) / θ ^ 2)
      = (x ^ 2 - 2 * x * T θ * Real.cos θ + T θ ^ 2) / θ ^ 2 := by
    field_simp; ring
  rw [hin2, Real.sqrt_div (chordSq_nonneg x (T θ) θ), Real.sqrt_sq hθ0.le]

/-- **A chord to a zero the limit point falls short of converges to the gap.**
No rate is involved: continuity of the radicand and `cos θ → 1` are all it takes. -/
theorem tendsto_sqrt_chordSq_of_le {T : ℝ → ℝ} {a x : ℝ} (hx : x ≤ a)
    (hT : Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 x)) :
    Tendsto (fun θ => Real.sqrt (a ^ 2 - 2 * a * T θ * Real.cos θ + T θ ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (a - x)) := by
  have hcos1 : Tendsto (fun θ : ℝ => Real.cos θ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using (Real.continuous_cos.tendsto 0).comp (tendsto_id.mono_left nhdsWithin_le_nhds)
  have h0 : Tendsto (fun θ => a ^ 2 - 2 * a * T θ * Real.cos θ + T θ ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (a ^ 2 - 2 * a * x * 1 + x ^ 2)) :=
    (tendsto_const_nhds.sub ((hT.const_mul (2 * a)).mul hcos1)).add (hT.pow 2)
  rw [show a ^ 2 - 2 * a * x * 1 + x ^ 2 = (a - x) ^ 2 by ring] at h0
  have hsqrt := (Real.continuous_sqrt.tendsto ((a - x) ^ 2)).comp h0
  rwa [Function.comp_def, Real.sqrt_sq (by linarith)] at hsqrt

/-- **The chord rate in closed form.**  With the endpoint slope `m = -x cot φ`
of `FTBranchLimitPoint.tendsto_ftTau_slope_nhdsGT_zero`, the rate `√(m² + x²)` is
`x/sin φ`.  This is where the paper's `x_1/sin(π/ρ)` comes from. -/
theorem sqrt_sq_add_sq_neg_mul_cot {x φ : ℝ} (hx : 0 < x) (hs : 0 < Real.sin φ) :
    Real.sqrt ((-x * Real.cos φ / Real.sin φ) ^ 2 + x ^ 2) = x / Real.sin φ := by
  rw [show (-x * Real.cos φ / Real.sin φ) ^ 2 + x ^ 2 = (x / Real.sin φ) ^ 2 by
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq φ, sq_nonneg x, hs]]
  exact Real.sqrt_sq (by positivity)

/-- **The spectral parameter has a nonzero limit after rescaling.**  The `ρ`
chords at the repeated smallest zero each contribute a factor `θ`, and what is
left over converges to something strictly positive.  This is what stops the
rescaled Rouché model degenerating to a `ρ`-fold root at the origin: an upper
bound `|z| = O(δ^ρ)` alone does not exclude `z/δ^ρ → 0`.

The limit is stated **at its value**, because the Rouché model needs the
cluster directions to be its own roots: `q(x₁)·α₁^ρ + z₀·x₁^r = 0` holds
exactly for this `z₀`, and a value correct only in modulus would satisfy
positivity and fail that equation.  `exists_tendsto_ftBranchZ_div_pow` keeps the
`0 < z₀` form for consumers that need nothing more. -/
theorem tendsto_ftBranchZ_div_pow {n r ρ : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ) (hρ : 2 ≤ ρ)
    (hmin : ∀ k, a i ≤ a k) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun δ => ftBranchZ a c r (n - 1) δ / δ ^ ρ) (𝓝[>] (0 : ℝ))
      (𝓝 (c * ((a i / Real.sin (π / ρ)) ^ ρ * ∏ k ∈ Sᶜ, (a k - a i)) / a i ^ r)) := by
  have hai : 0 < a i := ha i
  have hn : 0 < n := by omega
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  set T : ℝ → ℝ := fun θ => ftTau a r (n - 1) θ with hT
  have hiS : i ∈ S := (hS i).2 rfl
  obtain ⟨j, hj⟩ : (S.erase i).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hiS, hcard]; omega
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  have hjS : j ∈ S := Finset.mem_of_mem_erase hj
  have haij : a i = a j := ((hS j).1 hjS).symm
  have hTlim : Tendsto T l (𝓝 (a i)) :=
    tendsto_ftTau_nhdsGT_zero_of_repeated_min hn2 ha hr (Ne.symm hji) haij hmin
  set m : ℝ := -(a i) * Real.cos (π / ρ) / Real.sin (π / ρ) with hm
  have hslope : Tendsto (fun θ => (T θ - a i) / θ) l (𝓝 m) :=
    tendsto_ftTau_slope_nhdsGT_zero hn2 ha hr hS hcard hρ hmin
  set A : ℝ := Real.sqrt (m ^ 2 + a i ^ 2) with hA
  have hApos : 0 < A := Real.sqrt_pos.2 (by positivity)
  -- the `ρ` chords at the repeated zero, each divided by `θ`
  have hchordS : ∀ k ∈ S, Tendsto
      (fun θ => Real.sqrt (a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2) / θ) l (𝓝 A) := by
    intro k hk
    rw [(hS k).1 hk, hA]
    exact tendsto_sqrt_chordSq_div_of_slope hTlim hslope
  -- the remaining chords converge to their gaps
  have hgap : ∀ k ∉ S, a i < a k := by
    intro k hk
    rcases lt_or_eq_of_le (hmin k) with h | h
    · exact h
    · exact absurd ((hS k).2 h.symm) hk
  have hchordC : ∀ k ∈ Sᶜ, Tendsto
      (fun θ => Real.sqrt (a k ^ 2 - 2 * a k * T θ * Real.cos θ + T θ ^ 2)) l
      (𝓝 (a k - a i)) := fun k hk =>
    tendsto_sqrt_chordSq_of_le (hgap k (Finset.mem_compl.1 hk)).le hTlim
  set B : ℝ := ∏ k ∈ Sᶜ, (a k - a i) with hB
  have hBpos : 0 < B := Finset.prod_pos fun k hk =>
    sub_pos.2 (hgap k (Finset.mem_compl.1 hk))
  have hprodlim : Tendsto (fun θ => ftChordProd a (T θ) θ / θ ^ ρ) l (𝓝 (A ^ ρ * B)) := by
    have h3 := (tendsto_finsetProd S hchordS).mul (tendsto_finsetProd Sᶜ hchordC)
    rw [Finset.prod_const, hcard] at h3
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hθ0 : (0 : ℝ) < θ := hθ
    rw [ftChordProd, ← Finset.prod_mul_prod_compl S, Finset.prod_div_distrib,
      Finset.prod_const, hcard]
    field_simp
  have hρR : (2 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hπρ : π / ρ ∈ Ioo 0 π := by
    constructor
    · positivity
    · have : π / ρ ≤ π / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith [pi_pos]
      linarith [pi_pos]
  have hsρ : 0 < Real.sin (π / ρ) := Real.sin_pos_of_pos_of_lt_pi hπρ.1 hπρ.2
  have hAval : A = a i / Real.sin (π / ρ) := by
    rw [hA, hm]; exact sqrt_sq_add_sq_neg_mul_cot hai hsρ
  rw [show c * ((a i / Real.sin (π / ρ)) ^ ρ * ∏ k ∈ Sᶜ, (a k - a i)) / a i ^ r
      = c * (A ^ ρ * B) / a i ^ r by rw [← hAval, ← hB]]
  have hfinal := (hprodlim.const_mul c).div (hTlim.pow r) (by positivity)
  refine hfinal.congr' ?_
  have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le one_pos hr
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (div_pos pi_pos hr0)] with θ hθ hθarc
  have hθ0 : (0 : ℝ) < θ := hθ
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθarc
  have hb : FTBranchAt a r (n - 1) θ :=
    ftBranchAt_of_arc_principal hn ha hr (Or.inl hn2) hθarc
  have hTpos : 0 < T θ := ftTau_pos hb
  have hpar : Even (n + (n - 1) + 1) := ⟨n, by omega⟩
  have h1 : (θ : ℝ) ^ ρ ≠ 0 := pow_ne_zero _ (ne_of_gt hθ0)
  have h2 : T θ ^ r ≠ 0 := pow_ne_zero _ (ne_of_gt hTpos)
  have hkey : c * (ftChordProd a (T θ) θ / θ ^ ρ) / T θ ^ r
      = c * ftChordProd a (T θ) θ / T θ ^ r / θ ^ ρ := by field_simp
  simp only [Pi.div_apply]
  rw [ftBranchZ_eq_chordProd ha hpar hθπ hb rfl]
  exact hkey

/-- The `0 < z₀` form, for consumers that need only nonvanishing. -/
theorem exists_tendsto_ftBranchZ_div_pow {n r ρ : ℕ} {a : Fin n → ℝ} {S : Finset (Fin n)}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {i : Fin n}
    (hS : ∀ k, k ∈ S ↔ a k = a i) (hcard : S.card = ρ) (hρ : 2 ≤ ρ)
    (hmin : ∀ k, a i ≤ a k) {c : ℝ} (hc : 0 < c) :
    ∃ z₀ : ℝ, 0 < z₀ ∧
      Tendsto (fun δ => ftBranchZ a c r (n - 1) δ / δ ^ ρ) (𝓝[>] (0 : ℝ)) (𝓝 z₀) := by
  classical
  have hρR : (2 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hπρ : π / ρ ∈ Ioo 0 π := by
    constructor
    · positivity
    · have : π / ρ ≤ π / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith [pi_pos]
      linarith [pi_pos]
  have hsρ : 0 < Real.sin (π / ρ) := Real.sin_pos_of_pos_of_lt_pi hπρ.1 hπρ.2
  have hgap : ∀ k ∉ S, a i < a k := by
    intro k hk
    rcases lt_or_eq_of_le (hmin k) with h | h
    · exact h
    · exact absurd ((hS k).2 h.symm) hk
  have hBpos : 0 < ∏ k ∈ Sᶜ, (a k - a i) := Finset.prod_pos fun k hk =>
    sub_pos.2 (hgap k (Finset.mem_compl.1 hk))
  have hai : 0 < a i := ha i
  have h2 : 0 < (a i / Real.sin (π / ρ)) ^ ρ := pow_pos (div_pos hai hsρ) ρ
  exact ⟨_, div_pos (mul_pos hc (mul_pos h2 hBpos)) (pow_pos hai r),
    tendsto_ftBranchZ_div_pow hn2 ha hr hS hcard hρ hmin hc⟩

end ForgacsTran
