/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.BranchDivisorWitness
import ForgacsTran.InteriorBranchSeparation
import ForgacsTran.AmplitudeBand
import ForgacsTran.PhaseSupplyProducer

/-!
# The retained set is inhabited, and the window comparison fires

`BranchDivisorWitness` inhabits the amplitude **divisor**.  The retained set `S`
that `subsec:proof` deletes windows around is a different `Finset`, produced
inside `InteriorSupply.exists_interior_data_on_subinterval` as a union over a
finite cover, so nothing there transfers to it.

**What forces `S` is the amplitude floor, and it is the only clause that can.**
Of the four clauses `ft_interior_data_on_arc_two_le` concludes, three are
satisfied by `S = ∅`: the multiplicity and band clauses are `∀ θj ∈ S, …` and the
remainder bound never mentions `S`.  The floor
`A ∏_{θj ∈ S} |θ - θj|^{ν_j} ≤ |W(θ)|` is not, because at `S = ∅` the product is
`1` and the floor asserts a uniform positive lower bound on the amplitude across
the whole band.  So wherever the amplitude actually vanishes inside the band, `S`
must contain that angle — the product has to collapse, and with `1 ≤ ν_j` the only
way a factor vanishes is by coinciding with the angle.

That argument needs nothing about how `S` was built, which is why the finite cover
never has to be related to the branch.

## Main statements

* `mem_of_ftPrincipalAmp_eq_zero` — an amplitude zero in the band is a member of
  any `S` meeting the floor.
* `exists_nonempty_retainedSet_at_branch` — a concrete admissible pencil and
  numerator at which the interior producer's own `S` is inhabited.
* `windowRadius_le_common_fires` — and at which the seam's window comparison
  applies, on a genuine member rather than vacuously.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `subsec:proof`,
  `eq:amplitude-deletion`, `lem:amplitude-divisor`.

## Tags

retained set, amplitude floor, deletion window, Forgács–Tran branch
-/

namespace ForgacsTran

open Polynomial Set Real

/-- **An amplitude zero inside the band belongs to every retained set.**  The
floor forces it: at a zero of `W` the right side is `0`, the constant is positive,
and every factor of the product is a nonnegative power, so the product vanishes —
and `1 ≤ ν_j` is what stops `|θ - θj|^{ν_j}` from being the empty power `0^0 = 1`.

Stated over an abstract `S`, `A` and pencil, because the argument uses only the
floor and never how `S` was produced. -/
theorem mem_of_ftPrincipalAmp_eq_zero {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    {S : Finset ℝ} {ν : ℝ → ℕ} {AI θ : ℝ} (hA : 0 < AI)
    (hν : ∀ θj ∈ S, 1 ≤ ν θj)
    (hfloor : AI * ∏ θj ∈ S, |θ - θj| ^ ν θj ≤ ftPrincipalAmp Q B r z τ θ)
    (hzero : ftPrincipalAmp Q B r z τ θ = 0) :
    θ ∈ S := by
  classical
  rw [hzero] at hfloor
  set P : ℝ := ∏ θj ∈ S, |θ - θj| ^ ν θj with hP
  have hPnn : 0 ≤ P := Finset.prod_nonneg fun θj _ => pow_nonneg (abs_nonneg _) _
  have hPle : P ≤ 0 := by nlinarith
  have hP0 : P = 0 := le_antisymm hPle hPnn
  obtain ⟨θj, hθj, hzj⟩ := Finset.prod_eq_zero_iff.1 hP0
  have hν1 : ν θj ≠ 0 := by
    have := hν θj hθj; omega
  have habs : |θ - θj| = 0 := by
    exact (pow_eq_zero_iff hν1).1 hzj
  have : θ = θj := by
    have := abs_eq_zero.1 habs
    linarith [sub_eq_zero.1 this]
  rwa [this]

/-- **The corner's own antecedent shape.**  `ft_weighted_dominance` does not
produce the interior data — it takes it as an antecedent, with an abstract
`νd : ℝ → ℕ` and its own `ε`.  So this is the form that applies to whatever data
that antecedent is met with, and it says: an amplitude zero inside THAT `ε`'s band
is a member of THAT retained set.

The `ν` above is abstract for exactly this reason; specializing it to
`B.rootMultiplicity ∘ ftPrincipal τ` would not match the corner's binder. -/
theorem mem_of_dominance_interior_data {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {z : ℝ → ℝ} {B : Polynomial ℂ} {ε AI : ℝ} {Sd : Finset ℝ} {νd : ℝ → ℕ}
    (hA : 0 < AI) (hν : ∀ θj ∈ Sd, 1 ≤ νd θj)
    (hfloor : ∀ θ : ℝ, ε ≤ θ → θ ≤ π / r - ε →
      AI * ∏ θj ∈ Sd, |θ - θj| ^ νd θj
        ≤ ftPrincipalAmp (ftRootPoly c a) B r z (ftTauArc a r (n - 1) x₁) θ)
    {θs : ℝ} (hlo : ε ≤ θs) (hhi : θs ≤ π / r - ε)
    (hzero : ftAmp (ftRootPoly c a) B r ((z θs : ℝ) : ℂ)
      (ftPrincipal (ftTauArc a r (n - 1) x₁) θs) = 0) :
    θs ∈ Sd ∧ Sd.Nonempty := by
  have h0 : ftPrincipalAmp (ftRootPoly c a) B r z
      (ftTauArc a r (n - 1) x₁) θs = 0 := by
    rw [ftPrincipalAmp, hzero, norm_zero]
  have hmem := mem_of_ftPrincipalAmp_eq_zero hA hν (hfloor _ hlo hhi) h0
  exact ⟨hmem, ⟨_, hmem⟩⟩

/-- **The interior data on a band, at any spectral parameter agreeing with the
branch on the arc.**  `InteriorSupply.exists_interior_data_on_subinterval_two_le`
is stated at the raw `ftBranchZ` with `τ` abstract, so the extension to a
`θ ≤ 0` value is a rewrite and nothing more.  `ft_interior_data_on_arc_two_le` is
the `z := ftBranchZLower` instance of this; the `ρ = 1` corner needs the
`ftBranchZLowerAt` one, which is why the parameter is here rather than a second
copy of the wrapper. -/
theorem ft_interior_data_on_band_two_le {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {z : ℝ → ℝ} {B : Polynomial ℂ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    (hz : ∀ θ ∈ Ioo (0 : ℝ) (π / r), z θ = ftBranchZ a c r (n - 1) θ)
    {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ π / r - ε) :
    ∃ (CI σI AI : ℝ) (S : Finset ℝ), 0 < σI ∧ σI < 1 ∧ 0 < AI ∧
      (∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ π / r - ε →
        |ftRemainder (ftRootPoly c a) B r z (ftTauArc a r (n - 1) x₁) M θ|
          ≤ CI * σI ^ M) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ π / r - ε →
        AI * ∏ θj ∈ S, |θ - θj|
            ^ (B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj))
          ≤ ftPrincipalAmp (ftRootPoly c a) B r z (ftTauArc a r (n - 1) x₁) θ) ∧
      (∀ θj ∈ S, 1 ≤ B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj)) ∧
      (∀ θj ∈ S, θj ∈ Icc ε (π / r - ε)) := by
  have harc : Icc ε (π / r - ε) ⊆ Ioo (0 : ℝ) (π / r) := fun θ hθ =>
    ⟨lt_of_lt_of_le hε hθ.1, lt_of_le_of_lt hθ.2 (by linarith)⟩
  obtain ⟨CI, σI, AI, S, hσ0, hσ1, hA, hrem, hfloor, hν, hSband⟩ :=
    exists_interior_data_on_subinterval_two_le (τ := ftTauArc a r (n - 1) x₁)
      hn2 ha hc hr hB hB0
      (fun θ hθ => ftTauArc_agree a r (n - 1) x₁ hθ.1 hθ.2) hεb harc
  refine ⟨CI, σI, AI, S, hσ0, hσ1, hA, fun M θ h1 h2 => ?_, fun θ h1 h2 => ?_,
    hν, hSband⟩
  · simpa [ftRemainder, hz θ (harc ⟨h1, h2⟩)] using hrem M θ h1 h2
  · simpa [ftPrincipalAmp, hz θ (harc ⟨h1, h2⟩)] using hfloor θ h1 h2

/-- **The interior data on a band at `r = 1`**, the `z`-generic wrapper of
`InteriorSupply.exists_interior_data_on_subinterval_pi`.  The `3 ≤ n` is
`thm:FT-geometry`'s own exclusion of `(deg Q, r) = (2,1)`, not an artifact. -/
theorem ft_interior_data_on_band_one {n : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {z : ℝ → ℝ} {B : Polynomial ℂ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    (hz : ∀ θ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)),
      z θ = ftBranchZ a c 1 (n - 1) θ)
    {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ π / ((1 : ℕ) : ℝ) - ε) :
    ∃ (CI σI AI : ℝ) (S : Finset ℝ), 0 < σI ∧ σI < 1 ∧ 0 < AI ∧
      (∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ π / ((1 : ℕ) : ℝ) - ε →
        |ftRemainder (ftRootPoly c a) B 1 z (ftTauArc a 1 (n - 1) x₁) M θ|
          ≤ CI * σI ^ M) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ π / ((1 : ℕ) : ℝ) - ε →
        AI * ∏ θj ∈ S, |θ - θj|
            ^ (B.rootMultiplicity (ftPrincipal (ftTauArc a 1 (n - 1) x₁) θj))
          ≤ ftPrincipalAmp (ftRootPoly c a) B 1 z (ftTauArc a 1 (n - 1) x₁) θ) ∧
      (∀ θj ∈ S, 1 ≤ B.rootMultiplicity (ftPrincipal (ftTauArc a 1 (n - 1) x₁) θj)) ∧
      (∀ θj ∈ S, θj ∈ Icc ε (π / ((1 : ℕ) : ℝ) - ε)) := by
  have harc : Icc ε (π / ((1 : ℕ) : ℝ) - ε) ⊆ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)) :=
    fun θ hθ => ⟨lt_of_lt_of_le hε hθ.1, lt_of_le_of_lt hθ.2 (by linarith)⟩
  obtain ⟨CI, σI, AI, S, hσ0, hσ1, hA, hrem, hfloor, hν, hSband⟩ :=
    exists_interior_data_on_subinterval_pi (τ := ftTauArc a 1 (n - 1) x₁)
      hn3 ha hc hB hB0
      (fun θ hθ => ftTauArc_agree a 1 (n - 1) x₁ hθ.1 hθ.2) hεb harc
  refine ⟨CI, σI, AI, S, hσ0, hσ1, hA, fun M θ h1 h2 => ?_, fun θ h1 h2 => ?_,
    hν, hSband⟩
  · simpa [ftRemainder, hz θ (harc ⟨h1, h2⟩)] using hrem M θ h1 h2
  · simpa [ftPrincipalAmp, hz θ (harc ⟨h1, h2⟩)] using hfloor θ h1 h2

/-! ### The retained set at any pencil with a branch zero -/

/-- **A branch zero of `B` forces it into the interior producer's retained set.**
At every admissible pencil with `2 ≤ r`, if `B` vanishes at the branch point over
some angle of the open arc, then the `S` that `ft_interior_data_on_arc_two_le`
returns contains that angle — so `S` is inhabited, every member of it lies in the
amplitude divisor of the same band, and the seam's window comparison applies to a
genuine member rather than vacuously.

`S` is not chosen: it is whatever the producer returns, and `ε` is the band's own,
which contains the angle automatically because the angle is an amplitude zero. -/
theorem exists_nonempty_retainedSet_of_branch_zero {n r : ℕ} {a : Fin n → ℝ}
    {c x₁ : ℝ} {z : ℝ → ℝ} {B : Polynomial ℂ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : 0 < c) (hr : 2 ≤ r) (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    (hz : ∀ θ ∈ Ioo (0 : ℝ) (π / r), z θ = ftBranchZ a c r (n - 1) θ)
    {θs : ℝ} (hθs : θs ∈ Ioo (0 : ℝ) (π / r))
    (hmult : 1 ≤ B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θs)) :
    ∃ (ε σI AI : ℝ) (S : Finset ℝ), 0 < ε ∧ ε < π / r - ε ∧ 0 < σI ∧ σI < 1
      ∧ 0 < AI ∧ θs ∈ S ∧ S.Nonempty
      ∧ (∀ θj ∈ S, θj ∈ ftAmplitudeDivisor (ftRootPoly c a) B r z
          (ftTauArc a r (n - 1) x₁) ε (π / r - ε))
      ∧ ∀ M : ℕ, windowRadius σI S
            (fun θj => B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj))
            M θs
          ≤ ftWindowRadius (ftRootPoly c a) B r z (ftTauArc a r (n - 1) x₁) ε σI M := by
  classical
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  obtain ⟨ε, hε, hεlt, hband⟩ :=
    exists_band_at_branch (x₁ := x₁) (B := B) hn ha hc hr1 (Or.inl hn2) hz hB0
  -- the angle is an amplitude zero, so the band clause locates it
  have hamp : ftAmp (ftRootPoly c a) B r ((z θs : ℝ) : ℂ)
      (ftPrincipal (ftTauArc a r (n - 1) x₁) θs) = 0 :=
    ftAmp_eq_zero_at_branch_of_one_le_mult hn ha hc hr1 (Or.inl hn2) hz hB0 hθs hmult
  have hmemband : θs ∈ Icc ε (π / r - ε) := hband _ hθs hamp
  obtain ⟨CI, σI, AI, S, hσ0, hσ1, hA, hrem, hfloor, hν, hSband⟩ :=
    ft_interior_data_on_band_two_le (x₁ := x₁) (B := B) hn2 ha hc hr hB hB0 hz hε
      (by linarith)
  have hzero : ftPrincipalAmp (ftRootPoly c a) B r z
      (ftTauArc a r (n - 1) x₁) θs = 0 := by
    rw [ftPrincipalAmp, hamp, norm_zero]
  have hmem : θs ∈ S :=
    mem_of_ftPrincipalAmp_eq_zero hA hν (hfloor _ hmemband.1 hmemband.2) hzero
  -- every member of `S` sits in the divisor of the same band
  have hSD : ∀ θj ∈ S, θj ∈ ftAmplitudeDivisor (ftRootPoly c a) B r
      z (ftTauArc a r (n - 1) x₁) ε (π / r - ε) := by
    intro θj hθj
    have hb := hSband θj hθj
    exact mem_ftAmplitudeDivisor_at_branch hn ha hc hr1 (Or.inl hn2) hz hB0 hε hband
      ⟨lt_of_lt_of_le hε hb.1, lt_of_le_of_lt hb.2 (by linarith)⟩ (hν θj hθj)
  -- the multiplicity at `θs` is under `max (deg B) 1`, by the divisor's own count
  obtain ⟨hτband, -, -⟩ := ft_branch_geometry_band (x₁ := x₁) hn ha hc hr1
    (Or.inl hn2) hz hε
  have hcount := ftAmplitudeDivisor_count (Q := ftRootPoly c a) (B := B) (r := r)
    (z := z) (τ := ftTauArc a r (n - 1) x₁)
    (lo := ε) (hi := π / r - ε) hB0 (band_subset_Ioo_pi hr1 hε) hτband
  have hsingle := Finset.single_le_sum
    (f := fun θj => B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj))
    (fun i _ => Nat.zero_le _) (hSD θs hmem)
  have hνN : B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θs)
      ≤ max B.natDegree 1 := le_trans (le_trans hsingle hcount) (le_max_left _ _)
  refine ⟨ε, σI, AI, S, hε, hεlt, hσ0, hσ1, hA, hmem, ⟨_, hmem⟩, hSD, fun M => ?_⟩
  rw [ftWindowRadius]
  exact windowRadius_le_common hσ0 hσ1 (fun {θj} hθj => hSD θj hθj) hmem
    (hν θs hmem) hνN

/-! ### The same at named data -/

theorem quadArc_mem : (π / 4 : ℝ) ∈ Ioo (0 : ℝ) (π / ((2 : ℕ) : ℝ)) := by
  have := pi_pos
  constructor <;> [linarith; (push_cast; linarith)]

theorem quad_ha : ∀ k, 0 < (![1, 1] : Fin 2 → ℝ) k := by
  intro k; fin_cases k <;> norm_num

/-- The numerator: the real quadratic vanishing at the branch point over `π/4`. -/
noncomputable def quadB : Polynomial ℂ := branchWitnessB ![1, 1] 2 1 (π / 4)

theorem quadB_ne_zero : quadB ≠ 0 := branchWitnessB_ne_zero _ _ _ _

theorem hasRealCoeffs_quadB : HasRealCoeffs quadB := hasRealCoeffs_branchWitnessB _ _ _ _

/-- **The retained set is inhabited and the window comparison fires, at named
data.**  `Q = (1-t)^2` as `ftRootPoly 1 ![1,1]`, `r = 2`, and the numerator is the
real quadratic vanishing at the branch point over `π/4`.  Only `ε`, `σ`, `A` and
`S` are existential, and `S` is the producer's own. -/
theorem quad_nonempty_retainedSet :
    ∃ (ε σI AI : ℝ) (S : Finset ℝ), 0 < ε ∧ ε < π / ((2 : ℕ) : ℝ) - ε ∧ 0 < σI
      ∧ σI < 1 ∧ 0 < AI ∧ (π / 4 : ℝ) ∈ S ∧ S.Nonempty
      ∧ (∀ θj ∈ S, θj ∈ ftAmplitudeDivisor (ftRootPoly 1 ![1, 1]) quadB 2
          (ftBranchZLower ![1, 1] 1 2 1) (ftTauArc ![1, 1] 2 1 1) ε
          (π / ((2 : ℕ) : ℝ) - ε))
      ∧ ∀ M : ℕ, windowRadius σI S
            (fun θj => quadB.rootMultiplicity (ftPrincipal (ftTauArc ![1, 1] 2 1 1) θj))
            M (π / 4)
          ≤ ftWindowRadius (ftRootPoly 1 ![1, 1]) quadB 2
            (ftBranchZLower ![1, 1] 1 2 1) (ftTauArc ![1, 1] 2 1 1) ε σI M :=
  exists_nonempty_retainedSet_of_branch_zero (n := 2) (r := 2) (a := ![1, 1])
    (c := 1) (x₁ := 1) (z := ftBranchZLower ![1, 1] 1 2 1) (B := quadB) (by omega)
    quad_ha one_pos (by omega) hasRealCoeffs_quadB quadB_ne_zero
    (fun θ hθ => ftBranchZLower_agree _ _ _ _ hθ.1) quadArc_mem
    (one_le_rootMultiplicity_branchWitnessB ![1, 1] 2 1 (π / 4))

/-! ### The other half: `S` is empty for the generic numerator -/

/-- **`S` can be empty, and nonemptiness is a fact about `B`, not about the
pencil.**  The interior data's own multiplicity clause forces it: at `B = 1` every
`rootMultiplicity` is `0`, so `1 ≤ ν_j` has no solution and `S` has no member.

So "the retained set is inhabited" is not a theorem anyone could have proved in
general, and the composition does **not** need a nonemptiness hypothesis — when
`S` is empty the amplitude divisor is empty too, the window clause is vacuous on
both sides, and `windowRadius_le_common` is never reached.  What was missing was
only a witness that the inhabited case occurs, which is what the theorems above
supply. -/
theorem retainedSet_eq_empty_of_one {n r : ℕ} {a : Fin n → ℝ} {x₁ : ℝ}
    {S : Finset ℝ}
    (hν : ∀ θj ∈ S, 1 ≤ (1 : Polynomial ℂ).rootMultiplicity
      (ftPrincipal (ftTauArc a r (n - 1) x₁) θj)) :
    S = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro θj hθj
  have h1 := hν θj hθj
  rw [Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot])] at h1
  omega

/-- The producer's `S` at the constant numerator, at the same pencil as
`quad_nonempty_retainedSet` — empty, so the two witnesses bracket the question. -/
theorem quad_retainedSet_empty_at_one {ε : ℝ} (hε : 0 < ε)
    (hεb : ε ≤ π / ((2 : ℕ) : ℝ) - ε) :
    ∃ (σI AI : ℝ) (S : Finset ℝ), 0 < σI ∧ σI < 1 ∧ 0 < AI ∧ S = ∅ := by
  obtain ⟨-, σI, AI, S, hσ0, hσ1, hA, -, -, hν, -⟩ :=
    ft_interior_data_on_band_two_le (n := 2) (r := 2) (a := ![1, 1]) (c := 1) (x₁ := 1)
      (z := ftBranchZLower ![1, 1] 1 2 1) (B := 1) (by omega) quad_ha one_pos
      (by omega) hasRealCoeffs_one one_ne_zero
      (fun θ hθ => ftBranchZLower_agree _ _ _ _ hθ.1) hε hεb
  exact ⟨σI, AI, S, hσ0, hσ1, hA, retainedSet_eq_empty_of_one hν⟩

/-! ### The retained set IS the divisor -/

/-- **`S` and the amplitude divisor of the same band are equal**, at any admissible
pencil with `2 ≤ r`.  One inclusion is `mem_ftAmplitudeDivisor_at_branch` applied
to each member; the other is the floor argument applied at each divisor member,
which is an amplitude zero lying in the band by construction.

This collapses the seam: `windowRadius_le_common`'s `S ⊆ D` is then an equality,
and "is `S` inhabited" and "is the divisor inhabited" are one question, which is
why the empty case above is vacuous on both sides rather than only on one. -/
theorem retainedSet_eq_ftAmplitudeDivisor {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {z : ℝ → ℝ} {B : Polynomial ℂ} {ε AI : ℝ} {S : Finset ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hB0 : B ≠ 0)
    (hz : ∀ θ ∈ Ioo (0 : ℝ) (π / r), z θ = ftBranchZ a c r (n - 1) θ)
    (hε : 0 < ε) (hA : 0 < AI)
    (hband : ∀ θ ∈ Ioo (0 : ℝ) (π / r),
      ftAmp (ftRootPoly c a) B r ((z θ : ℝ) : ℂ)
          (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) = 0 → θ ∈ Icc ε (π / r - ε))
    (hν : ∀ θj ∈ S, 1 ≤ B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj))
    (hSband : ∀ θj ∈ S, θj ∈ Icc ε (π / r - ε))
    (hfloor : ∀ θ : ℝ, ε ≤ θ → θ ≤ π / r - ε →
      AI * ∏ θj ∈ S, |θ - θj|
          ^ (B.rootMultiplicity (ftPrincipal (ftTauArc a r (n - 1) x₁) θj))
        ≤ ftPrincipalAmp (ftRootPoly c a) B r z (ftTauArc a r (n - 1) x₁) θ) :
    S = ftAmplitudeDivisor (ftRootPoly c a) B r z
      (ftTauArc a r (n - 1) x₁) ε (π / r - ε) := by
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := hr
  apply Finset.Subset.antisymm
  · intro θj hθj
    have hb := hSband θj hθj
    exact mem_ftAmplitudeDivisor_at_branch hn ha hc hr1 (Or.inl hn2) hz hB0 hε hband
      ⟨lt_of_lt_of_le hε hb.1, lt_of_le_of_lt hb.2 (by linarith)⟩ (hν θj hθj)
  · intro θj hθj
    have hb : θj ∈ Icc ε (π / r - ε) :=
      ftAmplitudeDivisor_subset (Finset.mem_coe.2 hθj)
    have h0 : ftPrincipalAmp (ftRootPoly c a) B r z
        (ftTauArc a r (n - 1) x₁) θj = 0 := by
      rw [ftPrincipalAmp, ftAmplitudeDivisor_zero hθj, norm_zero]
    exact mem_of_ftPrincipalAmp_eq_zero hA hν (hfloor _ hb.1 hb.2) h0

end ForgacsTran
