/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.PrincipalSimpleBranch
import ForgacsTran.FTGeometryBranch
import ForgacsTran.InteriorSeparation
import ForgacsTran.FTGeometryClosure
import ForgacsTran.FTGeometryCone

/-!
# The compact interior, discharged at the constructed branch

`DominanceFT.interior_data_of_geometry` is the `Θ`-free half of
`thm:weighted-dominance`'s interior hypothesis: `eq:interior-remainder` and the
amplitude floor of `lem:amplitude-divisor` on one compact subinterval.  It takes
fifteen statements about a branch.  At the branch the paper constructs, fourteen
of them are theorems of the admissible class, and this module discharges them.

`ft_interior_data_at_branch` still asks for a separating radius on the
subinterval; `exists_interior_data_on_subinterval` does not.  A **single** radius
across a compact interior is strictly stronger than `thm:FT-geometry`, whose
separation is a modulus *ratio* compared at one angle, while one radius compares
`sup τ` against the non-principal infimum at *different* angles.  What the theorem
does give is enough: `InteriorSeparation` turns the pointwise gap into a radius on
a neighborhood of each angle, without following any root, and finitely many of
those cover the subinterval.  The pointwise gap is itself a theorem at every
admissible `r` — `r = 1` at `3 ≤ n`, `r ≥ 2` at `2 ≤ n` — so the supply is
unconditional throughout.

The amplitude divisor is **not** hypothesized.  `eq:amplitude-zero-count` reads
it off the arc: `arg t_+(θ) = θ` because `τ(θ) > 0`, so the branch is injective,
and `ftAmp` vanishes exactly where `B ∘ t_+` does, which happens at the arguments
of the zeros of `B` and nowhere else.  That makes the divisor a `Finset` with at
most `deg B` members counted with multiplicity, rather than an assumption.

## Main statements

* `arg_ftPrincipal` — `arg t_+(θ) = θ` on the viewing arc, hence
  `injOn_ftPrincipal`, the injectivity `lem:amplitude-divisor` runs on.  The pair
  being distinct is `FTGeometryAssembly.ftPrincipal_ne_arcPoint_of_pos`, consumed
  rather than reproved.
* `ftAmplitudeDivisor` — the divisor as a `Finset`, with
  `ftAmplitudeDivisor_spec` characterizing its members and
  `ftAmplitudeDivisor_count` the `eq:amplitude-zero-count` bound.
* `ft_interior_data_at_branch` — `interior_data_of_geometry`'s conclusion on a
  compact subinterval at the branch, over one separating radius for that
  subinterval.
* `exists_interior_data_on_subinterval` — the same with **no radius assumed**: the
  radius is produced per angle by `InteriorSeparation` from the pointwise gap
  `thm:FT-geometry` states, finitely many of those cover, and
  `InteriorSeparation.interior_data_of_pieces` reassembles.  What is left is that
  pointwise gap, and it is a theorem at every admissible `r`.
* `exists_interior_data_on_subinterval_pi`,
  `exists_interior_data_on_subinterval_two_le` — the gap discharged too, so the
  interior supply carries **no hypothesis beyond the admissible class**.  The two
  cover every `r` the paper admits: `r = 1` by
  `FTGeometryClosure.ft_geometry_at_branch_pi` at `3 ≤ n`, which is
  `thm:FT-geometry`'s own exclusion of `(deg Q, r) = (2,1)`, and `r ≥ 2` by
  `FTGeometryCone.ft_minModulus_at_branch_two_le` at `2 ≤ n`.

## Implementation notes

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Principal-pair
dominance and the fixed-numerator theorem» (`sec:dominance`,
`thm:weighted-dominance`), and «Spectral geometry, residues, and the principal
amplitude» (`lem:amplitude-divisor`, `eq:amplitude-zero-count`).

## Tags

interior supply, amplitude divisor, Forgacs-Tran branch, weighted dominance
-/

namespace ForgacsTran

open Real Set Polynomial

/-! ### The branch is injective, and its amplitude divisor is finite -/

/-- **`arg t_+(θ) = θ`.**  The principal branch is `τ(θ)e^{iθ}` with `τ(θ) > 0`
and `θ` inside `(0, π)`, so the argument recovers the parameter. -/
theorem arg_ftPrincipal {τ : ℝ → ℝ} {θ : ℝ} (hτ : 0 < τ θ) (hθ : θ ∈ Ioo 0 π) :
    Complex.arg (ftPrincipal τ θ) = θ := by
  have hIoc : θ ∈ Ioc (-π) π := ⟨lt_trans (by linarith [pi_pos]) hθ.1, hθ.2.le⟩
  rw [ftPrincipal, Complex.exp_mul_I]
  exact Complex.arg_mul_cos_add_sin_mul_I hτ hIoc

/-- **The injectivity `lem:amplitude-divisor` runs on.**  Distinct parameters of
the viewing arc give distinct branch points, because each carries its own
argument. -/
theorem injOn_ftPrincipal {τ : ℝ → ℝ} {K : Set ℝ} (hK : K ⊆ Ioo 0 π)
    (hτ : ∀ θ ∈ K, 0 < τ θ) : Set.InjOn (ftPrincipal τ) K := by
  intro x hx y hy hxy
  have := congrArg Complex.arg hxy
  rwa [arg_ftPrincipal (hτ x hx) (hK hx), arg_ftPrincipal (hτ y hy) (hK hy)] at this

/-- The zeros of the principal amplitude on a compact interval of the arc, as a
`Finset`: the arguments of the zeros of `B` that the branch actually meets. -/
noncomputable def ftAmplitudeDivisor (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ)
    (lo hi : ℝ) : Finset ℝ := by
  classical
  exact (B.roots.toFinset.image Complex.arg).filter
    (fun θ => θ ∈ Set.Icc lo hi ∧ ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0)

theorem ftAmplitudeDivisor_subset {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {lo hi : ℝ} :
    ↑(ftAmplitudeDivisor Q B r z τ lo hi) ⊆ Set.Icc lo hi := by
  classical
  intro θ hθ
  exact ((Finset.mem_filter.1 (Finset.mem_coe.1 hθ)).2).1

theorem ftAmplitudeDivisor_zero {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {lo hi : ℝ}
    {θ : ℝ} (hθ : θ ∈ ftAmplitudeDivisor Q B r z τ lo hi) :
    ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 := by
  classical
  exact ((Finset.mem_filter.1 hθ).2).2

/-- **The divisor is complete.**  Every parameter of the compact interval where
the amplitude vanishes is a member: `ftAmp` vanishes exactly where `B ∘ t_+`
does, and `arg t_+(θ) = θ` puts that parameter in the image. -/
theorem ftAmplitudeDivisor_complete {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    {lo hi : ℝ} (hB0 : B ≠ 0) (hK : Set.Icc lo hi ⊆ Ioo 0 π)
    (hτ : ∀ θ ∈ Set.Icc lo hi, 0 < τ θ)
    (hroot : ∀ θ ∈ Set.Icc lo hi, (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hsimple : ∀ θ ∈ Set.Icc lo hi,
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Set.Icc lo hi)
    (hzero : ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0) :
    θ ∈ ftAmplitudeDivisor Q B r z τ lo hi := by
  classical
  have hBz : B.eval (ftPrincipal τ θ) = 0 :=
    (ftAmp_eq_zero_iff (hroot θ hθ) (hsimple θ hθ)).1 hzero
  have hmem : ftPrincipal τ θ ∈ B.roots := (mem_roots hB0).2 hBz
  refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨ftPrincipal τ θ, ?_, ?_⟩, hθ, hzero⟩
  · exact Multiset.mem_toFinset.2 hmem
  · exact arg_ftPrincipal (hτ θ hθ) (hK hθ)

/-- **`eq:amplitude-zero-count` at the branch.**  The zeros of the principal
amplitude on a compact interval of the arc have total multiplicity at most
`deg B`. -/
theorem ftAmplitudeDivisor_count {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    {lo hi : ℝ} (hB0 : B ≠ 0) (hK : Set.Icc lo hi ⊆ Ioo 0 π)
    (hτ : ∀ θ ∈ Set.Icc lo hi, 0 < τ θ) :
    ∑ θj ∈ ftAmplitudeDivisor Q B r z τ lo hi,
        B.rootMultiplicity (ftPrincipal τ θj) ≤ B.natDegree :=
  amplitude_zero_count hB0
    ((injOn_ftPrincipal hK hτ).mono (ftAmplitudeDivisor_subset (Q := Q) (B := B) (r := r)
      (z := z) (τ := τ) (lo := lo) (hi := hi)))


/-! ### `interior_data_of_geometry` at the branch -/

/-! The branch-instantiation layer runs on **two** radius functions, and they are
not interchangeable.  `ftTau` is the constructed one and is junk at `θ = 0`;
`weighted_dominance_of_branch` quantifies over a free `τ` and evaluates it *at*
the endpoint (`ftPrincipal τ 0 = t_e`, and a derivative within `Ici 0` there), so
a caller must supply an extension of `ftTau` past the open arc.  Everything below
is therefore stated for such an extension, pinned to `ftTau` on the arc by
`hagree` alone — which is exactly what an endpoint-regularity producer has to
deliver alongside the endpoint value and derivative. -/

theorem ftPrincipal_congr {τ τ' : ℝ → ℝ} {θ : ℝ} (h : τ θ = τ' θ) :
    ftPrincipal τ θ = ftPrincipal τ' θ := by rw [ftPrincipal, ftPrincipal, h]

theorem ftPrincipalAmp_congr {Q B : Polynomial ℂ} {r : ℕ} {z τ τ' : ℝ → ℝ} {θ : ℝ}
    (h : τ θ = τ' θ) :
    ftPrincipalAmp Q B r z τ θ = ftPrincipalAmp Q B r z τ' θ := by
  rw [ftPrincipalAmp, ftPrincipalAmp, ftPrincipal_congr h]

theorem ftRemainder_congr {Q B : Polynomial ℂ} {r : ℕ} {z τ τ' : ℝ → ℝ} {M : ℕ} {θ : ℝ}
    (h : τ θ = τ' θ) :
    ftRemainder Q B r z τ M θ = ftRemainder Q B r z τ' M θ := by
  rw [ftRemainder, ftRemainder, ftPrincipal_congr h, h]


/-- **`interior_data_of_geometry` at the constructed branch.**  `eq:interior-remainder`
and the amplitude floor of `lem:amplitude-divisor` on the compact interval
`[e, π/r - e]`, with every hypothesis but one supplied from the admissible class:
positive zeros, `c > 0`, `r ≥ 1`, and `max{deg Q, r} > 1`.

The one that is not is `hpair`, the uniform separation radius of
`thm:FT-geometry` — one `R₀` above `τ` across the whole interval with the
principal pair the only denominator zeros inside it.  The pointwise disk clause
at `‖t‖ ≤ τ(θ)` is `FTGeometryClosure.ft_geometry_at_branch_pi` and needs no
hypothesis; what `hpair` adds is the uniformity, which
`FTGeometryAssembly.ft_geometry_compact_separation` produces from an enumeration
of the remaining zeros as continuous functions of the angle.  Mathlib carries no
continuity-of-roots statement at the pinned revision, so that enumeration cannot
be built here and the uniformity is taken as data.

The amplitude divisor is constructed rather than assumed, and comes with its
`eq:amplitude-zero-count` bound.

**Containment.**  `hpair` and `hτR` relate `τ` and the denominator's zeros; the
conclusion relates `ftRemainder` and `ftPrincipalAmp`, and no hypothesis mentions
either. -/
theorem ft_interior_data_at_branch {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} {B : Polynomial ℂ}
    {τ : ℝ → ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    (hagree : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / r), τ θ = ftTau a r (n - 1) θ)
    {lo hi R₀ : ℝ} (hlohi : lo ≤ hi) (harc : Set.Icc lo hi ⊆ Set.Ioo (0 : ℝ) (π / r))
    (hR₀ : 0 < R₀)
    (hτR : ∀ θ ∈ Set.Icc lo hi, τ θ < R₀)
    (hpair : ∀ θ ∈ Set.Icc lo hi, ∀ t : ℂ, ‖t‖ ≤ R₀ →
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval t = 0 →
      t = ftPrincipal τ θ
        ∨ t = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)) :
    ∃ (CI σI AI : ℝ),
      0 < σI ∧ σI < 1 ∧ 0 < AI ∧
      (∀ (M : ℕ) (θ : ℝ), lo ≤ θ → θ ≤ hi →
        |ftRemainder (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
          τ M θ| ≤ CI * σI ^ M) ∧
      (∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
        AI * ∏ θj ∈ ftAmplitudeDivisor (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
              τ lo hi,
            |θ - θj| ^ (B.rootMultiplicity (ftPrincipal τ θj))
          ≤ ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
              τ θ) ∧
      (∀ θj ∈ ftAmplitudeDivisor (ftRootPoly c a) B r (ftBranchZ a c r (n - 1))
          τ lo hi,
        1 ≤ B.rootMultiplicity (ftPrincipal τ θj)) := by
  classical
  set T := ftTau a r (n - 1) with hTdef
  set z := ftBranchZ a c r (n - 1) with hzdef
  set Q := ftRootPoly c a with hQdef
  set K : Set ℝ := Set.Icc lo hi with hKdef
  have hKsub : K ⊆ Ioo 0 (π / r) := harc
  have hKπ : K ⊆ Ioo 0 π := fun θ hθ => ftArc_subset hr (hKsub hθ)
  have hKne : K.Nonempty := ⟨lo, le_rfl, hlohi⟩
  obtain ⟨hrootA, hposA, -, hzcontA⟩ := ft_branch_supplies (a := a) (c := c) hn ha hc hr hnr
  -- everything the branch supplies is about `T`; `hagree` carries it to `τ`
  have hTeq : ∀ θ ∈ K, τ θ = T θ := fun θ hθ => hagree θ (hKsub hθ)
  have hprin : ∀ θ ∈ K, ftPrincipal τ θ = ftPrincipal T θ :=
    fun θ hθ => ftPrincipal_congr (hTeq θ hθ)
  have hτpos : ∀ θ ∈ K, 0 < τ θ := fun θ hθ => (hTeq θ hθ) ▸ hposA θ (hKsub hθ)
  have hτcont : ContinuousOn τ K :=
    ContinuousOn.congr (fun θ hθ =>
      (continuousAt_ftTau_principal hn ha hr hnr (hKsub hθ)).continuousWithinAt)
      (fun θ hθ => hTeq θ hθ)
  obtain ⟨θm, hθm, hmax⟩ := isCompact_Icc.exists_isMaxOn hKne hτcont
  set τmax := τ θm with hτmaxdef
  have hτmaxpos : 0 < τmax := hτpos θm hθm
  have hτmaxR : τmax < R₀ := hτR θm hθm
  set σ := τmax / R₀ with hσdef
  have hσ0 : 0 < σ := div_pos hτmaxpos hR₀
  have hσ1 : σ < 1 := (div_lt_one hR₀).2 hτmaxR
  -- the geometry group
  have hroot : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0 := by
    intro θ h1 h2
    rw [hprin θ ⟨h1, h2⟩]
    exact hrootA θ (hKsub ⟨h1, h2⟩)
  have hsimple := fun (θ : ℝ) (hθ : θ ∈ K) =>
    ft_principal_simple_at_branch (a := a) (c := c) hn ha hc.ne' hr hnr (hKsub hθ)
  have hsp : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0 := by
    intro θ h1 h2
    rw [hprin θ ⟨h1, h2⟩]
    exact (hsimple θ ⟨h1, h2⟩).1
  have hsm : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
        (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)) ≠ 0 := by
    intro θ h1 h2
    have h := (hsimple θ ⟨h1, h2⟩).2
    rw [conj_ftPrincipal] at h
    rwa [hTeq θ ⟨h1, h2⟩]
  have hne : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
      ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) :=
    fun θ h1 h2 => ftPrincipal_ne_arcPoint_of_pos (hτpos θ ⟨h1, h2⟩) (hKπ ⟨h1, h2⟩)
  -- the amplitude divisor
  set S := ftAmplitudeDivisor Q B r z τ lo hi with hSdef
  have hzeros : ∀ θ ∈ K, ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 → θ ∈ S :=
    fun θ hθ hz => ftAmplitudeDivisor_complete hB0 hKπ hτpos
      (fun θ' hθ' => hroot θ' hθ'.1 hθ'.2) (fun θ' hθ' => hsp θ' hθ'.1 hθ'.2) hθ hz
  -- the branch inputs
  have hγd : ∀ θ ∈ K, ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal τ) γ' θ := by
    intro θ hθ
    obtain ⟨γ', hγ'ne, hγ'⟩ := ftPrincipal_hasDerivAt_of_subset hn ha hr hnr hKsub θ hθ
    refine ⟨γ', hγ'ne, hγ'.congr_of_eventuallyEq ?_⟩
    filter_upwards [isOpen_Ioo.mem_nhds (hKsub hθ)] with x hx
    exact ftPrincipal_congr (hagree x hx)
  have hzc : ∀ θ ∈ K, ContinuousAt (fun θ' => ((z θ' : ℝ) : ℂ)) θ := by
    intro θ hθ
    have hopen : Ioo (0 : ℝ) (π / r) ∈ nhds θ := isOpen_Ioo.mem_nhds (hKsub hθ)
    exact Complex.continuous_ofReal.continuousAt.comp
      (hzcontA.continuousAt hopen)
  have hQ0 : Q.eval 0 ≠ 0 := by
    rw [hQdef, eval_ftRootPoly]
    refine mul_ne_zero (Complex.ofReal_ne_zero.2 hc.ne') (Finset.prod_ne_zero_iff.2 fun k _ => ?_)
    simpa using Complex.ofReal_ne_zero.2 (ha k).ne'
  -- `interior_data_of_geometry` parametrizes its interval as `[e, b - e]`; the
  -- subinterval `[lo, hi]` is that at `e = lo`, `b = hi + lo`.
  have hbe : hi + lo - lo = hi := by ring
  have hmain := interior_data_of_geometry (hasRealCoeffs_ftRootPoly c a) hB hr hQ0 (S := S)
      (e := lo) (b := hi + lo) hB0 hR₀
      (le_refl σ) hσ0 hσ1
      (fun θ h1 h2 => hτpos θ ⟨h1, by linarith⟩)
      (fun θ h1 h2 => hmax ⟨h1, by linarith⟩)
      (fun θ h1 h2 => hτR θ ⟨h1, by linarith⟩)
      (fun θ h1 h2 => hroot θ h1 (by linarith))
      (fun θ h1 h2 => hsp θ h1 (by linarith))
      (fun θ h1 h2 => hsm θ h1 (by linarith))
      (fun θ h1 h2 => hne θ h1 (by linarith))
      (fun θ h1 h2 t ht hz => hpair θ ⟨h1, by linarith⟩ t ht hz)
      (by rw [hbe]; exact ftAmplitudeDivisor_subset)
      (fun θj hj => ftAmplitudeDivisor_zero hj)
      (by rw [hbe]; exact hzeros) (by rw [hbe]; exact hγd) (by rw [hbe]; exact hzc)
  rw [hbe] at hmain
  obtain ⟨CI, σI, AI, hσ0', hσ1', hAI, hrem, hfloor, hν, -⟩ := hmain
  exact ⟨CI, σI, AI, hσ0', hσ1', hAI, hrem, hfloor, hν⟩


/-! ### The hypothesis set is inhabited

`ft_interior_data_at_branch` is conditional on the uniform separation radius, and
a conditional theorem is worth what its hypotheses are worth.  At `n = 2`,
`r = 1` the denominator is quadratic, so the principal pair exhausts its zeros
and the radius may be taken anywhere above `τ`.  That is the manuscript's
`rem:quadratic-case`, which `thm:FT-geometry` excludes and which this theorem
does not — nothing in `interior_data_of_geometry` needs the exclusion.  So the
witness certifies satisfiability without asserting anything the paper denies. -/

/-- A polynomial of degree at most two has no zero beyond two distinct ones it
already has. -/
theorem eq_of_root_of_natDegree_le_two {p : Polynomial ℂ} (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ 2) {u v w : ℂ} (hu : p.eval u = 0) (hv : p.eval v = 0)
    (huv : u ≠ v) (hw : p.eval w = 0) : w = u ∨ w = v := by
  classical
  by_contra hcon
  push Not at hcon
  have hmem : ({u, v, w} : Finset ℂ) ⊆ p.roots.toFinset := by
    intro x hx
    have : p.eval x = 0 := by
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hu
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hv
      · rw [Finset.mem_singleton.1 hx]; exact hw
    exact Multiset.mem_toFinset.2 ((mem_roots hp).2 this)
  have hcard : ({u, v, w} : Finset ℂ).card = 3 := by
    have hnu : u ∉ ({v, w} : Finset ℂ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨huv, fun h => hcon.1 h.symm⟩
    have hnv : v ∉ ({w} : Finset ℂ) := by
      simp only [Finset.mem_singleton]
      exact fun h => hcon.2 h.symm
    rw [Finset.card_insert_of_notMem hnu, Finset.card_insert_of_notMem hnv,
      Finset.card_singleton]
  have h3 : 3 ≤ p.roots.toFinset.card := hcard ▸ Finset.card_le_card hmem
  have h4 : p.roots.toFinset.card ≤ p.natDegree :=
    le_trans (Multiset.toFinset_card_le _) p.card_roots'
  omega

/-- **`ft_interior_data_at_branch`'s hypotheses are jointly satisfiable**, at a
quadratic pencil where the principal pair is the whole zero set. -/
theorem ft_interior_separation_quadratic {a : Fin 2 → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {e : ℝ} (he : 0 < e)
    (hlo : e ≤ π / ((1 : ℕ) : ℝ) - e) :
    ∃ R₀ : ℝ, 0 < R₀ ∧
      (∀ θ ∈ Set.Icc e (π / ((1 : ℕ) : ℝ) - e), ftTau a 1 (2 - 1) θ < R₀) ∧
      (∀ θ ∈ Set.Icc e (π / ((1 : ℕ) : ℝ) - e), ∀ t : ℂ, ‖t‖ ≤ R₀ →
        (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (2 - 1) θ : ℝ) : ℂ)).eval t = 0 →
        t = ftPrincipal (ftTau a 1 (2 - 1)) θ
          ∨ t = ((ftTau a 1 (2 - 1) θ : ℝ) : ℂ)
              * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)) := by
  classical
  set τ := ftTau a 1 (2 - 1) with hτdef
  set z := ftBranchZ a c 1 (2 - 1) with hzdef
  set K : Set ℝ := Set.Icc e (π / ((1 : ℕ) : ℝ) - e) with hKdef
  have hKsub : K ⊆ Ioo 0 (π / ((1 : ℕ) : ℝ)) := fun θ hθ =>
    ⟨lt_of_lt_of_le he hθ.1, lt_of_le_of_lt hθ.2 (by linarith)⟩
  have hKπ : K ⊆ Ioo 0 π := fun θ hθ => ftArc_subset le_rfl (hKsub hθ)
  obtain ⟨hrootA, hposA, -, -⟩ :=
    ft_branch_supplies (a := a) (c := c) (by norm_num) ha hc le_rfl (Or.inl le_rfl)
  have hτpos : ∀ θ ∈ K, 0 < τ θ := fun θ hθ => hposA θ (hKsub hθ)
  have hτcont : ContinuousOn τ K := fun θ hθ =>
    (continuousAt_ftTau_principal (by norm_num) ha le_rfl (Or.inl le_rfl)
      (hKsub hθ)).continuousWithinAt
  obtain ⟨θm, hθm, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨e, le_rfl, hlo⟩ hτcont
  refine ⟨τ θm + 1, by linarith [hτpos θm hθm], fun θ hθ => (hmax hθ).trans_lt (by linarith),
    fun θ hθ t _ hzero => ?_⟩
  set P := ftDen (ftRootPoly c a) 1 ((z θ : ℝ) : ℂ) with hPdef
  have hQ0 : (ftRootPoly c a).eval 0 ≠ 0 := by
    rw [eval_ftRootPoly]
    refine mul_ne_zero (Complex.ofReal_ne_zero.2 hc.ne') (Finset.prod_ne_zero_iff.2 fun k _ => ?_)
    simpa using Complex.ofReal_ne_zero.2 (ha k).ne'
  have hP0 : P.eval 0 ≠ 0 := by rw [hPdef, ftDen_eval]; simpa using hQ0
  have hPne : P ≠ 0 := fun h => hP0 (by rw [h]; simp)
  have hdeg : P.natDegree ≤ 2 := by
    refine le_trans (natDegree_add_le _ _) ?_
    rw [max_le_iff]
    refine ⟨le_of_eq (natDegree_ftRootPoly hc.ne' a), ?_⟩
    exact le_trans (natDegree_C_mul_le _ _) (by simp)
  have hu : P.eval (ftPrincipal τ θ) = 0 := hrootA θ (hKsub hθ)
  have hv : P.eval ((starRingEnd ℂ) (ftPrincipal τ θ)) = 0 :=
    ftPrincipal_conj_eval_eq_zero (hasRealCoeffs_ftRootPoly c a) hu
  have huv : ftPrincipal τ θ ≠ (starRingEnd ℂ) (ftPrincipal τ θ) := by
    rw [conj_ftPrincipal]
    exact ftPrincipal_ne_arcPoint_of_pos (hτpos θ hθ) (hKπ hθ)
  rcases eq_of_root_of_natDegree_le_two hPne hdeg hu hv huv hzero with h | h
  · exact Or.inl h
  · exact Or.inr (by rwa [conj_ftPrincipal] at h)

/-- **`interior_data_of_geometry` at the branch with no analytic hypothesis at
all**, on the quadratic pencil the separation witness covers.  This is what makes
`ft_interior_data_at_branch` a theorem with content rather than a shell. -/
theorem ft_interior_data_at_branch_nonvacuous {a : Fin 2 → ℝ} {c : ℝ} {B : Polynomial ℂ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    {e : ℝ} (he : 0 < e) (hlo : e ≤ π / ((1 : ℕ) : ℝ) - e) :
    ∃ (CI σI AI : ℝ),
      0 < σI ∧ σI < 1 ∧ 0 < AI ∧
      (∀ (M : ℕ) (θ : ℝ), e ≤ θ → θ ≤ π / ((1 : ℕ) : ℝ) - e →
        |ftRemainder (ftRootPoly c a) B 1 (ftBranchZ a c 1 (2 - 1))
          (ftTau a 1 (2 - 1)) M θ| ≤ CI * σI ^ M) ∧
      (∀ θ : ℝ, e ≤ θ → θ ≤ π / ((1 : ℕ) : ℝ) - e →
        AI * ∏ θj ∈ ftAmplitudeDivisor (ftRootPoly c a) B 1 (ftBranchZ a c 1 (2 - 1))
              (ftTau a 1 (2 - 1)) e (π / ((1 : ℕ) : ℝ) - e),
            |θ - θj| ^ (B.rootMultiplicity (ftPrincipal (ftTau a 1 (2 - 1)) θj))
          ≤ ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZ a c 1 (2 - 1))
              (ftTau a 1 (2 - 1)) θ) ∧
      (∀ θj ∈ ftAmplitudeDivisor (ftRootPoly c a) B 1 (ftBranchZ a c 1 (2 - 1))
          (ftTau a 1 (2 - 1)) e (π / ((1 : ℕ) : ℝ) - e),
        1 ≤ B.rootMultiplicity (ftPrincipal (ftTau a 1 (2 - 1)) θj)) := by
  obtain ⟨R₀, hR₀, hτR, hpair⟩ := ft_interior_separation_quadratic ha hc he hlo
  have harc : Set.Icc e (π / ((1 : ℕ) : ℝ) - e) ⊆ Set.Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)) :=
    fun θ hθ => ⟨lt_of_lt_of_le he hθ.1, lt_of_le_of_lt hθ.2 (by linarith)⟩
  exact ft_interior_data_at_branch (τ := ftTau a 1 (2 - 1)) (by norm_num) ha hc le_rfl
    (Or.inl le_rfl) hB hB0 (fun _ _ => rfl) hlo harc hR₀ hτR hpair


/-! ### The interior supply on a compact subinterval, with no separating radius assumed

`ft_interior_data_at_branch` still carries the uniform separation radius.  It need
not: `InteriorSeparation` produces a radius on a *neighborhood* of each angle from
the pointwise gap `thm:FT-geometry` already states, and finitely many of those
cover the subinterval.  Running the supply on each piece and reassembling with
`interior_data_of_pieces` leaves nothing about the separation to assume.

**Differs from the paper's route.**  `subsec:proof` works with one separating
circle across the compact interior.  Here the circle is allowed to change finitely
often, because one circle for the whole interior is a comparison between `sup τ`
and the non-principal infimum at *different* angles, which `thm:FT-geometry`'s
modulus ratio does not supply.  Nothing is lost: the constants reassemble over a
finite set, and `scripts/check_interior_fixed_radius.py` records that a single
circle does in fact serve on every pencil measured — as a measurement, not as an
assumption. -/

/-- **The interior supply on `[lo, hi]` from the pointwise gap alone.**  The
separating radius is no longer a hypothesis: `hmin` is `thm:FT-geometry`'s own
statement, that every non-principal denominator zero has modulus strictly above
`τ(θ)` at each angle separately, and everything else comes from the admissible
class.

At `r = 1` with `3 ≤ n` the last hypothesis is discharged too, by
`FTGeometryClosure.ft_geometry_at_branch_pi`, so the supply is then unconditional.

**Containment.**  No hypothesis mentions `ftRemainder` or `ftPrincipalAmp`; the
conclusion relates them. -/
theorem exists_interior_data_on_subinterval {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    {B : Polynomial ℂ} {τ : ℝ → ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    (hagree : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / r), τ θ = ftTau a r (n - 1) θ)
    {lo hi : ℝ} (hlohi : lo ≤ hi)
    (harc : Set.Icc lo hi ⊆ Set.Ioo (0 : ℝ) (π / r))
    (hmin : ∀ θ ∈ Set.Icc lo hi, ∀ w : ℂ,
      (ftDen (ftRootPoly c a) r ((ftBranchZ a c r (n - 1) θ : ℝ) : ℂ)).eval w = 0 →
      w ≠ ftPrincipal τ θ →
      w ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) → τ θ < ‖w‖) :
    ∃ (CI σI AI : ℝ) (S : Finset ℝ),
      0 < σI ∧ σI < 1 ∧ 0 < AI ∧
      (∀ (M : ℕ) (θ : ℝ), lo ≤ θ → θ ≤ hi →
        |ftRemainder (ftRootPoly c a) B r (ftBranchZ a c r (n - 1)) τ M θ|
          ≤ CI * σI ^ M) ∧
      (∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
        AI * ∏ θj ∈ S, |θ - θj| ^ (B.rootMultiplicity (ftPrincipal τ θj))
          ≤ ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1)) τ θ) ∧
      (∀ θj ∈ S, 1 ≤ B.rootMultiplicity (ftPrincipal τ θj)) ∧
      (∀ θj ∈ S, θj ∈ Set.Icc lo hi) := by
  classical
  set Q : Polynomial ℂ := ftRootPoly c a with hQdef
  set z : ℝ → ℝ := ftBranchZ a c r (n - 1) with hzdef
  set K : Set ℝ := Set.Icc lo hi with hKdef
  have hKπ : K ⊆ Ioo 0 π := fun θ hθ => ftArc_subset hr (harc hθ)
  obtain ⟨hrootA, hposA, -, hzcontA⟩ := ft_branch_supplies (a := a) (c := c) hn ha hc hr hnr
  have hTeq : ∀ θ ∈ K, τ θ = ftTau a r (n - 1) θ := fun θ hθ => hagree θ (harc hθ)
  have hprin : ∀ θ ∈ K, ftPrincipal τ θ = ftPrincipal (ftTau a r (n - 1)) θ :=
    fun θ hθ => ftPrincipal_congr (hTeq θ hθ)
  have hτpos : ∀ θ ∈ K, 0 < τ θ := fun θ hθ => (hTeq θ hθ) ▸ hposA θ (harc hθ)
  have hQ0 : Q.eval 0 ≠ 0 := by
    rw [hQdef, eval_ftRootPoly]
    refine mul_ne_zero (Complex.ofReal_ne_zero.2 hc.ne') (Finset.prod_ne_zero_iff.2 fun k _ => ?_)
    simpa using Complex.ofReal_ne_zero.2 (ha k).ne'
  have hPne : ∀ θ ∈ K, ftDen Q r ((z θ : ℝ) : ℂ) ≠ 0 := by
    intro θ _ h0
    exact hQ0 (by
      have : (ftDen Q r ((z θ : ℝ) : ℂ)).eval 0 = Q.eval 0 := by
        rw [ftDen_eval, zero_pow (by omega : r ≠ 0), mul_zero, add_zero]
      rw [← this, h0]; simp)
  have hroot : ∀ θ ∈ K, (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0 := by
    intro θ hθ; rw [hprin θ hθ]; exact hrootA θ (harc hθ)
  have hsimple := fun (θ : ℝ) (hθ : θ ∈ K) =>
    ft_principal_simple_at_branch (a := a) (c := c) hn ha hc.ne' hr hnr (harc hθ)
  have hsp : ∀ θ ∈ K,
      (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0 := by
    intro θ hθ; rw [hprin θ hθ]; exact (hsimple θ hθ).1
  have hsm : ∀ θ ∈ K, (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
      (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)) ≠ 0 := by
    intro θ hθ
    have h := (hsimple θ hθ).2
    rw [conj_ftPrincipal] at h
    rwa [hTeq θ hθ]
  have hne : ∀ θ ∈ K, ftPrincipal τ θ
      ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) :=
    fun θ hθ => ftPrincipal_ne_arcPoint_of_pos (hτpos θ hθ) (hKπ hθ)
  have hrootminus : ∀ θ ∈ K, (ftDen Q r ((z θ : ℝ) : ℂ)).eval
      (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)) = 0 := by
    intro θ hθ
    have h := ftPrincipal_conj_eval_eq_zero (hasRealCoeffs_ftRootPoly c a) (hroot θ hθ)
    rwa [conj_ftPrincipal] at h
  have hzc : ∀ θ ∈ K, ContinuousAt (fun θ' => ((z θ' : ℝ) : ℂ)) θ := by
    intro θ hθ
    exact Complex.continuous_ofReal.continuousAt.comp
      (hzcontA.continuousAt (isOpen_Ioo.mem_nhds (harc hθ)))
  have hτc : ∀ θ ∈ K, ContinuousAt τ θ := by
    intro θ hθ
    refine (continuousAt_ftTau_principal hn ha hr hnr (harc hθ)).congr ?_
    filter_upwards [isOpen_Ioo.mem_nhds (harc hθ)] with x hx using (hagree x hx).symm
  -- a radius on a ball about each angle, from the pointwise gap
  have key : ∀ θ₀ ∈ K, ∃ (ρ δ : ℝ), 0 < ρ ∧ 0 < δ ∧
      ∀ θ ∈ Set.Icc (θ₀ - δ) (θ₀ + δ), θ ∈ K →
        τ θ < ρ ∧ ∀ w : ℂ, ‖w‖ ≤ ρ → (ftDen Q r ((z θ : ℝ) : ℂ)).eval w = 0 →
          w = ftPrincipal τ θ
            ∨ w = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I) := by
    intro θ₀ hθ₀
    obtain ⟨ρ, hρpos, hev⟩ := exists_neighborhood_separation (hzc θ₀ hθ₀) (hτc θ₀ hθ₀)
      (hPne θ₀ hθ₀) (hτpos θ₀ hθ₀) (hroot θ₀ hθ₀) (hsp θ₀ hθ₀) (hsm θ₀ hθ₀)
      (hne θ₀ hθ₀) (hrootminus θ₀ hθ₀) (hmin θ₀ hθ₀)
    obtain ⟨d, hd0, hdsub⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨ρ, d / 2, hρpos, by positivity, fun θ hθball hθK => ?_⟩
    have hdist : dist θ θ₀ < d := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> [linarith [hθball.1]; linarith [hθball.2]]
    obtain ⟨hτθ, hsep⟩ := hdsub hdist
    exact ⟨hτθ, hsep (hPne θ hθK) (hroot θ hθK) (hrootminus θ hθK) (hτpos θ hθK)
      (hne θ hθK)⟩
  choose! ρ δ hρpos hδpos hprop using key
  -- finitely many of the balls cover
  obtain ⟨t, htK, htfin, htcover⟩ :=
    (isCompact_Icc (a := lo) (b := hi)).elim_finite_subcover_image
      (b := K) (c := fun θ₀ => Metric.ball θ₀ (δ θ₀))
      (fun θ _ => Metric.isOpen_ball)
      (fun θ hθ => Set.mem_biUnion hθ (Metric.mem_ball_self (hδpos θ hθ)))
  -- the closed pieces
  set F : Finset ℝ := htfin.toFinset with hF
  have hFmem : ∀ θ₀, θ₀ ∈ F ↔ θ₀ ∈ t := fun θ₀ => Set.Finite.mem_toFinset htfin
  have hFne : F.Nonempty := by
    obtain ⟨θ₀, hθ₀t, -⟩ := Set.mem_iUnion₂.1 (htcover ⟨le_rfl, hlohi⟩)
    exact ⟨θ₀, (hFmem θ₀).2 hθ₀t⟩
  set A : ℝ → ℝ := fun θ₀ => max lo (θ₀ - δ θ₀) with hA
  set Bd : ℝ → ℝ := fun θ₀ => min hi (θ₀ + δ θ₀) with hBd
  have hpiece : ∀ θ₀ ∈ F, Set.Icc (A θ₀) (Bd θ₀) ⊆ K := fun θ₀ _ θ hθ =>
    ⟨le_trans (le_max_left _ _) hθ.1, le_trans hθ.2 (min_le_left _ _)⟩
  have hpieceball : ∀ θ₀ ∈ F, ∀ θ ∈ Set.Icc (A θ₀) (Bd θ₀),
      θ ∈ Set.Icc (θ₀ - δ θ₀) (θ₀ + δ θ₀) := fun θ₀ _ θ hθ =>
    ⟨le_trans (le_max_right _ _) hθ.1, le_trans hθ.2 (min_le_right _ _)⟩
  have hAB : ∀ θ₀ ∈ F, A θ₀ ≤ Bd θ₀ := by
    intro θ₀ hθ₀
    have hθ₀K : θ₀ ∈ K := htK ((hFmem θ₀).1 hθ₀)
    have hd := hδpos θ₀ hθ₀K
    exact le_trans (max_le hθ₀K.1 (by linarith)) (le_min hθ₀K.2 (by linarith))
  -- the supply on each piece
  have hsupply : ∀ θ₀ ∈ F, ∃ CIi σIi AIi : ℝ, 0 ≤ CIi ∧ 0 < σIi ∧ σIi < 1 ∧ 0 < AIi ∧
      (∀ (M : ℕ) (θ : ℝ), θ ∈ Set.Icc (A θ₀) (Bd θ₀) →
        |ftRemainder Q B r z τ M θ| ≤ CIi * σIi ^ M) ∧
      (∀ θ : ℝ, θ ∈ Set.Icc (A θ₀) (Bd θ₀) →
        AIi * ∏ θj ∈ ftAmplitudeDivisor Q B r z τ (A θ₀) (Bd θ₀),
            |θ - θj| ^ (B.rootMultiplicity (ftPrincipal τ θj))
          ≤ ftPrincipalAmp Q B r z τ θ) ∧
      (∀ θj ∈ ftAmplitudeDivisor Q B r z τ (A θ₀) (Bd θ₀),
        1 ≤ B.rootMultiplicity (ftPrincipal τ θj)) := by
    intro θ₀ hθ₀
    have hθ₀K : θ₀ ∈ K := htK ((hFmem θ₀).1 hθ₀)
    obtain ⟨CIi, σIi, AIi, hσ0, hσ1, hA0, hrem, hfloor, hν⟩ :=
      ft_interior_data_at_branch (τ := τ) hn ha hc hr hnr hB hB0 hagree (hAB θ₀ hθ₀)
        (fun θ hθ => harc (hpiece θ₀ hθ₀ hθ)) (hρpos θ₀ hθ₀K)
        (fun θ hθ => (hprop θ₀ hθ₀K θ (hpieceball θ₀ hθ₀ θ hθ) (hpiece θ₀ hθ₀ hθ)).1)
        (fun θ hθ w hw hzero =>
          (hprop θ₀ hθ₀K θ (hpieceball θ₀ hθ₀ θ hθ) (hpiece θ₀ hθ₀ hθ)).2 w hw hzero)
    exact ⟨max CIi 0, σIi, AIi, le_max_right _ _, hσ0, hσ1, hA0,
      fun M θ hθ => le_trans (hrem M θ hθ.1 hθ.2)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hσ0.le M)),
      fun θ hθ => hfloor θ hθ.1 hθ.2, hν⟩
  choose! CIi σIi AIi hCI0 hσ0 hσ1 hA0 hrem hfloor hν using hsupply
  obtain ⟨CI, σI, AI, hσIpos, hσIlt, hAIpos, hremall, hfloorall, hνall, hSsuball⟩ :=
    interior_data_of_pieces (Q := Q) (B := B) (r := r) (z := z) (τ := τ)
      (lo := lo) (hi := hi) (t := F) hFne
      (P := fun θ₀ θ => θ ∈ Set.Icc (A θ₀) (Bd θ₀))
      (S := fun θ₀ => ftAmplitudeDivisor Q B r z τ (A θ₀) (Bd θ₀))
      (ν := fun θj => B.rootMultiplicity (ftPrincipal τ θj))
      (fun θ h1 h2 => by
        obtain ⟨θ₀, hθ₀t, hθ₀b⟩ := Set.mem_iUnion₂.1 (htcover ⟨h1, h2⟩)
        have hθ₀K : θ₀ ∈ K := htK hθ₀t
        have hdist : |θ - θ₀| < δ θ₀ := by
          simpa [Real.dist_eq] using Metric.mem_ball.1 hθ₀b
        rw [abs_lt] at hdist
        exact ⟨θ₀, (hFmem θ₀).2 hθ₀t,
          ⟨max_le h1 (by linarith [hdist.1]), le_min h2 (by linarith [hdist.2])⟩⟩)
      hCI0 hσ0 hσ1 hA0
      (fun θ₀ hθ₀ θj hθj => hpiece θ₀ hθ₀ (ftAmplitudeDivisor_subset hθj))
      hrem hfloor hν
  exact ⟨CI, σI, AI, F.biUnion (fun θ₀ => ftAmplitudeDivisor Q B r z τ (A θ₀) (Bd θ₀)),
    hσIpos, hσIlt, hAIpos, hremall, hfloorall, hνall, hSsuball⟩


/-- **The interior supply on a compact subinterval, unconditionally.**  At `r = 1`
with a simple or repeated smallest zero and `3 ≤ n` — the manuscript's own
exclusion of `(deg Q, r) = (2,1)` — `FTGeometryClosure.ft_geometry_at_branch_pi`
discharges the pointwise gap, so nothing at all is assumed beyond the admissible
class and the extension of `ftTau` past the open arc.

This is `interior_data_of_geometry`'s conclusion at the paper's own branch with an
empty hypothesis list, which is what `thm:weighted-dominance`'s interior group
needed and did not have. -/
theorem exists_interior_data_on_subinterval_pi {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    {B : Polynomial ℂ} {τ : ℝ → ℝ}
    (hn3 : 3 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    (hagree : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)), τ θ = ftTau a 1 (n - 1) θ)
    {lo hi : ℝ} (hlohi : lo ≤ hi)
    (harc : Set.Icc lo hi ⊆ Set.Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ))) :
    ∃ (CI σI AI : ℝ) (S : Finset ℝ),
      0 < σI ∧ σI < 1 ∧ 0 < AI ∧
      (∀ (M : ℕ) (θ : ℝ), lo ≤ θ → θ ≤ hi →
        |ftRemainder (ftRootPoly c a) B 1 (ftBranchZ a c 1 (n - 1)) τ M θ|
          ≤ CI * σI ^ M) ∧
      (∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
        AI * ∏ θj ∈ S, |θ - θj| ^ (B.rootMultiplicity (ftPrincipal τ θj))
          ≤ ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZ a c 1 (n - 1)) τ θ) ∧
      (∀ θj ∈ S, 1 ≤ B.rootMultiplicity (ftPrincipal τ θj)) ∧
      (∀ θj ∈ S, θj ∈ Set.Icc lo hi) := by
  obtain ⟨za, b, -, -, hdisk⟩ := ft_geometry_at_branch_pi hn3 ha hc
  refine exists_interior_data_on_subinterval (by omega) ha hc le_rfl (Or.inl (by omega))
    hB hB0 hagree hlohi harc ?_
  intro θ hθ w hzero hwp hwm
  by_contra hcon
  push Not at hcon
  have hθarc : θ ∈ Set.Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)) := harc hθ
  have hTeq : τ θ = ftTau a 1 (n - 1) θ := hagree θ hθarc
  have hprin : ftPrincipal τ θ = ftPrincipal (ftTau a 1 (n - 1)) θ :=
    ftPrincipal_congr hTeq
  rcases hdisk θ hθarc w hzero (by rw [← hTeq]; exact hcon) with h | h
  · exact hwp (by rw [h, ← hprin])
  · refine hwm ?_
    rw [h, conj_ftPrincipal, ← hTeq]


/-- **The interior supply on a compact subinterval at every `r ≥ 2`,
unconditionally.**  The exact parallel of `exists_interior_data_on_subinterval_pi`
with `FTGeometryCone.ft_minModulus_at_branch_two_le` in place of
`FTGeometryClosure.ft_geometry_at_branch_pi`.

Together the two cover every `r ≥ 1` the paper admits: `r = 1` needs `3 ≤ n`,
which is `thm:FT-geometry`'s own exclusion of `(deg Q, r) = (2,1)`, and `r ≥ 2`
needs only `2 ≤ n`.  So `thm:weighted-dominance`'s interior group carries no
hypothesis beyond the admissible class at any `r`. -/
theorem exists_interior_data_on_subinterval_two_le {n r : ℕ} {a : Fin n → ℝ} {c : ℝ}
    {B : Polynomial ℂ} {τ : ℝ → ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    (hagree : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / r), τ θ = ftTau a r (n - 1) θ)
    {lo hi : ℝ} (hlohi : lo ≤ hi)
    (harc : Set.Icc lo hi ⊆ Set.Ioo (0 : ℝ) (π / r)) :
    ∃ (CI σI AI : ℝ) (S : Finset ℝ),
      0 < σI ∧ σI < 1 ∧ 0 < AI ∧
      (∀ (M : ℕ) (θ : ℝ), lo ≤ θ → θ ≤ hi →
        |ftRemainder (ftRootPoly c a) B r (ftBranchZ a c r (n - 1)) τ M θ|
          ≤ CI * σI ^ M) ∧
      (∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
        AI * ∏ θj ∈ S, |θ - θj| ^ (B.rootMultiplicity (ftPrincipal τ θj))
          ≤ ftPrincipalAmp (ftRootPoly c a) B r (ftBranchZ a c r (n - 1)) τ θ) ∧
      (∀ θj ∈ S, 1 ≤ B.rootMultiplicity (ftPrincipal τ θj)) ∧
      (∀ θj ∈ S, θj ∈ Set.Icc lo hi) := by
  refine exists_interior_data_on_subinterval (by omega) ha hc (by omega) (Or.inl hn2)
    hB hB0 hagree hlohi harc ?_
  intro θ hθ w hzero hwp hwm
  have hθarc : θ ∈ Set.Ioo (0 : ℝ) (π / r) := harc hθ
  have hTeq : τ θ = ftTau a r (n - 1) θ := hagree θ hθarc
  have hprin : ftPrincipal τ θ = ftPrincipal (ftTau a r (n - 1)) θ :=
    ftPrincipal_congr hTeq
  rw [hTeq]
  refine ft_minModulus_at_branch_two_le hn2 ha hc hr θ hθarc w hzero ?_ ?_
  · rw [← hprin]; exact hwp
  · rw [conj_ftPrincipal, ← hTeq]; exact hwm

end ForgacsTran
