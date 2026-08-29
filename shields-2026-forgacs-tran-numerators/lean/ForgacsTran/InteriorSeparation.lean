/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import Shields.Analysis.Complex.ArgumentPrinciple.Polynomial
import ForgacsTran.DominanceFT
import ForgacsTran.FTGeometryAssembly

/-!
# The separating circle, without tracking a root

`thm:FT-geometry`'s compact-separation clause says the non-principal denominator
zeros stay away from the principal pair uniformly on a compact subinterval.
`FTGeometryAssembly.ft_geometry_compact_separation` proves it, but takes an
enumeration of those zeros as continuous functions of the angle — continuity of
roots, which the pinned Mathlib does not carry.

No enumeration is needed.  The **count** of zeros inside a fixed circle is what
the argument gets to move, and Rouché controls it without ever saying which zero
went where: the pencil enters `D = Q + zX^r` linearly, so two parameters differ
on the circle `|t| = R` by exactly `|z₂ - z₁|R^r`, and once that is below the
circle's own minimum of `|D|` the counts agree.

`Shields.card_rootsIn_add_eq` is that step, already proved.  What is added here is
the parameter form — the count is locally constant in the angle — and the reading
of a count of two as the disk clause: the principal pair are two simple zeros, so
a disk holding exactly two zeros with multiplicity holds them and nothing else.

## Main statements

* `ftDen_eq_add_ftDen` — the pencil's linear dependence on the spectral parameter.
* `card_rootsIn_ftDen_eq_of_norm_lt` — Rouché between two parameters, over the
  circle's minimum of `|D|`.
* `exists_min_norm_on_sphere` — that minimum, produced by compactness.
* `card_rootsIn_ftDen_eventuallyEq` — **the count is locally constant in the
  angle**, given continuity of `z` and no zero on the circle at the base angle.
* `card_rootsIn_eq_two_of_pair` — a disk carrying the principal pair and no other
  zero carries exactly two zeros with multiplicity.
* `pair_of_card_rootsIn_eq_two` — its converse, which is the disk clause: a count
  of two forces every zero of the disk to be one of the pair.
* `exists_local_separation` — the two composed: at an angle where the pair are the
  only zeros in a closed disk, the pair are the only zeros in that same disk for
  **every nearby angle**.  This is the local half of the uniform separation, with
  no root enumerated anywhere.
* `exists_separation_radius` — a radius at one angle, fitted between `τ(θ₀)` and
  the finitely many other moduli, and missed by the zero set so the circle is free.
* `exists_neighborhood_separation` — that radius, surviving a neighborhood.
* `exists_finite_separation_cover` — **the compact interior covered by finitely
  many separating radii**, which is what `thm:weighted-dominance`'s interior
  hypothesis is met on.  Its inputs are exactly what the branch already supplies:
  `FTGeometryClosure.ft_geometry_at_branch_pi` gives the pointwise gap (as the disk
  clause, its contrapositive), `PrincipalSimpleBranch.ft_principal_simple_at_branch`
  the two simplicity clauses, and `FTGeometryAssembly.ftPrincipal_ne_arcPoint_of_pos`
  the pair being distinct.

## Implementation notes

**A single radius for the whole interior is not produced, and is not what
`thm:FT-geometry` gives.**  The theorem's separation is a modulus *ratio*, compared
at one angle; one radius across the interior compares `sup τ` against the
non-principal infimum at *different* angles, and no same-angle statement settles
that.  The cover is therefore finite rather than a singleton, which costs nothing
downstream — `DominanceFTSupply.interior_data_of_geometry` runs on each piece with that
piece's radius, and its constants reassemble over a finite set.

`scripts/check_interior_fixed_radius.py` measures the stronger form: on eight
pencils and four interior parameters the whole interior does admit one radius,
margins `2.85x` to `34x`, because `sup τ` and the non-principal infimum fall at the
same endpoint.  That is a monotonicity property of the branch and is deliberately
not assumed here, so nothing depends on a pencil having been sampled.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry,
residues, and the principal amplitude» (`sec:geometry`, `thm:FT-geometry`), the
compact-separation clause.

## Tags

Rouche, root count, separating circle, Forgacs-Tran geometry
-/

namespace ForgacsTran

open Polynomial Metric Complex

/-! ### The pencil is linear in the spectral parameter -/

/-- `D(·, w₂) = D(·, w₁) + (w₂ - w₁)X^r`.  This is the whole reason a root count
transfers between two parameters without any root being followed. -/
theorem ftDen_eq_add_ftDen {Q : Polynomial ℂ} {r : ℕ} (w₁ w₂ : ℂ) :
    ftDen Q r w₂ = ftDen Q r w₁ + C (w₂ - w₁) * X ^ r := by
  simp only [ftDen, map_sub]
  ring

/-- The minimum of `|D|` on a circle, produced by compactness — positive exactly
when the circle carries no zero. -/
theorem exists_min_norm_on_sphere {P : Polynomial ℂ} {R : ℝ} (hR : 0 < R)
    (hns : ∀ t ∈ sphere (0 : ℂ) R, P.eval t ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ sphere (0 : ℂ) R, m ≤ ‖P.eval t‖ := by
  have hne : ((R : ℂ)) ∈ sphere (0 : ℂ) R := by
    simp [abs_of_pos hR]
  obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_sphere (0 : ℂ) R).exists_isMinOn ⟨_, hne⟩
    (P.continuous.norm.continuousOn)
  exact ⟨‖P.eval t₀‖, norm_pos_iff.mpr (hns t₀ ht₀), fun t ht => isMinOn_iff.mp hmin t ht⟩

/-- **Rouché between two spectral parameters.**  The two pencils differ on the
circle by `|w₂ - w₁|R^r`; below the circle's own minimum of `|D(·,w₁)|` the two
counts agree. -/
theorem card_rootsIn_ftDen_eq_of_norm_lt {Q : Polynomial ℂ} {r : ℕ} {R m : ℝ} (hR : 0 < R)
    {w₁ w₂ : ℂ}
    (hm : ∀ t ∈ sphere (0 : ℂ) R, m ≤ ‖(ftDen Q r w₁).eval t‖)
    (hlt : ‖w₂ - w₁‖ * R ^ r < m) :
    (Shields.rootsIn (ftDen Q r w₁) 0 R).card
      = (Shields.rootsIn (ftDen Q r w₂) 0 R).card := by
  rw [ftDen_eq_add_ftDen w₁ w₂]
  refine Shields.card_rootsIn_add_eq hR fun t ht => ?_
  have hnt : ‖t‖ = R := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 ht
  have hval : ‖(C (w₂ - w₁) * X ^ r).eval t‖ = ‖w₂ - w₁‖ * R ^ r := by
    rw [eval_mul, eval_C, eval_pow, eval_X, norm_mul, norm_pow, hnt]
  rw [hval]
  exact lt_of_lt_of_le hlt (hm t ht)

/-- **The count inside a fixed circle is locally constant in the angle.**  Nothing
is assumed about how the zeros move; only that `z` is continuous and that the
circle carries no zero at the base angle. -/
theorem card_rootsIn_ftDen_eventuallyEq {Q : Polynomial ℂ} {r : ℕ} {R : ℝ} (hR : 0 < R)
    {z : ℝ → ℝ} {θ₀ : ℝ} (hz : ContinuousAt (fun θ => ((z θ : ℝ) : ℂ)) θ₀)
    (hns : ∀ t ∈ sphere (0 : ℂ) R, (ftDen Q r ((z θ₀ : ℝ) : ℂ)).eval t ≠ 0) :
    ∀ᶠ θ in nhds θ₀,
      (Shields.rootsIn (ftDen Q r ((z θ : ℝ) : ℂ)) 0 R).card
        = (Shields.rootsIn (ftDen Q r ((z θ₀ : ℝ) : ℂ)) 0 R).card := by
  obtain ⟨m, hmpos, hm⟩ := exists_min_norm_on_sphere hR hns
  have hRr : (0 : ℝ) < R ^ r := pow_pos hR r
  have hball : ∀ᶠ θ in nhds θ₀,
      ‖((z θ : ℝ) : ℂ) - ((z θ₀ : ℝ) : ℂ)‖ < m / R ^ r := by
    have := hz (Metric.ball_mem_nhds ((z θ₀ : ℝ) : ℂ) (by positivity : (0:ℝ) < m / R ^ r))
    filter_upwards [this] with θ hθ
    simpa [Complex.dist_eq] using mem_ball.1 hθ
  filter_upwards [hball] with θ hθ
  refine (card_rootsIn_ftDen_eq_of_norm_lt hR hm ?_).symm
  rw [← lt_div_iff₀ hRr]
  exact hθ

/-! ### A count of two is the disk clause -/

/-- A simple zero appears exactly once in the root multiset.  `char 0` gives
`mult(P') = mult(P) - 1`, so a multiplicity of two or more would put the zero on
the derivative. -/
theorem count_roots_eq_one {P : Polynomial ℂ} {t : ℂ} (hP : P ≠ 0) (hroot : P.eval t = 0)
    (hsimple : (derivative P).eval t ≠ 0) : P.roots.count t = 1 := by
  classical
  have hIsRoot : P.IsRoot t := hroot
  have hd := derivative_rootMultiplicity_of_root (R := ℂ) hIsRoot
  have hpos : 0 < P.rootMultiplicity t := (rootMultiplicity_pos hP).2 hroot
  have hle : P.rootMultiplicity t ≤ 1 := by
    by_contra h
    push Not at h
    have h2 : 1 ≤ P.rootMultiplicity t - 1 := by omega
    have hdne : derivative P ≠ 0 := fun h0 => hsimple (by rw [h0]; simp)
    exact hsimple ((rootMultiplicity_pos hdne).1 (by rw [hd]; omega))
  rw [count_roots]
  omega

/-- **A disk carrying the principal pair and nothing else carries exactly two
zeros**, counted with multiplicity: both members are simple, so each contributes
one and the count is `2`. -/
theorem card_rootsIn_eq_two_of_pair {P : Polynomial ℂ} {R : ℝ} {tp tm : ℂ} (hP : P ≠ 0)
    (hne : tp ≠ tm)
    (hrp : P.eval tp = 0) (hrm : P.eval tm = 0)
    (hsp : (derivative P).eval tp ≠ 0) (hsm : (derivative P).eval tm ≠ 0)
    (hbp : ‖tp‖ < R) (hbm : ‖tm‖ < R)
    (honly : ∀ t : ℂ, ‖t‖ < R → P.eval t = 0 → t = tp ∨ t = tm) :
    (Shields.rootsIn P 0 R).card = 2 := by
  classical
  set M : Multiset ℂ := Shields.rootsIn P 0 R with hM
  have hmemM : ∀ a : ℂ, a ∈ M ↔ (a ∈ P.roots ∧ ‖a‖ < R) := by
    intro a
    rw [hM, Shields.mem_rootsIn, mem_ball, dist_zero_right]
  have hcount : ∀ a : ℂ, ‖a‖ < R → M.count a = P.roots.count a := by
    intro a ha
    rw [hM, Shields.rootsIn, Multiset.count_filter_of_pos (by simpa [dist_zero_right] using ha)]
  have hsupp : M.toFinset = ({tp, tm} : Finset ℂ) := by
    apply Finset.Subset.antisymm
    · intro a ha
      obtain ⟨-, haR⟩ := (hmemM a).1 (Multiset.mem_toFinset.1 ha)
      have := honly a haR ((mem_roots hP).1 ((hmemM a).1 (Multiset.mem_toFinset.1 ha)).1)
      simpa using this
    · intro a ha
      refine Multiset.mem_toFinset.2 ((hmemM a).2 ?_)
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact ⟨(mem_roots hP).2 hrp, hbp⟩
      · rw [Finset.mem_singleton.1 ha]
        exact ⟨(mem_roots hP).2 hrm, hbm⟩
  have hsum := Multiset.toFinset_sum_count_eq M
  rw [hsupp, Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    hcount tp hbp, hcount tm hbm, count_roots_eq_one hP hrp hsp,
    count_roots_eq_one hP hrm hsm] at hsum
  omega

/-- **The disk clause from the count.**  If the disk carries exactly two zeros and
the principal pair are two of them, it carries nothing else. -/
theorem pair_of_card_rootsIn_eq_two {P : Polynomial ℂ} {R : ℝ} {tp tm : ℂ} (hP : P ≠ 0)
    (hne : tp ≠ tm)
    (hrp : P.eval tp = 0) (hrm : P.eval tm = 0)
    (hbp : ‖tp‖ < R) (hbm : ‖tm‖ < R)
    (hcard : (Shields.rootsIn P 0 R).card = 2)
    {t : ℂ} (ht : ‖t‖ < R) (hroot : P.eval t = 0) : t = tp ∨ t = tm := by
  classical
  by_contra hcon
  push Not at hcon
  set M : Multiset ℂ := Shields.rootsIn P 0 R with hM
  have hmem : ∀ a : ℂ, ‖a‖ < R → P.eval a = 0 → a ∈ M := by
    intro a ha hra
    rw [hM, Shields.mem_rootsIn]
    exact ⟨(mem_roots hP).2 hra, by simpa [dist_zero_right] using ha⟩
  have hsub : ({tp, tm, t} : Finset ℂ) ⊆ M.toFinset := by
    intro a ha
    refine Multiset.mem_toFinset.2 ?_
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact hmem _ hbp hrp
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact hmem _ hbm hrm
    · rw [Finset.mem_singleton.1 ha]; exact hmem _ ht hroot
  have hcard3 : ({tp, tm, t} : Finset ℂ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne, fun h => hcon.1 h.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact fun h => hcon.2 h.symm),
      Finset.card_singleton]
  have h3 : 3 ≤ M.toFinset.card := hcard3 ▸ Finset.card_le_card hsub
  have h4 : M.toFinset.card ≤ M.card := Multiset.toFinset_card_le M
  omega

/-- **The local half of `thm:FT-geometry`'s compact separation, with no root
enumerated.**  At an angle where the principal pair are the only zeros in the disk
of radius `R` and the circle carries none, the same holds at every nearby angle.

The count is what moves: it is `2` at the base angle by
`card_rootsIn_eq_two_of_pair`, locally constant by
`card_rootsIn_ftDen_eventuallyEq`, and back to the disk clause by
`pair_of_card_rootsIn_eq_two`.  No zero is followed at any point, which is why
continuity of roots — absent from the pinned Mathlib — is not needed.

The conclusion quantifies over the pair at the *nearby* angle rather than naming
it, and that is deliberate: naming it would be following a root.  A caller does
not need it named — along the Forgács–Tran branch `ftPrincipal τ θ` and its
conjugate are two distinct zeros at every angle with no continuity used, so the
caller supplies them and the conclusion closes. -/
theorem exists_local_separation {Q : Polynomial ℂ} {r : ℕ} {R : ℝ} (hR : 0 < R)
    {z : ℝ → ℝ} {θ₀ : ℝ} {tp tm : ℂ}
    (hz : ContinuousAt (fun θ => ((z θ : ℝ) : ℂ)) θ₀)
    (hns : ∀ t ∈ sphere (0 : ℂ) R, (ftDen Q r ((z θ₀ : ℝ) : ℂ)).eval t ≠ 0)
    (hP : ftDen Q r ((z θ₀ : ℝ) : ℂ) ≠ 0) (hne : tp ≠ tm)
    (hrp : (ftDen Q r ((z θ₀ : ℝ) : ℂ)).eval tp = 0)
    (hrm : (ftDen Q r ((z θ₀ : ℝ) : ℂ)).eval tm = 0)
    (hsp : (derivative (ftDen Q r ((z θ₀ : ℝ) : ℂ))).eval tp ≠ 0)
    (hsm : (derivative (ftDen Q r ((z θ₀ : ℝ) : ℂ))).eval tm ≠ 0)
    (hbp : ‖tp‖ < R) (hbm : ‖tm‖ < R)
    (honly : ∀ t : ℂ, ‖t‖ < R → (ftDen Q r ((z θ₀ : ℝ) : ℂ)).eval t = 0 →
      t = tp ∨ t = tm) :
    ∀ᶠ θ in nhds θ₀, ∀ (up um : ℂ), up ≠ um →
      (ftDen Q r ((z θ : ℝ) : ℂ)).eval up = 0 → (ftDen Q r ((z θ : ℝ) : ℂ)).eval um = 0 →
      ‖up‖ < R → ‖um‖ < R → ftDen Q r ((z θ : ℝ) : ℂ) ≠ 0 →
      ∀ t : ℂ, ‖t‖ < R → (ftDen Q r ((z θ : ℝ) : ℂ)).eval t = 0 → t = up ∨ t = um := by
  have hbase : (Shields.rootsIn (ftDen Q r ((z θ₀ : ℝ) : ℂ)) 0 R).card = 2 :=
    card_rootsIn_eq_two_of_pair hP hne hrp hrm hsp hsm hbp hbm honly
  filter_upwards [card_rootsIn_ftDen_eventuallyEq hR hz hns] with θ hθ
  intro up um hupm hrup hrum hbup hbum hPθ t ht hrt
  refine pair_of_card_rootsIn_eq_two hPθ hupm hrup hrum hbup hbum ?_ ht hrt
  rw [hθ, hbase]


/-! ### From the pointwise gap to a local radius, and then to a cover

`thm:FT-geometry` gives the gap **pointwise**: at each angle every non-principal
zero has modulus strictly above `τ(θ)`.  `hpair` wants one radius across a whole
compact interior, and that is a comparison between `sup τ` and `inf` of the
non-principal modulus — across *different* angles, which no same-angle statement
settles.  What the pointwise gap does give, through `exists_local_separation`, is
a radius that works on a *neighborhood*; compactness then covers the interior with
finitely many of them.

That is the route taken here.  It needs no property of the non-principal modulus
beyond the pointwise gap, so it cannot fail on a pencil nobody sampled — which is
what a monotonicity route would risk. -/

/-- **A separating radius at one angle.**  The zeros are finitely many and the
non-principal ones all sit strictly above `τ(θ₀)`, so a radius fits between:
above `τ(θ₀)`, below every other modulus, and missed by the zero set entirely so
the circle is free. -/
theorem exists_separation_radius {Q : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {θ₀ : ℝ}
    (hP : ftDen Q r ((z θ₀ : ℝ) : ℂ) ≠ 0) (hτ : 0 < τ θ₀)
    (hmin : ∀ w : ℂ, (ftDen Q r ((z θ₀ : ℝ) : ℂ)).eval w = 0 →
      w ≠ ftPrincipal τ θ₀ →
      w ≠ ((τ θ₀ : ℝ) : ℂ) * Complex.exp (-((θ₀ : ℝ) : ℂ) * I) → τ θ₀ < ‖w‖) :
    ∃ ρ : ℝ, τ θ₀ < ρ ∧
      (∀ w ∈ sphere (0 : ℂ) ρ, (ftDen Q r ((z θ₀ : ℝ) : ℂ)).eval w ≠ 0) ∧
      (∀ w : ℂ, ‖w‖ < ρ → (ftDen Q r ((z θ₀ : ℝ) : ℂ)).eval w = 0 →
        w = ftPrincipal τ θ₀
          ∨ w = ((τ θ₀ : ℝ) : ℂ) * Complex.exp (-((θ₀ : ℝ) : ℂ) * I)) := by
  classical
  set D : Polynomial ℂ := ftDen Q r ((z θ₀ : ℝ) : ℂ) with hD
  set tp : ℂ := ftPrincipal τ θ₀ with htp
  set tm : ℂ := ((τ θ₀ : ℝ) : ℂ) * Complex.exp (-((θ₀ : ℝ) : ℂ) * I) with htm
  set T : Finset ℂ := D.roots.toFinset.filter (fun w => w ≠ tp ∧ w ≠ tm) with hT
  have hTgap : ∀ w ∈ T, τ θ₀ < ‖w‖ := by
    intro w hw
    have hf := Finset.mem_filter.1 hw
    exact hmin w ((mem_roots hP).1 (Multiset.mem_toFinset.1 hf.1)) hf.2.1 hf.2.2
  obtain ⟨ρ, hρgt, hρlt⟩ : ∃ ρ : ℝ, τ θ₀ < ρ ∧ ∀ w ∈ T, ρ < ‖w‖ := by
    rcases T.eq_empty_or_nonempty with hTe | hTne
    · exact ⟨τ θ₀ + 1, by linarith, fun w hw => absurd hw (by simp [hTe])⟩
    · obtain ⟨w₀, hw₀, hw₀min⟩ := T.exists_min_image (fun w => ‖w‖) hTne
      refine ⟨(τ θ₀ + ‖w₀‖) / 2, by linarith [hTgap w₀ hw₀], fun w hw => ?_⟩
      have := hw₀min w hw
      linarith [hTgap w₀ hw₀]
  have hnp : ‖tp‖ = τ θ₀ := norm_ftPrincipal_eq hτ
  have hnm : ‖tm‖ = τ θ₀ := by
    rw [htm, ← conj_polar, RCLike.norm_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hτ, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hclass : ∀ w : ℂ, D.eval w = 0 → w = tp ∨ w = tm ∨ w ∈ T := by
    intro w hw
    by_cases hwp : w = tp
    · exact Or.inl hwp
    by_cases hwm : w = tm
    · exact Or.inr (Or.inl hwm)
    exact Or.inr (Or.inr (Finset.mem_filter.2
      ⟨Multiset.mem_toFinset.2 ((mem_roots hP).2 hw), hwp, hwm⟩))
  refine ⟨ρ, hρgt, fun w hw hzero => ?_, fun w hw hzero => ?_⟩
  · have hnw : ‖w‖ = ρ := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 hw
    rcases hclass w hzero with rfl | rfl | hwT
    · rw [hnp] at hnw; linarith
    · rw [hnm] at hnw; linarith
    · exact absurd hnw (ne_of_gt (hρlt w hwT))
  · rcases hclass w hzero with h | h | hwT
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd hw (not_lt.2 (hρlt w hwT).le)

/-- **The separating radius survives a neighborhood.**  At `θ₀` the radius `ρ` of
`exists_separation_radius` works; the count is locally constant, so it works at
every nearby angle too — provided the pair is still inside, which continuity of
`τ` supplies.

Nothing about the non-principal zeros is carried across: `exists_local_separation`
moves a *count*, and the pair at the nearby angle is handed to it by the branch. -/
theorem exists_neighborhood_separation {Q : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {θ₀ : ℝ}
    (hzc : ContinuousAt (fun θ => ((z θ : ℝ) : ℂ)) θ₀) (hτc : ContinuousAt τ θ₀)
    (hP : ftDen Q r ((z θ₀ : ℝ) : ℂ) ≠ 0) (hτ : 0 < τ θ₀)
    (hrootplus : (ftDen Q r ((z θ₀ : ℝ) : ℂ)).eval (ftPrincipal τ θ₀) = 0)
    (hsp : (derivative (ftDen Q r ((z θ₀ : ℝ) : ℂ))).eval (ftPrincipal τ θ₀) ≠ 0)
    (hsm : (derivative (ftDen Q r ((z θ₀ : ℝ) : ℂ))).eval
      (((τ θ₀ : ℝ) : ℂ) * Complex.exp (-((θ₀ : ℝ) : ℂ) * I)) ≠ 0)
    (hne : ftPrincipal τ θ₀ ≠ ((τ θ₀ : ℝ) : ℂ) * Complex.exp (-((θ₀ : ℝ) : ℂ) * I))
    (hrootminus : (ftDen Q r ((z θ₀ : ℝ) : ℂ)).eval
      (((τ θ₀ : ℝ) : ℂ) * Complex.exp (-((θ₀ : ℝ) : ℂ) * I)) = 0)
    (hmin : ∀ w : ℂ, (ftDen Q r ((z θ₀ : ℝ) : ℂ)).eval w = 0 →
      w ≠ ftPrincipal τ θ₀ →
      w ≠ ((τ θ₀ : ℝ) : ℂ) * Complex.exp (-((θ₀ : ℝ) : ℂ) * I) → τ θ₀ < ‖w‖) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ θ in nhds θ₀,
      τ θ < ρ ∧
      (ftDen Q r ((z θ : ℝ) : ℂ) ≠ 0 →
        (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0 →
        (ftDen Q r ((z θ : ℝ) : ℂ)).eval
            (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) = 0 →
        0 < τ θ →
        ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I) →
        ∀ w : ℂ, ‖w‖ ≤ ρ → (ftDen Q r ((z θ : ℝ) : ℂ)).eval w = 0 →
          w = ftPrincipal τ θ
            ∨ w = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) := by
  obtain ⟨R, hRgt, hRsphere, hRdisk⟩ := exists_separation_radius hP hτ hmin
  -- the returned radius sits strictly inside the one the disk clause holds at, so a
  -- caller gets `τ θ < ρ` and the clause on the CLOSED disk of radius `ρ`
  set ρ : ℝ := (τ θ₀ + R) / 2 with hρdef
  have hρgt : τ θ₀ < ρ := by rw [hρdef]; linarith
  have hρR : ρ < R := by rw [hρdef]; linarith
  have hρpos : 0 < ρ := lt_trans hτ hρgt
  have hnp : ‖ftPrincipal τ θ₀‖ = τ θ₀ := norm_ftPrincipal_eq hτ
  have hnm : ‖((τ θ₀ : ℝ) : ℂ) * Complex.exp (-((θ₀ : ℝ) : ℂ) * I)‖ = τ θ₀ := by
    rw [← conj_polar, RCLike.norm_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hτ, Complex.norm_exp_ofReal_mul_I, mul_one]
  refine ⟨ρ, hρpos, ?_⟩
  have hτnear : ∀ᶠ θ in nhds θ₀, τ θ < ρ := by
    have := hτc (Iio_mem_nhds hρgt)
    filter_upwards [this] with θ hθ using hθ
  filter_upwards [hτnear,
    exists_local_separation (lt_trans hρpos hρR) hzc hRsphere hP hne hrootplus hrootminus
      hsp hsm (by rw [hnp]; exact lt_trans hρgt hρR) (by rw [hnm]; exact lt_trans hρgt hρR)
      hRdisk]
    with θ hθτ hθsep
  refine ⟨hθτ, fun hPθ hrp hrm hτθ hneθ w hw hzero => ?_⟩
  have hnpθ : ‖ftPrincipal τ θ‖ = τ θ := norm_ftPrincipal_eq hτθ
  have hnmθ : ‖((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)‖ = τ θ := by
    rw [← conj_polar, RCLike.norm_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hτθ, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact hθsep _ _ hneθ hrp hrm (by rw [hnpθ]; exact lt_trans hθτ hρR)
    (by rw [hnmθ]; exact lt_trans hθτ hρR) hPθ w (lt_of_le_of_lt hw hρR) hzero


/-- **The compact interior is covered by finitely many separating radii.**  Each
angle carries one by `exists_neighborhood_separation`; compactness reduces to
finitely many.  This is the subdivision `thm:weighted-dominance`'s interior
hypothesis is met on: `interior_data_of_geometry` runs on each piece with that
piece's radius, and the constants reassemble over a finite set.

A single radius for the whole interior is **not** what this produces, and is not
what `thm:FT-geometry` gives — the theorem's separation is a modulus *ratio*,
compared at one angle, while a fixed radius compares `sup τ` against the
non-principal infimum across *different* angles.  Measured on eight pencils the
whole interior does admit one radius, with the two extrema falling at the same
endpoint; that is a monotonicity property of the branch and is deliberately not
assumed here, so nothing depends on a pencil having been sampled. -/
theorem exists_finite_separation_cover {Q : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    {K : Set ℝ} (hK : IsCompact K)
    (hzc : ∀ θ ∈ K, ContinuousAt (fun θ' => ((z θ' : ℝ) : ℂ)) θ)
    (hτc : ∀ θ ∈ K, ContinuousAt τ θ)
    (hP : ∀ θ ∈ K, ftDen Q r ((z θ : ℝ) : ℂ) ≠ 0)
    (hτpos : ∀ θ ∈ K, 0 < τ θ)
    (hrootplus : ∀ θ ∈ K, (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0)
    (hrootminus : ∀ θ ∈ K, (ftDen Q r ((z θ : ℝ) : ℂ)).eval
      (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) = 0)
    (hsp : ∀ θ ∈ K, (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0)
    (hsm : ∀ θ ∈ K, (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
      (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0)
    (hne : ∀ θ ∈ K, ftPrincipal τ θ
      ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I))
    (hmin : ∀ θ ∈ K, ∀ w : ℂ, (ftDen Q r ((z θ : ℝ) : ℂ)).eval w = 0 →
      w ≠ ftPrincipal τ θ →
      w ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I) → τ θ < ‖w‖) :
    ∃ (ρ : ℝ → ℝ) (U : ℝ → Set ℝ) (t : Set ℝ), t ⊆ K ∧ t.Finite ∧
      K ⊆ ⋃ θ₀ ∈ t, U θ₀ ∧
      (∀ θ₀ ∈ t, 0 < ρ θ₀) ∧
      (∀ θ₀ ∈ t, ∀ θ ∈ U θ₀, θ ∈ K →
        τ θ < ρ θ₀ ∧
        ∀ w : ℂ, ‖w‖ ≤ ρ θ₀ → (ftDen Q r ((z θ : ℝ) : ℂ)).eval w = 0 →
          w = ftPrincipal τ θ
            ∨ w = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) := by
  classical
  have key : ∀ θ₀ ∈ K, ∃ (ρ : ℝ) (U : Set ℝ), 0 < ρ ∧ IsOpen U ∧ θ₀ ∈ U ∧
      ∀ θ ∈ U, θ ∈ K → τ θ < ρ ∧
        ∀ w : ℂ, ‖w‖ ≤ ρ → (ftDen Q r ((z θ : ℝ) : ℂ)).eval w = 0 →
          w = ftPrincipal τ θ
            ∨ w = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I) := by
    intro θ₀ hθ₀
    obtain ⟨ρ, hρpos, hev⟩ := exists_neighborhood_separation (hzc θ₀ hθ₀) (hτc θ₀ hθ₀)
      (hP θ₀ hθ₀) (hτpos θ₀ hθ₀) (hrootplus θ₀ hθ₀) (hsp θ₀ hθ₀) (hsm θ₀ hθ₀)
      (hne θ₀ hθ₀) (hrootminus θ₀ hθ₀) (hmin θ₀ hθ₀)
    obtain ⟨V, hVsub, hVopen, hVmem⟩ := _root_.mem_nhds_iff.1 hev
    refine ⟨ρ, V, hρpos, hVopen, hVmem, fun θ hθV hθK => ?_⟩
    obtain ⟨hτθ, hsep⟩ := hVsub hθV
    exact ⟨hτθ, hsep (hP θ hθK) (hrootplus θ hθK) (hrootminus θ hθK) (hτpos θ hθK)
      (hne θ hθK)⟩
  choose! ρ U hρpos hUopen hUmem hUprop using key
  obtain ⟨t, htK, htfin, htcover⟩ :=
    hK.elim_finite_subcover_image (b := K) (c := U) (fun θ hθ => hUopen θ hθ)
      (fun θ hθ => Set.mem_biUnion hθ (hUmem θ hθ))
  exact ⟨ρ, U, t, htK, htfin, htcover, fun θ₀ hθ₀ => hρpos θ₀ (htK hθ₀),
    fun θ₀ hθ₀ => hUprop θ₀ (htK hθ₀)⟩


/-! ### Reassembling the interior data across the pieces

`DominanceFTSupply.interior_data_of_geometry` runs on each piece of the cover with that
piece's radius, and its conclusions combine over a finite set.  The theorem itself
is untouched: `hpair` is satisfiable **per piece**, so the binder stays exactly as
it stands and only what a caller does with it changes.

The remainder bound takes the max of the constants and the max of the ratios.  The
amplitude floor is the delicate one.  The combined divisor is the union, so at a
`θ` inside piece `i` the product runs over divisor points that piece does not own,
and those factors have to be given back: each is at most `L = max(hi - lo, 1)`, and
their exponents sum to at most

  `N = ∑_{θj ∈ ⋃ S i} ν θj`,

the **total multiplicity** and not the number of divisor points.  The two differ
exactly when a zero of `B` on the arc is multiple, which is the case
`lem:amplitude-divisor` exists for, so `L^{|S|}` would be wrong on the pencils that
matter.  Dividing the smallest piece constant by `L^N` absorbs them. -/

/-- **The interior supply on a subdivided interval.**  Every hypothesis is one
piece's copy of `interior_data_of_geometry`'s conclusion; the output is that
conclusion on the whole interval, over the union of the divisors.

The pieces need not be disjoint and need not be intervals — all that is used is
that every parameter of `[lo, hi]` lies in one of them.  A divisor point on a
shared boundary is therefore owned by both pieces and no exponent is lost; a
divisor point owned by neither piece a given `θ` lies in is what the `L^N` factor
pays for. -/
theorem interior_data_of_pieces {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ} {lo hi : ℝ}
    {ι : Type*} {t : Finset ι} (htne : t.Nonempty) {P : ι → ℝ → Prop}
    (hcover : ∀ θ : ℝ, lo ≤ θ → θ ≤ hi → ∃ i ∈ t, P i θ)
    {S : ι → Finset ℝ} {ν : ℝ → ℕ} {CI σI AI : ι → ℝ}
    (hCI : ∀ i ∈ t, 0 ≤ CI i)
    (hσ0 : ∀ i ∈ t, 0 < σI i) (hσ1 : ∀ i ∈ t, σI i < 1) (hA : ∀ i ∈ t, 0 < AI i)
    (hSsub : ∀ i ∈ t, ∀ θj ∈ S i, θj ∈ Set.Icc lo hi)
    (hrem : ∀ i ∈ t, ∀ (M : ℕ) (θ : ℝ), P i θ →
      |ftRemainder Q B r z τ M θ| ≤ CI i * σI i ^ M)
    (hfloor : ∀ i ∈ t, ∀ θ : ℝ, P i θ →
      AI i * ∏ θj ∈ S i, |θ - θj| ^ ν θj ≤ ftPrincipalAmp Q B r z τ θ)
    (hν : ∀ i ∈ t, ∀ θj ∈ S i, 1 ≤ ν θj) :
    ∃ (CI' σI' AI' : ℝ),
      0 < σI' ∧ σI' < 1 ∧ 0 < AI' ∧
      (∀ (M : ℕ) (θ : ℝ), lo ≤ θ → θ ≤ hi →
        |ftRemainder Q B r z τ M θ| ≤ CI' * σI' ^ M) ∧
      (∀ θ : ℝ, lo ≤ θ → θ ≤ hi →
        AI' * ∏ θj ∈ t.biUnion S, |θ - θj| ^ ν θj ≤ ftPrincipalAmp Q B r z τ θ) ∧
      (∀ θj ∈ t.biUnion S, 1 ≤ ν θj) ∧
      (∀ θj ∈ t.biUnion S, θj ∈ Set.Icc lo hi) := by
  classical
  set T : Finset ℝ := t.biUnion S with hT
  have hTmem : ∀ θj ∈ T, ∃ i ∈ t, θj ∈ S i := by
    intro θj hθj; simpa [hT, Finset.mem_biUnion] using hθj
  set L : ℝ := max (hi - lo) 1 with hL
  have hL1 : (1 : ℝ) ≤ L := le_max_right _ _
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  set N : ℕ := ∑ θj ∈ T, ν θj with hN
  set σI' : ℝ := t.sup' htne σI with hσ'
  set CI' : ℝ := t.sup' htne CI with hC'
  set AI' : ℝ := (t.inf' htne AI) / L ^ N with hA'
  have hσ'lt : σI' < 1 := (Finset.sup'_lt_iff htne).2 hσ1
  have hσ'pos : 0 < σI' := by
    obtain ⟨i, hit⟩ := htne
    exact lt_of_lt_of_le (hσ0 i hit) (Finset.le_sup' σI hit)
  have hAinf : 0 < t.inf' htne AI := (Finset.lt_inf'_iff htne).2 hA
  have hA'pos : 0 < AI' := div_pos hAinf (pow_pos hL0 N)
  refine ⟨CI', σI', AI', hσ'pos, hσ'lt, hA'pos, ?_, ?_, ?_, ?_⟩
  · -- the remainder: the largest constant and the slowest ratio
    intro M θ h1 h2
    obtain ⟨i, hit, hPi⟩ := hcover θ h1 h2
    refine le_trans (hrem i hit M θ hPi) ?_
    have hσle : σI i ^ M ≤ σI' ^ M :=
      pow_le_pow_left₀ (hσ0 i hit).le (Finset.le_sup' σI hit) M
    exact mul_le_mul (Finset.le_sup' CI hit) hσle (pow_nonneg (hσ0 i hit).le M)
      (le_trans (hCI i hit) (Finset.le_sup' CI hit))
  · -- the floor: the divisor points this piece does not own, given back
    intro θ h1 h2
    obtain ⟨i, hit, hPi⟩ := hcover θ h1 h2
    have hsub : S i ⊆ T := Finset.subset_biUnion_of_mem S hit
    have hnn : ∀ θj ∈ T, (0 : ℝ) ≤ |θ - θj| ^ ν θj := fun θj _ => by positivity
    have hprodnn : (0 : ℝ) ≤ ∏ θj ∈ S i, |θ - θj| ^ ν θj :=
      Finset.prod_nonneg fun θj _ => by positivity
    have hle : ∀ θj ∈ T, |θ - θj| ≤ L := by
      intro θj hθj
      obtain ⟨j, hjt, hθjS⟩ := hTmem θj hθj
      obtain ⟨hjlo, hjhi⟩ := hSsub j hjt θj hθjS
      have hb : |θ - θj| ≤ hi - lo := by
        rw [abs_le]
        constructor
        · linarith
        · linarith
      exact le_trans hb (le_max_left _ _)
    have hrest : ∏ θj ∈ T \ S i, |θ - θj| ^ ν θj ≤ L ^ N := by
      have hstep : ∏ θj ∈ T \ S i, |θ - θj| ^ ν θj ≤ ∏ θj ∈ T \ S i, L ^ ν θj :=
        Finset.prod_le_prod (fun θj _ => by positivity)
          (fun θj hθj => pow_le_pow_left₀ (abs_nonneg _)
            (hle θj (Finset.mem_sdiff.1 hθj).1) (ν θj))
      refine le_trans hstep ?_
      rw [Finset.prod_pow_eq_pow_sum]
      refine pow_le_pow_right₀ hL1 ?_
      rw [hN]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun _ _ _ => Nat.zero_le _)
    have hsplit : ∏ θj ∈ T, |θ - θj| ^ ν θj
        = (∏ θj ∈ T \ S i, |θ - θj| ^ ν θj) * ∏ θj ∈ S i, |θ - θj| ^ ν θj :=
      (Finset.prod_sdiff hsub).symm
    calc AI' * ∏ θj ∈ T, |θ - θj| ^ ν θj
        = AI' * (∏ θj ∈ T \ S i, |θ - θj| ^ ν θj) * ∏ θj ∈ S i, |θ - θj| ^ ν θj := by
          rw [hsplit]; ring
      _ ≤ AI' * L ^ N * ∏ θj ∈ S i, |θ - θj| ^ ν θj := by
          have := mul_le_mul_of_nonneg_left hrest hA'pos.le
          exact mul_le_mul_of_nonneg_right this hprodnn
      _ = (t.inf' htne AI) * ∏ θj ∈ S i, |θ - θj| ^ ν θj := by
          rw [hA', div_mul_cancel₀ _ (pow_pos hL0 N).ne']
      _ ≤ AI i * ∏ θj ∈ S i, |θ - θj| ^ ν θj :=
          mul_le_mul_of_nonneg_right (Finset.inf'_le AI hit) hprodnn
      _ ≤ ftPrincipalAmp Q B r z τ θ := hfloor i hit θ hPi
  · intro θj hθj
    obtain ⟨i, hit, hθjS⟩ := hTmem θj hθj
    exact hν i hit θj hθjS
  · intro θj hθj
    obtain ⟨i, hit, hθjS⟩ := hTmem θj hθj
    exact hSsub i hit θj hθjS

end ForgacsTran
