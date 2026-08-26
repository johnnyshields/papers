/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.RCLike.Lemmas
import Shields.Analysis.Complex.ArgumentPrinciple.Polynomial

/-!
# Real-rooted complex polynomials, and transferring a root count between discs

## Main results

* `Shields.IsRealRooted`: a polynomial over `ℂ` that splits with every root real.
* `Shields.card_rootsIn_eq_rootMultiplicity`: on a small enough disc the root count is the
  multiplicity of the center.
* `Shields.exists_radius_card_rootsIn_eq_one`: around a simple root, a disc containing exactly one
  root.
* `Shields.im_eq_zero_of_mem_rootsIn`: a root of a real-coefficient polynomial in a disc centered on
  the real axis, isolated from its conjugate, is itself real.

## Implementation notes

`IsRealRooted` is stated for polynomials over `ℂ` rather than as a statement about a real
polynomial, because the perturbation arguments that consume it live over `ℂ` and coercing back and
forth at each step is what the predicate exists to avoid.

## Tags

polynomial, real-rooted, root multiplicity, root counting
-/

namespace Shields

open Complex Filter Metric Polynomial

/-! ### The normalization is inert

A family of polynomials is often normalized by an explicit nonzero factor depending on the index
but not on the parameter `s`, hence constant on each disc.  The following four statements are what
make such a normalization inert: it changes neither the zero set nor any zero count. -/

/-- A nonzero constant factor moves no zero. -/
theorem eval_C_mul_eq_zero_iff {a : ℂ} (ha : a ≠ 0) (P : Polynomial ℂ) (z : ℂ) :
    (C a * P).eval z = 0 ↔ P.eval z = 0 := by
  simp [ha]

/-- A nonvanishing factor moves no zero, at the level of functions. -/
theorem setOf_mul_eq_zero {g F : ℂ → ℂ} (hg : ∀ z, g z ≠ 0) :
    {z : ℂ | g z * F z = 0} = {z : ℂ | F z = 0} := by
  ext z
  simp [hg z]

/-- A nonzero constant factor changes no root of the disc, with multiplicity. -/
theorem rootsIn_C_mul {a : ℂ} (ha : a ≠ 0) (P : Polynomial ℂ) (c : ℂ) (R : ℝ) :
    rootsIn (C a * P) c R = rootsIn P c R := by
  simp only [rootsIn, Polynomial.roots_C_mul P ha]

/-- A nonzero constant factor changes no zero count. -/
theorem card_rootsIn_C_mul {a : ℂ} (ha : a ≠ 0) (P : Polynomial ℂ) (c : ℂ) (R : ℝ) :
    (rootsIn (C a * P) c R).card = (rootsIn P c R).card := by
  rw [rootsIn_C_mul ha]

/-! ### Zero transfer on a disc -/

/-- **Zero transfer, disc form.**  If the finite functions converge
uniformly on the circle `|s - c| = R` to a limit with no zero on that circle, then for all
sufficiently large `n` the finite and limiting functions have the same number of zeros in the open
disc, counted with multiplicity.

The classical statement allows a Jordan domain whose boundary carries no zero of the limit.  **The
Jordan-domain generality is not formalized; what is proved here is the disc case**, which is what
the argument principle of `Shields.Analysis.Complex.ArgumentPrinciple.Polynomial` supplies. -/
theorem zero_transfer_disc {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℕ → Polynomial ℂ}
    {f₀ : Polynomial ℂ}
    (hunif : TendstoUniformlyOn (fun n z => (f n).eval z) (fun z => f₀.eval z) atTop
      (sphere c R))
    (hns : ∀ z ∈ sphere c R, f₀.eval z ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, (rootsIn (f n) c R).card = (rootsIn f₀ c R).card :=
  eventually_atTop.mp (eventually_card_rootsIn_eq hR hunif hns)

/-- Zero transfer for the normalized family.  Normalizing each `f n` by a nonzero constant `g n`
leaves the conclusion of `zero_transfer_disc` unchanged, so such a normalization
is inert. -/
theorem zero_transfer_disc_normalized {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℕ → Polynomial ℂ}
    {f₀ : Polynomial ℂ} {g : ℕ → ℂ} (hg : ∀ n, g n ≠ 0)
    (hunif : TendstoUniformlyOn (fun n z => (f n).eval z) (fun z => f₀.eval z) atTop
      (sphere c R))
    (hns : ∀ z ∈ sphere c R, f₀.eval z ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, (rootsIn (C (g n) * f n) c R).card = (rootsIn f₀ c R).card := by
  obtain ⟨N, hN⟩ := zero_transfer_disc hR hunif hns
  refine ⟨N, fun n hn => ?_⟩
  rw [card_rootsIn_C_mul (hg n)]
  exact hN n hn

/-! ### Isolation of a zero, and the count on an isolating disc -/

/-- A zero of a nonzero polynomial is isolated: some ball about `s₀` contains no other zero.  The
roots form a finite set, so its complement is an open neighborhood of `s₀` once `s₀` itself is
removed. -/
theorem exists_ball_eq_of_eval_eq_zero {P : Polynomial ℂ} (hP : P ≠ 0) (s₀ : ℂ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ ball s₀ ρ, P.eval z = 0 → z = s₀ := by
  set S : Finset ℂ := P.roots.toFinset.erase s₀ with hS
  have hopen : IsOpen ((S : Set ℂ)ᶜ) := (S.finite_toSet.isClosed).isOpen_compl
  have hmem : s₀ ∈ (S : Set ℂ)ᶜ := by simp [hS]
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp hopen s₀ hmem
  refine ⟨ρ, hρ, fun z hz hzero => ?_⟩
  by_contra hne
  have hzS : z ∈ S := by
    rw [hS, Finset.mem_erase]
    exact ⟨hne, Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨hP, hzero⟩)⟩
  exact (hsub hz) (Finset.mem_coe.mpr hzS)

/-- On a disc that isolates the zero `s₀`, the zero count with multiplicity is exactly the root
multiplicity of `s₀`.  No hypothesis `P ≠ 0` is needed: for `P = 0` both sides are `0`. -/
theorem card_rootsIn_eq_rootMultiplicity {P : Polynomial ℂ} {s₀ : ℂ} {R : ℝ}
    (hR : 0 < R) (hiso : ∀ z ∈ ball s₀ R, P.eval z = 0 → z = s₀) :
    (rootsIn P s₀ R).card = P.rootMultiplicity s₀ := by
  have hall : ∀ r ∈ rootsIn P s₀ R, r = s₀ := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := mem_rootsIn.mp hr
    exact hiso r hr2 (mem_roots'.mp hr1).2
  have hrep : rootsIn P s₀ R = Multiset.replicate (rootsIn P s₀ R).card s₀ :=
    Multiset.eq_replicate_card.mpr hall
  have hcount : (rootsIn P s₀ R).count s₀ = (rootsIn P s₀ R).card := by
    conv_lhs => rw [hrep]
    exact Multiset.count_replicate_self _ _
  rw [← hcount]
  have hps : dist s₀ s₀ < R := by simpa using hR
  simp only [rootsIn]
  rw [Multiset.count_filter_of_pos (p := fun r : ℂ => dist r s₀ < R) hps, count_roots]

/-! ### Attraction of the finite-`n` zeros -/

/-- **A limit zero of multiplicity `m` is the limit of exactly `m` finite-`n` zeros.**  For every
sufficiently small radius `R` there is an `N` beyond which
`f n` has exactly `f₀.rootMultiplicity s₀` zeros in `ball s₀ R`, counted with multiplicity.

Nothing is asserted about those finite-`n` zeros beyond their number: neither their reality nor
their simplicity.

The convergence hypothesis is uniform on a fixed closed disc about `s₀`, which is what local
uniformity supplies; the conclusion is drawn on the smaller circles inside it. -/
theorem exists_radius_card_rootsIn_eq_rootMultiplicity {f : ℕ → Polynomial ℂ}
    {f₀ : Polynomial ℂ} (hf₀ : f₀ ≠ 0) (s₀ : ℂ) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hunif : TendstoUniformlyOn (fun n z => (f n).eval z) (fun z => f₀.eval z) atTop
      (closedBall s₀ ρ₀)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ ∀ R : ℝ, 0 < R → R < ρ →
      ∃ N : ℕ, ∀ n ≥ N, (rootsIn (f n) s₀ R).card = f₀.rootMultiplicity s₀ := by
  obtain ⟨ρ₁, hρ₁, hiso⟩ := exists_ball_eq_of_eval_eq_zero hf₀ s₀
  refine ⟨min ρ₁ ρ₀, lt_min hρ₁ hρ₀, min_le_right _ _, fun R hR hRlt => ?_⟩
  have hR1 : R < ρ₁ := hRlt.trans_le (min_le_left _ _)
  have hR0 : R ≤ ρ₀ := (hRlt.trans_le (min_le_right _ _)).le
  have hisoR : ∀ z ∈ ball s₀ R, f₀.eval z = 0 → z = s₀ := fun z hz =>
    hiso z (ball_subset_ball hR1.le hz)
  have hns : ∀ z ∈ sphere s₀ R, f₀.eval z ≠ 0 := by
    intro z hz hzero
    rw [mem_sphere] at hz
    have hzb : z ∈ ball s₀ ρ₁ := by rw [mem_ball, hz]; exact hR1
    have hzs := hiso z hzb hzero
    rw [hzs, dist_self] at hz
    exact hR.ne' hz.symm
  have hsub : sphere s₀ R ⊆ closedBall s₀ ρ₀ := by
    intro z hz
    rw [mem_sphere] at hz
    rw [mem_closedBall, hz]
    exact hR0
  obtain ⟨N, hN⟩ := zero_transfer_disc hR (hunif.mono hsub) hns
  refine ⟨N, fun n hn => ?_⟩
  rw [hN n hn, card_rootsIn_eq_rootMultiplicity hR hisoR]

/-- A zero at which the derivative does not vanish is simple. -/
theorem rootMultiplicity_eq_one_of_derivative_ne_zero {P : Polynomial ℂ} (hP : P ≠ 0) {s₀ : ℂ}
    (hroot : P.eval s₀ = 0) (hder : (derivative P).eval s₀ ≠ 0) :
    P.rootMultiplicity s₀ = 1 := by
  have h1 : 0 < P.rootMultiplicity s₀ := (rootMultiplicity_pos hP).2 hroot
  have h2 : ¬ 1 < P.rootMultiplicity s₀ := by
    rw [one_lt_rootMultiplicity_iff_isRoot hP]
    exact fun h => hder h.2
  omega

/-- **Every simple limit zero attracts one unique finite-`n` zero.**
For every sufficiently small radius the finite functions eventually have exactly one zero in the
disc about `s₀`, counted with multiplicity.

Uniqueness here is the count `1` with multiplicity.  Neither the
reality nor the simplicity of that finite-`n` zero is asserted. -/
theorem exists_radius_card_rootsIn_eq_one {f : ℕ → Polynomial ℂ}
    {f₀ : Polynomial ℂ} (hf₀ : f₀ ≠ 0) {s₀ : ℂ} (hsimple : f₀.rootMultiplicity s₀ = 1)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hunif : TendstoUniformlyOn (fun n z => (f n).eval z) (fun z => f₀.eval z) atTop
      (closedBall s₀ ρ₀)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ ∀ R : ℝ, 0 < R → R < ρ →
      ∃ N : ℕ, ∀ n ≥ N, (rootsIn (f n) s₀ R).card = 1 := by
  obtain ⟨ρ, hρ, hρle, hmain⟩ :=
    exists_radius_card_rootsIn_eq_rootMultiplicity hf₀ s₀ hρ₀ hunif
  refine ⟨ρ, hρ, hρle, fun R hR hRlt => ?_⟩
  obtain ⟨N, hN⟩ := hmain R hR hRlt
  exact ⟨N, fun n hn => by rw [hN n hn, hsimple]⟩

/-! ### Real-rootedness, and the reality of the limit

Mathlib carries no Laguerre--Pólya class and no real-rootedness predicate at the pinned revision,
so `IsRealRooted` below is a local definition.  It is a concrete condition on a polynomial, not a
class-theoretic one. -/

/-- **Real-rootedness of a complex polynomial**, defined locally because Mathlib has no such
predicate: the root count with multiplicity is the degree, and every root is real.

Over `ℂ` the first clause is automatic — `isRealRooted_iff_forall_im` — so the content is the
second.  It is kept because it is the condition as one states it over a general field. -/
def IsRealRooted (p : Polynomial ℂ) : Prop :=
  p.roots.card = p.natDegree ∧ ∀ z ∈ p.roots, z.im = 0

/-- Over `ℂ` the degree clause of `IsRealRooted` is automatic: every complex polynomial splits. -/
theorem isRealRooted_iff_forall_im {p : Polynomial ℂ} :
    IsRealRooted p ↔ ∀ z ∈ p.roots, z.im = 0 :=
  ⟨And.right, fun h => ⟨splits_iff_card_roots.mp (IsAlgClosed.splits p), h⟩⟩

/-- **Conjugation symmetry of a real-coefficient polynomial**: evaluation commutes with complex
conjugation. -/
theorem eval_conj_of_coeff_im_eq_zero {p : Polynomial ℂ} (hp : ∀ i, (p.coeff i).im = 0) (z : ℂ) :
    p.eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (p.eval z) := by
  rw [eval_eq_sum_range, eval_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, Complex.conj_eq_iff_im.mpr (hp i)]

/-- Conjugation symmetry for a polynomial presented as the image of a real one. -/
theorem eval_map_conj (q : Polynomial ℝ) (z : ℂ) :
    (q.map (algebraMap ℝ ℂ)).eval ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) ((q.map (algebraMap ℝ ℂ)).eval z) := by
  simp only [eval_map, ← aeval_def]
  exact Polynomial.aeval_conj q z

/-- The roots of a real-coefficient polynomial come in conjugate pairs. -/
theorem mem_roots_conj_of_coeff_im_eq_zero {p : Polynomial ℂ} (hp : ∀ i, (p.coeff i).im = 0)
    {z : ℂ} (hz : z ∈ p.roots) : (starRingEnd ℂ) z ∈ p.roots := by
  obtain ⟨hp0, hzero⟩ := mem_roots'.mp hz
  refine mem_roots'.mpr ⟨hp0, ?_⟩
  rw [IsRoot.def, eval_conj_of_coeff_im_eq_zero hp]
  rw [IsRoot.def] at hzero
  rw [hzero, map_zero]

/-- **Reality is inherited by the limit.**  If every `f n`
has all its roots real and `f n → f₀` uniformly on the closed disc `|s - c| ≤ R`, then every zero
of `f₀` in the open disc is real.

The proof is local at a putative nonreal zero `w`.  A radius `r` is chosen below `|Im w|`, below the
isolation radius of `w` as a zero of `f₀`, and below `R - |w - c|`, so that `ball w r` misses the
real axis and sits inside `ball c R` while `sphere w r` carries no zero of `f₀`.  Zero transfer on
that circle hands `f n` a zero in `ball w r` for some large `n`, and that zero is nonreal.

The convergence hypothesis is uniform on the **closed disc**, not merely on its boundary circle:
zero transfer is applied on an interior circle around `w`, which boundary data alone does not
reach.  No hypothesis is needed on the boundary circle `|s - c| = R`, and none on the position of
the center `c`, because the argument never leaves `ball w r`. -/
theorem im_eq_zero_of_mem_rootsIn {f : ℕ → Polynomial ℂ} {f₀ : Polynomial ℂ} {c : ℂ} {R : ℝ}
    (hreal : ∀ᶠ n in atTop, IsRealRooted (f n))
    (hunif : TendstoUniformlyOn (fun n z => (f n).eval z) (fun z => f₀.eval z) atTop
      (closedBall c R)) :
    ∀ w ∈ rootsIn f₀ c R, w.im = 0 := by
  intro w hw
  by_contra him
  obtain ⟨hwroot, hwball⟩ := mem_rootsIn.mp hw
  have hf₀ : f₀ ≠ 0 := (mem_roots'.mp hwroot).1
  have hw0 : f₀.eval w = 0 := (mem_roots'.mp hwroot).2
  obtain ⟨ρ₁, hρ₁, hiso⟩ := exists_ball_eq_of_eval_eq_zero hf₀ w
  have himpos : 0 < |w.im| := abs_pos.mpr him
  have hdist : dist w c < R := mem_ball.mp hwball
  set m : ℝ := min (min ρ₁ |w.im|) (R - dist w c)
  have hmpos : 0 < m := lt_min (lt_min hρ₁ himpos) (by linarith)
  set r : ℝ := m / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hrm : r < m := by rw [hr]; linarith
  have hr1 : r < ρ₁ := hrm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hr2 : r < |w.im| := hrm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hr3 : r < R - dist w c := hrm.trans_le (min_le_right _ _)
  -- The small circle carries no zero of the limit.
  have hns : ∀ z ∈ sphere w r, f₀.eval z ≠ 0 := by
    intro z hz hzero
    rw [mem_sphere] at hz
    have hzb : z ∈ ball w ρ₁ := by rw [mem_ball, hz]; exact hr1
    have hzw := hiso z hzb hzero
    rw [hzw, dist_self] at hz
    exact hrpos.ne' hz.symm
  -- The small circle sits inside the disc on which the convergence is uniform.
  have hsub : sphere w r ⊆ closedBall c R := by
    intro z hz
    rw [mem_sphere] at hz
    rw [mem_closedBall]
    calc dist z c ≤ dist z w + dist w c := dist_triangle z w c
      _ = r + dist w c := by rw [hz]
      _ ≤ R := by linarith
  have hisoR : ∀ z ∈ ball w r, f₀.eval z = 0 → z = w := fun z hz =>
    hiso z (ball_subset_ball hr1.le hz)
  have hcard : (rootsIn f₀ w r).card = f₀.rootMultiplicity w :=
    card_rootsIn_eq_rootMultiplicity hrpos hisoR
  have hpos : 0 < f₀.rootMultiplicity w := (rootMultiplicity_pos hf₀).2 hw0
  -- Zero transfer on that circle produces a nonreal zero of some `f n`.
  obtain ⟨n, hn1, hn2⟩ :=
    (hreal.and (eventually_card_rootsIn_eq hrpos (hunif.mono hsub) hns)).exists
  have hcpos : 0 < (rootsIn (f n) w r).card := by rw [hn2, hcard]; exact hpos
  obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.mp hcpos
  obtain ⟨hzroot, hzball⟩ := mem_rootsIn.mp hz
  have hzim : z.im = 0 := hn1.2 z hzroot
  have hle : |w.im| ≤ dist w z := by
    rw [dist_eq_norm]
    simpa [hzim] using Complex.abs_im_le_norm (w - z)
  have hzw : dist w z < r := by rw [dist_comm]; exact mem_ball.mp hzball
  linarith

/-- **Reality is inherited by the limit**, stated on the zero set.  Every zero of the limit in the
open disc is real. -/
theorem im_eq_zero_of_eval_eq_zero {f : ℕ → Polynomial ℂ} {f₀ : Polynomial ℂ} {c : ℂ} {R : ℝ}
    (hf₀ : f₀ ≠ 0) (hreal : ∀ᶠ n in atTop, IsRealRooted (f n))
    (hunif : TendstoUniformlyOn (fun n z => (f n).eval z) (fun z => f₀.eval z) atTop
      (closedBall c R)) :
    ∀ w ∈ ball c R, f₀.eval w = 0 → w.im = 0 := fun w hw hzero =>
  im_eq_zero_of_mem_rootsIn hreal hunif w (mem_rootsIn.mpr ⟨mem_roots'.mpr ⟨hf₀, hzero⟩, hw⟩)

end Shields
