/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Analysis.Fredholm.HSDeterminant

/-!
# The Hilbert--Schmidt norm of a kernel, and convergence in it

Mathlib carries no Schatten class, no Hilbert--Schmidt norm and no trace norm, so the
sentence "the factors converge in Hilbert--Schmidt norm, hence their product converges in
trace norm, where `det(Id + ·)` is continuous" has no vocabulary to be stated in.  What it
*says* about a kernel on a countable index set is elementary, and that is what is proved
here: the squared Hilbert--Schmidt norm is the sum of the squared entry moduli,

\[
  \lVert C\rVert_{\mathrm{HS}}^{2}=\sum_{i,j}\lvert C_{ij}\rvert^{2},
\]

a product envelope bounds it by the product of the two envelope energies, entrywise
convergence under a common envelope upgrades to convergence in this norm, and convergence
in this norm gives convergence of the Fredholm determinants of `Shields.fredholmDet`.

## Main results

* `Shields.hsNormSq_le_mul` — the envelope bound.
* `Shields.tendsto_hsNormSq_sub` — entrywise convergence under a common product envelope
  implies Hilbert--Schmidt convergence.  This is the paper's "splitting off a finite
  rectangle and estimating both tails by the majorants above", carried out by Tannery's
  theorem instead.
* `Shields.tendsto_fredholmDet_of_hs` — Hilbert--Schmidt convergence of the factors gives
  convergence of the determinants.  This is the conclusion the trace-norm sentence is used
  for, with no trace norm in the statement or the proof.

## Papers depending on this file

* `growing-rank-edrei` — the collective limit of the excitation determinant.
-/

open Filter Topology

namespace Shields

variable {ι κ : Type*}

/-- A summable nonnegative family is square-summable: each term is at most the total. -/
theorem summable_sq_of_nonneg {f : ι → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hf : Summable f) :
    Summable fun i => (f i) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) (hf.mul_left (∑' j, f j))
  have hle : f i ≤ ∑' j, f j := hf.le_tsum i fun j _ => hf0 j
  calc (f i) ^ 2 = f i * f i := sq (f i)
    _ ≤ (∑' j, f j) * f i := mul_le_mul_of_nonneg_right hle (hf0 i)

/-- The squared Hilbert--Schmidt norm of a kernel: the sum of the squared entry moduli. -/
noncomputable def hsNormSq (C : ι → κ → ℂ) : ℝ := ∑' p : ι × κ, ‖C p.1 p.2‖ ^ 2

theorem hsNormSq_nonneg (C : ι → κ → ℂ) : 0 ≤ hsNormSq C :=
  tsum_nonneg fun _ => sq_nonneg _

/-- Two kernels sharing a product envelope have their difference under twice that envelope. -/
theorem norm_sub_le_two_mul {F C : ι → κ → ℂ} {e : ι → ℝ} {g : κ → ℝ}
    (hF : ∀ i j, ‖F i j‖ ≤ e i * g j) (hC : ∀ i j, ‖C i j‖ ≤ e i * g j) (i : ι) (j : κ) :
    ‖F i j - C i j‖ ≤ 2 * e i * g j := by
  calc ‖F i j - C i j‖ ≤ ‖F i j‖ + ‖C i j‖ := norm_sub_le _ _
    _ ≤ e i * g j + e i * g j := add_le_add (hF i j) (hC i j)
    _ = 2 * e i * g j := by ring

/-- The product of two square-summable envelopes is summable over the product index. -/
theorem summable_sq_mul_sq {e : ι → ℝ} {g : κ → ℝ} (he : Summable fun i => (e i) ^ 2)
    (hg : Summable fun j => (g j) ^ 2) :
    Summable fun p : ι × κ => (e p.1) ^ 2 * (g p.2) ^ 2 :=
  he.mul_of_nonneg hg (fun i => sq_nonneg (e i)) fun j => sq_nonneg (g j)

/-- A product envelope makes the squared entry moduli summable. -/
theorem summable_normSq_of_envelope (C : ι → κ → ℂ) {e : ι → ℝ} {g : κ → ℝ}
    (_he0 : ∀ i, 0 ≤ e i) (_hg0 : ∀ j, 0 ≤ g j)
    (he : Summable fun i => (e i) ^ 2) (hg : Summable fun j => (g j) ^ 2)
    (hC : ∀ i j, ‖C i j‖ ≤ e i * g j) :
    Summable fun p : ι × κ => ‖C p.1 p.2‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun p => ?_) (summable_sq_mul_sq he hg)
  calc ‖C p.1 p.2‖ ^ 2 ≤ (e p.1 * g p.2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hC p.1 p.2) 2
    _ = (e p.1) ^ 2 * (g p.2) ^ 2 := by ring

/-- **The envelope bound on the Hilbert--Schmidt norm.**  The energies of the two
envelopes multiply. -/
theorem hsNormSq_le_mul (C : ι → κ → ℂ) {e : ι → ℝ} {g : κ → ℝ}
    (he0 : ∀ i, 0 ≤ e i) (hg0 : ∀ j, 0 ≤ g j)
    (he : Summable fun i => (e i) ^ 2) (hg : Summable fun j => (g j) ^ 2)
    (hC : ∀ i j, ‖C i j‖ ≤ e i * g j) :
    hsNormSq C ≤ (∑' i, (e i) ^ 2) * ∑' j, (g j) ^ 2 := by
  have hprod := summable_sq_mul_sq he hg
  have heq : (∑' i, (e i) ^ 2) * (∑' j, (g j) ^ 2)
      = ∑' p : ι × κ, (e p.1) ^ 2 * (g p.2) ^ 2 := by
    refine tsum_mul_tsum_of_summable_norm ?_ ?_
    · exact he.congr fun i => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    · exact hg.congr fun j => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [hsNormSq, heq]
  refine Summable.tsum_le_tsum (fun p => ?_)
    (summable_normSq_of_envelope C he0 hg0 he hg hC) hprod
  calc ‖C p.1 p.2‖ ^ 2 ≤ (e p.1 * g p.2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hC p.1 p.2) 2
    _ = (e p.1) ^ 2 * (g p.2) ^ 2 := by ring

/-- Each entry is controlled by the Hilbert--Schmidt norm. -/
theorem normSq_le_hsNormSq (C : ι → κ → ℂ)
    (hs : Summable fun p : ι × κ => ‖C p.1 p.2‖ ^ 2) (i : ι) (j : κ) :
    ‖C i j‖ ^ 2 ≤ hsNormSq C := by
  rw [hsNormSq]
  simpa using hs.le_tsum (i, j) fun p _ => sq_nonneg _

/-- **Convergence in Hilbert--Schmidt norm is entrywise convergence.**  Each entry of the
difference is squeezed by the norm of the difference. -/
theorem tendsto_of_tendsto_hsNormSq_sub {α : Type*} {l : Filter α} (F : α → ι → κ → ℂ)
    (C : ι → κ → ℂ)
    (hsum : ∀ n, Summable fun p : ι × κ => ‖F n p.1 p.2 - C p.1 p.2‖ ^ 2)
    (hHS : Tendsto (fun n => hsNormSq fun i j => F n i j - C i j) l (𝓝 0)) (i : ι) (j : κ) :
    Tendsto (fun n => F n i j) l (𝓝 (C i j)) := by
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  have h0 : Tendsto (fun n => ‖F n i j - C i j‖ ^ 2) l (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg _) (fun n =>
      normSq_le_hsNormSq (fun i j => F n i j - C i j) (hsum n) i j) hHS
  simpa [Real.sqrt_sq (norm_nonneg _)] using h0.sqrt

/-- **Entrywise convergence under a common product envelope is Hilbert--Schmidt
convergence.** -/
theorem tendsto_hsNormSq_sub {α : Type*} {l : Filter α} (F : α → ι → κ → ℂ)
    (C : ι → κ → ℂ) {e : ι → ℝ} {g : κ → ℝ}
    (he0 : ∀ i, 0 ≤ e i) (hg0 : ∀ j, 0 ≤ g j)
    (he : Summable fun i => (e i) ^ 2) (hg : Summable fun j => (g j) ^ 2)
    (hF : ∀ n i j, ‖F n i j‖ ≤ e i * g j) (hC : ∀ i j, ‖C i j‖ ≤ e i * g j)
    (hlim : ∀ i j, Tendsto (fun n => F n i j) l (𝓝 (C i j))) :
    Tendsto (fun n => hsNormSq fun i j => F n i j - C i j) l (𝓝 0) := by
  have hbound : Summable fun p : ι × κ => (2 * (e p.1) * (g p.2)) ^ 2 :=
    ((summable_sq_mul_sq he hg).mul_left 4).congr fun p => by ring
  have key : Tendsto (fun n => ∑' p : ι × κ, ‖F n p.1 p.2 - C p.1 p.2‖ ^ 2) l
      (𝓝 (∑' _p : ι × κ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hbound (fun p => ?_) ?_
    · have hs0 : Tendsto (fun n => F n p.1 p.2 - C p.1 p.2) l (𝓝 (C p.1 p.2 - C p.1 p.2)) :=
        (hlim p.1 p.2).sub tendsto_const_nhds
      rw [sub_self] at hs0
      simpa using hs0.norm.pow 2
    · filter_upwards with n p
      have h1 := norm_sub_le_two_mul (hF n) hC p.1 p.2
      have h2 : (0 : ℝ) ≤ 2 * e p.1 * g p.2 :=
        mul_nonneg (mul_nonneg (by norm_num) (he0 p.1)) (hg0 p.2)
      calc ‖‖F n p.1 p.2 - C p.1 p.2‖ ^ 2‖ = ‖F n p.1 p.2 - C p.1 p.2‖ ^ 2 := by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        _ ≤ (2 * e p.1 * g p.2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  simpa [hsNormSq] using key

/-- **Hilbert--Schmidt convergence of the factors gives convergence of the Fredholm
determinants.**  This is what the trace-norm sentence of `prop:app-Fredholm` and of
`thm:collective` is used for: no Schatten norm appears, the common envelope supplying
what trace-class continuity would. -/
theorem tendsto_fredholmDet_of_hs {α : Type*} {l : Filter α} [LinearOrder ι] [LinearOrder κ]
    (F : α → ι → κ → ℂ) (C : ι → κ → ℂ) {e : ι → ℝ} {g : κ → ℝ}
    (he0 : ∀ i, 0 ≤ e i) (hg0 : ∀ j, 0 ≤ g j) (he : Summable e) (hg : Summable g)
    (hF : ∀ n i j, ‖F n i j‖ ≤ e i * g j) (hC : ∀ i j, ‖C i j‖ ≤ e i * g j)
    (hHS : Tendsto (fun n => hsNormSq fun i j => F n i j - C i j) l (𝓝 0)) :
    Tendsto (fun n => fredholmDet (F n)) l (𝓝 (fredholmDet C)) := by
  have hesq : Summable fun i => (e i) ^ 2 := summable_sq_of_nonneg he0 he
  have hgsq : Summable fun j => (g j) ^ 2 := summable_sq_of_nonneg hg0 hg
  have he2 : Summable fun i => (2 * e i) ^ 2 := (hesq.mul_left 4).congr fun i => by ring
  have hsum : ∀ n, Summable fun p : ι × κ => ‖F n p.1 p.2 - C p.1 p.2‖ ^ 2 := fun n =>
    summable_normSq_of_envelope (fun i j => F n i j - C i j) (e := fun i => 2 * e i) (g := g)
      (fun i => mul_nonneg (by norm_num) (he0 i)) hg0 he2 hgsq (norm_sub_le_two_mul (hF n) hC)
  have hptw : ∀ i j, Tendsto (fun n => F n i j) l (𝓝 (C i j)) :=
    tendsto_of_tendsto_hsNormSq_sub F C hsum hHS
  exact tendsto_fredholmDet_of_summable_envelope F C he0 hg0 he hg hF hptw


/-! ### Axiom footprint -/

/-- info: 'Shields.hsNormSq_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hsNormSq_le_mul

/-- info: 'Shields.tendsto_hsNormSq_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_hsNormSq_sub

/-- info: 'Shields.tendsto_fredholmDet_of_hs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_fredholmDet_of_hs

end Shields
