/-
Vendored from ProjectVD, `VD/MathlibSubmitted/Scaling.lean`, by Stefan Kebekus (GitHub `kebekus`).

  https://github.com/kebekus/ProjectVD

ProjectVD formalizes Value Distribution Theory for meromorphic functions on the complex plane and
is being upstreamed to Mathlib piece by piece.  It is submitted upstream as Mathlib pull request #41303, `feat: Invariance of meromorphicity under scaling`,
  https://github.com/leanprover-community/mathlib4/pull/41303

The copy is verbatim except that `import VD.X` becomes `import Vendor.ProjectVD.X`, and the two
Mathlib modules ProjectVD depends on that postdate the pinned Mathlib revision are imported from
their own vendored copies (the `Vendor.PR<number><Slug>` modules imported below).  No
declaration, statement or proof is changed; upstream namespaces, names and section scaffolding are
kept, so consuming code is written exactly as it will be against a merged Mathlib.

When this material merges and the Mathlib pin is bumped past it, delete this file and import the
upstream module.

Upstream copyright and authorship follow, verbatim.
-/

/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Vendor.ProjectVD.MathlibPending.BoundednessCharacteristic

/-!
## Scaling by a Nonzero Constant
-/

open Asymptotics Filter Function Metric MeromorphicOn Real Set Topology ValueDistribution

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- MeromorphicAt is invariant under scaling. -/
@[simp] theorem meromorphicAt_const_smul_iff_meromorphicAt {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    MeromorphicAt (s • f) z ↔ MeromorphicAt f z := by
  constructor
  <;> intro hf
  · rw [((eq_inv_smul_iff₀ hs).mpr rfl : f = s⁻¹ • s • f)]
    fun_prop
  · fun_prop

/-- MeromorphicAt is invariant under scaling. -/
@[simp] theorem meromorphicAt_fun_const_smul_iff_meromorphicAt {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    MeromorphicAt (fun x ↦ s • f x) z ↔ MeromorphicAt f z :=
  meromorphicAt_const_smul_iff_meromorphicAt hs

/-- MeromorphicOn is invariant under scaling. -/
@[simp] theorem meromorphicOn_const_smul_iff_meromorphicOn {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    MeromorphicOn (s • f) U ↔ MeromorphicOn f U :=
  ⟨fun hf x hx ↦ (meromorphicAt_const_smul_iff_meromorphicAt hs).mp (hf x hx),
    fun hf x hx ↦ (meromorphicAt_const_smul_iff_meromorphicAt hs).mpr (hf x hx)⟩

/-- MeromorphicOn is invariant under scaling. -/
@[simp] theorem meromorphicOn_fun_const_smul_iff_meromorphicOn {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    MeromorphicOn (fun x ↦ s • f x) U ↔ MeromorphicOn f U :=
  meromorphicOn_const_smul_iff_meromorphicOn hs

/-- Meromorphic is invariant under scaling. -/
@[simp] theorem meromorphic_const_smul_iff_meromorphic {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    Meromorphic (s • f) ↔ Meromorphic f :=
  ⟨fun hf x ↦ (meromorphicAt_const_smul_iff_meromorphicAt hs).mp (hf x),
    fun hf x ↦ (meromorphicAt_const_smul_iff_meromorphicAt hs).mpr (hf x)⟩

/-- Meromorphic is invariant under scaling. -/
@[simp] theorem meromorphic_fun_const_smul_iff_meromorphic {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    Meromorphic (fun x ↦ s • f x) ↔ Meromorphic f :=
  meromorphic_const_smul_iff_meromorphic hs

/-- meromorphicOrderAt is invariant under scaling. -/
@[simp] theorem meromorphicOrderAt_const_smul_iff_meromorphicOrderAt {f : 𝕜 → E} {s : 𝕜}
    (hs : s ≠ 0) :
    meromorphicOrderAt (s • f) z = meromorphicOrderAt f z := by
  by_cases hf : MeromorphicAt f z
  · rw [(by aesop : s • f = (fun (_ : 𝕜) ↦ s) • f),
      meromorphicOrderAt_smul_of_ne_zero (by fun_prop) hs]
  simp_all

/-- meromorphicOrderAt is invariant under scaling. -/
@[simp] theorem meromorphicOrderAt_fun_const_smul_iff_meromorphicOrderAt {f : 𝕜 → E} {s : 𝕜}
    (hs : s ≠ 0) :
    meromorphicOrderAt (fun x ↦ s • f x) z = meromorphicOrderAt f z :=
  meromorphicOrderAt_const_smul_iff_meromorphicOrderAt hs

/-- The divisor of a function is invariant when scaling of the function. -/
@[simp] theorem divisor_const_smul {f : 𝕜 → E} {s : 𝕜} {U : Set 𝕜} (hs : s ≠ 0) :
    divisor (s • f) U = divisor f U := by
  ext z
  by_cases h₁f : MeromorphicOn f U
  · by_cases hz : z ∈ U
    · rw [divisor_apply h₁f hz, divisor_apply (by simp_all) hz]
      simp_all
    · simp_all
  · simp_all only [ne_eq, not_false_eq_true, meromorphicOn_const_smul_iff_meromorphicOn,
    divisor_eq_zero_of_not_meromorphicOn]

/-- The divisor of a function is invariant when scaling of the function. -/
@[simp] theorem divisor_fun_const_smul {f : 𝕜 → E} {s : 𝕜} {U : Set 𝕜} (hs : s ≠ 0) :
    divisor (fun x ↦ s • f x) U = divisor f U :=
  divisor_const_smul hs

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Special case of `analyticAt_const`, required to make `fun_prop` work. -/
@[fun_prop] theorem analyticAt_zero {G H : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H] {x : G} : AnalyticAt 𝕜 (0 : G → H) x :=
  analyticAt_const

attribute [fun_prop] AnalyticAt.meromorphicNFAt

@[fun_prop] theorem MeromorphicNFAt.smul_const {f : 𝕜 → E} {s : 𝕜} (hf : MeromorphicNFAt f z) :
    MeromorphicNFAt (s • f) z := by
  by_cases h : s = 0
  · rw [h, zero_smul]
    fun_prop
  exact hf.smul_analytic (by fun_prop) h

/-- MeromorphicNFAt is invariant under scaling. -/
@[simp] theorem meromorphicNFAt_const_smul_iff_meromorphicNFAt {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    MeromorphicNFAt (s • f) z ↔ MeromorphicNFAt f z := by
  constructor
  <;> intro hf
  · rw [((eq_inv_smul_iff₀ hs).mpr rfl : f = s⁻¹ • s • f)]
    fun_prop
  · fun_prop

/-- MeromorphicNFAt is invariant under scaling. -/
@[simp] theorem meromorphicNFAt_fun_const_smul_iff_meromorphiNFcAt {f : 𝕜 → E} {s : 𝕜}
    (hs : s ≠ 0) :
    MeromorphicNFAt (fun x ↦ s • f x) z ↔ MeromorphicNFAt f z :=
  meromorphicNFAt_const_smul_iff_meromorphicNFAt hs

/-- MeromorphicNFOn is invariant under scaling. -/
@[simp] theorem meromorphicNFOn_const_smul_iff_meromorphicNFOn {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    MeromorphicNFOn (s • f) U ↔ MeromorphicNFOn f U :=
  ⟨fun hf _ hx ↦ (meromorphicNFAt_const_smul_iff_meromorphicNFAt hs).mp (hf hx),
    fun hf _ hx ↦ (meromorphicNFAt_const_smul_iff_meromorphicNFAt hs).mpr (hf hx)⟩

/-- MeromorphicNFOn is invariant under scaling. -/
@[simp] theorem meromorphicNFOn_fun_const_smul_iff_meromorphicNFOn {f : 𝕜 → E} {s : 𝕜}
    (hs : s ≠ 0) :
    MeromorphicNFOn (fun x ↦ s • f x) U ↔ MeromorphicNFOn f U :=
  meromorphicNFOn_const_smul_iff_meromorphicNFOn hs
