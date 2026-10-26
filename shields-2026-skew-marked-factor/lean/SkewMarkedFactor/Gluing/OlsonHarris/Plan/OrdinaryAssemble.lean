/-
Copyright (c) 2026 John Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: John Shields
-/
-- TODO-COPIED: skew-gluing/lean/SkewGluing/OlsonHarris/Plan/Assemble.lean
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.EdgeCase
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.Kernel
import SkewMarkedFactor.Gluing.OlsonHarris.Plan.MarkFacts

/-!
# Ordinary composition and reversal

The ordinary proof sections of the gluing composition theorem.
The unrelated corner-case assembly is not copied.
-/

namespace SkewMarkedFactor.Gluing

namespace Plan

open MvPolynomial

/-! ### Skew-supported combinations -/

/-- The combinations supported on skew diagrams. -/
noncomputable def skewSpace : Submodule ℚ ShapeSpace :=
  Finsupp.supported ℚ ℚ {X : Diagram | IsSkew X}

theorem mem_skewSpace {h : ShapeSpace} : h ∈ skewSpace ↔ IsSkewSupported h := by
  unfold skewSpace IsSkewSupported
  rw [Finsupp.mem_supported]
  constructor
  · intro hh X hX; exact hh hX
  · intro hh X hX; exact hh X hX

theorem shape_mem_skewSpace {X : Diagram} (hX : IsSkew X) : shape X ∈ skewSpace := by
  rw [mem_skewSpace]
  intro Y hY
  have : Y ∈ ({X} : Finset Diagram) := Finsupp.support_single_subset hY
  rw [Finset.mem_singleton] at this
  rw [this]; exact hX

/-- Two linear maps that agree on the basis elements of skew diagrams agree on the
skew-supported combinations. -/
theorem ext_skew {M : Type*} [AddCommMonoid M] [Module ℚ M] (f g : ShapeSpace →ₗ[ℚ] M)
    (hfg : ∀ X : Diagram, IsSkew X → f (shape X) = g (shape X)) {h : ShapeSpace}
    (hh : h ∈ skewSpace) : f h = g h := by
  have hle : skewSpace ≤ LinearMap.eqLocus f g := by
    unfold skewSpace
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨X, hX, rfl⟩
    exact hfg X hX
  exact hle hh

theorem leftOp_shape (m : ℕ) (X : Diagram) :
    leftOp m (shape X) = ∑ Y ∈ leftRibbons X m, (ribbonSign Y : ℚ) • shape (X \ Y) := by
  simp [leftOp, shape, Finsupp.linearCombination_single]

theorem rightOp_shape (m : ℕ) (X : Diagram) :
    rightOp m (shape X) = ∑ Y ∈ rightRibbons X m, (ribbonSign Y : ℚ) • shape (X \ Y) := by
  simp [rightOp, shape, Finsupp.linearCombination_single]

theorem leftOp_mem {h : ShapeSpace} (hh : h ∈ skewSpace) (m : ℕ) : leftOp m h ∈ skewSpace := by
  have hh' := hh
  clear hh
  unfold skewSpace at hh'
  rw [Finsupp.supported_eq_span_single] at hh'
  induction hh' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨X, hX, rfl⟩ := hx
    change leftOp m (shape X) ∈ skewSpace
    rw [leftOp_shape]
    refine Submodule.sum_mem _ fun Y hY => Submodule.smul_mem _ _ ?_
    exact shape_mem_skewSpace (isSkew_sdiff_leftRibbon hX hY)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem rightOp_mem {h : ShapeSpace} (hh : h ∈ skewSpace) (m : ℕ) : rightOp m h ∈ skewSpace := by
  have hh' := hh
  clear hh
  unfold skewSpace at hh'
  rw [Finsupp.supported_eq_span_single] at hh'
  induction hh' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨X, hX, rfl⟩ := hx
    change rightOp m (shape X) ∈ skewSpace
    rw [rightOp_shape]
    refine Submodule.sum_mem _ fun Y hY => Submodule.smul_mem _ _ ?_
    exact shape_mem_skewSpace (isSkew_sdiff_rightRibbon hX hY)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem leftWord_mem (ν : List ℕ) {h : ShapeSpace} (hh : h ∈ skewSpace) :
    leftWord ν h ∈ skewSpace := by
  induction ν generalizing h with
  | nil => simpa [leftWord] using hh
  | cons m ν ih => exact ih (leftOp_mem hh m)

theorem rightWord_mem (ν : List ℕ) {h : ShapeSpace} (hh : h ∈ skewSpace) :
    rightWord ν h ∈ skewSpace := by
  induction ν generalizing h with
  | nil => simpa [rightWord] using hh
  | cons m ν ih => exact rightOp_mem (ih hh) m

/-! ### Linear extension of a function on diagrams -/

/-- The linear extension of `F : Diagram → Λ` to the shape space. -/
noncomputable def Flin (F : Diagram → Lambda) : ShapeSpace →ₗ[ℚ] Lambda :=
  Finsupp.linearCombination ℚ F

theorem Flin_shape (F : Diagram → Lambda) (X : Diagram) : Flin F (shape X) = F X := by
  simp [Flin, shape, Finsupp.linearCombination_single]

theorem smul_int_eq (z : ℤ) (f : Lambda) : ((z : ℚ)) • f = (z : Lambda) * f := by
  rw [Algebra.smul_def]
  simp

theorem Flin_leftOp_shape (F : Diagram → Lambda) (m : ℕ) (X : Diagram) :
    Flin F (leftOp m (shape X)) = ribbonSumLeft F X m := by
  rw [leftOp_shape, map_sum]
  unfold ribbonSumLeft
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_smul, Flin_shape, smul_int_eq]

theorem Flin_rightOp_shape (F : Diagram → Lambda) (m : ℕ) (X : Diagram) :
    Flin F (rightOp m (shape X)) = ribbonSumRight F X m := by
  rw [rightOp_shape, map_sum]
  unfold ribbonSumRight
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_smul, Flin_shape, smul_int_eq]

/-! ### The derivations `∂_m` -/

theorem pDeriv_hh {a : ℕ} (ha : 0 < a) (j : ℤ) : pDeriv a (hh j) = hh (j - a) := by
  by_cases hj : j < 0
  · rw [hh_of_neg hj, hh_of_neg (by omega : j - a < 0)]
    exact map_zero _
  · by_cases h0 : j = 0
    · subst h0
      rw [hh_zero, hh_of_neg (by omega : (0 : ℤ) - a < 0)]
      exact Derivation.map_one_eq_zero _
    · obtain ⟨k, hk⟩ : ∃ k : ℕ+, (k : ℤ) = j := ⟨⟨j.toNat, by omega⟩, by simp; omega⟩
      subst hk
      rw [hh_pnat, pDeriv_X]

theorem pDeriv_comm {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (f : Lambda) :
    pDeriv a (pDeriv b f) = pDeriv b (pDeriv a f) := by
  have h : ⁅pDeriv a, pDeriv b⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pDeriv_X, pDeriv_X, pDeriv_hh ha, pDeriv_hh hb]
    simp only [Derivation.zero_apply]
    rw [sub_eq_zero]
    congr 1
    ring
  have := congrArg (fun D : Derivation ℚ Lambda Lambda => D f) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at this
  exact sub_eq_zero.mp this

theorem pDerivWord_cons (a : ℕ) (l : List ℕ) (f : Lambda) :
    pDerivWord (a :: l) f = pDerivWord l (pDeriv a f) := rfl

theorem pDerivWord_nil (f : Lambda) : pDerivWord [] f = f := rfl

theorem pDerivWord_append (l : List ℕ) (a : ℕ) (f : Lambda) :
    pDerivWord (l ++ [a]) f = pDeriv a (pDerivWord l f) := by
  induction l generalizing f with
  | nil => rfl
  | cons b l ih => simp [pDerivWord_cons, ih]

theorem pDerivWord_perm {l₁ l₂ : List ℕ} (hp : l₁.Perm l₂) (hpos : ∀ a ∈ l₁, 0 < a)
    (f : Lambda) : pDerivWord l₁ f = pDerivWord l₂ f := by
  induction hp generalizing f with
  | nil => rfl
  | cons x _ ih =>
    rw [pDerivWord_cons, pDerivWord_cons]
    exact ih (fun a ha => hpos a (List.mem_cons_of_mem _ ha)) _
  | swap x y l =>
    simp only [pDerivWord_cons]
    rw [pDeriv_comm (hpos x (by simp)) (hpos y (by simp))]
  | trans h₁ _ ih₁ ih₂ =>
    rw [ih₁ hpos, ih₂ (fun a ha => hpos a (h₁.mem_iff.mpr ha))]

/-- A scalar killed by every derivation of the word passes through the word. -/
theorem pDerivWord_mul_of_killed {c : Lambda} {l : List ℕ} (hc : ∀ a ∈ l, pDeriv a c = 0)
    (f : Lambda) : pDerivWord l (c * f) = c * pDerivWord l f := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    rw [pDerivWord_cons, pDerivWord_cons, Derivation.leibniz, hc a (by simp), smul_zero,
      add_zero, smul_eq_mul, ih (fun b hb => hc b (List.mem_cons_of_mem _ hb))]

/-! ### Killed scalars -/

/-- `c` is annihilated by every derivation `∂_{a q}`, `a > 0`, of period `q`. -/
def Killed (ω : MarkedInner) (c : Lambda) : Prop :=
  ∀ a : ℕ, 0 < a → pDeriv (a * ω.period.toNat) c = 0

theorem Killed.mul {ω : MarkedInner} {c d : Lambda} (hc : Killed ω c) (hd : Killed ω d) :
    Killed ω (c * d) := by
  intro a ha
  rw [Derivation.leibniz, hc a ha, hd a ha]
  simp

theorem Killed.pow {ω : MarkedInner} {c : Lambda} (hc : Killed ω c) (n : ℕ) :
    Killed ω (c ^ n) := by
  intro a ha
  rw [Derivation.leibniz_pow, hc a ha]
  simp

theorem killed_intCast (ω : MarkedInner) (z : ℤ) : Killed ω (z : Lambda) := by
  intro a _
  exact Derivation.map_intCast _ z

theorem killed_prod (ω : MarkedInner) (l : List Lambda) (h : ∀ c ∈ l, Killed ω c) :
    Killed ω l.prod := by
  induction l with
  | nil =>
    intro a _
    simp
  | cons c l ih =>
    rw [List.prod_cons]
    exact (h c (by simp)).mul (ih fun d hd => h d (List.mem_cons_of_mem _ hd))

/-! ### The edge case: the modified composition kills the kernel -/

section Edge

variable {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .a ∨ ω.case = .b)

/-- The scalar `± (s_W s_{\overline W} s_{\overline O})^m` of the edge compatibility. -/
noncomputable def edgeScalar (ω : MarkedInner) (m : ℕ) : Lambda :=
  (edgeSign ω m : Lambda) * hatFactor ω ^ m

/-- The scalar of a word. -/
noncomputable def wordScalar (ω : MarkedInner) (ν : List ℕ) : Lambda :=
  (ν.map (edgeScalar ω)).prod

include hω hc in
theorem killed_edgeScalar (m : ℕ) : Killed ω (edgeScalar ω m) := by
  unfold edgeScalar
  refine (killed_intCast ω _).mul (Killed.pow ?_ m)
  intro a ha
  exact pDeriv_hatFactor hω hc ha

include hω hc in
theorem killed_wordScalar (ν : List ℕ) : Killed ω (wordScalar ω ν) := by
  unfold wordScalar
  apply killed_prod
  intro c hc'
  obtain ⟨m, -, rfl⟩ := List.mem_map.mp hc'
  exact killed_edgeScalar hω hc m

theorem edgeSign_ne_zero (ω : MarkedInner) (m : ℕ) : (edgeSign ω m : Lambda) ≠ 0 := by
  have : edgeSign ω m ≠ 0 := by
    unfold edgeSign
    cases ω.case <;> simp
  exact_mod_cast this

include hω in
theorem edgeScalar_ne_zero (m : ℕ) : edgeScalar ω m ≠ 0 :=
  mul_ne_zero (edgeSign_ne_zero ω m) (pow_ne_zero _ (hatFactor_ne_zero hω))

include hω in
theorem wordScalar_ne_zero (ν : List ℕ) : wordScalar ω ν ≠ 0 := by
  unfold wordScalar
  apply List.prod_ne_zero
  intro h0
  obtain ⟨m, -, hm⟩ := List.mem_map.mp h0
  exact edgeScalar_ne_zero hω m hm

/-- The edge equations, extended linearly from basis diagrams to skew-supported combinations. -/
theorem edge_left {Y : ShapeSpace} (hY : Y ∈ skewSpace) (hE : EdgeCompat ω) {m : ℕ}
    (hm : 0 < m) :
    pDeriv (m * ω.period.toNat) (Flin (modComp ω) Y) =
      edgeScalar ω m * Flin (modComp ω) (leftOp m Y) := by
  have := ext_skew
    ((pDeriv (m * ω.period.toNat)).toLinearMap.comp (Flin (modComp ω)))
    ((LinearMap.mulLeft ℚ (edgeScalar ω m)).comp ((Flin (modComp ω)).comp (leftOp m)))
    (fun X hX => by
      simp only [LinearMap.comp_apply, Flin_shape,
        LinearMap.mulLeft_apply, Flin_leftOp_shape]
      exact (hE X hX m hm).1.trans (by rw [edgeScalar]))
    hY
  simpa using this

theorem edge_right {Y : ShapeSpace} (hY : Y ∈ skewSpace) (hE : EdgeCompat ω) {m : ℕ}
    (hm : 0 < m) :
    pDeriv (m * ω.period.toNat) (Flin (modComp ω) Y) =
      edgeScalar ω m * Flin (modComp ω) (rightOp m Y) := by
  have := ext_skew
    ((pDeriv (m * ω.period.toNat)).toLinearMap.comp (Flin (modComp ω)))
    ((LinearMap.mulLeft ℚ (edgeScalar ω m)).comp ((Flin (modComp ω)).comp (rightOp m)))
    (fun X hX => by
      simp only [LinearMap.comp_apply, Flin_shape,
        LinearMap.mulLeft_apply, Flin_rightOp_shape]
      exact (hE X hX m hm).2.trans (by rw [edgeScalar]))
    hY
  simpa using this

theorem leftWord_cons (m : ℕ) (ν : List ℕ) (Y : ShapeSpace) :
    leftWord (m :: ν) Y = leftWord ν (leftOp m Y) := rfl

theorem rightWord_cons (m : ℕ) (ν : List ℕ) (Y : ShapeSpace) :
    rightWord (m :: ν) Y = rightOp m (rightWord ν Y) := rfl

theorem wordScalar_cons (m : ℕ) (ν : List ℕ) :
    wordScalar ω (m :: ν) = edgeScalar ω m * wordScalar ω ν := by
  simp [wordScalar]

theorem killed_apply {c : Lambda} (hk : Killed ω c) {ν : List ℕ} (hν : ∀ a ∈ ν, 0 < a) :
    ∀ b ∈ ν.map (fun a => a * ω.period.toNat), pDeriv b c = 0 := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  exact hk a (hν a ha)

include hω hc in
/-- Iterating the left equation along a word `ν`. -/
theorem edge_leftWord (hE : EdgeCompat ω) (ν : List ℕ) (hν : ∀ m ∈ ν, 0 < m) :
    ∀ {Y : ShapeSpace}, Y ∈ skewSpace →
      pDerivWord (ν.map fun a => a * ω.period.toNat) (Flin (modComp ω) Y) =
        wordScalar ω ν * Flin (modComp ω) (leftWord ν Y) := by
  induction ν with
  | nil => intro Y _; simp [pDerivWord, wordScalar, leftWord]
  | cons m ν ih =>
    intro Y hY
    have hm : 0 < m := hν m (by simp)
    have hν' : ∀ a ∈ ν, 0 < a := fun a ha => hν a (List.mem_cons_of_mem _ ha)
    rw [List.map_cons, pDerivWord_cons, edge_left hY hE hm,
      pDerivWord_mul_of_killed (killed_apply (killed_edgeScalar hω hc m) hν'),
      ih hν' (leftOp_mem hY m), wordScalar_cons, leftWord_cons, mul_assoc]

include hω hc in
/-- Iterating the right equation along a word `ν`. -/
theorem edge_rightWord (hE : EdgeCompat ω) (ν : List ℕ) (hν : ∀ m ∈ ν, 0 < m) :
    ∀ {Y : ShapeSpace}, Y ∈ skewSpace →
      pDerivWord (ν.map fun a => a * ω.period.toNat) (Flin (modComp ω) Y) =
        wordScalar ω ν * Flin (modComp ω) (rightWord ν Y) := by
  induction ν with
  | nil => intro Y _; simp [pDerivWord, wordScalar, rightWord]
  | cons m ν ih =>
    intro Y hY
    have hm : 0 < m := hν m (by simp)
    have hν' : ∀ a ∈ ν, 0 < a := fun a ha => hν a (List.mem_cons_of_mem _ ha)
    have hY' : rightWord ν Y ∈ skewSpace := rightWord_mem ν hY
    have hperm : (((m :: ν).map fun a => a * ω.period.toNat)).Perm
        ((ν.map fun a => a * ω.period.toNat) ++ [m * ω.period.toNat]) := by
      rw [List.map_cons]
      exact (List.perm_append_singleton _ _).symm
    rw [pDerivWord_perm hperm (by
        intro a ha
        simp only [List.mem_map] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        have := hν b hb
        have hq : 0 < ω.period.toNat := by
          have := hω.2.2.1
          unfold MarkedInner.IsNarrow at this
          omega
        positivity), pDerivWord_append, ih hν' hY]
    have hk : Killed ω (wordScalar ω ν) := killed_wordScalar hω hc ν
    rw [Derivation.leibniz, hk m hm, smul_zero, add_zero, smul_eq_mul,
      edge_right hY' hE hm, wordScalar_cons, rightWord_cons]
    ring

include hω hc in
/-- **The modified composition kills the kernel of `schur`**, in the ordinary cases. -/
theorem edge_kernel (hE : EdgeCompat ω) :
    shapeKernelSpan ≤ LinearMap.ker (Flin (modComp ω)) := by
  unfold shapeKernelSpan
  rw [Submodule.span_le]
  rintro h (⟨X, v, hX, rfl⟩ | ⟨ν, Z, hν, hZ, rfl⟩)
  · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, Flin_shape, Flin_shape,
      modComp_translate, sub_self]
  · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
    have hZ' : shape Z ∈ skewSpace := shape_mem_skewSpace hZ
    have h1 := edge_leftWord hω hc hE ν hν hZ'
    have h2 := edge_rightWord hω hc hE ν hν hZ'
    rw [h1] at h2
    exact sub_eq_zero.mpr (mul_left_cancel₀ (wordScalar_ne_zero hω ν) h2).symm

end Edge

/-! ### From equal modified compositions to equal composites -/

section Cancel

variable {ω : MarkedInner}

theorem cellSchur_ne_zero_of_connected {D : Diagram} (hD : IsConnectedSkew D) :
    cellSchur D ≠ 0 := by
  rw [cellSchur_of_isConnectedSkew hD]
  exact (barekatIrreducibility _ _).ne_zero

theorem card_eq_of_cellSchur_eq {D D' : Diagram} (hD : IsConnectedSkew D)
    (hD' : IsConnectedSkew D') (h : cellSchur D = cellSchur D') : D.card = D'.card := by
  have h1 := isWeightedHomogeneous_cellSchur hD.1
  have h2 := isWeightedHomogeneous_cellSchur hD'.1
  rw [← h] at h2
  exact IsWeightedHomogeneous.inj_right (cellSchur_ne_zero_of_connected hD) h1 h2

theorem modComp_connected {D : Diagram} (hD : IsConnectedSkew D) :
    modComp ω D = componentT ω D := by
  unfold modComp
  rw [edgeComponents_eq_singleton hD.2, Finset.prod_singleton]

theorem modCompC_connected {D : Diagram} (hD : IsConnectedSkew D) :
    modCompC ω D = componentTc ω D := by
  unfold modCompC
  rw [edgeComponents_eq_singleton hD.2, Finset.prod_singleton]

theorem hat_factors_ne_zero (hω : ω.IsLegal) :
    cellSchur ω.W ≠ 0 ∧ cellSchur (hatMarkFin ω) ≠ 0 ∧ cellSchur (hatMiddleFin ω) ≠ 0 := by
  have := hatFactor_ne_zero hω
  unfold hatFactor at this
  rw [mul_ne_zero_iff, mul_ne_zero_iff] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- Equal Schur functions of connected outers, and equal `componentT` values, give equal Schur
functions of the composites (the cancellation of the factors `s_W`, `s_{\overline W}`,
`s_{\overline O}`, thesis Cor. 5.4.11). -/
theorem cellSchur_compose_eq_of_componentT (hω : ω.IsLegal) {D D' : Diagram}
    (hD : IsConnectedSkew D) (hD' : IsConnectedSkew D') (h : cellSchur D = cellSchur D')
    (heq : componentT ω D = componentT ω D') :
    cellSchur (ω.compose D) = cellSchur (ω.compose D') := by
  obtain ⟨h1, h2, h3⟩ := hat_factors_ne_zero hω
  have hc := card_eq_of_cellSchur_eq hD hD' h
  have hr := numRows_eq_of_cellSchur_eq hD hD' h
  have hk := numCols_eq_of_cellSchur_eq hD hD' h
  have hs := span_eq_of_cellSchur_eq hD hD' h
  unfold componentT at heq
  rw [hc, hr, hk, hs] at heq
  have hne : cellSchur ω.W ^ (D'.card - numRows D') * cellSchur (hatMarkFin ω) ^
      (D'.card - numCols D') * cellSchur (hatMiddleFin ω) ^ (D'.card - span D') ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ h2)) (pow_ne_zero _ h3)
  exact mul_left_cancel₀ hne heq

/-- The ordinary-case deduction: from the kernel statement to equal composites. -/
theorem cellSchur_compose_eq_of_kernel {T : ShapeSpace →ₗ[ℚ] Lambda}
    (hker : shapeKernelSpan ≤ LinearMap.ker T) {D D' : Diagram} (hD : IsConnectedSkew D)
    (hD' : IsConnectedSkew D') (h : cellSchur D = cellSchur D') :
    T (shape D) = T (shape D') := by
  have hmem : shape D - shape D' ∈ skewSpace :=
    sub_mem (shape_mem_skewSpace hD.1) (shape_mem_skewSpace hD'.1)
  have h0 : shapeSchur (shape D - shape D') = 0 := by
    have : shapeSchur = Flin cellSchur := rfl
    rw [this, map_sub, Flin_shape, Flin_shape, h, sub_self]
  have := hker (kernel_schur (mem_skewSpace.mp hmem) h0)
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  exact this

end Cancel

/-! ### The two halves of the composition theorem -/

/-- **Composition, ordinary marks**, from `edgeCompat_a`, `edgeCompat_b` and `kernel_schur`. -/
theorem cellSchur_compose_eq_of_ordinary_plan {ω : MarkedInner} (hω : ω.IsLegal)
    (hcase : ω.case = .a ∨ ω.case = .b) {D D' : Diagram} (hD : IsConnectedSkew D)
    (hD' : IsConnectedSkew D') (h : cellSchur D = cellSchur D') :
    cellSchur (ω.compose D) = cellSchur (ω.compose D') := by
  have hE : EdgeCompat ω := by
    rcases hcase with hc | hc
    · exact edgeCompat_a hω hc
    · exact edgeCompat_b hω hc
  have hT := cellSchur_compose_eq_of_kernel (edge_kernel hω hcase hE) hD hD' h
  rw [Flin_shape, Flin_shape, modComp_connected hD, modComp_connected hD'] at hT
  exact cellSchur_compose_eq_of_componentT hω hD hD' h hT


end Plan
end SkewMarkedFactor.Gluing
