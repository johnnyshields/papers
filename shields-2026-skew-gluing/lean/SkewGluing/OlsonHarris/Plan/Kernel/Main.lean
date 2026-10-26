import SkewGluing.OlsonHarris.Plan.Kernel.YoungSpace

/-!
# The kernel of `schur` on the shape space

Formalizes `shields-2026-skew-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `def:gluing-graph`): thesis Thm. 5.2.2 (`OlsonHarris2024HopfApplications`): an
element of the shape space supported on skew diagrams with Schur function zero is a combination of
the relations `[X] = [X + v]` and `p_ν ⇀ [Z] = [Z] ↼ p_ν`.

The proof follows the route of the source: modulo the relations, every skew shape `[λ / μ]` is a
combination of Ferrers shapes (`mem_range_sup_kernel_shape`), and the Schur functions of the Ferrers
shapes are linearly independent (`linearIndependent_ferrersSchur`).

Uses `pDeriv_cellSchur_left`, `pDeriv_cellSchur_right`, `pPoly_mul_cellSchur_ferrers` and
`exists_pProd_expansion`.

Sorry-free.
-/

namespace SkewGluing

namespace Plan

namespace KernelAux

open MvPolynomial Shields

/-! ### Skew-supported combinations -/

/-- The combinations supported on skew diagrams. -/
noncomputable def skewSupportedSpace : Submodule ℚ ShapeSpace :=
  Finsupp.supported ℚ ℚ {X : Diagram | IsSkew X}

theorem shape_mem_skewSupportedSpace {X : Diagram} (hX : IsSkew X) :
    shape X ∈ skewSupportedSpace :=
  Finsupp.single_mem_supported ℚ _ hX

theorem mem_skewSupportedSpace {h : ShapeSpace} :
    h ∈ skewSupportedSpace ↔ IsSkewSupported h := by
  unfold skewSupportedSpace IsSkewSupported
  rw [Finsupp.mem_supported]
  exact ⟨fun hh X hX => hh hX, fun hh X hX => hh X hX⟩

/-- An element of the skew-supported space is a combination of basis elements of skew
diagrams: induction principle. -/
theorem skewSupportedSpace_induction {P : ShapeSpace → Prop} (h0 : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b)) (hsmul : ∀ (c : ℚ) a, P a → P (c • a))
    (hshape : ∀ X, IsSkew X → P (shape X)) {h : ShapeSpace} (hh : h ∈ skewSupportedSpace) :
    P h := by
  have hh' := hh
  clear hh
  unfold skewSupportedSpace at hh'
  rw [Finsupp.supported_eq_span_single] at hh'
  induction hh' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨X, hX, rfl⟩ := hx
    exact hshape X hX
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd _ _ hx hy
  | smul a x _ hx => exact hsmul _ _ hx

theorem leftOp_mem_skewSupportedSpace {h : ShapeSpace} (hh : h ∈ skewSupportedSpace) (m : ℕ) :
    leftOp m h ∈ skewSupportedSpace := by
  refine skewSupportedSpace_induction (P := fun h => leftOp m h ∈ skewSupportedSpace)
    (by simp) (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    (fun c a ha => by rw [map_smul]; exact Submodule.smul_mem _ _ ha) ?_ hh
  intro X hX
  rw [leftOp_shape]
  exact Submodule.sum_mem _ fun Y hY => Submodule.smul_mem _ _
    (shape_mem_skewSupportedSpace (isSkew_sdiff_of_mem_leftRibbons hX hY))

theorem rightOp_mem_skewSupportedSpace {h : ShapeSpace} (hh : h ∈ skewSupportedSpace) (m : ℕ) :
    rightOp m h ∈ skewSupportedSpace := by
  refine skewSupportedSpace_induction (P := fun h => rightOp m h ∈ skewSupportedSpace)
    (by simp) (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    (fun c a ha => by rw [map_smul]; exact Submodule.smul_mem _ _ ha) ?_ hh
  intro X hX
  rw [rightOp_shape]
  exact Submodule.sum_mem _ fun Y hY => Submodule.smul_mem _ _
    (shape_mem_skewSupportedSpace (isSkew_sdiff_of_mem_rightRibbons hX hY))

theorem leftWord_mem_skewSupportedSpace (nu : List ℕ) {h : ShapeSpace}
    (hh : h ∈ skewSupportedSpace) : leftWord nu h ∈ skewSupportedSpace := by
  induction nu generalizing h with
  | nil => simpa [leftWord] using hh
  | cons m nu ih => exact ih (leftOp_mem_skewSupportedSpace hh m)

theorem rightWord_mem_skewSupportedSpace (nu : List ℕ) {h : ShapeSpace}
    (hh : h ∈ skewSupportedSpace) : rightWord nu h ∈ skewSupportedSpace := by
  induction nu generalizing h with
  | nil => simpa [rightWord] using hh
  | cons m nu ih => exact rightOp_mem_skewSupportedSpace (ih hh) m

/-! ### The Schur function of the actions -/

theorem shapeSchur_shape (X : Diagram) : shapeSchur (shape X) = cellSchur X := by
  simp [shapeSchur, shape, Finsupp.linearCombination_single]

theorem smul_int_eq (z : ℤ) (f : Lambda) : (z : ℚ) • f = (z : Lambda) * f := by
  rw [Algebra.smul_def]
  simp

theorem shapeSchur_leftOp {h : ShapeSpace} (hh : h ∈ skewSupportedSpace) {m : ℕ} (hm : 0 < m) :
    shapeSchur (leftOp m h) = pDeriv m (shapeSchur h) := by
  refine skewSupportedSpace_induction
    (P := fun h => shapeSchur (leftOp m h) = pDeriv m (shapeSchur h)) (by simp)
    (fun a b ha hb => by rw [map_add, map_add, map_add, ha, hb, map_add])
    (fun c a ha => by rw [map_smul, map_smul, map_smul, ha, Derivation.map_smul]) ?_ hh
  intro X hX
  rw [leftOp_shape, map_sum, shapeSchur_shape, pDeriv_cellSchur_left hX hm]
  unfold ribbonSumLeft
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_smul, shapeSchur_shape, smul_int_eq]

theorem shapeSchur_rightOp {h : ShapeSpace} (hh : h ∈ skewSupportedSpace) {m : ℕ} (hm : 0 < m) :
    shapeSchur (rightOp m h) = pDeriv m (shapeSchur h) := by
  refine skewSupportedSpace_induction
    (P := fun h => shapeSchur (rightOp m h) = pDeriv m (shapeSchur h)) (by simp)
    (fun a b ha hb => by rw [map_add, map_add, map_add, ha, hb, map_add])
    (fun c a ha => by rw [map_smul, map_smul, map_smul, ha, Derivation.map_smul]) ?_ hh
  intro X hX
  rw [rightOp_shape, map_sum, shapeSchur_shape, pDeriv_cellSchur_right hX hm]
  unfold ribbonSumRight
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_smul, shapeSchur_shape, smul_int_eq]

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

theorem pDerivWord_append (l : List ℕ) (a : ℕ) (f : Lambda) :
    pDerivWord (l ++ [a]) f = pDeriv a (pDerivWord l f) := by
  induction l generalizing f with
  | nil => rfl
  | cons b l ih => simp [pDerivWord_cons, ih]

theorem pDerivWord_comm {l : List ℕ} (hl : ∀ a ∈ l, 0 < a) {b : ℕ} (hb : 0 < b) (f : Lambda) :
    pDerivWord l (pDeriv b f) = pDeriv b (pDerivWord l f) := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    rw [pDerivWord_cons, pDerivWord_cons,
      pDeriv_comm (hl a List.mem_cons_self) hb, ih fun x hx => hl x (List.mem_cons_of_mem _ hx)]

theorem pDerivWord_reverse {l : List ℕ} (hl : ∀ a ∈ l, 0 < a) (f : Lambda) :
    pDerivWord l.reverse f = pDerivWord l f := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    have hl' : ∀ x ∈ l, 0 < x := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    rw [List.reverse_cons, pDerivWord_append, ih hl', pDerivWord_cons,
      pDerivWord_comm hl' (hl a List.mem_cons_self)]

theorem shapeSchur_leftWord {nu : List ℕ} (hnu : ∀ m ∈ nu, 0 < m) {h : ShapeSpace}
    (hh : h ∈ skewSupportedSpace) : shapeSchur (leftWord nu h) = pDerivWord nu (shapeSchur h) := by
  induction nu generalizing h with
  | nil => rfl
  | cons m nu ih =>
    have hm : 0 < m := hnu m List.mem_cons_self
    have hnu' : ∀ k ∈ nu, 0 < k := fun k hk => hnu k (List.mem_cons_of_mem _ hk)
    simp only [leftWord, LinearMap.comp_apply]
    rw [ih hnu' (leftOp_mem_skewSupportedSpace hh m), shapeSchur_leftOp hh hm]
    rfl

theorem shapeSchur_rightWord_reverse {nu : List ℕ} (hnu : ∀ m ∈ nu, 0 < m) {h : ShapeSpace}
    (hh : h ∈ skewSupportedSpace) :
    shapeSchur (rightWord nu h) = pDerivWord nu.reverse (shapeSchur h) := by
  induction nu generalizing h with
  | nil => rfl
  | cons m nu ih =>
    have hm : 0 < m := hnu m List.mem_cons_self
    have hnu' : ∀ k ∈ nu, 0 < k := fun k hk => hnu k (List.mem_cons_of_mem _ hk)
    simp only [rightWord, LinearMap.comp_apply]
    rw [shapeSchur_rightOp (rightWord_mem_skewSupportedSpace nu hh) hm, ih hnu' hh,
      List.reverse_cons, pDerivWord_append]

theorem shapeSchur_rightWord {nu : List ℕ} (hnu : ∀ m ∈ nu, 0 < m) {h : ShapeSpace}
    (hh : h ∈ skewSupportedSpace) : shapeSchur (rightWord nu h) = pDerivWord nu (shapeSchur h) := by
  rw [shapeSchur_rightWord_reverse hnu hh, pDerivWord_reverse hnu]

/-- `schur` kills the relations. -/
theorem shapeKernelSpan_le_ker : shapeKernelSpan ≤ LinearMap.ker shapeSchur := by
  unfold shapeKernelSpan
  rw [Submodule.span_le]
  rintro _ (⟨X, v, _, rfl⟩ | ⟨nu, Z, hnu, hZ, rfl⟩)
  · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, shapeSchur_shape, shapeSchur_shape,
      cellSchur_translate, sub_self]
  · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub,
      shapeSchur_rightWord hnu (shape_mem_skewSupportedSpace hZ),
      shapeSchur_leftWord hnu (shape_mem_skewSupportedSpace hZ), sub_self]

/-! ### Skew diagrams are translates of `λ / μ` -/

theorem exists_translate_skewDiagram {X : Diagram} (hX : IsSkew X) :
    ∃ (v : ℤ × ℤ) (lam mu : YoungDiagram), mu ≤ lam ∧ X = translate v (skewDiagram lam mu) := by
  set S1 : ℤ := ∑ x ∈ X, |x.1| with hS1
  set S2 : ℤ := ∑ x ∈ X, |x.2| with hS2
  have hnn : ∀ x ∈ translate (S1, S2) X, 0 ≤ x.1 ∧ 0 ≤ x.2 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have h1 : |y.1| ≤ S1 := Finset.single_le_sum (f := fun x : ℤ × ℤ => |x.1|)
      (fun _ _ => abs_nonneg _) hy
    have h2 : |y.2| ≤ S2 := Finset.single_le_sum (f := fun x : ℤ × ℤ => |x.2|)
      (fun _ _ => abs_nonneg _) hy
    have := neg_abs_le y.1
    have := neg_abs_le y.2
    simp only [Prod.fst_add, Prod.snd_add]
    constructor <;> omega
  obtain ⟨lam, mu, hmu, hD⟩ := exists_young_pair_of_isSkew (isSkew_translate (S1, S2) hX) hnn
  refine ⟨(-S1, -S2), lam, mu, hmu, ?_⟩
  rw [hD, translate_translate]
  have : ((-S1, -S2) : ℤ × ℤ) + (S1, S2) = 0 := by ext <;> simp
  rw [this, translate_zero]

/-! ### Right removal from Ferrers shapes stays among Ferrers shapes -/

theorem exists_young_sdiff_upset {sigma : YoungDiagram} {Y : Diagram}
    (hY : IsUpsetIn (skewDiagram sigma ⊥) Y) :
    ∃ tau : YoungDiagram, skewDiagram sigma ⊥ \ Y = skewDiagram tau ⊥ := by
  have hnn : ∀ x ∈ skewDiagram sigma ⊥ \ Y, 0 ≤ x.1 ∧ 0 ≤ x.2 := fun x hx =>
    nonneg_of_mem_skewDiagram (Finset.mem_sdiff.mp hx).1
  have hlow : ∀ x ∈ skewDiagram sigma ⊥ \ Y, ∀ i j : ℕ, (i : ℤ) ≤ x.1 → (j : ℤ) ≤ x.2 →
      ((i : ℤ), (j : ℤ)) ∈ skewDiagram sigma ⊥ \ Y := by
    intro x hx i j hi hj
    obtain ⟨hxs, hxY⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨a, b, rfl⟩ := nat_cell_of_mem_skewDiagram hxs
    have hi' : i ≤ a := by simpa using hi
    have hj' : j ≤ b := by simpa using hj
    have hij : ((i : ℤ), (j : ℤ)) ∈ skewDiagram sigma ⊥ :=
      mem_skewDiagram_bot.mpr (sigma.up_left_mem hi' hj' (mem_skewDiagram_bot.mp hxs))
    refine Finset.mem_sdiff.mpr ⟨hij, fun hijY => hxY ?_⟩
    exact hY.2 _ hxs _ hijY hi hj
  exact exists_young_of_lowerSet hnn hlow |>.imp fun tau h => h.symm

theorem rightOp_range_ferrersShape (m : ℕ) {g : ShapeSpace}
    (hg : g ∈ LinearMap.range ferrersShape) :
    rightOp m g ∈ LinearMap.range ferrersShape := by
  obtain ⟨y, rfl⟩ := hg
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, map_add]
    exact add_mem ha hb
  | single sigma c =>
    have : Finsupp.single sigma c = c • Finsupp.single sigma (1 : ℚ) := by simp
    rw [this, map_smul, map_smul]
    refine Submodule.smul_mem _ _ ?_
    have h1 : ferrersShape (Finsupp.single sigma 1) = shape (skewDiagram sigma ⊥) := by
      simp [ferrersShape, Finsupp.linearCombination_single]
    rw [h1, rightOp_shape]
    refine Submodule.sum_mem _ fun Y hY => Submodule.smul_mem _ _ ?_
    obtain ⟨tau, htau⟩ := exists_young_sdiff_upset (mem_rightRibbons.mp hY).2.2.2
    rw [htau]
    exact ⟨Finsupp.single tau 1, by simp [ferrersShape, Finsupp.linearCombination_single]⟩

theorem rightWord_range_ferrersShape (nu : List ℕ) {g : ShapeSpace}
    (hg : g ∈ LinearMap.range ferrersShape) : rightWord nu g ∈ LinearMap.range ferrersShape := by
  induction nu with
  | nil => simpa [rightWord] using hg
  | cons m nu ih =>
    simp only [rightWord, LinearMap.comp_apply]
    exact rightOp_range_ferrersShape m ih

/-! ### Every skew shape is a combination of Ferrers shapes modulo the relations -/

theorem ferrersMap_injective : Function.Injective ferrersMap :=
  linearIndependent_iff_injective_finsuppLinearCombination.mp linearIndependent_ferrersSchur

theorem ferrersMap_sum_expansion (l : List (ℚ × List ℕ)) (hl : ∀ p ∈ l, ∀ m ∈ p.2, 0 < m) :
    ferrersMap (l.map fun p => p.1 • addWord p.2 (Finsupp.single ⊥ (1 : ℚ))).sum =
      (l.map fun p => p.1 • pProd p.2).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.sum_cons, map_add, ih fun q hq => hl q (List.mem_cons_of_mem _ hq),
      List.map_cons, List.sum_cons, map_smul, ferrersMap_addWord (hl p List.mem_cons_self)]
    have : ferrersMap (Finsupp.single (⊥ : YoungDiagram) (1 : ℚ)) = 1 := by
      rw [ferrersMap_single, one_smul, ferrersSchur_bot]
    rw [this, mul_one]

/-- The skew shape `[λ / μ]` lies in the sum of the Ferrers shapes and the relations. -/
theorem shape_skewDiagram_mem {lam mu : YoungDiagram} (hmu : mu ≤ lam) :
    shape (skewDiagram lam mu) ∈ LinearMap.range ferrersShape ⊔ shapeKernelSpan := by
  obtain ⟨l, hpos, hfl⟩ := exists_pProd_expansion (ferrersSchur mu)
  have hZ : shape (skewDiagram lam ⊥) ∈ skewSupportedSpace :=
    shape_mem_skewSupportedSpace (isSkew_skewDiagram lam ⊥)
  set y : YoungSpace := (l.map fun p => p.1 • addWord p.2 (Finsupp.single ⊥ (1 : ℚ))).sum
    with hy
  have hyμ : y = Finsupp.single mu 1 := by
    apply ferrersMap_injective
    rw [hy, ferrersMap_sum_expansion l hpos, ← hfl, ferrersMap_single, one_smul]
  have hshape : skewShapeMap lam y = shape (skewDiagram lam mu) := by
    rw [hyμ, skewShapeMap_single]
    simp [hmu]
  have hbot : skewShapeMap lam (Finsupp.single ⊥ (1 : ℚ)) = shape (skewDiagram lam ⊥) := by
    rw [skewShapeMap_single]
    simp
  have hexp : skewShapeMap lam y =
      (l.map fun p => p.1 • leftWord p.2 (shape (skewDiagram lam ⊥))).sum := by
    rw [hy, map_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, map_smul, skewShapeMap_addWord, hbot]
  have hfer : (l.map fun p => p.1 • rightWord p.2 (shape (skewDiagram lam ⊥))).sum ∈
      LinearMap.range ferrersShape := by
    refine list_sum_mem fun g hg => ?_
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hg
    refine Submodule.smul_mem _ _ (rightWord_range_ferrersShape _ ?_)
    exact ⟨Finsupp.single lam 1, by simp [ferrersShape, Finsupp.linearCombination_single]⟩
  have hrel : (l.map fun p => p.1 • rightWord p.2 (shape (skewDiagram lam ⊥))).sum -
      (l.map fun p => p.1 • leftWord p.2 (shape (skewDiagram lam ⊥))).sum ∈ shapeKernelSpan := by
    clear hfl hexp hshape hyμ hy hfer
    induction l with
    | nil => simp
    | cons p l ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
        add_sub_add_comm]
      refine add_mem ?_ (ih fun q hq => hpos q (List.mem_cons_of_mem _ hq))
      rw [← smul_sub]
      refine Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨p.2, _,
        hpos p List.mem_cons_self, isSkew_skewDiagram lam ⊥, rfl⟩))
  have : shape (skewDiagram lam mu) =
      (l.map fun p => p.1 • rightWord p.2 (shape (skewDiagram lam ⊥))).sum -
      ((l.map fun p => p.1 • rightWord p.2 (shape (skewDiagram lam ⊥))).sum -
        (l.map fun p => p.1 • leftWord p.2 (shape (skewDiagram lam ⊥))).sum) := by
    rw [sub_sub_cancel, ← hexp, hshape]
  rw [this]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left hfer) (Submodule.mem_sup_right hrel)

theorem shape_mem_range_sup_kernel {X : Diagram} (hX : IsSkew X) :
    shape X ∈ LinearMap.range ferrersShape ⊔ shapeKernelSpan := by
  obtain ⟨v, lam, mu, hmu, rfl⟩ := exists_translate_skewDiagram hX
  have hrel : shape (translate v (skewDiagram lam mu)) - shape (skewDiagram lam mu) ∈
      shapeKernelSpan := by
    have : shape (skewDiagram lam mu) - shape (translate v (skewDiagram lam mu)) ∈
        shapeKernelSpan :=
      Submodule.subset_span (Or.inl ⟨_, v, isSkew_skewDiagram lam mu, rfl⟩)
    rw [← neg_sub]
    exact Submodule.neg_mem _ this
  have := Submodule.add_mem _ (shape_skewDiagram_mem hmu) (Submodule.mem_sup_right hrel)
  simpa using this

theorem mem_range_sup_kernel_shape {h : ShapeSpace} (hh : h ∈ skewSupportedSpace) :
    h ∈ LinearMap.range ferrersShape ⊔ shapeKernelSpan := by
  refine skewSupportedSpace_induction
    (P := fun h => h ∈ LinearMap.range ferrersShape ⊔ shapeKernelSpan) (zero_mem _)
    (fun a b ha hb => add_mem ha hb) (fun c a ha => Submodule.smul_mem _ _ ha)
    (fun X hX => shape_mem_range_sup_kernel hX) hh

theorem shapeSchur_ferrersShape : shapeSchur.comp ferrersShape = ferrersMap := by
  apply Finsupp.lhom_ext
  intro sigma c
  simp [ferrersShape, ferrersMap, ferrersSchur, shapeSchur_shape,
    Finsupp.linearCombination_single]

/-- **Thesis Thm. 5.2.2.** -/
theorem kernel_schur_aux {h : ShapeSpace} (hh : IsSkewSupported h) (h0 : shapeSchur h = 0) :
    h ∈ shapeKernelSpan := by
  obtain ⟨g, hg, k, hk, rfl⟩ := Submodule.mem_sup.mp
    (mem_range_sup_kernel_shape (mem_skewSupportedSpace.mpr hh))
  obtain ⟨y, rfl⟩ := hg
  have hk0 : shapeSchur k = 0 := LinearMap.mem_ker.mp (shapeKernelSpan_le_ker hk)
  have hy0 : ferrersMap y = 0 := by
    rw [← shapeSchur_ferrersShape, LinearMap.comp_apply]
    rw [map_add, hk0, add_zero] at h0
    exact h0
  have : y = 0 := ferrersMap_injective (by rw [hy0, map_zero])
  rw [this, map_zero, zero_add]
  exact hk

end KernelAux

end Plan

end SkewGluing
