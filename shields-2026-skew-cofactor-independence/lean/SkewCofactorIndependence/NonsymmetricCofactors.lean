/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCofactorIndependence.BoundaryCofactors

/-!
# Nonsymmetric dense cofactor independence

The all-order nonsymmetric clause of `thm:cofactor-relations`.  Private-label
induction acts on the actual complementary diagrams; weighted homogeneous
components separate labels, and the complete symmetric relation kernel rules
out support in one row.  The public theorem assumes no derivative, rank, or
boundary-nonproportionality certificate.
-/
namespace SkewCofactorIndependence
open scoped BigOperators
namespace BetaDiagram
variable {n : ℕ}

/-- An actual rational relation splits by its actual entry labels. -/
theorem cofactor_relation_label_group (D : BetaDiagram (n + 1)) (hd : D.Dense)
    (c : Fin (n + 1) × Fin (n + 1) → ℚ) (h : cofactorRelationMap D c = 0)
    (s : Fin (n + 1) × Fin (n + 1)) :
    (∑ t, if D.row t.1 - D.col t.2 = D.row s.1 - D.col s.2 then
      c t • D.cofactor t.1 t.2 else 0) = 0 := by
  classical
  let d := -((D.area - (D.row s.1 - D.col s.2) : ℤ) : ℝ)
  have he := congrArg (MvPolynomial.weightedHomogeneousComponent reverseIndexWeight d) h
  simp only [map_zero] at he
  change MvPolynomial.weightedHomogeneousComponent reverseIndexWeight d
    (∑ t, c t • D.cofactor t.1 t.2) = 0 at he
  rw [map_sum] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro t _
  rw [map_smul]
  have ht := D.cofactor_reverse_homogeneous hd t.1 t.2
  by_cases hl : D.row t.1 - D.col t.2 = D.row s.1 - D.col s.2
  · simp only [hl, ite_true]
    dsimp [d]
    rw [hl] at ht
    rw [ht.weightedHomogeneousComponent_same]
  · simp only [hl, ite_false]
    have hne : d ≠ -((D.area - (D.row t.1 - D.col t.2) : ℤ) : ℝ) := by
      intro he
      apply hl
      have hc : D.area - (D.row s.1 - D.col s.2) =
          D.area - (D.row t.1 - D.col t.2) := by
        exact_mod_cast (neg_injective he)
      omega
    rw [ht.weightedHomogeneousComponent_ne d hne, smul_zero]

/-- A singleton label group cannot carry a nonzero coefficient. -/
theorem cofactor_relation_singleton (D : BetaDiagram (n + 1)) (hd : D.Dense)
    (c : Fin (n + 1) × Fin (n + 1) → ℚ) (h : cofactorRelationMap D c = 0)
    (s : Fin (n + 1) × Fin (n + 1))
    (ho : ∀ t, D.row t.1 - D.col t.2 = D.row s.1 - D.col s.2 → t ≠ s → c t = 0) :
    c s = 0 := by
  classical
  have hg := D.cofactor_relation_label_group hd c h s
  rw [Finset.sum_eq_single s] at hg
  · simp only [ite_true] at hg
    exact (smul_eq_zero.mp hg).resolve_right (D.cofactor_ne_zero hd _ _)
  · intro t _ hts
    split_ifs with hl
    · rw [ho t hl hts, zero_smul]
    · rfl
  · simp

/-- A two-site label group is exactly the sum of its two actual cofactor terms. -/
theorem cofactor_relation_pair (D : BetaDiagram (n + 1)) (hd : D.Dense)
    (c : Fin (n + 1) × Fin (n + 1) → ℚ) (h : cofactorRelationMap D c = 0)
    (s t : Fin (n + 1) × Fin (n + 1)) (hst : s ≠ t)
    (hl : D.row t.1 - D.col t.2 = D.row s.1 - D.col s.2)
    (ho : ∀ x, D.row x.1 - D.col x.2 = D.row s.1 - D.col s.2 →
      x ≠ s → x ≠ t → c x = 0) :
    c s • D.cofactor s.1 s.2 + c t • D.cofactor t.1 t.2 = 0 := by
  classical
  have hg := D.cofactor_relation_label_group hd c h s
  have hf : ∀ x : Fin (n + 1) × Fin (n + 1),
      (if D.row x.1 - D.col x.2 = D.row s.1 - D.col s.2 then
        c x • D.cofactor x.1 x.2 else 0) =
      (if x = s then c s • D.cofactor s.1 s.2 else 0) +
        (if x = t then c t • D.cofactor t.1 t.2 else 0) := by
    intro x
    by_cases hxs : x = s
    · subst x
      simp [hst]
    · by_cases hxt : x = t
      · subst x
        simp [hl, hxs]
      · by_cases he : D.row x.1 - D.col x.2 = D.row s.1 - D.col s.2
        · simp [he, hxs, hxt, ho x he hxs hxt]
        · simp [he, hxs, hxt]
  simp_rw [hf] at hg
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hg

/-- Strict lists make a label unique within a row. -/
theorem label_row_injective (D : BetaDiagram (n + 1)) (i : Fin (n + 1)) :
    Function.Injective (fun j => D.row i - D.col j) := by
  intro j k he
  change D.row i - D.col j = D.row i - D.col k at he
  apply D.col_strictAnti.injective
  omega

/-- Strict lists make a label unique within a column. -/
theorem label_col_injective (D : BetaDiagram (n + 1)) (j : Fin (n + 1)) :
    Function.Injective (fun i => D.row i - D.col j) := by
  intro i k he
  change D.row i - D.col j = D.row k - D.col j at he
  apply D.row_strictAnti.injective
  omega

/-- A relation supported only in the last column splits into singleton degrees. -/
theorem cofactor_relation_last_column (D : BetaDiagram (n + 1)) (hd : D.Dense)
    (c : Fin (n + 1) × Fin (n + 1) → ℚ) (h : cofactorRelationMap D c = 0)
    (ho : ∀ i j, j ≠ Fin.last n → c (i, j) = 0) : c = 0 := by
  funext s
  by_cases hj : s.2 = Fin.last n
  · apply D.cofactor_relation_singleton hd c h s
    intro t hl hts
    by_cases ht : t.2 = Fin.last n
    · have hi : t.1 = s.1 := D.label_col_injective (Fin.last n) (by simpa [ht, hj] using hl)
      exact False.elim (hts (Prod.ext hi (ht.trans hj.symm)))
    · exact ho _ _ ht
  · exact ho _ _ hj

/-- Distinct actual weighted degrees make the last-column family independent. -/
theorem last_column_cofactor_independent (D : BetaDiagram (n + 1)) (hd : D.Dense) :
    LinearIndependent ℚ (fun i : Fin (n + 1) => D.cofactor i (Fin.last n)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let b : Fin (n + 1) × Fin (n + 1) → ℚ :=
    fun s => if s.2 = Fin.last n then c s.1 else 0
  have hb : cofactorRelationMap D b = 0 := by
    simpa [cofactorRelationMap,b,Fintype.sum_prod_type] using hc
  have hz := D.cofactor_relation_last_column hd b hb
    (by intro i j hj; simp only [b,hj,ite_false])
  simpa only [b,ite_true,Pi.zero_apply] using congrFun hz (i,Fin.last n)

/-- A boundary-supported relation has at most two sites per degree group. -/
theorem cofactor_relation_boundaries (D : BetaDiagram (n + 2)) (hd : D.Dense)
    (hs : ¬ D.Symmetric) (c : Fin (n + 2) × Fin (n + 2) → ℚ)
    (h : cofactorRelationMap D c = 0)
    (ho : ∀ i j, i ≠ 0 → j ≠ Fin.last (n + 1) → c (i, j) = 0) : c = 0 := by
  classical
  have htop : ∀ j, c (0,j) = 0 := by
    intro j
    by_cases hj : j = Fin.last (n + 1)
    · subst j
      apply D.cofactor_relation_singleton hd c h (0,Fin.last (n + 1))
      intro t hl ht
      have hne : t.1 ≠ 0 ∨ t.2 ≠ Fin.last (n + 1) := by
        by_contra he
        push Not at he
        exact ht (Prod.ext he.1 he.2)
      have hh := D.index_lt_largestLabel t.1 t.2 hne
      dsimp [largestLabel] at hh
      change D.row t.1 - D.col t.2 = D.row 0 - D.col (Fin.last (n + 1)) at hl
      omega
    · by_cases hex : ∃ i, D.row i - D.col (Fin.last (n + 1)) = D.row 0 - D.col j
      · obtain ⟨i, hiLabel⟩ := hex
        have hi : i ≠ 0 := by
          intro hi
          subst i
          exact hj (D.label_row_injective 0 hiLabel.symm)
        have hp := D.cofactor_relation_pair hd c h (0,j) (i,Fin.last (n + 1))
          (by intro he; exact hi (congrArg Prod.fst he).symm) hiLabel
          (by
            intro t hl ht0 hti
            by_cases htrow : t.1 = 0
            · have htcol : t.2 = j := D.label_row_injective 0 (by simpa [htrow] using hl)
              exact False.elim (ht0 (Prod.ext htrow htcol))
            · by_cases htcol : t.2 = Fin.last (n + 1)
              · have htrow' : t.1 = i := D.label_col_injective (Fin.last (n + 1))
                  (by simpa [htcol] using hl.trans hiLabel.symm)
                exact False.elim (hti (Prod.ext htrow' htcol))
              · exact ho _ _ htrow htcol)
        exact (D.boundary_pair_independent hd hs i j hi hj _ _ hp).1
      · apply D.cofactor_relation_singleton hd c h (0,j)
        intro t hl ht
        by_cases htrow : t.1 = 0
        · have htcol : t.2 = j := D.label_row_injective 0 (by simpa [htrow] using hl)
          exact False.elim (ht (Prod.ext htrow htcol))
        · by_cases htcol : t.2 = Fin.last (n + 1)
          · exact False.elim (hex ⟨t.1, by simpa [htcol] using hl⟩)
          · exact ho _ _ htrow htcol
  apply D.cofactor_relation_last_column hd c h
  intro i j hj
  by_cases hi : i = 0
  · subst i
    exact htop j
  · exact ho i j hi hj

/-- Differentiating a relation gives the actual child's relation, with the common sign removed. -/
theorem cofactor_relation_private_child (D : BetaDiagram (n + 2)) (hd : D.Dense)
    (r k : Fin (n + 2)) (hp : D.PrivateLabel r k)
    (c : Fin (n + 2) × Fin (n + 2) → ℚ) (h : cofactorRelationMap D c = 0) :
    cofactorRelationMap (D.deleteSite hd r k)
      (fun s => c (r.succAbove s.1,k.succAbove s.2)) = 0 := by
  classical
  let v := D.siteGenerator hd r k
  have he := congrArg (MvPolynomial.pderiv v) h
  simp only [map_zero] at he
  change MvPolynomial.pderiv v (∑ s, c s • D.cofactor s.1 s.2) = 0 at he
  simp only [map_sum, Derivation.map_smul, Fintype.sum_prod_type] at he
  rw [Fin.sum_univ_succAbove _ r] at he
  have hb : ∀ j, MvPolynomial.pderiv v (D.cofactor r j) = 0 :=
    fun j => D.cofactor_pderiv_private_boundary hd r k r j hp (Or.inl rfl)
  simp only [hb, smul_zero, Finset.sum_const_zero, zero_add] at he
  have hc : ∀ a, (∑ j, c (r.succAbove a,j) • MvPolynomial.pderiv v
      (D.cofactor (r.succAbove a) j)) =
      ∑ b, c (r.succAbove a,k.succAbove b) •
        ((-1) ^ (r.val+k.val) * (D.deleteSite hd r k).cofactor a b) := by
    intro a
    rw [Fin.sum_univ_succAbove _ k]
    rw [D.cofactor_pderiv_private_boundary hd r k _ k hp (Or.inr rfl), smul_zero, zero_add]
    apply Finset.sum_congr rfl
    intro b _
    rw [D.cofactor_pderiv_private hd r k hp]
  simp_rw [hc] at he
  have hf : (∑ a, ∑ b, c (r.succAbove a,k.succAbove b) •
      ((-1 : CompleteRing) ^ (r.val+k.val) * (D.deleteSite hd r k).cofactor a b)) =
      (-1 : CompleteRing) ^ (r.val+k.val) *
        cofactorRelationMap (D.deleteSite hd r k)
          (fun s => c (r.succAbove s.1,k.succAbove s.2)) := by
    simp only [cofactorRelationMap, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type,
      Finset.mul_sum, Algebra.mul_smul_comm]
  rw [hf] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (by norm_num))

/-- Actual independent child cofactors kill precisely the coefficients off its deleted axes. -/
theorem cofactor_relation_kill_off_private_axes (D : BetaDiagram (n + 2)) (hd : D.Dense)
    (r k : Fin (n + 2)) (hp : D.PrivateLabel r k)
    (hli : LinearIndependent ℚ (fun s : Fin (n + 1) × Fin (n + 1) =>
      (D.deleteSite hd r k).cofactor s.1 s.2))
    (c : Fin (n + 2) × Fin (n + 2) → ℚ) (h : cofactorRelationMap D c = 0) :
    ∀ i j, i ≠ r → j ≠ k → c (i,j) = 0 := by
  have hchild := D.cofactor_relation_private_child hd r k hp c h
  have hz := (Fintype.linearIndependent_iff.mp hli)
    (fun s => c (r.succAbove s.1,k.succAbove s.2)) hchild
  intro i j hi hj
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hi
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hj
  simpa [ha,hb] using hz (a,b)

/-- The complete symmetric relation kernel supplies antisymmetry at every site. -/
theorem symmetric_relation_antisymmetric (D : BetaDiagram (n + 1)) (hd : D.Dense)
    (hs : D.Symmetric) (c : Fin (n + 1) × Fin (n + 1) → ℚ)
    (h : cofactorRelationMap D c = 0) : ∀ s, c s + c (siteReflection s) = 0 := by
  classical
  have hm : c ∈ Submodule.span ℚ (Set.range (fun s : Fin (n + 1) × Fin (n + 1) =>
      Pi.single s (1 : ℚ) - Pi.single (siteReflection s) 1)) := by
    rw [← symmetric_cofactor_kernel D hd hs]
    exact h
  intro s
  let f : (Fin (n + 1) × Fin (n + 1) → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun x => x s + x (siteReflection s)
      map_add' := by intros; simp; ring
      map_smul' := by intros; simp; ring }
  have hle : Submodule.span ℚ (Set.range (fun t : Fin (n + 1) × Fin (n + 1) =>
      Pi.single t (1 : ℚ) - Pi.single (siteReflection t) 1)) ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro x ⟨t,rfl⟩
    change ((Pi.single t (1 : ℚ) - Pi.single (siteReflection t) 1 :
      Fin (n + 1) × Fin (n + 1) → ℚ) s) +
      ((Pi.single t (1 : ℚ) - Pi.single (siteReflection t) 1 :
        Fin (n + 1) × Fin (n + 1) → ℚ) (siteReflection s)) = 0
    have he : siteReflection s = t ↔ s = siteReflection t := by
      constructor <;> intro h
      · simpa using congrArg siteReflection h
      · simp [h]
    have he' : siteReflection s = siteReflection t ↔ s = t :=
      (Function.Involutive.injective siteReflection_involutive).eq_iff
    simp only [Pi.sub_apply, Pi.single_apply]
    by_cases hst : s = t <;> by_cases hsrt : s = siteReflection t <;>
      simp [hst, hsrt, he, he', eq_comm]
  exact hle hm

/-- Even the one-row auxiliary case admits no nonzero symmetric relation supported in row zero. -/
theorem symmetric_relation_one_row (D : BetaDiagram (n + 1)) (hd : D.Dense)
    (hs : D.Symmetric) (c : Fin (n + 1) × Fin (n + 1) → ℚ)
    (h : cofactorRelationMap D c = 0) (ho : ∀ i j, i ≠ 0 → c (i, j) = 0) : c = 0 := by
  have ha := D.symmetric_relation_antisymmetric hd hs c h
  funext s
  change c s = 0
  by_cases hi : s.1 = 0
  · rcases s with ⟨i,j⟩
    change i = 0 at hi
    subst i
    have hh := ha (0,j)
    by_cases hj : j = Fin.last n
    · subst j
      simp only [siteReflection, Fin.rev_last, Fin.rev_zero] at hh
      linarith
    · have hjr : j.rev ≠ 0 := by
        intro he
        apply hj
        simpa only [Fin.rev_rev, Fin.rev_zero] using congrArg Fin.rev he
      rw [show c (siteReflection (0,j)) = 0 from ho _ _ hjr, add_zero] at hh
      exact hh
  · exact ho _ _ hi

/-- Equal exterior margins lift actual symmetry of the corner child to the parent. -/
theorem symmetric_of_corner_symmetry_of_equal_margins (D : BetaDiagram (n + 2))
    (hd : D.Dense) (hs : (D.deleteSite hd 0 (Fin.last (n + 1))).Symmetric)
    (hm : D.row 0 - D.row (0 : Fin (n + 1)).succ =
      D.col (Fin.last n).castSucc - D.col (Fin.last (n + 1))) : D.Symmetric := by
  obtain ⟨t,hr,hc⟩ := hs
  have h := hr 0
  simp only [deleteSite, Fin.zero_succAbove, Fin.succAbove_last, Fin.rev_zero] at h
  have h0 : D.row 0 = t - D.col (Fin.last (n + 1)) := by omega
  have hfull : ∀ k : Fin (n + 2), D.row k = t - D.col k.rev := by
    intro k
    induction k using Fin.cases with
    | zero => simpa using h0
    | succ k =>
        simpa only [deleteSite, Fin.zero_succAbove, Fin.succAbove_last, Fin.rev_succ] using hr k
  refine ⟨t,hfull,?_⟩
  intro k
  have h := hfull k.rev
  simp only [Fin.rev_rev] at h
  omega

/-- The second private site's complementary child cannot share the corner child's symmetry. -/
theorem second_child_nonsymmetric (D : BetaDiagram (n + 3)) (hd : D.Dense)
    (hs : (D.deleteSite hd 0 (Fin.last (n + 2))).Symmetric) :
    ¬ (D.deleteSite hd (0 : Fin (n + 2)).succ (Fin.last (n + 2))).Symmetric := by
  intro hq
  obtain ⟨r,hr,hcr⟩ := hs
  obtain ⟨q,hq,hcq⟩ := hq
  have hsecond : (0 : Fin (n + 2)).succ ≠ Fin.last (n + 2) := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_succ, Fin.val_zero, Fin.val_last] at hv
    omega
  have hlastR := hr (Fin.last (n + 1))
  have hlastQ := hq (Fin.last (n + 1))
  simp only [deleteSite, Fin.zero_succAbove, Fin.succAbove_last, Fin.rev_last,
    Fin.castSucc_zero, Fin.succAbove_ne_last_last hsecond] at hlastR hlastQ
  have hlast : (Fin.last (n + 1)).succ = Fin.last (n + 2) := by ext; simp
  simp only [hlast] at hlastR hlastQ
  change D.row (Fin.last (n + 2)) = q - D.col 0 at hlastQ
  have he : r = q := by omega
  have htopR := hr 0
  have htopQ := hq 0
  have hzero : (0 : Fin (n + 2)).succ.succAbove 0 = 0 :=
    Fin.succAbove_ne_zero_zero (Fin.succ_ne_zero _)
  simp only [deleteSite, Fin.zero_succAbove, Fin.succAbove_last, Fin.rev_zero, hzero] at htopR htopQ
  have hstrict := D.row_strictAnti
    (show (0 : Fin (n + 3)) < (0 : Fin (n + 2)).succ by simp)
  omega

/-- Half-turn preserves strict density. -/
theorem rotate_dense (D : BetaDiagram n) (hd : D.Dense) : D.rotate.Dense := by
  intro i j
  have h := hd j.rev i.rev
  change -D.row j.rev < -D.col i.rev
  omega

/-- Half-turn preserves and reflects actual beta symmetry. -/
theorem rotate_symmetric_iff (D : BetaDiagram n) : D.rotate.Symmetric ↔ D.Symmetric := by
  constructor <;> rintro ⟨c,hr,hc⟩ <;> refine ⟨-c,?_,?_⟩ <;> intro i
  · have h := hc i.rev
    simp only [rotate, Fin.rev_rev] at h
    omega
  · have h := hr i.rev
    simp only [rotate, Fin.rev_rev] at h
    omega
  · have h := hc i.rev
    simp only [Fin.rev_rev] at h
    simp only [rotate, Fin.rev_rev]
    omega
  · have h := hr i.rev
    simp only [Fin.rev_rev] at h
    simp only [rotate, Fin.rev_rev]
    omega

/-- The actual cofactor family is transported by a half-turn, with no residual sign. -/
theorem rotate_cofactor (D : BetaDiagram (n + 1)) (i j : Fin (n + 1)) :
    D.rotate.cofactor i j = D.cofactor j.rev i.rev := by
  have hm : D.rotate.matrix = D.matrix.transpose.submatrix Fin.revPerm Fin.revPerm := by
    ext a b
    simp only [matrix, rotate, Matrix.of_apply, Matrix.submatrix_apply,
      Matrix.transpose_apply, Fin.revPerm_apply]
    congr 1
    ring_nf
  have ha := congrArg Matrix.adjugate hm
  rw [Matrix.adjugate_submatrix_equiv_self, ← Matrix.adjugate_transpose] at ha
  have he := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) CompleteRing => M j i) ha
  simpa only [Fin.revPerm_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
    Matrix.adjugate_fin_succ_eq_det_submatrix, cofactor] using he

/-- Independence after rotating is independence of the full original indexed family. -/
theorem cofactor_independent_of_rotate (D : BetaDiagram (n + 1))
    (h : LinearIndependent ℚ (fun s : Fin (n + 1) × Fin (n + 1) =>
      D.rotate.cofactor s.1 s.2)) :
    LinearIndependent ℚ (fun s : Fin (n + 1) × Fin (n + 1) => D.cofactor s.1 s.2) := by
  have hi : Function.Injective (@siteReflection (n + 1)) :=
    Function.Involutive.injective siteReflection_involutive
  convert h.comp siteReflection hi using 1
  funext s
  simp [siteReflection, D.rotate_cofactor]

/-- The induction step in the orientation with the smaller top margin. -/
theorem cofactor_independent_oriented_step (D : BetaDiagram (n + 3)) (hd : D.Dense)
    (hs : ¬ D.Symmetric)
    (ih : ∀ E : BetaDiagram (n + 2), E.Dense → ¬ E.Symmetric →
      LinearIndependent ℚ (fun s : Fin (n + 2) × Fin (n + 2) => E.cofactor s.1 s.2))
    (hor : D.row 0 - D.row (0 : Fin (n + 2)).succ <
      D.col (Fin.last (n + 1)).castSucc - D.col (Fin.last (n + 2))) :
    LinearIndependent ℚ (fun s : Fin (n + 3) × Fin (n + 3) => D.cofactor s.1 s.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc' : cofactorRelationMap D c = 0 := hc
  let R := D.deleteSite hd 0 (Fin.last (n + 2))
  have hdR : R.Dense := D.deleteSite_dense hd _ _
  by_cases hsR : R.Symmetric
  · let Q := D.deleteSite hd (0 : Fin (n + 2)).succ (Fin.last (n + 2))
    have hdQ : Q.Dense := D.deleteSite_dense hd _ _
    have hsQ : ¬ Q.Symmetric := D.second_child_nonsymmetric hd hsR
    have hkill := D.cofactor_relation_kill_off_private_axes hd
      (0 : Fin (n + 2)).succ (Fin.last (n + 2))
      (D.second_label_private hor) (ih Q hdQ hsQ) c hc'
    have hr := D.cofactor_relation_private_child hd 0 (Fin.last (n + 2)) D.corner_private c hc'
    let cr : Fin (n + 2) × Fin (n + 2) → ℚ := fun s => c (s.1.succ,s.2.castSucc)
    have hcr : cofactorRelationMap R cr = 0 := by
      simpa only [R,cr,Fin.zero_succAbove,Fin.succAbove_last] using hr
    have hrow : ∀ i j, i ≠ 0 → cr (i,j) = 0 := by
      intro i j hi
      apply hkill _ _
      · intro he
        exact hi (Fin.succ_injective _ he)
      · simp
    have hzero := R.symmetric_relation_one_row hdR hsR cr hcr hrow
    have hlast : ∀ i j, j ≠ Fin.last (n + 2) → c (i,j) = 0 := by
      intro i j hj
      by_cases hi : i = (0 : Fin (n + 2)).succ
      · subst i
        obtain ⟨b,hb⟩ := Fin.exists_succAbove_eq hj
        have hh := congrFun hzero (0,b)
        have hb' : b.castSucc = j := by simpa only [Fin.succAbove_last] using hb
        simpa only [cr,hb',Pi.zero_apply] using hh
      · exact hkill i j hi hj
    have hcz := D.cofactor_relation_last_column hd c hc' hlast
    intro s
    exact congrFun hcz s
  · have hkill := D.cofactor_relation_kill_off_private_axes hd 0 (Fin.last (n + 2))
      D.corner_private (ih R hdR hsR) c hc'
    have hz := D.cofactor_relation_boundaries hd hs c hc' hkill
    intro s
    exact congrFun hz s

/-- The actual two-by-two base, proved with the one-row child's empty cofactor. -/
theorem nonsymmetric_cofactor_independent_two (D : BetaDiagram 2) (hd : D.Dense)
    (hs : ¬ D.Symmetric) :
    LinearIndependent ℚ (fun s : Fin 2 × Fin 2 => D.cofactor s.1 s.2) := by
  classical
  let R := D.deleteSite hd 0 (Fin.last 1)
  have hi : LinearIndependent ℚ (fun s : Fin 1 × Fin 1 => R.cofactor s.1 s.2) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc s
    have heFin : ∀ i : Fin 1, i = 0 := by
      intro i
      apply Fin.ext
      have := i.isLt
      simp only [Fin.val_zero]
      omega
    have he : ∀ t : Fin 1 × Fin 1, t = (0,0) :=
      fun t => Prod.ext (heFin t.1) (heFin t.2)
    have hh : c (0,0) • (1 : CompleteRing) = 0 := by
      simpa only [Fintype.sum_prod_type,Fin.sum_univ_one,cofactor_order_one] using hc
    have hz : c (0,0) = 0 := (smul_eq_zero.mp hh).resolve_right one_ne_zero
    simpa only [he s] using hz
  rw [Fintype.linearIndependent_iff]
  intro c hc s
  have hkill := D.cofactor_relation_kill_off_private_axes hd 0 (Fin.last 1)
    D.corner_private hi c hc
  have hz := D.cofactor_relation_boundaries hd hs c hc hkill
  exact congrFun hz s

/-- Every dense nonsymmetric diagram has its full all-order rational cofactor independence. -/
theorem nonsymmetric_cofactor_independent (D : BetaDiagram (n + 1)) (hd : D.Dense)
    (hs : ¬ D.Symmetric) :
    LinearIndependent ℚ (fun s : Fin (n + 1) × Fin (n + 1) => D.cofactor s.1 s.2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · exact False.elim (hs ⟨D.row 0 + D.col 0,
        by intro i; fin_cases i; simp,
        by intro i; fin_cases i; simp⟩)
    · rcases n with _ | n
      · exact D.nonsymmetric_cofactor_independent_two hd hs
      · have hchild : ∀ E : BetaDiagram (n + 2), E.Dense → ¬ E.Symmetric →
            LinearIndependent ℚ (fun s : Fin (n + 2) × Fin (n + 2) => E.cofactor s.1 s.2) := by
          intro E he hse
          exact ih (n + 1) (by omega) E he hse
        let R := D.deleteSite hd 0 (Fin.last (n + 2))
        have hdR : R.Dense := D.deleteSite_dense hd _ _
        by_cases hsR : R.Symmetric
        · have hne : D.topMargin ≠ D.bottomMargin := by
            intro he
            exact hs (D.symmetric_of_corner_symmetry_of_equal_margins hd hsR he)
          rcases lt_or_gt_of_ne hne with hor | hor
          · exact D.cofactor_independent_oriented_step hd hs hchild hor
          · apply D.cofactor_independent_of_rotate
            apply D.rotate.cofactor_independent_oriented_step (D.rotate_dense hd)
              (fun h => hs ((D.rotate_symmetric_iff).mp h)) hchild
            change D.rotate.topMargin < D.rotate.bottomMargin
            simpa only [D.rotate_topMargin,D.rotate_bottomMargin] using hor
        · rw [Fintype.linearIndependent_iff]
          intro c hc s
          have hkill := D.cofactor_relation_kill_off_private_axes hd 0 (Fin.last (n + 2))
            D.corner_private (hchild R hdR hsR) c hc
          have hz := D.cofactor_relation_boundaries hd hs c hc hkill
          exact congrFun hz s

/-- Exact rational rank of the actual full cofactor map. -/
theorem nonsymmetric_cofactor_rank (D : BetaDiagram (n + 1)) (hd : D.Dense)
    (hs : ¬ D.Symmetric) :
    Module.finrank ℚ (LinearMap.range (cofactorRelationMap D)) = (n + 1) ^ 2 := by
  rw [cofactorRelationMap_range,
    finrank_span_eq_card (D.nonsymmetric_cofactor_independent hd hs)]
  simp only [Fintype.card_prod,Fintype.card_fin,pow_two]

/-- No rational relation survives for the actual signed cofactor family. -/
theorem nonsymmetric_cofactor_kernel (D : BetaDiagram (n + 1)) (hd : D.Dense)
    (hs : ¬ D.Symmetric) : LinearMap.ker (cofactorRelationMap D) = ⊥ := by
  apply le_antisymm
  · intro c hc
    have hz := Fintype.linearIndependent_iff.mp (D.nonsymmetric_cofactor_independent hd hs) c hc
    rw [funext hz]
    exact Submodule.zero_mem _
  · exact bot_le

/-- The nonsymmetric clause of `thm:cofactor-relations`, under precisely standing geometry. -/
theorem nonsymmetric_cofactor_relations (D : BetaDiagram (n + 1)) (_hn : 1 ≤ n)
    (_hN : D.Normalized) (hd : D.Dense) (hs : ¬ D.Symmetric) :
    LinearIndependent ℚ (fun s : Fin (n + 1) × Fin (n + 1) => D.cofactor s.1 s.2) ∧
    LinearMap.ker (cofactorRelationMap D) = ⊥ ∧
    Module.finrank ℚ (LinearMap.range (cofactorRelationMap D)) = (n + 1) ^ 2 :=
  ⟨D.nonsymmetric_cofactor_independent hd hs,D.nonsymmetric_cofactor_kernel hd hs,
    D.nonsymmetric_cofactor_rank hd hs⟩

end BetaDiagram
end SkewCofactorIndependence
