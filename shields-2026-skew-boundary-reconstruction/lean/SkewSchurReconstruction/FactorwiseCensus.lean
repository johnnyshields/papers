/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.FactorwiseWitness
import SkewSchurReconstruction.BoundaryReconstruction
import SkewSchurReconstruction.FactorwiseCensusModel
import Mathlib.Data.List.OfFn

/-!
# The first factorwise ribbon equality

Formalizes the finite census in "Composition and reversal", `rem:factorwise`,
in "The seam chain and the composition problem" (`sec:application`).
The canonical ribbon has positive prescribed row lengths and adjacent overlaps one.
Its signature is an explicitly evaluated actual Jacobi--Trudi determinant, not a
replacement definition of the Schur function.  In sizes at most eight the finite
collision theorem and reversal prove that the signature is faithful.  The actual
five-row diagrams supply occurrence at size nine.  Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators Matrix

private theorem ribbon_outer_inner {n : ℕ} (w : Fin n → ℕ) (i : Fin n) :
    ribbonOuter w i = ribbonInner w i + (w i - 1) + 1 := by
  have h : ∀ k : Fin n,
      (if i ≤ k then w k - 1 else 0) =
        (if k = i then w i - 1 else 0) + (if i < k then w k - 1 else 0) := by
    intro k
    split_ifs <;> simp_all <;> omega
  simp only [ribbonOuter, ribbonInner, h, Finset.sum_add_distrib]
  simp
  omega

/-- The actual partition boundaries associated to a positive composition. -/
def ribbonDiagram (a : List ℕ) (ha : ∀ k ∈ a, 0 < k) : Diagram a.length where
  outer := ribbonOuter a.get
  inner := ribbonInner a.get
  outer_antitone := by
    intro i j hij
    simp only [ribbonOuter]
    apply Nat.add_le_add_left
    apply Finset.sum_le_sum
    intro k _
    split_ifs <;> omega
  inner_antitone := by
    intro i j hij
    simp only [ribbonInner]
    apply Finset.sum_le_sum
    intro k _
    split_ifs <;> omega
  row_nonempty := by
    intro i
    have hp := ha (a.get i) (List.get_mem a i)
    have he := ribbon_outer_inner a.get i
    omega

/-- The canonical ribbon realizes every prescribed positive row length. -/
theorem ribbonDiagram_rowLength (a : List ℕ) (ha : ∀ k ∈ a, 0 < k)
    (i : Fin a.length) : (ribbonDiagram a ha).rowLength i = a.get i := by
  have hp := ha (a.get i) (List.get_mem a i)
  have he := ribbon_outer_inner a.get i
  simp only [Diagram.rowLength, ribbonDiagram]
  omega

theorem ribbonDiagram_rowLengthList (a : List ℕ) (ha : ∀ k ∈ a, 0 < k) :
    (ribbonDiagram a ha).rowLengthList = a := by
  unfold Diagram.rowLengthList
  have hrow : (ribbonDiagram a ha).rowLength = a.get :=
    funext (ribbonDiagram_rowLength a ha)
  rw [hrow]
  exact List.ofFn_get a

/-- Successive rows share exactly one cell. -/
theorem ribbonDiagram_overlap (a : List ℕ) (ha : ∀ k ∈ a, 0 < k)
    (i : Fin a.length) (hi : i.val + 1 < a.length) :
    (ribbonDiagram a ha).overlap i hi = 1 := by
  have he : ribbonInner a.get i =
      ∑ k : Fin a.length, if (⟨i.val + 1, hi⟩ : Fin a.length) ≤ k
        then a.get k - 1 else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    have hc : i < k ↔ (⟨i.val + 1, hi⟩ : Fin a.length) ≤ k := by
      change i.val < k.val ↔ i.val + 1 ≤ k.val
      omega
    simp only [hc]
  simp only [Diagram.overlap, ribbonDiagram, ribbonOuter]
  rw [he]
  omega

/-- The canonical ribbon of a nonempty positive composition is connected. -/
theorem ribbonDiagram_connected (a : List ℕ) (ha : ∀ k ∈ a, 0 < k) (hne : a ≠ []) :
    (ribbonDiagram a ha).Connected := by
  refine ⟨List.length_pos_iff.mpr hne, ?_⟩
  intro i hi
  have h := ribbonDiagram_overlap a ha i hi
  simp only [Diagram.overlap] at h
  omega

private theorem ribbon_reverse_boundaries {n : ℕ} (w : Fin n → ℕ) (i : Fin n) :
    ribbonOuter (fun k => w k.rev) i + ribbonInner w i.rev =
        1 + ∑ k : Fin n, (w k - 1) ∧
      ribbonInner (fun k => w k.rev) i + ribbonOuter w i.rev =
        1 + ∑ k : Fin n, (w k - 1) := by
  have hge : (∑ k : Fin n, if i ≤ k then w k.rev - 1 else 0) =
      ∑ k : Fin n, if k ≤ i.rev then w k - 1 else 0 := by
    rw [← Equiv.sum_comp Fin.revPerm]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Fin.revPerm_apply, Fin.rev_rev]
    have hc : i ≤ k.rev ↔ k ≤ i.rev := by
      simp only [Fin.le_def, Fin.val_rev]
      omega
    simp only [hc]
  have hgt : (∑ k : Fin n, if i < k then w k.rev - 1 else 0) =
      ∑ k : Fin n, if k < i.rev then w k - 1 else 0 := by
    rw [← Equiv.sum_comp Fin.revPerm]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Fin.revPerm_apply, Fin.rev_rev]
    have hc : i < k.rev ↔ k < i.rev := by
      simp only [Fin.lt_def, Fin.val_rev]
      omega
    simp only [hc]
  constructor
  · simp only [ribbonOuter, ribbonInner, hge]
    rw [Nat.add_assoc, ← Finset.sum_add_distrib]
    apply congrArg (fun s : ℕ => 1 + s)
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> omega
  · simp only [ribbonOuter, ribbonInner, hgt]
    rw [← Nat.add_assoc, Nat.add_comm _ 1, Nat.add_assoc, ← Finset.sum_add_distrib]
    apply congrArg (fun s : ℕ => 1 + s)
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> omega

private theorem ribbon_get_reverse (a : List ℕ) (i : Fin a.reverse.length) :
    a.reverse.get i = a.get ⟨a.length - 1 - i.val, by
      have hi := i.isLt
      simp only [List.length_reverse] at hi
      omega⟩ := by
  simp only [List.get_eq_getElem, List.getElem_reverse]

/-- Reversing all rows preserves the actual ribbon Schur function. -/
theorem ribbonDiagram_schur_reverse (a : List ℕ) (ha : ∀ k ∈ a, 0 < k) :
    (ribbonDiagram a.reverse (by simpa using ha)).schurFunction =
      (ribbonDiagram a ha).schurFunction := by
  rw [Diagram.schurFunction_eq_jacobiTrudiDet,
    Diagram.schurFunction_eq_jacobiTrudiDet]
  have hlen : a.reverse.length = a.length := List.length_reverse
  have hm : (ribbonDiagram a.reverse (by simpa using ha)).jacobiTrudiMatrix =
      ((ribbonDiagram a ha).jacobiTrudiMatrix.transpose.submatrix
        (fun i => (Fin.cast hlen i).rev) (fun i => (Fin.cast hlen i).rev)) := by
    apply Matrix.ext
    intro i j
    have hi := (ribbon_reverse_boundaries a.get (Fin.cast hlen i)).1
    have hj := (ribbon_reverse_boundaries a.get (Fin.cast hlen j)).2
    have hget (k : Fin a.length) :
        a.reverse.get ((Fin.castOrderIso hlen).symm k) = a.get k.rev := by
      rw [ribbon_get_reverse]
      apply congrArg a.get
      apply Fin.ext
      change a.length - 1 - k.val = a.length - (k.val + 1)
      omega
    have hout : ribbonOuter a.reverse.get i =
        ribbonOuter (fun k => a.get k.rev) (Fin.cast hlen i) := by
      unfold ribbonOuter
      rw [← Equiv.sum_comp (Fin.castOrderIso hlen).toEquiv.symm]
      apply congrArg (fun s : ℕ => 1 + s)
      apply Finset.sum_congr rfl
      intro k _
      have hc : i ≤ (Fin.castOrderIso hlen).symm k ↔ Fin.cast hlen i ≤ k := by
        change i.val ≤ k.val ↔ i.val ≤ k.val
        rfl
      apply ite_congr (propext hc)
      · intro _
        exact congrArg (fun s : ℕ => s - 1) (hget k)
      · intro _
        rfl
    have hinn : ribbonInner a.reverse.get j =
        ribbonInner (fun k => a.get k.rev) (Fin.cast hlen j) := by
      unfold ribbonInner
      rw [← Equiv.sum_comp (Fin.castOrderIso hlen).toEquiv.symm]
      apply Finset.sum_congr rfl
      intro k _
      have hc : j < (Fin.castOrderIso hlen).symm k ↔ Fin.cast hlen j < k := by
        change j.val < k.val ↔ j.val < k.val
        rfl
      apply ite_congr (propext hc)
      · intro _
        exact congrArg (fun s : ℕ => s - 1) (hget k)
      · intro _
        rfl
    change complete ((ribbonOuter a.reverse.get i : ℤ) -
        ribbonInner a.reverse.get j - i.val + j.val) =
      complete ((ribbonOuter a.get (Fin.cast hlen j).rev : ℤ) -
        ribbonInner a.get (Fin.cast hlen i).rev -
        (Fin.cast hlen j).rev.val + (Fin.cast hlen i).rev.val)
    rw [hout, hinn]
    apply congrArg complete
    have hii := i.isLt
    have hjj := j.isLt
    simp only [List.length_reverse] at hii hjj
    simp only [Fin.val_rev, Fin.val_cast]
    omega
  rw [hm]
  let e : Fin a.reverse.length ≃ Fin a.length :=
    (Fin.castOrderIso hlen).toEquiv.trans Fin.revPerm
  change (((ribbonDiagram a ha).jacobiTrudiMatrix.transpose).submatrix e e).det = _
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_transpose]

/-- The computational determinant is the ordinary determinant, for every integer matrix. -/
theorem censusDet_eq_det (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) :
    censusDet n M = M.det := by
  induction n with
  | zero => simp [censusDet]
  | succ n ih =>
    rw [censusDet, Matrix.det_succ_row_zero]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with h
    · simp [h]
    · rw [ih]

private theorem census_specialize_complete (t : Bool) (k : ℤ) :
    specialize (fun p : ℕ+ => (censusValues t).getD (p.val - 1) 0) (complete k) =
      censusComplete t k := by
  by_cases hzero : k = 0
  · subst k
    simp [censusComplete]
  · by_cases hpos : 0 < k
    · simp only [censusComplete, ite_eq_right hzero, ite_eq_left hpos,
        complete_of_pos hpos]
      let p : ℕ+ := ⟨k.toNat, by omega⟩
      change specialize (fun q : ℕ+ => (censusValues t).getD (q.val - 1) 0)
        (MvPolynomial.X p) = (censusValues t).getD (p.val - 1) 0
      simpa only [complete_nat] using
        specialize_complete (fun q : ℕ+ => (censusValues t).getD (q.val - 1) 0) p
    · have hneg : k < 0 := by omega
      rw [complete_of_neg hneg, map_zero]
      simp [censusComplete, hzero, hpos]

/-- The signature components come from ring homomorphisms applied to the actual Schur function. -/
theorem ribbonCensusSignature_eq_specialization (a : List ℕ) (ha : ∀ k ∈ a, 0 < k) :
    ribbonCensusSignature a =
      (specialize (fun p : ℕ+ => (censusValues false).getD (p.val - 1) 0)
        (ribbonDiagram a ha).schurFunction,
       specialize (fun p : ℕ+ => (censusValues true).getD (p.val - 1) 0)
        (ribbonDiagram a ha).schurFunction) := by
  have h (t : Bool) : censusDet a.length (censusMatrix t a) =
      specialize (fun p : ℕ+ => (censusValues t).getD (p.val - 1) 0)
        (ribbonDiagram a ha).schurFunction := by
    rw [censusDet_eq_det, Diagram.schurFunction_eq_jacobiTrudiDet, RingHom.map_det]
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    exact (census_specialize_complete t _).symm
  exact Prod.ext (h false) (h true)

/-- The enumeration covers arbitrary positive compositions, not selected examples. -/
theorem mem_censusWords (fuel : ℕ) (a : List ℕ) (ha : ∀ k ∈ a, 0 < k)
    (hlen : a.length ≤ fuel) : a ∈ censusWords fuel a.sum := by
  induction fuel generalizing a with
  | zero =>
    have he : a = [] := List.length_eq_zero_iff.mp (by omega)
    subst a
    simp [censusWords]
  | succ fuel ih =>
    cases a with
    | nil => simp [censusWords]
    | cons p a =>
      have hp : 0 < p := ha p (by simp)
      have htail : ∀ k ∈ a, 0 < k := fun k hk => ha k (by simp [hk])
      have hs : p + a.sum ≠ 0 := by omega
      simp only [List.sum_cons]
      rw [censusWords, ite_eq_right hs]
      simp only [List.mem_flatMap]
      refine ⟨p - 1, List.mem_range.mpr (by omega), ?_⟩
      have he : p - 1 + 1 = p := by omega
      rw [he]
      apply List.mem_map.mpr
      refine ⟨a, ?_, rfl⟩
      have hsub : p + a.sum - p = a.sum := by omega
      rw [hsub]
      apply ih a htail
      simp only [List.length_cons] at hlen
      omega

private theorem positive_length_le_sum (a : List ℕ) (ha : ∀ k ∈ a, 0 < k) :
    a.length ≤ a.sum := by
  induction a with
  | nil => simp
  | cons p a ih =>
    have hp := ha p (by simp)
    have ht := ih (fun k hk => ha k (by simp [hk]))
    simp only [List.length_cons, List.sum_cons]
    omega

/-- Actual Schur equality below nine permits only identity or whole reversal. -/
theorem ribbon_census_below_nine (a b : List ℕ)
    (ha : ∀ k ∈ a, 0 < k) (hb : ∀ k ∈ b, 0 < k)
    (hsize : b.sum = a.sum) (hbound : a.sum ≤ 8)
    (heq : (ribbonDiagram a ha).schurFunction = (ribbonDiagram b hb).schurFunction) :
    b = a ∨ b = a.reverse := by
  have hsig : ribbonCensusSignature a = ribbonCensusSignature b := by
    rw [ribbonCensusSignature_eq_specialization a ha,
      ribbonCensusSignature_eq_specialization b hb, heq]
  have hma := mem_censusWords a.sum a ha (positive_length_le_sum a ha)
  have hmb := mem_censusWords a.sum b hb (by
    rw [← hsize]
    exact positive_length_le_sum b hb)
  rw [← hsize] at hmb
  have hmb' : b ∈ censusWords a.sum a.sum := by simpa only [hsize] using hmb
  exact censusRecords_collisions a.sum hbound
    (a, ribbonCensusSignature a) (List.mem_map.mpr ⟨a, hma, rfl⟩)
    (b, ribbonCensusSignature b) (List.mem_map.mpr ⟨b, hmb', rfl⟩) hsig

/-- On the complete finite census range, the computational signature is equivalent to actual
polynomial equality.  Faithfulness is proved, not assumed as a signature contract. -/
theorem ribbonCensusSignature_eq_iff (a b : List ℕ)
    (ha : ∀ k ∈ a, 0 < k) (hb : ∀ k ∈ b, 0 < k)
    (hsize : b.sum = a.sum) (hbound : a.sum ≤ 8) :
    ribbonCensusSignature a = ribbonCensusSignature b ↔
      (ribbonDiagram a ha).schurFunction = (ribbonDiagram b hb).schurFunction := by
  constructor
  · intro hsig
    have hma := mem_censusWords a.sum a ha (positive_length_le_sum a ha)
    have hmb : b ∈ censusWords a.sum a.sum := by
      simpa only [hsize] using mem_censusWords b.sum b hb (positive_length_le_sum b hb)
    have hc := censusRecords_collisions a.sum hbound
      (a, ribbonCensusSignature a) (List.mem_map.mpr ⟨a, hma, rfl⟩)
      (b, ribbonCensusSignature b) (List.mem_map.mpr ⟨b, hmb, rfl⟩) hsig
    rcases hc with rfl | rfl
    · rfl
    · exact (ribbonDiagram_schur_reverse a ha).symm
  · intro heq
    rw [ribbonCensusSignature_eq_specialization a ha,
      ribbonCensusSignature_eq_specialization b hb, heq]

private theorem ribbonDiagram_degree (a : List ℕ) (ha : ∀ k ∈ a, 0 < k) :
    (ribbonDiagram a ha).cofactorDegree 0 = (a.sum : ℤ) := by
  by_cases hnil : a = []
  · subst a
    change (MvPolynomial.weightedTotalDegree' completeDegreeWeight
      (ribbonDiagram [] ha).schurFunction).unbotD 0 = 0
    rw [Diagram.schurFunction_empty]
    simp [MvPolynomial.weightedTotalDegree']
  · rw [Diagram.cofactorDegree_zero _ (ribbonDiagram_connected a ha hnil)]
    simp_rw [ribbonDiagram_rowLength]
    have hsum : (∑ i : Fin a.length, a.get i) = a.sum := by
      rw [← List.sum_ofFn, List.ofFn_get]
    exact_mod_cast hsum

/-- Actual Schur equality supplies the total size, including the empty composition. -/
theorem ribbon_sum_eq_of_schur_eq (a b : List ℕ)
    (ha : ∀ k ∈ a, 0 < k) (hb : ∀ k ∈ b, 0 < k)
    (heq : (ribbonDiagram a ha).schurFunction = (ribbonDiagram b hb).schurFunction) :
    b.sum = a.sum := by
  have hdegree := congrArg (fun p : CompleteRing =>
    (MvPolynomial.weightedTotalDegree' completeDegreeWeight p).unbotD 0) heq
  change (ribbonDiagram a ha).cofactorDegree 0 =
    (ribbonDiagram b hb).cofactorDegree 0 at hdegree
  rw [ribbonDiagram_degree a ha, ribbonDiagram_degree b hb] at hdegree
  exact_mod_cast hdegree.symm

/-- The final finite assertion of `rem:factorwise`, quantified over all positive compositions. -/
theorem factorwise_census_minimal (a b : List ℕ)
    (ha : ∀ k ∈ a, 0 < k) (hb : ∀ k ∈ b, 0 < k)
    (hbound : a.sum ≤ 9)
    (heq : (ribbonDiagram a ha).schurFunction = (ribbonDiagram b hb).schurFunction)
    (hne : b ≠ a) (hrev : b ≠ a.reverse) : a.sum = 9 := by
  have hsize := ribbon_sum_eq_of_schur_eq a b ha hb heq
  by_contra h
  have hsmall : a.sum ≤ 8 := by omega
  rcases ribbon_census_below_nine a b ha hb hsize hsmall heq with h | h
  · exact hne h
  · exact hrev h

/-- Occurrence at nine is supplied by actual connected ribbon diagrams. -/
theorem factorwise_census_occurs_at_nine :
    ∃ X Y : Diagram 5, X.Connected ∧ Y.Connected ∧
      X.rowLengthList.sum = 9 ∧ Y.rowLengthList.sum = 9 ∧
      X.schurFunction = Y.schurFunction ∧
      Y.rowLengthList ≠ X.rowLengthList ∧
      Y.rowLengthList ≠ X.rowLengthList.reverse := by
  refine ⟨factorwiseLeft, factorwiseRight, factorwiseLeft_connected,
    factorwiseRight_connected, ?_, ?_, factorwise_schur_eq,
    factorwise_not_global_reversal.1, factorwise_not_global_reversal.2⟩
  · rw [factorwiseLeft_rowLengths]
    decide
  · rw [factorwiseRight_rowLengths]
    decide

private theorem diagram_eq_of_boundaries {n : ℕ} (X Y : Diagram n)
    (ho : X.outer = Y.outer) (hi : X.inner = Y.inner) : X = Y := by
  cases X
  cases Y
  dsimp at ho hi
  cases ho
  cases hi
  rfl

private theorem ribbon_factorwiseLeft_schur :
    (ribbonDiagram [1, 2, 1, 3, 2] (by decide)).schurFunction =
      factorwiseLeft.schurFunction := by
  have ho : (ribbonDiagram [1, 2, 1, 3, 2] (by decide)).outer =
      factorwiseLeft.outer := by
    funext i
    fin_cases i <;> decide
  have hi : (ribbonDiagram [1, 2, 1, 3, 2] (by decide)).inner =
      factorwiseLeft.inner := by
    funext i
    fin_cases i <;> decide
  exact congrArg Diagram.schurFunction (diagram_eq_of_boundaries _ _ ho hi)

private theorem ribbon_factorwiseRight_schur :
    (ribbonDiagram [1, 3, 2, 1, 2] (by decide)).schurFunction =
      factorwiseRight.schurFunction := by
  have ho : (ribbonDiagram [1, 3, 2, 1, 2] (by decide)).outer =
      factorwiseRight.outer := by
    funext i
    fin_cases i <;> decide
  have hi : (ribbonDiagram [1, 3, 2, 1, 2] (by decide)).inner =
      factorwiseRight.inner := by
    funext i
    fin_cases i <;> decide
  exact congrArg Diagram.schurFunction (diagram_eq_of_boundaries _ _ ho hi)

/-- Four actual ribbons arising from the two displayed witnesses and their whole reversals. -/
def factorwiseFourRibbons : Fin 4 → Diagram 5 :=
  ![factorwiseLeft, factorwiseRight,
    ribbonDiagram [2, 3, 1, 2, 1] (by decide),
    ribbonDiagram [2, 1, 2, 3, 1] (by decide)]

theorem factorwiseFourRibbons_rowLengths (i : Fin 4) :
    (factorwiseFourRibbons i).rowLengthList =
      (![([1, 2, 1, 3, 2] : List ℕ), [1, 3, 2, 1, 2],
        [2, 3, 1, 2, 1], [2, 1, 2, 3, 1]] : Fin 4 → List ℕ) i := by
  fin_cases i <;>
    simp [factorwiseFourRibbons, factorwiseLeft_rowLengths, factorwiseRight_rowLengths,
      ribbonDiagram_rowLengthList]

/-- Independent factor reversal produces at least four distinct actual size-nine ribbons
with the same Schur function.  This asserts occurrence, not a maximum class size. -/
theorem factorwise_census_four_at_nine :
    Function.Injective factorwiseFourRibbons ∧
      (∀ i, (factorwiseFourRibbons i).Connected) ∧
      (∀ i, (factorwiseFourRibbons i).rowLengthList.sum = 9) ∧
      ∀ i, (factorwiseFourRibbons i).schurFunction = factorwiseLeft.schurFunction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hrows := congrArg Diagram.rowLengthList hij
    rw [factorwiseFourRibbons_rowLengths, factorwiseFourRibbons_rowLengths] at hrows
    have hinj : Function.Injective
        (![([1, 2, 1, 3, 2] : List ℕ), [1, 3, 2, 1, 2],
          [2, 3, 1, 2, 1], [2, 1, 2, 3, 1]] : Fin 4 → List ℕ) := by decide
    exact hinj hrows
  · intro i
    fin_cases i
    · exact factorwiseLeft_connected
    · exact factorwiseRight_connected
    · exact ribbonDiagram_connected [2, 3, 1, 2, 1] (by decide) (by decide)
    · exact ribbonDiagram_connected [2, 1, 2, 3, 1] (by decide) (by decide)
  · intro i
    rw [factorwiseFourRibbons_rowLengths]
    fin_cases i <;> decide
  · intro i
    fin_cases i
    · rfl
    · exact factorwise_schur_eq.symm
    · change (ribbonDiagram ([1, 2, 1, 3, 2] : List ℕ).reverse
        (by decide)).schurFunction = factorwiseLeft.schurFunction
      exact (ribbonDiagram_schur_reverse _ (by decide)).trans ribbon_factorwiseLeft_schur
    · change (ribbonDiagram ([1, 3, 2, 1, 2] : List ℕ).reverse
        (by decide)).schurFunction = factorwiseLeft.schurFunction
      exact (ribbonDiagram_schur_reverse _ (by decide)).trans
        (ribbon_factorwiseRight_schur.trans factorwise_schur_eq.symm)

end SkewSchurReconstruction
