/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.RibbonDetermination
import SkewClassInflation.ThreePartCutRelations

/-!
# Determination propagation and the first undetermined interval

The three-part coefficients used in the nonsymmetric ribbon input to
`lem:overlap-power-rigidity` of `shields-2026-skew-class-inflation.tex`
propagate determination inside the actual normalized inventory class.
The first undetermined coordinate forces antisymmetry of the signed cut
function on the preceding interval.  Sorry-free.
-/

namespace SkewClassInflation

/-- The signed difference of the two actual reflected cut indicators. -/
noncomputable def compositionCutSign {N : ℕ} (α : Composition N) (x : ℕ) : ℤ :=
  (if x ∈ properCuts α then 1 else 0) - (if N - x ∈ properCuts α then 1 else 0)

/-- Even-type coordinates have zero signed cut value. -/
theorem compositionCutSign_eq_zero_of_not_one {N : ℕ} (α : Composition N) (x : ℕ)
    (hx : compositionCutType α x ≠ 1) : compositionCutSign α x = 0 := by
  classical
  have hr := even_cut_reflect_iff α x hx
  simp only [compositionCutSign, hr, sub_self]

/-- At single-type coordinates the sign is determined by the unreflected cut. -/
theorem compositionCutSign_of_one {N : ℕ} (α : Composition N) (x : ℕ)
    (hx : compositionCutType α x = 1) :
    compositionCutSign α x = if x ∈ properCuts α then 1 else -1 := by
  classical
  simp only [compositionCutSign, single_cut_reflect_iff_not α x hx]
  split_ifs <;> omega

/-- Determining one of two single-type parts determines the other when the third is even. -/
theorem cutDetermined_of_two_single {N : ℕ} (α : Composition N) (k : ℕ) (a b c : ℕ+)
    (hsum : a.val + b.val + c.val = N)
    (ha : compositionCutType α a.val = 1) (hb : compositionCutType α b.val = 1)
    (hc : compositionCutType α c.val ≠ 1) (hda : cutDetermined α k a.val) :
    cutDetermined α k b.val := by
  intro β hβ
  have hi := two_single_agreement_invariant α β hβ.1.symm a b c hsum ha hb hc
  have hfixed := hda β hβ
  have hlogic (P Q R S : Prop) (h : (P ↔ Q) ↔ (R ↔ S)) (hp : R ↔ P) : S ↔ Q := by
    clear * - P Q R S h hp
    tauto
  exact hlogic _ _ _ _ hi hfixed

/-- Two determined agreeing single-type parts determine the third single-type part. -/
theorem cutDetermined_of_three_single {N : ℕ} (α : Composition N) (k : ℕ) (a b c : ℕ+)
    (hsum : a.val + b.val + c.val = N)
    (ha : compositionCutType α a.val = 1) (hb : compositionCutType α b.val = 1)
    (hc : compositionCutType α c.val = 1)
    (hda : cutDetermined α k a.val) (hdb : cutDetermined α k b.val)
    (hab : a.val ∈ properCuts α ↔ b.val ∈ properCuts α) :
    cutDetermined α k c.val := by
  intro β hβ
  have hi := three_single_agreement_invariant α β hβ.1.symm a b c hsum ha hb hc
  have hfixedA := hda β hβ
  have hfixedB := hdb β hβ
  have hlogic (P Q R U V W : Prop)
      (h : ((P ↔ Q) ∧ (Q ↔ R)) ↔ ((U ↔ V) ∧ (V ↔ W)))
      (hp : U ↔ P) (hq : V ↔ Q) (hpq : P ↔ Q) : W ↔ R := by
    clear * - P Q R U V W h hp hq hpq
    tauto
  exact hlogic _ _ _ _ _ _ hi hfixedA hfixedB hab

/-- A least undetermined coordinate exists in every nonempty actual undetermined set. -/
theorem exists_first_undetermined {N : ℕ} (α : Composition N) (k : ℕ)
    (hne : (undeterminedCuts α k).Nonempty) :
    ∃ m ∈ undeterminedCuts α k, ∀ x < m, cutDetermined α k x := by
  classical
  refine ⟨(undeterminedCuts α k).min' hne, Finset.min'_mem _ _, ?_⟩
  intro x hx
  by_contra hnot
  have ht : compositionCutType α x = 1 := by
    by_contra he
    exact hnot (cutDetermined_of_not_one α k x he)
  have hp : 0 < x ∧ x < N := by
    by_contra he
    have hz := compositionCutType_outside α x (by omega)
    omega
  have hmem : x ∈ undeterminedCuts α k :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr hp, hnot⟩
  have hle := Finset.min'_le _ _ hmem
  omega

/-- Determined parts complementary to an undetermined point are even or opposite singles. -/
theorem undetermined_cut_types {N : ℕ} (α : Composition N) (k m : ℕ)
    (hm : m ∈ undeterminedCuts α k) (x : ℕ) (hx : 0 < x) (hxm : x < m)
    (hdx : cutDetermined α k x) (hdy : cutDetermined α k (m - x)) :
    (compositionCutType α x ≠ 1 ∧ compositionCutType α (m - x) ≠ 1) ∨
      (compositionCutType α x = 1 ∧ compositionCutType α (m - x) = 1 ∧
        ¬ (x ∈ properCuts α ↔ m - x ∈ properCuts α)) := by
  classical
  have hproper := Finset.mem_Ioo.mp (Finset.mem_filter.mp hm).1
  have href := undeterminedCuts_reflect α k m hm
  have hc := undeterminedCuts_type_one α k (N - m) href
  have hnot := (Finset.mem_filter.mp href).2
  let a : ℕ+ := ⟨x, hx⟩
  let b : ℕ+ := ⟨m - x, by omega⟩
  let c : ℕ+ := ⟨N - m, by omega⟩
  have hs : a.val + b.val + c.val = N := by dsimp [a, b, c]; omega
  have hda : cutDetermined α k a.val := hdx
  have hdb : cutDetermined α k b.val := hdy
  by_cases ha : compositionCutType α x = 1 <;>
    by_cases hb : compositionCutType α (m - x) = 1
  · refine Or.inr ⟨ha, hb, ?_⟩
    intro hagree
    exact hnot (cutDetermined_of_three_single α k a b c hs ha hb hc hda hdb hagree)
  · exact False.elim (hnot (cutDetermined_of_two_single α k a c b
      (by omega) ha hc hb hda))
  · exact False.elim (hnot (cutDetermined_of_two_single α k b c a
      (by omega) hb hc ha hdb))
  · exact Or.inl ⟨ha, hb⟩

/-- Determined complementary points have opposite signed values around an undetermined point. -/
theorem undetermined_cutSign_antisymm {N : ℕ} (α : Composition N) (k m : ℕ)
    (hm : m ∈ undeterminedCuts α k) (x : ℕ) (hx : 0 < x) (hxm : x < m)
    (hdx : cutDetermined α k x) (hdy : cutDetermined α k (m - x)) :
    compositionCutSign α (m - x) = -compositionCutSign α x := by
  classical
  rcases undetermined_cut_types α k m hm x hx hxm hdx hdy with ⟨ha, hb⟩ | ⟨ha, hb, hab⟩
  · rw [compositionCutSign_eq_zero_of_not_one α x ha,
      compositionCutSign_eq_zero_of_not_one α (m - x) hb, neg_zero]
  · rw [compositionCutSign_of_one α x ha, compositionCutSign_of_one α (m - x) hb]
    by_cases hA : x ∈ properCuts α <;> by_cases hB : m - x ∈ properCuts α <;>
      simp [hA, hB] at hab ⊢

/-- The actual signed cut function is antisymmetric before its first undetermined coordinate. -/
theorem first_undetermined_cutSign_antisymm {N : ℕ} (α : Composition N) (k m : ℕ)
    (hm : m ∈ undeterminedCuts α k) (hmin : ∀ x < m, cutDetermined α k x)
    (x : ℕ) (hx : 0 < x) (hxm : x < m) :
    compositionCutSign α (m - x) = -compositionCutSign α x :=
  undetermined_cutSign_antisymm α k m hm x hx hxm
    (hmin x hxm) (hmin (m - x) (by omega))

/-- The signed cut function is antisymmetric across the actual total weight. -/
theorem compositionCutSign_reflect {N : ℕ} (α : Composition N) (x : ℕ) (hx : x ≤ N) :
    compositionCutSign α (N - x) = -compositionCutSign α x := by
  classical
  simp only [compositionCutSign, Nat.sub_sub_self hx]
  ring

/-- Determined points separated by an undetermined coordinate have equal signed values. -/
theorem undetermined_cutSign_shift {N : ℕ} (α : Composition N) (k m : ℕ)
    (hm : m ∈ undeterminedCuts α k) (x : ℕ) (hx : 0 < x) (hxm : x + m < N)
    (hdx : cutDetermined α k x) (hdy : cutDetermined α k (x + m)) :
    compositionCutSign α (x + m) = compositionCutSign α x := by
  have href := undeterminedCuts_reflect α k m hm
  have hcomp : N - m - x = N - (x + m) := by omega
  have hdet : cutDetermined α k (N - (x + m)) := by
    by_cases ht : compositionCutType α (x + m) = 1
    · exact (cutDetermined_reflect α k (x + m) ht).mp hdy
    · have he : compositionCutType α (N - (x + m)) = compositionCutType α (x + m) := by
        unfold compositionCutType
        rw [Nat.sub_sub_self (by omega : x + m ≤ N)]
        exact Nat.add_comm _ _
      exact cutDetermined_of_not_one α k (N - (x + m)) (fun h => ht (he.symm.trans h))
  have ha := undetermined_cutSign_antisymm α k (N - m) href x hx (by omega) hdx
    (by simpa only [hcomp] using hdet)
  rw [hcomp, compositionCutSign_reflect α (x + m) (by omega)] at ha
  omega

end SkewClassInflation
