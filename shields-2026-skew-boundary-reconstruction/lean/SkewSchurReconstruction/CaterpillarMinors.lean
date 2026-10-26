/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.MongeMinors

/-!
# Caterpillar maximal minors

Formalizes `prop:caterpillar` in “The cancellation chain and the composition
problem” (`subsec:seam-interpretation`).  Double omissions use their increasing
row-to-column map, and actual determinant initial forms are produced by
`monge_minor_initialForm`.  The strict separated-pair comparison is a sum of
adjacent-row Strict-Monge inequalities.  Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

/-- The increasing column index after two omissions `a < b`. -/
def doubleOmissionIndex (a b t : ℕ) : ℕ :=
  t + (if a ≤ t then 1 else 0) + (if b - 1 ≤ t then 1 else 0)

/-- The actual increasing map into the two-column-larger grid. -/
def doubleOmissionColumn {m : ℕ} (a b : Fin (m + 2)) (t : Fin m) : Fin (m + 2) :=
  ⟨doubleOmissionIndex a.val b.val t.val, by
    have ht := t.isLt
    unfold doubleOmissionIndex
    split_ifs <;> omega⟩

theorem doubleOmissionColumn_strictMono {m : ℕ} (a b : Fin (m + 2)) :
    StrictMono (doubleOmissionColumn a b) := by
  intro s t hst
  change doubleOmissionIndex a.val b.val s.val < doubleOmissionIndex a.val b.val t.val
  have hs : s.val < t.val := hst
  unfold doubleOmissionIndex
  split_ifs <;> omega

theorem doubleOmissionColumn_ge {m : ℕ} (a b : Fin (m + 2)) (t : Fin m) :
    (⟨t.val, by have := t.isLt; omega⟩ : Fin (m + 2)) ≤ doubleOmissionColumn a b t := by
  change t.val ≤ doubleOmissionIndex a.val b.val t.val
  unfold doubleOmissionIndex
  split_ifs <;> omega

theorem doubleOmissionColumn_ne_left {m : ℕ} {a b : Fin (m + 2)} (hab : a < b)
    (t : Fin m) : doubleOmissionColumn a b t ≠ a := by
  intro he
  have hv := congrArg Fin.val he
  change doubleOmissionIndex a.val b.val t.val = a.val at hv
  have ha : a.val < b.val := hab
  unfold doubleOmissionIndex at hv
  split_ifs at hv <;> omega

theorem doubleOmissionColumn_ne_right {m : ℕ} {a b : Fin (m + 2)} (hab : a < b)
    (t : Fin m) : doubleOmissionColumn a b t ≠ b := by
  intro he
  have hv := congrArg Fin.val he
  change doubleOmissionIndex a.val b.val t.val = b.val at hv
  have ha : a.val < b.val := hab
  unfold doubleOmissionIndex at hv
  split_ifs at hv <;> omega

/-- The column map retains exactly the complement of the two omitted columns. -/
theorem doubleOmissionColumn_image {m : ℕ} {a b : Fin (m + 2)} (hab : a < b) :
    Finset.univ.image (doubleOmissionColumn a b) = (Finset.univ.erase a).erase b := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨doubleOmissionColumn_ne_right hab t, doubleOmissionColumn_ne_left hab t⟩
  · rw [Finset.card_image_of_injective _ (doubleOmissionColumn_strictMono a b).injective,
      Finset.card_erase_of_mem (by simp [ne_of_gt hab]),
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin,
      Finset.card_univ, Fintype.card_fin]
    omega

/-- The rectangular staircase whose maximal minors omit two columns. -/
noncomputable def caterpillarMatrix {m : ℕ} (A : Fin m → ℤ) (d : Fin (m + 2) → ℤ) :
    Matrix (Fin m) (Fin (m + 2)) CompleteRing :=
  Matrix.of fun t j => complete (d j - A t)

/-- The maximal determinant after retaining the sorted double-omission columns. -/
noncomputable def caterpillarMinor {m : ℕ} (A : Fin m → ℤ) (d : Fin (m + 2) → ℤ)
    (a b : Fin (m + 2)) : CompleteRing :=
  ((caterpillarMatrix A d).submatrix id (doubleOmissionColumn a b)).det

/-- Its increasing determinant monomial, without any sign or valuation dependence. -/
noncomputable def caterpillarMonomial {m : ℕ} (A : Fin m → ℤ) (d : Fin (m + 2) → ℤ)
    (a b : Fin (m + 2)) : CompleteRing :=
  ∏ t, complete (d (doubleOmissionColumn a b t) - A t)

/-- The weight of the increasing determinant monomial for the selected columns. -/
noncomputable def caterpillarWeight {m : ℕ} (w : ConvexWeight) (A : Fin m → ℤ)
    (d : Fin (m + 2) → ℤ) (a b : Fin (m + 2)) : ℝ :=
  ∑ t, w.weight (d (doubleOmissionColumn a b t) - A t).toNat

private theorem caterpillar_feasible {m : ℕ} {A : Fin m → ℤ} {d : Fin (m + 2) → ℤ}
    (hd : StrictMono d)
    (hf : ∀ t, A t ≤ d ⟨t.val, by have := t.isLt; omega⟩)
    (a b : Fin (m + 2)) : ∀ t, A t ≤ d (doubleOmissionColumn a b t) := by
  intro t
  exact (hf t).trans (hd.monotone (doubleOmissionColumn_ge a b t))

/-- The selected determinant has the actual increasing monomial as its initial form. -/
theorem caterpillarMinor_initialForm {m : ℕ} (w : ConvexWeight)
    {A : Fin m → ℤ} {d : Fin (m + 2) → ℤ} (hA : StrictMono A) (hd : StrictMono d)
    (hf : ∀ t, A t ≤ d ⟨t.val, by have := t.isLt; omega⟩)
    (a b : Fin (m + 2)) :
    initialForm w.generatorWeight (caterpillarMinor A d a b) = caterpillarMonomial A d a b := by
  exact monge_minor_initialForm w hA (hd.comp (doubleOmissionColumn_strictMono a b))
    (caterpillar_feasible hd hf a b)

theorem caterpillarMinor_ne_zero {m : ℕ} (w : ConvexWeight)
    {A : Fin m → ℤ} {d : Fin (m + 2) → ℤ} (hA : StrictMono A) (hd : StrictMono d)
    (hf : ∀ t, A t ≤ d ⟨t.val, by have := t.isLt; omega⟩)
    (a b : Fin (m + 2)) : caterpillarMinor A d a b ≠ 0 := by
  exact monge_minor_ne_zero w hA (hd.comp (doubleOmissionColumn_strictMono a b))
    (caterpillar_feasible hd hf a b)

/-- The assigned weight is the least weight of the actual determinant, not a surrogate. -/
theorem caterpillarMinor_leastWeight {m : ℕ} (w : ConvexWeight)
    {A : Fin m → ℤ} {d : Fin (m + 2) → ℤ} (hA : StrictMono A) (hd : StrictMono d)
    (hf : ∀ t, A t ≤ d ⟨t.val, by have := t.isLt; omega⟩) (a b : Fin (m + 2)) :
    leastWeight w.generatorWeight (caterpillarMinor A d a b) = caterpillarWeight w A d a b := by
  have hn := caterpillarMinor_ne_zero w hA hd hf a b
  have hh : MvPolynomial.IsWeightedHomogeneous w.generatorWeight
      (initialForm w.generatorWeight (caterpillarMinor A d a b))
      (caterpillarWeight w A d a b) := by
    rw [caterpillarMinor_initialForm w hA hd hf a b]
    exact complete_prod_convex_homogeneous Finset.univ
      (fun t => d (doubleOmissionColumn a b t) - A t) w
      (fun t _ => sub_nonneg.mpr (caterpillar_feasible hd hf a b t))
  have hl : MvPolynomial.IsWeightedHomogeneous w.generatorWeight
      (initialForm w.generatorWeight (caterpillarMinor A d a b))
      (leastWeight w.generatorWeight (caterpillarMinor A d a b)) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _
  exact MvPolynomial.IsWeightedHomogeneous.inj_right (initialForm_ne_zero hn) hl hh

/-- The two crossing pairs retain the same unordered pair of columns in every row. -/
theorem doubleOmissionColumn_crossing_pairs {m : ℕ} (i j k l : Fin (m + 2))
    (hij : i < j) (hjk : j < k) (hkl : k < l) (t : Fin m) :
    (doubleOmissionColumn i k t = doubleOmissionColumn i l t ∧
      doubleOmissionColumn j l t = doubleOmissionColumn j k t) ∨
    (doubleOmissionColumn i k t = doubleOmissionColumn j k t ∧
      doubleOmissionColumn j l t = doubleOmissionColumn i l t) := by
  have hi : i.val < j.val := hij
  have hj : j.val < k.val := hjk
  have hk : k.val < l.val := hkl
  have hn :
      (doubleOmissionIndex i.val k.val t.val = doubleOmissionIndex i.val l.val t.val ∧
        doubleOmissionIndex j.val l.val t.val = doubleOmissionIndex j.val k.val t.val) ∨
      (doubleOmissionIndex i.val k.val t.val = doubleOmissionIndex j.val k.val t.val ∧
        doubleOmissionIndex j.val l.val t.val = doubleOmissionIndex i.val l.val t.val) := by
    unfold doubleOmissionIndex
    split_ifs <;> omega
  rcases hn with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨Fin.ext h₁, Fin.ext h₂⟩
  · exact Or.inr ⟨Fin.ext h₁, Fin.ext h₂⟩

/-- Exact crossing monomial identity in `prop:caterpillar`. -/
theorem caterpillar_crossing_monomial {m : ℕ} (A : Fin m → ℤ) (d : Fin (m + 2) → ℤ)
    (i j k l : Fin (m + 2)) (hij : i < j) (hjk : j < k) (hkl : k < l) :
    caterpillarMonomial A d i k * caterpillarMonomial A d j l =
      caterpillarMonomial A d i l * caterpillarMonomial A d j k := by
  unfold caterpillarMonomial
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t _
  rcases doubleOmissionColumn_crossing_pairs i j k l hij hjk hkl t with
    ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂, mul_comm]

theorem caterpillar_crossing_weight {m : ℕ} (w : ConvexWeight) (A : Fin m → ℤ)
    (d : Fin (m + 2) → ℤ) (i j k l : Fin (m + 2))
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    caterpillarWeight w A d i k + caterpillarWeight w A d j l =
      caterpillarWeight w A d i l + caterpillarWeight w A d j k := by
  unfold caterpillarWeight
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rcases doubleOmissionColumn_crossing_pairs i j k l hij hjk hkl t with
    ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂, add_comm]

private noncomputable def caterpillarEntryWeight {m : ℕ} (w : ConvexWeight)
    (A : Fin m → ℤ) (d : Fin (m + 2) → ℤ) (t c : ℕ) : ℝ :=
  if ht : t < m then
    if hc : c < m + 2 then w.weight (d ⟨c, hc⟩ - A ⟨t, ht⟩).toNat else 0
  else 0

private theorem sum_range_prefix (f : ℕ → ℝ) {a m : ℕ} (ha : a ≤ m) :
    (∑ t ∈ Finset.range m, if t < a then f t else 0) = ∑ t ∈ Finset.range a, f t := by
  rw [← Finset.sum_filter]
  have he : (Finset.range m).filter (fun t => t < a) = Finset.range a := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he]

private theorem doubleOmission_cost_decomposition (F : ℕ → ℕ → ℝ) {m a b : ℕ}
    (hab : a < b) (ha : a ≤ m) (hb : b - 1 ≤ m) :
    (∑ t ∈ Finset.range m, F t (doubleOmissionIndex a b t)) =
      (∑ t ∈ Finset.range m, F t (t + 2)) +
      (∑ t ∈ Finset.range a, (F t t - F t (t + 1))) +
      (∑ t ∈ Finset.range (b - 1), (F t (t + 1) - F t (t + 2))) := by
  have hpoint : ∀ t, F t (doubleOmissionIndex a b t) =
      F t (t + 2) + (if t < a then F t t - F t (t + 1) else 0) +
        (if t < b - 1 then F t (t + 1) - F t (t + 2) else 0) := by
    intro t
    by_cases hta : t < a
    · have htb : t < b - 1 := by omega
      have hna : ¬ a ≤ t := by omega
      have hnb : ¬ b - 1 ≤ t := by omega
      simp only [doubleOmissionIndex, ite_eq_right hna, ite_eq_right hnb,
        Nat.add_zero, ite_eq_left hta, ite_eq_left htb]
      ring
    · have hat : a ≤ t := by omega
      by_cases htb : t < b - 1
      · have hnb : ¬ b - 1 ≤ t := by omega
        simp only [doubleOmissionIndex, ite_eq_left hat, ite_eq_right hnb,
          Nat.add_zero, ite_eq_right hta, ite_eq_left htb]
        ring
      · have hbt : b - 1 ≤ t := by omega
        simp only [doubleOmissionIndex, ite_eq_left hat, ite_eq_left hbt,
          ite_eq_right hta, ite_eq_right htb, Nat.add_assoc]
        ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_range_prefix (fun t => F t t - F t (t + 1)) ha,
    sum_range_prefix (fun t => F t (t + 1) - F t (t + 2)) hb]

private theorem caterpillarWeight_range {m : ℕ} (w : ConvexWeight)
    (A : Fin m → ℤ) (d : Fin (m + 2) → ℤ) (a b : Fin (m + 2)) :
    caterpillarWeight w A d a b =
      ∑ t ∈ Finset.range m,
        caterpillarEntryWeight w A d t (doubleOmissionIndex a.val b.val t) := by
  rw [← Fin.sum_univ_eq_sum_range]
  unfold caterpillarWeight
  apply Finset.sum_congr rfl
  intro t _
  have hc : doubleOmissionIndex a.val b.val t.val < m + 2 := by
    have ht := t.isLt
    unfold doubleOmissionIndex
    split_ifs <;> omega
  simp only [caterpillarEntryWeight, dite_eq_left t.isLt, dite_eq_left hc,
    doubleOmissionColumn]

/-- Strict rejection of the separated pairing for every admissible convex weight. -/
theorem caterpillar_separated_weight_strict {m : ℕ} (w : ConvexWeight)
    {A : Fin m → ℤ} {d : Fin (m + 2) → ℤ} (hA : StrictMono A) (hd : StrictMono d)
    (hf : ∀ t, A t ≤ d ⟨t.val, by have := t.isLt; omega⟩)
    (i j k l : Fin (m + 2)) (hij : i < j) (hjk : j < k) (hkl : k < l) :
    caterpillarWeight w A d i k + caterpillarWeight w A d j l <
      caterpillarWeight w A d i j + caterpillarWeight w A d k l := by
  have hi : i.val < j.val := hij
  have hj : j.val < k.val := hjk
  have hk : k.val < l.val := hkl
  have hl := l.isLt
  have hjpos : 1 ≤ j.val := by omega
  have hkpos : 1 ≤ k.val := by omega
  have hkm : k.val ≤ m := by omega
  let F := caterpillarEntryWeight w A d
  let u : ℕ → ℝ := fun t => F t t - F t (t + 1)
  let v : ℕ → ℝ := fun t => F t (t + 1) - F t (t + 2)
  have hF : ∀ t c (ht : t < m) (hc : c < m + 2),
      F t c = w.weight (d ⟨c, hc⟩ - A ⟨t, ht⟩).toNat := by
    intro t c ht hc
    simp only [F, caterpillarEntryWeight, dite_eq_left ht, dite_eq_left hc]
  have hlocal : ∀ s ∈ Finset.Ico j.val k.val, 0 < u s - v (s - 1) := by
    intro s hs
    obtain ⟨hjs, hsk⟩ := Finset.mem_Ico.mp hs
    have hsp : 1 ≤ s := by omega
    have hsm : s < m := by omega
    have hpred : s - 1 < m := by omega
    have hc₀ : s < m + 2 := by omega
    have hc₁ : s + 1 < m + 2 := by omega
    have hm := w.strict_monge_int
      (hA (show (⟨s - 1, hpred⟩ : Fin m) < ⟨s, hsm⟩ by
        change s - 1 < s
        omega))
      (hd (show (⟨s, hc₀⟩ : Fin (m + 2)) < ⟨s + 1, hc₁⟩ by
        change s < s + 1
        omega))
      (hf ⟨s, hsm⟩)
    dsimp only [u, v]
    have he₁ : s - 1 + 1 = s := Nat.sub_add_cancel hsp
    have he₂ : s - 1 + 2 = s + 1 := by omega
    rw [he₁, he₂, hF s s hsm hc₀, hF s (s + 1) hsm hc₁,
      hF (s - 1) s hpred hc₀, hF (s - 1) (s + 1) hpred hc₁]
    linarith
  have hgap : 0 < ∑ s ∈ Finset.Ico j.val k.val, (u s - v (s - 1)) := by
    apply Finset.sum_pos hlocal
    exact ⟨j.val, Finset.mem_Ico.mpr ⟨le_rfl, hj⟩⟩
  have hu := Finset.sum_Ico_eq_sub u (show j.val ≤ k.val by omega)
  have hv := Finset.sum_Ico_eq_sub v (show j.val - 1 ≤ k.val - 1 by omega)
  have hshift := Finset.sum_Ico_add_right_sub_eq (f := v) (j.val - 1) (k.val - 1) 1
  rw [Nat.sub_add_cancel hjpos, Nat.sub_add_cancel hkpos] at hshift
  rw [Finset.sum_sub_distrib, hshift, hu, hv] at hgap
  have hik : i.val < k.val := by omega
  have hjl : j.val < l.val := by omega
  have h₁ := doubleOmission_cost_decomposition (m := m) F hik (by omega) (by omega)
  have h₂ := doubleOmission_cost_decomposition (m := m) F hjl (by omega) (by omega)
  have h₃ := doubleOmission_cost_decomposition (m := m) F hi (by omega) (by omega)
  have h₄ := doubleOmission_cost_decomposition (m := m) F hk (by omega) (by omega)
  simp only [caterpillarWeight_range]
  change (∑ t ∈ Finset.range m, F t (doubleOmissionIndex i.val k.val t)) +
      (∑ t ∈ Finset.range m, F t (doubleOmissionIndex j.val l.val t)) <
    (∑ t ∈ Finset.range m, F t (doubleOmissionIndex i.val j.val t)) +
      (∑ t ∈ Finset.range m, F t (doubleOmissionIndex k.val l.val t))
  rw [h₁, h₂, h₃, h₄]
  dsimp only [u, v] at hgap
  linarith

/-- The full crossing identity and strict separated weight comparison of `prop:caterpillar`. -/
theorem caterpillar {m : ℕ} (w : ConvexWeight)
    {A : Fin m → ℤ} {d : Fin (m + 2) → ℤ} (hA : StrictMono A) (hd : StrictMono d)
    (hf : ∀ t, A t ≤ d ⟨t.val, by have := t.isLt; omega⟩)
    (i j k l : Fin (m + 2)) (hij : i < j) (hjk : j < k) (hkl : k < l) :
    caterpillarMonomial A d i k * caterpillarMonomial A d j l =
        caterpillarMonomial A d i l * caterpillarMonomial A d j k ∧
    caterpillarWeight w A d i k + caterpillarWeight w A d j l =
        caterpillarWeight w A d i l + caterpillarWeight w A d j k ∧
    caterpillarWeight w A d i k + caterpillarWeight w A d j l <
        caterpillarWeight w A d i j + caterpillarWeight w A d k l := by
  exact ⟨caterpillar_crossing_monomial A d i j k l hij hjk hkl,
    caterpillar_crossing_weight w A d i j k l hij hjk hkl,
    caterpillar_separated_weight_strict w hA hd hf i j k l hij hjk hkl⟩

end SkewSchurReconstruction
