/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Monoid
import Shields.Combinatorics.Young.JacobiTrudi

/-!
# The elementary symmetric function as a sum over subsets

`Shields.elemHom a q α` is defined as the skew Schur function of a column of length `q`
in `a` variables.  A column tableau is a strictly increasing tuple, so it is the same
thing as a `q`-element subset of `{0, …, a-1}`, and

\[
  e_q(\alpha_0,\dots,\alpha_{a-1})
    = \sum_{|S|=q,\ S\subseteq\{0,\dots,a-1\}}\ \prod_{i\in S}\alpha_i .
\]

## Main results

* `Shields.elemHom_eq_sum_powersetCard` — the subset form.
* `Shields.elemHom_mono` — monotonicity in the number of variables, for a nonnegative
  alphabet.
* `Shields.elemHom_le_exp` — the uniform bound `e_q ≤ exp(∑ α)`, obtained from
  `∏(1+α_i)` rather than from a counting argument.
* `Shields.tendsto_elemHom` — **the infinite elementary symmetric function**: for a
  summable nonnegative alphabet the finite `e_q` converge, monotonically, to their
  supremum.  This is what an infinite alphabet needs to be a legitimate limit of finite
  ones.
* `Shields.hasSum_elemHom` — the limit is the sum over all `q`-element subsets of `ℕ`.
* `Shields.tendsto_elemHom_const` — the free parameter: `b` variables each equal to
  `γ/b` give `e_q → γ^q/q!`, the coefficient of `e^{γt}`.

## Papers depending on this file

* `growing-rank-edrei` — the passage of the supersymmetric hook criterion to an infinite
  alphabet, and to the exponential factor of a Schoenberg--Edrei symbol.
-/

open Finset

namespace Shields

variable {R : Type*} [CommRing R]

/-! ### Column tableaux are subsets -/

section ColumnSet

variable {q a : ℕ}

/-- The set of entries of a bounded column tableau. -/
def columnSet (T : BoundedSkewSSYT (rect q 1) ⊥ a) : Finset ℕ :=
  (Finset.range q).image fun i => T i 0

theorem mem_skewCells_col {i : ℕ} (hi : i < q) :
    ((i, 0) : ℕ × ℕ) ∈ skewCells (rect q 1) ⊥ :=
  mem_skewCells.mpr ⟨mem_rect.mpr ⟨hi, Nat.zero_lt_one⟩, YoungDiagram.notMem_bot _⟩

theorem columnSet_strictMonoOn (T : BoundedSkewSSYT (rect q 1) ⊥ a) :
    ∀ i₁ < q, ∀ i₂ < q, i₁ < i₂ → T i₁ 0 < T i₂ 0 := by
  intro i₁ _ i₂ hi₂ hlt
  exact T.1.col_strict' hlt (mem_rect.mpr ⟨hi₂, Nat.zero_lt_one⟩) (YoungDiagram.notMem_bot _)

theorem columnSet_injOn (T : BoundedSkewSSYT (rect q 1) ⊥ a) :
    Set.InjOn (fun i => T i 0) (Finset.range q) := by
  intro i₁ h₁ i₂ h₂ h
  rw [Finset.coe_range, Set.mem_Iio] at h₁ h₂
  rcases lt_trichotomy i₁ i₂ with hlt | heq | hgt
  · exact absurd h (columnSet_strictMonoOn T i₁ h₁ i₂ h₂ hlt).ne
  · exact heq
  · exact absurd h.symm (columnSet_strictMonoOn T i₂ h₂ i₁ h₁ hgt).ne

theorem card_columnSet (T : BoundedSkewSSYT (rect q 1) ⊥ a) : (columnSet T).card = q := by
  rw [columnSet, Finset.card_image_of_injOn (columnSet_injOn T), Finset.card_range]

theorem columnSet_subset (T : BoundedSkewSSYT (rect q 1) ⊥ a) :
    columnSet T ⊆ Finset.range a := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_range.mpr (T.lt_of_mem_cells (mem_skewCells_col (Finset.mem_range.mp hi)))

/-- The entries of the column tableau with a prescribed set of values. -/
noncomputable def colEntry (S : Finset ℕ) (hS : S.card = q) (i j : ℕ) : ℕ :=
  if h : i < q ∧ j = 0 then S.orderEmbOfFin hS ⟨i, h.1⟩ else 0

theorem colEntry_of {S : Finset ℕ} (hS : S.card = q) {i : ℕ} (hi : i < q) :
    colEntry S hS i 0 = S.orderEmbOfFin hS ⟨i, hi⟩ := by
  rw [colEntry, dif_pos (⟨hi, rfl⟩ : i < q ∧ (0 : ℕ) = 0)]

theorem colEntry_of_not {S : Finset ℕ} (hS : S.card = q) {i j : ℕ}
    (h : ¬ (i < q ∧ j = 0)) : colEntry S hS i j = 0 := dif_neg h

/-- The column tableau with a prescribed set of entries. -/
noncomputable def colTableau (S : Finset ℕ) (hS : S.card = q) (hSa : S ⊆ Finset.range a) :
    BoundedSkewSSYT (rect q 1) ⊥ a :=
  ⟨{ entry := colEntry S hS
     row_weak' := by
       intro i j₁ j₂ hj hlam _
       exact absurd (mem_rect.mp hlam).2 (by omega)
     col_strict' := by
       intro i₁ i₂ j hi hlam _
       obtain ⟨hi₂, hj⟩ := mem_rect.mp hlam
       have hj0 : j = 0 := by omega
       subst hj0
       rw [colEntry_of hS (show i₁ < q by omega), colEntry_of hS hi₂]
       exact (S.orderEmbOfFin hS).strictMono (show (⟨i₁, _⟩ : Fin q) < ⟨i₂, hi₂⟩ from hi)
     zeros' := by
       intro i j hc
       refine colEntry_of_not hS fun h => hc ?_
       rw [h.2]
       exact mem_skewCells_col h.1 },
   by
     intro i j hc
     obtain ⟨hlam, _⟩ := mem_skewCells.mp hc
     obtain ⟨hi, hj⟩ := mem_rect.mp hlam
     have hj0 : j = 0 := by omega
     subst hj0
     change colEntry S hS i 0 < a
     rw [colEntry_of hS hi]
     exact Finset.mem_range.mp (hSa (Finset.orderEmbOfFin_mem S hS ⟨i, hi⟩))⟩

theorem colTableau_apply {S : Finset ℕ} (hS : S.card = q) (hSa : S ⊆ Finset.range a)
    {i : ℕ} (hi : i < q) :
    colTableau S hS hSa i 0 = S.orderEmbOfFin hS ⟨i, hi⟩ := colEntry_of hS hi

theorem columnSet_colTableau {S : Finset ℕ} (hS : S.card = q) (hSa : S ⊆ Finset.range a) :
    columnSet (colTableau S hS hSa) = S := by
  ext x
  simp only [columnSet, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [colTableau_apply hS hSa hi]
    exact Finset.orderEmbOfFin_mem S hS ⟨i, hi⟩
  · intro hx
    have hrange : x ∈ Set.range (S.orderEmbOfFin hS) := by
      rw [Finset.range_orderEmbOfFin S hS]; exact_mod_cast hx
    obtain ⟨i, hi⟩ := hrange
    refine ⟨i, i.isLt, ?_⟩
    rw [colTableau_apply hS hSa i.isLt]
    simpa using hi

theorem colTableau_columnSet (T : BoundedSkewSSYT (rect q 1) ⊥ a) :
    colTableau (columnSet T) (card_columnSet T) (columnSet_subset T) = T := by
  refine BoundedSkewSSYT.ext fun i j => ?_
  by_cases hc : (i, j) ∈ skewCells (rect q 1) ⊥
  · obtain ⟨hlam, _⟩ := mem_skewCells.mp hc
    obtain ⟨hi, hj⟩ := mem_rect.mp hlam
    have hj0 : j = 0 := by omega
    subst hj0
    rw [colTableau_apply _ _ hi]
    refine (Finset.orderEmbOfFin_unique (s := columnSet T) (card_columnSet T)
      (f := fun x : Fin q => T x 0) (fun x => Finset.mem_image.mpr
        ⟨x, Finset.mem_range.mpr x.isLt, rfl⟩)
      (fun x y hxy => columnSet_strictMonoOn T x x.isLt y y.isLt hxy) ▸ rfl :
      (columnSet T).orderEmbOfFin (card_columnSet T) ⟨i, hi⟩ = T i 0)
  · rw [(colTableau (columnSet T) (card_columnSet T) (columnSet_subset T)).zeros hc,
      T.zeros hc]

end ColumnSet

/-! ### The subset form -/

/-- **The elementary symmetric function is the sum over subsets.**  A bounded column
tableau is a strictly increasing tuple of entries below `a`, hence a `q`-element subset
of `range a`, and the tableau weight is the product over that subset. -/
theorem elemHom_eq_sum_powersetCard (a q : ℕ) (α : ℕ → R) :
    elemHom a q α = ∑ S ∈ Finset.powersetCard q (Finset.range a), ∏ i ∈ S, α i := by
  rw [elemHom, skewSchur]
  refine Finset.sum_bij' (i := fun T _ => columnSet T)
    (j := fun S hS => colTableau S (Finset.mem_powersetCard.mp hS).2
      (Finset.mem_powersetCard.mp hS).1)
    (fun T _ => Finset.mem_powersetCard.mpr ⟨columnSet_subset T, card_columnSet T⟩)
    (fun S _ => Finset.mem_univ _)
    (fun T _ => colTableau_columnSet T)
    (fun S hS => columnSet_colTableau _ _)
    (fun T _ => ?_)
  simp only [skewCells_bot, cells_rect]
  rw [Finset.prod_product]
  simp only [Finset.prod_range_one]
  rw [columnSet, Finset.prod_image (fun i hi j hj h => columnSet_injOn T
    (by simpa using hi) (by simpa using hj) h)]

/-! ### The infinite alphabet -/

section Limits

open Filter Topology

variable {α : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i)

include hα

theorem elemHom_nonneg (a q : ℕ) : 0 ≤ elemHom a q α := by
  rw [elemHom_eq_sum_powersetCard]
  exact Finset.sum_nonneg fun S _ => Finset.prod_nonneg fun i _ => hα i

/-- Adding a variable can only increase an elementary symmetric function of a
nonnegative alphabet: the subsets of the shorter range are among those of the longer. -/
theorem elemHom_mono (q : ℕ) : Monotone fun a => elemHom a q α := by
  refine monotone_nat_of_le_succ fun a => ?_
  rw [elemHom_eq_sum_powersetCard, elemHom_eq_sum_powersetCard]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun S _ _ => Finset.prod_nonneg fun i _ => hα i)
  intro S hS
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  exact Finset.mem_powersetCard.mpr
    ⟨hsub.trans (Finset.range_mono (Nat.le_succ a)), hcard⟩

/-- Every elementary symmetric function is bounded by the full product `∏ (1 + α_i)`,
since the `q`-subsets are among all subsets. -/
theorem elemHom_le_prod_one_add (a q : ℕ) :
    elemHom a q α ≤ ∏ i ∈ Finset.range a, (1 + α i) := by
  rw [elemHom_eq_sum_powersetCard, Finset.prod_one_add]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun S _ _ => Finset.prod_nonneg fun i _ => hα i)
  intro S hS
  exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1

/-- **The uniform bound.**  A summable alphabet bounds every elementary symmetric
function of every truncation by one constant. -/
theorem elemHom_le_exp (hs : Summable α) (a q : ℕ) :
    elemHom a q α ≤ Real.exp (∑' i, α i) :=
  ((elemHom_le_prod_one_add hα a q).trans (Real.prod_one_add_le_exp_sum _ hα)).trans
    (Real.exp_le_exp.mpr (Summable.sum_le_tsum _ (fun i _ => hα i) hs))

/-- The truncations of `e_q` are bounded above by the exponential of the total mass. -/
theorem bddAbove_range_elemHom (hs : Summable α) (q : ℕ) :
    BddAbove (Set.range fun a => elemHom a q α) :=
  ⟨Real.exp (∑' i, α i), by rintro _ ⟨a, rfl⟩; exact elemHom_le_exp hα hs a q⟩

/-- **The infinite elementary symmetric function exists.**  For a summable nonnegative
alphabet the truncated `e_q` increase and are bounded, so they converge; this is exactly
the hypothesis that the coefficients of an infinite-alphabet symbol are limits of the
finite ones. -/
theorem tendsto_elemHom (hs : Summable α) (q : ℕ) :
    Tendsto (fun a => elemHom a q α) atTop (𝓝 (⨆ a, elemHom a q α)) :=
  tendsto_atTop_ciSup (elemHom_mono hα q) (bddAbove_range_elemHom hα hs q)

/-- The limit is the sum over *all* `q`-element subsets of `ℕ`. -/
theorem hasSum_elemHom (hs : Summable α) (q : ℕ) :
    HasSum (fun S : {S : Finset ℕ // S.card = q} => ∏ i ∈ S.1, α i)
      (⨆ a, elemHom a q α) := by
  have hbdd := bddAbove_range_elemHom hα hs q
  refine hasSum_of_isLUB_of_nonneg _ (fun S => Finset.prod_nonneg fun i _ => hα i) ⟨?_, ?_⟩
  · -- every finite family of `q`-subsets sits inside one truncation
    rintro _ ⟨F, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : ℕ, ∀ S ∈ F, S.1 ⊆ Finset.range a := by
      obtain ⟨a, ha⟩ := (F.sup fun S => S.1).exists_nat_subset_range
      exact ⟨a, fun S hS =>
        (Finset.le_sup (f := fun S : {S : Finset ℕ // S.card = q} => S.1) hS).trans ha⟩
    calc ∑ S ∈ F, ∏ i ∈ S.1, α i
        = ∑ S ∈ F.map (Function.Embedding.subtype _), ∏ i ∈ S, α i :=
          (Finset.sum_subtype_map_embedding
            (f := fun S : {S : Finset ℕ // S.card = q} => ∏ i ∈ S.1, α i) fun _ _ => rfl).symm
      _ ≤ ∑ S ∈ Finset.powersetCard q (Finset.range a), ∏ i ∈ S, α i :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun S hS => by
              obtain ⟨T, hT, rfl⟩ := Finset.mem_map.mp hS
              exact Finset.mem_powersetCard.mpr ⟨ha T hT, T.2⟩)
            (fun S _ _ => Finset.prod_nonneg fun i _ => hα i)
      _ = elemHom a q α := (elemHom_eq_sum_powersetCard a q α).symm
      _ ≤ ⨆ a, elemHom a q α := le_ciSup hbdd a
  · -- and every truncation is one such family
    refine fun c hc => ciSup_le fun a => ?_
    rw [elemHom_eq_sum_powersetCard, ← Finset.sum_subtype_of_mem (fun S => ∏ i ∈ S, α i)
      fun S hS => (Finset.mem_powersetCard.mp hS).2]
    exact hc ⟨_, rfl⟩

end Limits

/-! ### The exponential factor -/

/-- On a constant alphabet the elementary symmetric function is a binomial coefficient. -/
theorem elemHom_const (a q : ℕ) (x : R) :
    elemHom a q (fun _ => x) = (a.choose q : ℕ) * x ^ q := by
  rw [elemHom_eq_sum_powersetCard]
  have hterm : ∀ S ∈ Finset.powersetCard q (Finset.range a),
      (∏ _i ∈ S, x) = x ^ q := fun S hS => by
    rw [Finset.prod_const, (Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_range, nsmul_eq_mul]

/-- `\binom{b}{q}/b^q \to 1/q!`: the descending factorial is `b^q` times a product of
factors `1 - i/b`. -/
theorem tendsto_choose_div_pow (q : ℕ) :
    Filter.Tendsto (fun b : ℕ => (b.choose q : ℝ) / (b : ℝ) ^ q) Filter.atTop
      (nhds (1 / (Nat.factorial q : ℝ))) := by
  have h : Asymptotics.IsEquivalent Filter.atTop
      (fun b : ℕ => (b.choose q : ℝ) / (b : ℝ) ^ q)
      (fun b : ℕ => ((b : ℝ) ^ q / Nat.factorial q) / (b : ℝ) ^ q) :=
    (isEquivalent_choose q).div Asymptotics.IsEquivalent.refl
  refine h.symm.tendsto_nhds (tendsto_const_nhds.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop 1] with b hb
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  field_simp

/-- **The free parameter.**  The alphabet of `b` variables each equal to `γ/b` has
elementary symmetric functions converging to `γ^q/q!`, the Taylor coefficients of
`e^{γt}`: an exponential factor is a limit of finite alphabets, coefficient by
coefficient. -/
theorem tendsto_elemHom_const (γ : ℝ) (q : ℕ) :
    Filter.Tendsto (fun b : ℕ => elemHom b q (fun _ => γ / b)) Filter.atTop
      (nhds (γ ^ q / (Nat.factorial q : ℝ))) := by
  have hrw : ∀ b : ℕ, 0 < b →
      elemHom b q (fun _ => γ / b) = γ ^ q * ((b.choose q : ℝ) / (b : ℝ) ^ q) := by
    intro b hb
    have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    rw [elemHom_const, div_pow]
    field_simp
  have h := (tendsto_choose_div_pow q).const_mul (γ ^ q)
  rw [mul_one_div] at h
  refine Filter.Tendsto.congr' ?_ h
  · filter_upwards [Filter.eventually_gt_atTop 0] with b hb
    rw [hrw b hb]

/-! ### Two alphabets side by side -/

/-- **Pascal's rule for elementary symmetric functions**: a `q+1`-subset of the first
`a+1` letters either omits the last letter or contains it. -/
theorem elemHom_succ (a q : ℕ) (α : ℕ → R) :
    elemHom (a + 1) (q + 1) α = elemHom a (q + 1) α + α a * elemHom a q α := by
  rw [elemHom_eq_sum_powersetCard, elemHom_eq_sum_powersetCard,
    elemHom_eq_sum_powersetCard, Finset.range_add_one,
    Finset.powersetCard_succ_insert (by simp) q]
  rw [Finset.sum_union (by
    refine Finset.disjoint_left.mpr fun S hS hS' => ?_
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS'
    simpa using (Finset.mem_powersetCard.mp hS).1 (Finset.mem_insert_self a T))]
  congr 1
  rw [Finset.sum_image (fun S hS T hT h => by
    have hSa : a ∉ S := fun hx => by simpa using (Finset.mem_powersetCard.mp hS).1 hx
    have hTa : a ∉ T := fun hx => by simpa using (Finset.mem_powersetCard.mp hT).1 hx
    have := congrArg (fun (X : Finset ℕ) => X.erase a) h
    simpa [Finset.erase_insert hSa, Finset.erase_insert hTa] using this)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hSa : a ∉ S := fun hx => by simpa using (Finset.mem_powersetCard.mp hS).1 hx
  rw [Finset.prod_insert hSa]

/-- The alphabet of `a + b` letters made of `α` on the first block and `β` on the second. -/
noncomputable def concatAlphabet (a : ℕ) (α β : ℕ → R) : ℕ → R :=
  fun i => if i < a then α i else β (i - a)

/-- `e_q` reads only the first `a` letters. -/
theorem elemHom_congr {a q : ℕ} {α α' : ℕ → R} (h : ∀ i < a, α i = α' i) :
    elemHom a q α = elemHom a q α' := by
  rw [elemHom_eq_sum_powersetCard, elemHom_eq_sum_powersetCard]
  refine Finset.sum_congr rfl fun S hS => ?_
  exact Finset.prod_congr rfl fun i hi =>
    h i (Finset.mem_range.mp ((Finset.mem_powersetCard.mp hS).1 hi))

/-- On its first block the concatenated alphabet is the first one. -/
theorem elemHom_concatAlphabet_left {a q a₀ : ℕ} (h : a₀ ≤ a) (α β : ℕ → R) :
    elemHom a₀ q (concatAlphabet a α β) = elemHom a₀ q α :=
  elemHom_congr fun _i hi => if_pos (lt_of_lt_of_le hi h)

/-- **The two-alphabet convolution** `e_q(A ∪ B) = ∑_{p+p'=q} e_p(A) e_{p'}(B)`.  This is
what lets an infinite alphabet and a free parameter be passed to the limit together. -/
theorem elemHom_concat (a : ℕ) (α β : ℕ → R) :
    ∀ b q : ℕ, elemHom (a + b) q (concatAlphabet a α β)
      = ∑ p ∈ Finset.range (q + 1), elemHom a p α * elemHom b (q - p) β := by
  intro b
  induction b with
  | zero =>
      intro q
      have hleft : elemHom (a + 0) q (concatAlphabet a α β) = elemHom a q α := by
        rw [Nat.add_zero]; exact elemHom_concatAlphabet_left le_rfl α β
      rw [hleft, Finset.sum_eq_single q]
      · rw [Nat.sub_self, elemHom_zero, mul_one]
      · intro p hp hpq
        have : 0 < q - p := by
          have := Finset.mem_range.mp hp
          omega
        rw [elemHom_eq_zero_of_lt this, mul_zero]
      · intro h
        exact absurd (Finset.self_mem_range_succ q) h
  | succ b ih =>
      intro q
      cases q with
      | zero =>
          rw [Finset.sum_range_one, Nat.sub_zero, elemHom_zero, elemHom_zero,
            elemHom_zero, mul_one]
      | succ q =>
          have hab : a + (b + 1) = (a + b) + 1 := by ring
          have hlast : concatAlphabet a α β (a + b) = β b := by
            rw [concatAlphabet, if_neg (by omega)]
            congr 1
            omega
          have hS : (∑ p ∈ Finset.range (q + 1), elemHom a p α * elemHom b (q + 1 - p) β)
              + β b * ∑ p ∈ Finset.range (q + 1), elemHom a p α * elemHom b (q - p) β
              = ∑ p ∈ Finset.range (q + 1),
                  elemHom a p α * elemHom (b + 1) (q + 1 - p) β := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p hp => ?_
            have hq : q + 1 - p = (q - p) + 1 := by
              have := Finset.mem_range.mp hp
              omega
            rw [hq, elemHom_succ]
            ring
          rw [hab, elemHom_succ, hlast, ih (q + 1), ih q,
            Finset.sum_range_succ (fun p => elemHom a p α * elemHom b (q + 1 - p) β),
            Finset.sum_range_succ (fun p => elemHom a p α * elemHom (b + 1) (q + 1 - p) β),
            Nat.sub_self, elemHom_zero, elemHom_zero]
          linear_combination hS

/-- Hence so does the two-alphabet coefficient. -/
theorem superHom_concatAlphabet_left {b a q a₀ : ℕ} (h : a₀ ≤ a) (β α γβ : ℕ → R) :
    superHom b a₀ q β (concatAlphabet a α γβ) = superHom b a₀ q β α := by
  rw [superHom, superHom]
  exact Finset.sum_congr rfl fun p _ => by
    rw [elemHom_concatAlphabet_left h]


/-! ### Axiom footprint -/

/-- info: 'Shields.tendsto_elemHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_elemHom

/-- info: 'Shields.hasSum_elemHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasSum_elemHom

/-- info: 'Shields.tendsto_elemHom_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendsto_elemHom_const

end Shields
