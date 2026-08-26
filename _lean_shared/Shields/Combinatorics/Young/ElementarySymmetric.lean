/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
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
  have hprod : ∏ i ∈ Finset.range a, (1 + α i)
      = ∑ S ∈ (Finset.range a).powerset, ∏ i ∈ S, α i := by
    have h := Finset.prod_add (fun i => α i) (fun _ => (1 : ℝ)) (Finset.range a)
    simp only [Finset.prod_const_one, mul_one] at h
    rw [← h]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [elemHom_eq_sum_powersetCard, hprod]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun S _ _ => Finset.prod_nonneg fun i _ => hα i)
  intro S hS
  exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1

/-- **The uniform bound.**  A summable alphabet bounds every elementary symmetric
function of every truncation by one constant. -/
theorem elemHom_le_exp (hs : Summable α) (a q : ℕ) :
    elemHom a q α ≤ Real.exp (∑' i, α i) := by
  refine (elemHom_le_prod_one_add hα a q).trans ?_
  have h1 : ∏ i ∈ Finset.range a, (1 + α i) ≤ ∏ i ∈ Finset.range a, Real.exp (α i) :=
    Finset.prod_le_prod (fun i _ => by linarith [hα i])
      (fun i _ => by rw [add_comm]; exact Real.add_one_le_exp _)
  refine h1.trans ?_
  rw [← Real.exp_sum]
  exact Real.exp_le_exp.mpr (Summable.sum_le_tsum _ (fun i _ => hα i) hs)

/-- **The infinite elementary symmetric function exists.**  For a summable nonnegative
alphabet the truncated `e_q` increase and are bounded, so they converge; this is exactly
the hypothesis that the coefficients of an infinite-alphabet symbol are limits of the
finite ones. -/
theorem tendsto_elemHom (hs : Summable α) (q : ℕ) :
    Tendsto (fun a => elemHom a q α) atTop (𝓝 (⨆ a, elemHom a q α)) :=
  tendsto_atTop_ciSup (elemHom_mono hα q)
    ⟨Real.exp (∑' i, α i), by rintro _ ⟨a, rfl⟩; exact elemHom_le_exp hα hs a q⟩

/-- The limit is the sum over *all* `q`-element subsets of `ℕ`. -/
theorem hasSum_elemHom (hs : Summable α) (q : ℕ) :
    HasSum (fun S : {S : Finset ℕ // S.card = q} => ∏ i ∈ S.1, α i)
      (⨆ a, elemHom a q α) := by
  have hbdd : BddAbove (Set.range fun a => elemHom a q α) :=
    ⟨Real.exp (∑' i, α i), by rintro _ ⟨a, rfl⟩; exact elemHom_le_exp hα hs a q⟩
  -- every finite family of `q`-subsets sits inside one truncation
  have hbound : ∀ F : Finset {S : Finset ℕ // S.card = q},
      ∑ S ∈ F, ∏ i ∈ S.1, α i ≤ ⨆ a, elemHom a q α := by
    intro F
    obtain ⟨a, ha⟩ : ∃ a : ℕ, ∀ S ∈ F, S.1 ⊆ Finset.range a := by
      refine ⟨(F.sup fun S => S.1.sup id) + 1, fun S hS x hx => ?_⟩
      have h1 : x ≤ S.1.sup id := Finset.le_sup (f := id) hx
      have h2 : S.1.sup id ≤ F.sup fun S : {S : Finset ℕ // S.card = q} => S.1.sup id :=
        Finset.le_sup (f := fun S : {S : Finset ℕ // S.card = q} => S.1.sup id) hS
      exact Finset.mem_range.mpr (by omega)
    have himg : Finset.image (fun S : {S : Finset ℕ // S.card = q} => S.1) F
        ⊆ Finset.powersetCard q (Finset.range a) := by
      intro S hS
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
      exact Finset.mem_powersetCard.mpr ⟨ha T hT, T.2⟩
    calc ∑ S ∈ F, ∏ i ∈ S.1, α i
        = ∑ S ∈ Finset.image (fun S : {S : Finset ℕ // S.card = q} => S.1) F,
            ∏ i ∈ S, α i :=
          (Finset.sum_image (g := fun S : {S : Finset ℕ // S.card = q} => S.1)
            (f := fun S : Finset ℕ => ∏ i ∈ S, α i)
            (fun (S : {S : Finset ℕ // S.card = q}) _ (T : {S : Finset ℕ // S.card = q}) _
              (h : S.1 = T.1) => Subtype.ext h)).symm
      _ ≤ ∑ S ∈ Finset.powersetCard q (Finset.range a), ∏ i ∈ S, α i :=
          Finset.sum_le_sum_of_subset_of_nonneg himg
            (fun S _ _ => Finset.prod_nonneg fun i _ => hα i)
      _ = elemHom a q α := (elemHom_eq_sum_powersetCard a q α).symm
      _ ≤ ⨆ a, elemHom a q α := le_ciSup hbdd a
  apply hasSum_of_isLUB_of_nonneg
  · intro S
    exact Finset.prod_nonneg fun i _ => hα i
  refine ⟨?_, ?_⟩
  · rintro _ ⟨F, rfl⟩
    exact hbound F
  · intro c hc
    refine ciSup_le fun a => ?_
    rw [elemHom_eq_sum_powersetCard]
    have hsub : ∀ S ∈ Finset.powersetCard q (Finset.range a), S.card = q :=
      fun S hS => (Finset.mem_powersetCard.mp hS).2
    set G : Finset {S : Finset ℕ // S.card = q} :=
      (Finset.powersetCard q (Finset.range a)).attach.image
        (fun S => ⟨S.1, hsub S.1 S.2⟩) with hG
    have hGsum : ∑ S ∈ Finset.powersetCard q (Finset.range a), ∏ i ∈ S, α i
        = ∑ S ∈ G, ∏ i ∈ S.1, α i := by
      rw [hG, Finset.sum_image
        (g := fun S : {x : Finset ℕ // x ∈ Finset.powersetCard q (Finset.range a)} =>
          (⟨S.1, hsub S.1 S.2⟩ : {S : Finset ℕ // S.card = q}))
        (f := fun S : {S : Finset ℕ // S.card = q} => ∏ i ∈ S.1, α i)
        (fun S _ T _ h => Subtype.ext (congrArg (fun x : {S : Finset ℕ // S.card = q} => x.1) h))]
      exact (Finset.sum_attach _ (fun S => ∏ i ∈ S, α i)).symm
    rw [hGsum]
    exact hc ⟨G, rfl⟩

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
  have hq : (0 : ℝ) < (Nat.factorial q : ℝ) := by exact_mod_cast Nat.factorial_pos q
  have hprod : Filter.Tendsto (fun b : ℕ => ∏ i ∈ Finset.range q, (1 - (i : ℝ) / b))
      Filter.atTop (nhds 1) := by
    have h := tendsto_finsetProd (f := fun (i : ℕ) (b : ℕ) => 1 - (i : ℝ) / b)
      (a := fun _ : ℕ => (1 : ℝ)) (x := Filter.atTop) (Finset.range q)
      (fun i _ => by
        simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop)).sub
          (tendsto_const_div_atTop_nhds_zero_nat (i : ℝ)))
    simpa using h
  have hkey : ∀ b : ℕ, q ≤ b → 0 < b →
      (b.choose q : ℝ) / (b : ℝ) ^ q
        = (∏ i ∈ Finset.range q, (1 - (i : ℝ) / b)) / (Nat.factorial q : ℝ) := by
    intro b hqb hb
    have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    have hdesc : ((b.descFactorial q : ℕ) : ℝ) = ∏ i ∈ Finset.range q, ((b : ℝ) - i) := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      refine Finset.prod_congr rfl fun i hi => ?_
      have : i ≤ b := le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) hqb)
      exact Nat.cast_sub this
    have hchoose : (Nat.factorial q : ℝ) * (b.choose q : ℝ)
        = ∏ i ∈ Finset.range q, ((b : ℝ) - i) := by
      rw [← hdesc, ← Nat.cast_mul, Nat.descFactorial_eq_factorial_mul_choose]
    have hsplit : (∏ i ∈ Finset.range q, (1 - (i : ℝ) / b))
        = (∏ i ∈ Finset.range q, ((b : ℝ) - i)) / (b : ℝ) ^ q := by
      rw [eq_div_iff (by positivity)]
      have hpow : ((b : ℝ) ^ q) = ∏ _i ∈ Finset.range q, (b : ℝ) := by
        rw [Finset.prod_const, Finset.card_range]
      rw [hpow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => by field_simp
    rw [hsplit, div_div, mul_comm ((b : ℝ) ^ q), ← div_div, ← hchoose]
    field_simp
  refine Filter.Tendsto.congr' ?_ (hprod.div_const (Nat.factorial q : ℝ))
  filter_upwards [Filter.eventually_ge_atTop (max q 1)] with b hb
  exact (hkey b (le_trans (le_max_left _ _) hb) (lt_of_lt_of_le Nat.zero_lt_one
    (le_trans (le_max_right _ _) hb))).symm

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
    have : a ∈ Finset.range a := by
      have := (Finset.mem_powersetCard.mp hS).1
      exact this (Finset.mem_insert_self a T)
    simp at this)]
  congr 1
  rw [Finset.sum_image (fun S hS T hT h => by
    have hSa : a ∉ S := fun hx => by
      have := (Finset.mem_powersetCard.mp hS).1 hx
      simp at this
    have hTa : a ∉ T := fun hx => by
      have := (Finset.mem_powersetCard.mp hT).1 hx
      simp at this
    have := congrArg (fun (X : Finset ℕ) => X.erase a) h
    simpa [Finset.erase_insert hSa, Finset.erase_insert hTa] using this)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hSa : a ∉ S := fun hx => by
    have := (Finset.mem_powersetCard.mp hS).1 hx
    simp at this
  rw [Finset.prod_insert hSa]

/-- The alphabet of `a + b` letters made of `α` on the first block and `β` on the second. -/
noncomputable def concatAlphabet (a : ℕ) (α β : ℕ → R) : ℕ → R :=
  fun i => if i < a then α i else β (i - a)

/-- **The two-alphabet convolution** `e_q(A ∪ B) = ∑_{p+p'=q} e_p(A) e_{p'}(B)`.  This is
what lets an infinite alphabet and a free parameter be passed to the limit together. -/
theorem elemHom_concat (a : ℕ) (α β : ℕ → R) :
    ∀ b q : ℕ, elemHom (a + b) q (concatAlphabet a α β)
      = ∑ p ∈ Finset.range (q + 1), elemHom a p α * elemHom b (q - p) β := by
  intro b
  induction b with
  | zero =>
      intro q
      have hpref : ∀ i < a, concatAlphabet a α β i = α i := fun i hi => if_pos hi
      have hleft : elemHom (a + 0) q (concatAlphabet a α β) = elemHom a q α := by
        rw [Nat.add_zero, elemHom_eq_sum_powersetCard, elemHom_eq_sum_powersetCard]
        refine Finset.sum_congr rfl fun S hS => ?_
        exact Finset.prod_congr rfl fun i hi =>
          hpref i (Finset.mem_range.mp ((Finset.mem_powersetCard.mp hS).1 hi))
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

/-- Hence so does the two-alphabet coefficient. -/
theorem superHom_concatAlphabet_left {b a q a₀ : ℕ} (h : a₀ ≤ a) (β α γβ : ℕ → R) :
    superHom b a₀ q β (concatAlphabet a α γβ) = superHom b a₀ q β α := by
  rw [superHom, superHom]
  exact Finset.sum_congr rfl fun p _ => by
    rw [elemHom_concatAlphabet_left h]

end Shields
