/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.LinearCombination
import Shields.Order.Monotone.Fin

/-!
# Extremal products along an increasing selection

An increasing selection is a strictly monotone `Fin r → Fin n`, and `topSel` is the one that
takes the first `r` indices.  For a family indexed by `Fin n` whose terms decrease, `topSel` is
the selection whose `r`-fold product is largest: a strictly monotone selection dominates its own
index, so every factor it picks is no larger than the factor `topSel` picks in the same slot.
Injectivity is enough, since reordering the factors leaves the product alone.

The last two results turn that bound around.  A finite family of complex numbers can be listed in
decreasing order of modulus, and a family so listed whose initial products are all nonnegative
reals has every term real -- each term is the ratio of two consecutive initial products.

## Main results

* `Shields.exists_strictMono_prod_eq`: a product over an injective family is a product over the
  increasing enumeration of its image.
* `Shields.prod_le_prod_topSel`, `Shields.prod_le_prod_topSel_of_injective`: for an antitone
  nonnegative family, no selection of `r` terms beats the initial segment.
* `Shields.norm_prod_le_norm_prod_topSel`: the same bound on moduli of complex products.
* `Shields.exists_perm_norm_antitone`: a finite family of complex numbers can be listed in
  decreasing order of modulus.
* `Shields.real_of_prod_initial_real`: a modulus-decreasing family with real initial products is
  real.

## Implementation notes

`topSel` is Mathlib's `Fin.castLE` and the initial segment is the `Finset` filter `(c : ℕ) < r`
rather than an `Iio`, because the order `r` ranges over the naturals up to `n` and is compared
across values, so it is not an element of `Fin n`.

## Tags

monotone, increasing selection, rearrangement, product, initial segment, modulus
-/

namespace Shields

/-- The first `r` indices of `Fin n`, as a strictly monotone selection.  This is
Mathlib's `Fin.castLE`; the abbreviation names the role it plays below. -/
abbrev topSel {r n : ℕ} (hrn : r ≤ n) : Fin r → Fin n := Fin.castLE hrn

theorem strictMono_topSel {r n : ℕ} (hrn : r ≤ n) : StrictMono (topSel hrn) :=
  Fin.strictMono_castLE hrn

/-- A strictly monotone selection dominates the identity on indices.  This is
`Shields.val_le_of_strictMono` composed with the strict monotonicity of `Fin.val`. -/
theorem val_le_val_of_strictMono {r n : ℕ} {f : Fin r → Fin n} (hf : StrictMono f) (i : Fin r) :
    (i : ℕ) ≤ (f i : ℕ) :=
  val_le_of_strictMono (Fin.val_strictMono.comp hf) i

/-- A product over an injective family is a product over the increasing
enumeration of its image. -/
theorem exists_strictMono_prod_eq {M : Type*} [CommMonoid M] {r n : ℕ}
    {u : Fin r → Fin n} (hu : Function.Injective u) (F : Fin n → M) :
    ∃ g : Fin r → Fin n, StrictMono g ∧ ∏ x, F (u x) = ∏ x, F (g x) := by
  have hcard : (Finset.image u Finset.univ).card = r := by
    rw [Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin]
  refine ⟨(Finset.image u Finset.univ).orderEmbOfFin hcard,
    (Finset.orderEmbOfFin _ hcard).strictMono, ?_⟩
  have h1 : ∏ b ∈ Finset.image u Finset.univ, F b = ∏ x, F (u x) :=
    Finset.prod_image fun x _ y _ h => hu h
  have h2 : ∏ b ∈ Finset.image ((Finset.image u Finset.univ).orderEmbOfFin hcard)
      Finset.univ, F b = ∏ x, F ((Finset.image u Finset.univ).orderEmbOfFin hcard x) :=
    Finset.prod_image fun x _ y _ h =>
      (Finset.orderEmbOfFin _ hcard).injective h
  rw [← h1, ← h2, Finset.image_orderEmbOfFin_univ]

/-- A product over the first `r` indices of `Fin n`, as a product along `topSel`. -/
theorem prod_filter_val_lt {M : Type*} [CommMonoid M] {r n : ℕ} (hrn : r ≤ n)
    (F : Fin n → M) :
    ∏ c ∈ Finset.univ.filter (fun c : Fin n => (c : ℕ) < r), F c
      = ∏ x : Fin r, F (topSel hrn x) := by
  have himg : (Finset.univ.filter (fun c : Fin n => (c : ℕ) < r))
      = Finset.image (topSel hrn) Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      exact ⟨⟨(i : ℕ), hi⟩, rfl⟩
    · rintro ⟨c, rfl⟩
      exact c.2
  rw [himg]
  exact Finset.prod_image fun x _ y _ h =>
    Fin.ext (by simpa [topSel] using congrArg Fin.val h)

/-- Splitting the last factor off an initial segment: the product over the indices below
`c + 1` is the product over those below `c` times the factor at `c`. -/
theorem prod_filter_val_lt_succ {M : Type*} [CommMonoid M] {n : ℕ} (F : Fin n → M) (c : Fin n) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < (c : ℕ) + 1), F i
      = (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < (c : ℕ)), F i) * F c := by
  have hins : Finset.univ.filter (fun i : Fin n => (i : ℕ) < (c : ℕ) + 1)
      = insert c (Finset.univ.filter (fun i : Fin n => (i : ℕ) < (c : ℕ))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | h) <;> omega
  rw [hins, Finset.prod_insert (by simp), mul_comm]

/-- **The largest `r`-fold product is the product of the `r` largest.**  For an
antitone nonnegative sequence, no strictly monotone selection of `r` terms beats
the initial segment. -/
theorem prod_le_prod_topSel {n r : ℕ} (hrn : r ≤ n) {a : Fin n → ℝ}
    (hnn : ∀ c, 0 ≤ a c) (hanti : ∀ c d : Fin n, c ≤ d → a d ≤ a c)
    {g : Fin r → Fin n} (hg : StrictMono g) :
    ∏ x, a (g x) ≤ ∏ x, a (topSel hrn x) := by
  refine Finset.prod_le_prod (fun x _ => hnn _) fun x _ => ?_
  refine hanti _ _ ?_
  rw [Fin.le_def]
  simpa [topSel] using val_le_val_of_strictMono hg x

/-- `Shields.prod_le_prod_topSel` against an arbitrary injective selection.  Reordering the
factors leaves the product alone, so injectivity is all the bound needs. -/
theorem prod_le_prod_topSel_of_injective {n r : ℕ} (hrn : r ≤ n) {a : Fin n → ℝ}
    (hnn : ∀ c, 0 ≤ a c) (hanti : ∀ c d : Fin n, c ≤ d → a d ≤ a c)
    {u : Fin r → Fin n} (hu : Function.Injective u) :
    ∏ x, a (u x) ≤ ∏ x, a (topSel hrn x) := by
  obtain ⟨g, hg, hgeq⟩ := exists_strictMono_prod_eq hu a
  rw [hgeq]
  exact prod_le_prod_topSel hrn hnn hanti hg

/-- **The modulus-largest `r`-fold product is the product of the `r` modulus-largest terms.**
For a family listed in decreasing order of modulus, no selection of `r` distinct terms beats the
initial segment. -/
theorem norm_prod_le_norm_prod_topSel {n r : ℕ} (hrn : r ≤ n) {mu : Fin n → ℂ}
    (hanti : ∀ c d : Fin n, c ≤ d → ‖mu d‖ ≤ ‖mu c‖)
    {u : Fin r → Fin n} (hu : Function.Injective u) :
    ‖∏ x, mu (u x)‖ ≤ ‖∏ x, mu (topSel hrn x)‖ := by
  rw [norm_prod, norm_prod]
  exact prod_le_prod_topSel_of_injective hrn (fun _ => norm_nonneg _) hanti hu

/-- A finite family of complex numbers can be listed in decreasing order of modulus. -/
theorem exists_perm_norm_antitone {n : ℕ} (f : Fin n → ℂ) :
    ∃ σ : Equiv.Perm (Fin n), ∀ c d : Fin n, c ≤ d → ‖f (σ d)‖ ≤ ‖f (σ c)‖ := by
  refine ⟨Tuple.sort (fun i => -‖f i‖), fun c d hcd => ?_⟩
  have hm := Tuple.monotone_sort (fun i => -‖f i‖) hcd
  simp only [Function.comp_apply] at hm
  linarith

/-- **A modulus-decreasing family with real initial products is real.**  If the moduli of `f`
are antitone and every product `∏_{c < r} f c` is a nonnegative real, then each `f c` is real:
it is the ratio of two consecutive such products, and where the smaller of the two vanishes some
earlier factor does, which by the ordering forces `f c` itself to vanish. -/
theorem real_of_prod_initial_real {n : ℕ} {f : Fin n → ℂ}
    (hanti : ∀ c d : Fin n, c ≤ d → ‖f d‖ ≤ ‖f c‖)
    (hP : ∀ r : ℕ, r ≤ n → ∃ v : ℝ, 0 ≤ v ∧
      ∏ c ∈ Finset.univ.filter (fun c : Fin n => (c : ℕ) < r), f c = (v : ℂ))
    (c : Fin n) : ∃ v : ℝ, f c = (v : ℂ) := by
  obtain ⟨v1, -, hv1⟩ := hP ((c : ℕ) + 1) c.2
  obtain ⟨v0, -, hv0⟩ := hP (c : ℕ) (le_of_lt c.2)
  have hstep := prod_filter_val_lt_succ f c
  by_cases hv0z : v0 = 0
  · refine ⟨0, ?_⟩
    obtain ⟨i, hi, hlz⟩ := Finset.prod_eq_zero_iff.mp
      (hv0.trans (by rw [hv0z, Complex.ofReal_zero]))
    have hile : i ≤ c := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact le_of_lt (by exact_mod_cast hi)
    have h1 : ‖f c‖ ≤ 0 := by simpa [hlz] using hanti i c hile
    simpa using norm_eq_zero.mp (le_antisymm h1 (norm_nonneg _))
  · refine ⟨v1 / v0, ?_⟩
    have hv0C : ((v0 : ℝ) : ℂ) ≠ 0 := by simpa using hv0z
    have heq : ((v1 : ℝ) : ℂ) = ((v0 : ℝ) : ℂ) * f c := by rw [← hv1, ← hv0, hstep]
    rw [Complex.ofReal_div, eq_div_iff hv0C]
    linear_combination -heq


/-! ### Axiom footprint -/

/-- info: 'Shields.norm_prod_le_norm_prod_topSel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_prod_le_norm_prod_topSel

/-- info: 'Shields.exists_perm_norm_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_perm_norm_antitone

/-- info: 'Shields.real_of_prod_initial_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms real_of_prod_initial_real

end Shields
