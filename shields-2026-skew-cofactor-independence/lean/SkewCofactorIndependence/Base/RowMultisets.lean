/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-boundary-reconstruction/lean/SkewSchurReconstruction/RowMultisets.lean
import Shields.Combinatorics.Young.LGVTableau
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.Sym.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Row tableaux and finite multisets

The one-row tableau model of complete functions used in "Capped cofactors and admissible
convex weights" (`sec:coordinates`) is identified with finite weakly increasing words
and their multisets. Sorry-free.
-/

namespace SkewCofactorIndependence.Base

/-- A weakly increasing word of fixed length over a finite alphabet. -/
abbrev MonotoneRowWord (b k : ℕ) := {f : Fin k → Fin b // Monotone f}

/-- The multiset underlying a finite row word. -/
def monotoneRowWordToSym {b k : ℕ} (w : MonotoneRowWord b k) : Sym (Fin b) k :=
  ⟨(List.ofFn w.1 : Multiset (Fin b)), by simp⟩

theorem monotoneRowWordToSym_injective (b k : ℕ) :
    Function.Injective (@monotoneRowWordToSym b k) := by
  intro w v h
  apply Subtype.ext
  apply List.ofFn_injective
  have hm : (List.ofFn w.1 : Multiset (Fin b)) = List.ofFn v.1 :=
    congrArg Subtype.val h
  have hp : List.Perm (List.ofFn w.1) (List.ofFn v.1) := Quotient.exact hm
  exact hp.eq_of_pairwise' w.2.sortedLE_ofFn.pairwise v.2.sortedLE_ofFn.pairwise

private theorem ofFn_get_cast {α : Type*} (l : List α) {k : ℕ} (h : l.length = k) :
    List.ofFn (fun i : Fin k => l.get (Fin.cast h.symm i)) = l := by
  subst k
  simp

/-- Sorting gives the canonical increasing word associated with a multiset. -/
def symToMonotoneRowWord {b k : ℕ} (s : Sym (Fin b) k) : MonotoneRowWord b k := by
  let l := s.1.sort
  have hlen : l.length = k := (Multiset.length_sort (s := s.1) (· ≤ ·)).trans s.2
  refine ⟨fun i => l.get (Fin.cast hlen.symm i), ?_⟩
  have hs : l.SortedLE := (Multiset.pairwise_sort _ _).sortedLE
  intro i j hij
  apply hs.monotone_get
  exact hij

theorem monotoneRowWordToSym_symToMonotoneRowWord {b k : ℕ} (s : Sym (Fin b) k) :
    monotoneRowWordToSym (symToMonotoneRowWord s) = s := by
  apply Subtype.ext
  change ((List.ofFn (fun i : Fin k =>
    (s.1.sort (· ≤ ·)).get (Fin.cast
      ((Multiset.length_sort (s := s.1) (· ≤ ·)).trans s.2).symm i))) :
      Multiset (Fin b)) = s.1
  rw [ofFn_get_cast (s.1.sort (· ≤ ·))
    ((Multiset.length_sort (s := s.1) (· ≤ ·)).trans s.2)]
  exact Multiset.sort_eq _ _

/-- Finite multisets are equivalent to their increasing row words. -/
def symMonotoneRowWordEquiv (b k : ℕ) : Sym (Fin b) k ≃ MonotoneRowWord b k where
  toFun := symToMonotoneRowWord
  invFun := monotoneRowWordToSym
  left_inv := monotoneRowWordToSym_symToMonotoneRowWord
  right_inv w := monotoneRowWordToSym_injective b k
    (monotoneRowWordToSym_symToMonotoneRowWord (monotoneRowWordToSym w))

/-- Fill the unique row with the letters of an increasing word, and zero outside it. -/
def monotoneRowWordToTableau {b k : ℕ} (w : MonotoneRowWord b k) :
    Shields.BoundedSSYT (Shields.rect 1 k) b :=
  ⟨{ entry := fun i j => if h : i = 0 ∧ j < k then (w.1 ⟨j, h.2⟩).val else 0
     row_weak' := by
       intro i j₁ j₂ hj hcell
       obtain ⟨hi, hj₂⟩ := Shields.mem_rect.mp hcell
       have hi0 : i = 0 := by omega
       have hj₁ : j₁ < k := by omega
       rw [dite_eq_left (show i = 0 ∧ j₁ < k from ⟨hi0, hj₁⟩),
         dite_eq_left (show i = 0 ∧ j₂ < k from ⟨hi0, hj₂⟩)]
       exact w.2 (show (⟨j₁, hj₁⟩ : Fin k) ≤ ⟨j₂, hj₂⟩ from hj.le)
     col_strict' := by
       intro i₁ i₂ j hi hcell
       exact absurd (Shields.mem_rect.mp hcell).1 (by omega)
     zeros' := by
       intro i j hcell
       exact dite_eq_right (fun h => hcell (Shields.mem_rect.mpr ⟨by omega, h.2⟩)) },
   by
     intro i j hcell
     obtain ⟨hi, hj⟩ := Shields.mem_rect.mp hcell
     have hi0 : i = 0 := by omega
     change (if h : i = 0 ∧ j < k then (w.1 ⟨j, h.2⟩).val else 0) < b
     rw [dite_eq_left (show i = 0 ∧ j < k from ⟨hi0, hj⟩)]
     exact (w.1 ⟨j, hj⟩).isLt⟩

/-- Read the letters of a bounded one-row tableau. -/
def tableauToMonotoneRowWord {b k : ℕ}
    (T : Shields.BoundedSSYT (Shields.rect 1 k) b) : MonotoneRowWord b k :=
  ⟨fun j => ⟨T 0 j, T.lt (Shields.mem_rect.mpr ⟨Nat.zero_lt_one, j.isLt⟩)⟩,
   by
     intro i j hij
     exact Shields.boundedSSYT_row_mono T (show i.val ≤ j.val from hij) j.isLt⟩

theorem tableauToMonotoneRowWord_monotoneRowWordToTableau {b k : ℕ}
    (w : MonotoneRowWord b k) :
    tableauToMonotoneRowWord (monotoneRowWordToTableau w) = w := by
  apply Subtype.ext
  funext j
  apply Fin.ext
  change (if h : (0 : ℕ) = 0 ∧ j.val < k then (w.1 ⟨j.val, h.2⟩).val else 0) = (w.1 j).val
  rw [dite_eq_left (show (0 : ℕ) = 0 ∧ j.val < k from ⟨rfl, j.isLt⟩)]

theorem monotoneRowWordToTableau_tableauToMonotoneRowWord {b k : ℕ}
    (T : Shields.BoundedSSYT (Shields.rect 1 k) b) :
    monotoneRowWordToTableau (tableauToMonotoneRowWord T) = T := by
  apply Shields.BoundedSSYT.ext
  intro i j
  by_cases hc : (i, j) ∈ Shields.rect 1 k
  · obtain ⟨hi, hj⟩ := Shields.mem_rect.mp hc
    have hi0 : i = 0 := by omega
    subst i
    change (if _h : (0 : ℕ) = 0 ∧ j < k then T 0 j else 0) = T 0 j
    rw [dite_eq_left (show (0 : ℕ) = 0 ∧ j < k from ⟨rfl, hj⟩)]
  · rw [Shields.BoundedSSYT.zeros _ hc, T.zeros hc]

/-- Bounded one-row tableaux are precisely increasing words. -/
def monotoneRowWordTableauEquiv (b k : ℕ) :
    MonotoneRowWord b k ≃ Shields.BoundedSSYT (Shields.rect 1 k) b where
  toFun := monotoneRowWordToTableau
  invFun := tableauToMonotoneRowWord
  left_inv := tableauToMonotoneRowWord_monotoneRowWordToTableau
  right_inv := monotoneRowWordToTableau_tableauToMonotoneRowWord

/-- Sorting a multiset and filling its row identifies the two indexing sets. -/
def symRowTableauEquiv (b k : ℕ) :
    Sym (Fin b) k ≃ Shields.BoundedSSYT (Shields.rect 1 k) b :=
  (symMonotoneRowWordEquiv b k).trans (monotoneRowWordTableauEquiv b k)

open scoped BigOperators

/-- A one-row tableau's cell product is its word product. -/
theorem rowTableau_weight {R : Type*} [CommMonoid R] {b k : ℕ}
    (T : Shields.BoundedSSYT (Shields.rect 1 k) b) (β : ℕ → R) :
    (∏ c ∈ (Shields.rect 1 k).cells, β (T c.1 c.2)) =
      ∏ j : Fin k, β (T 0 j) := by
  change (∏ c ∈ Finset.range 1 ×ˢ Finset.range k, β (T c.1 c.2)) = _
  rw [Finset.prod_product, Finset.prod_range_one]
  exact Finset.prod_range (fun j => β (T 0 j))

/-- The multiset product of a row word is its indexed product. -/
theorem monotoneRowWordToSym_weight {R : Type*} [CommMonoid R] {b k : ℕ}
    (w : MonotoneRowWord b k) (β : Fin b → R) :
    ((monotoneRowWordToSym w).1.map β).prod = ∏ j : Fin k, β (w.1 j) := by
  simp only [monotoneRowWordToSym, Multiset.map_coe, Multiset.prod_coe,
    List.map_ofFn, List.prod_ofFn, Function.comp_apply]

/-- Sorting and filling preserve every multiplicative letter weight. -/
theorem symRowTableauEquiv_weight {R : Type*} [CommMonoid R] {b k : ℕ}
    (s : Sym (Fin b) k) (β : ℕ → R) :
    (∏ c ∈ (Shields.rect 1 k).cells, β (symRowTableauEquiv b k s c.1 c.2)) =
      (s.1.map (fun i => β i.val)).prod := by
  rw [rowTableau_weight]
  have hw := monotoneRowWordToSym_weight (symToMonotoneRowWord s) (fun i => β i.val)
  rw [monotoneRowWordToSym_symToMonotoneRowWord] at hw
  rw [hw]
  apply Finset.prod_congr rfl
  intro j _
  change β ((if h : (0 : ℕ) = 0 ∧ j.val < k then
    ((symToMonotoneRowWord s).1 ⟨j.val, h.2⟩).val else 0)) =
      β (((symToMonotoneRowWord s).1 j).val)
  rw [dite_eq_left (show (0 : ℕ) = 0 ∧ j.val < k from ⟨rfl, j.isLt⟩)]

/-- Complete tableau functions are sums of letter products over finite multisets. -/
theorem completeHom_eq_sum_sym {R : Type*} [CommRing R] (b k : ℕ) (β : ℕ → R) :
    Shields.completeHom b k β =
      ∑ s : Sym (Fin b) k, (s.1.map (fun i => β i.val)).prod := by
  rw [Shields.completeHom, Shields.skewSchur_bot, Shields.schur]
  symm
  apply Fintype.sum_equiv (symRowTableauEquiv b k)
  intro s
  exact (symRowTableauEquiv_weight s β).symm

/-- The tableau-defined complete function is Mathlib's complete symmetric polynomial. -/
theorem completeHom_eq_hsymm (b k : ℕ) :
    Shields.completeHom b k
        (fun i => if hi : i < b then (MvPolynomial.X ⟨i, hi⟩ : MvPolynomial (Fin b) ℤ)
          else 0) =
      MvPolynomial.hsymm (Fin b) ℤ k := by
  rw [completeHom_eq_sum_sym, MvPolynomial.hsymm]
  apply Finset.sum_congr rfl
  intro s _
  have hf : (fun i : Fin b => if hi : i.val < b then
      (MvPolynomial.X ⟨i.val, hi⟩ : MvPolynomial (Fin b) ℤ) else 0) =
      MvPolynomial.X := by
    funext i
    simp only [dite_eq_left i.isLt]
  rw [hf]

end SkewCofactorIndependence.Base
