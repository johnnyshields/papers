/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Shields.Combinatorics.Young.ElementarySymmetric
import Shields.Combinatorics.Young.LGVOddTableau
import SkewJacobiNegative.Gluing.SchurBridge
import Vendor.AlgebraicCombinatorics.SymmetricFunctions.Definitions

/-!
# Evaluating `Λ` at complete and elementary alphabets; the dual Jacobi--Trudi identity

Formalizes `shields-2026-skew-factor-gluing.tex`, «Component keys» (`sec:minimal-fibers`), the
involution `ι` with `ι(h_j) = e_j`, and the second Jacobi--Trudi identity that identifies
`ι(s_D)` with a skew Schur function of the transposed shape.

The algebra `Λ = ℚ[h₁, h₂, …]` has two families of evaluations into a commutative `ℚ`-algebra `R`
at an alphabet `x : ℕ → R` in `a` variables: `evalComplete a x`, sending `h_k` to the complete
homogeneous polynomial `h_k(x₀, …, x_{a-1})`, and `evalElem a x`, sending `h_k` to the elementary
polynomial `e_k(x₀, …, x_{a-1})`.  This file proves

* `Profile.aeval_elem_schur`: the second Jacobi--Trudi identity,
  `evalElem a x (s_P) = s_{λ'/μ'}(x)`, from the mixed-alphabet Jacobi--Trudi theorem of
  `Shields.Combinatorics.Young.LGVOddTableau` at zero even variables;
* `completeHom_varAlphabet`, `elemHom_varAlphabet`: in the `a` variables `x_i` of
  `MvPolynomial (Fin a) ℚ` the tableau definitions agree with `hsymm` and `esymm`
  (a one-row tableau is a multiset, via its weakly increasing word);
* `evalComplete_elem`: the Newton--Girard identity in the form `h_k ↦ e_k` of `ι` after
  `evalComplete`, i.e. `evalComplete a x ∘ ι = evalElem a x`;
* `eq_of_evalComplete_eq`: a function in `Λ` is determined by its evaluations at all alphabets
  `x₀, …, x_{a-1}` of independent variables.

Sorry-free.
-/

namespace SkewJacobiNegative.Gluing

open MvPolynomial

/-! ### One-row tableaux are multisets -/

section OneRow

variable (a p : ℕ)

/-- The weakly increasing word of a multiset on `a` letters, as natural numbers. -/
def sortWord (s : Sym (Fin a) p) : List ℕ := (s.1.sort (· ≤ ·)).map Fin.val

theorem length_sortWord (s : Sym (Fin a) p) : (sortWord a p s).length = p := by
  simp [sortWord, Multiset.length_sort]

theorem pairwise_sortWord (s : Sym (Fin a) p) : (sortWord a p s).Pairwise (· ≤ ·) := by
  unfold sortWord
  rw [List.pairwise_map]
  exact Multiset.pairwise_sort _ _

theorem sortWord_lt (s : Sym (Fin a) p) {j : ℕ} (hj : j < p) :
    (sortWord a p s).getD j 0 < a := by
  have hj' : j < (sortWord a p s).length := by rw [length_sortWord]; exact hj
  rw [List.getD_eq_getElem _ _ hj']
  simp only [sortWord, List.getElem_map]
  exact Fin.isLt _

/-- The one-row tableau of a multiset: its weakly increasing word. -/
def tableauOfSym (s : Sym (Fin a) p) : Shields.BoundedSkewSSYT (Shields.rect 1 p) ⊥ a :=
  ⟨{ entry := fun i j => if i = 0 then (sortWord a p s).getD j 0 else 0
     row_weak' := by
       intro i j₁ j₂ hj hlam hmu
       simp only [Shields.mem_rect] at hlam
       have hi : i = 0 := by omega
       subst hi
       simp only [ite_true]
       have h1 : j₁ < (sortWord a p s).length := by rw [length_sortWord]; omega
       have h2 : j₂ < (sortWord a p s).length := by rw [length_sortWord]; omega
       rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
       exact List.pairwise_iff_getElem.mp (pairwise_sortWord a p s) j₁ j₂ h1 h2 hj
     col_strict' := by
       intro i₁ i₂ j hi hlam hmu
       simp only [Shields.mem_rect] at hlam
       omega
     zeros' := by
       intro i j hc
       simp only [Shields.mem_skewCells, Shields.mem_rect] at hc
       by_cases hi : i = 0
       · subst hi
         have : p ≤ j := by
           by_contra h
           exact hc ⟨⟨by omega, by omega⟩, YoungDiagram.notMem_bot _⟩
         simp only [ite_true]
         apply List.getD_eq_default
         rw [length_sortWord]; exact this
       · simp [hi] },
   by
     intro i j hc
     simp only [Shields.mem_skewCells, Shields.mem_rect] at hc
     have hi : i = 0 := by omega
     subst hi
     have := sortWord_lt a p s hc.1.2
     change (if (0 : ℕ) = 0 then _ else 0) < a
     rw [ite_eq_left rfl]
     exact this⟩

theorem tableauOfSym_apply (s : Sym (Fin a) p) (i j : ℕ) :
    (tableauOfSym a p s) i j = if i = 0 then (sortWord a p s).getD j 0 else 0 := rfl

theorem entry_lt (T : Shields.BoundedSkewSSYT (Shields.rect 1 p) ⊥ a) (j : Fin p) :
    T 0 j < a :=
  T.2 0 j (by simp [Shields.mem_skewCells, Shields.mem_rect, j.isLt])

/-- The multiset of the entries of a one-row tableau. -/
def symOfTableau (T : Shields.BoundedSkewSSYT (Shields.rect 1 p) ⊥ a) : Sym (Fin a) p :=
  ⟨((List.ofFn fun j : Fin p => (⟨T 0 j, entry_lt a p T j⟩ : Fin a)) : Multiset (Fin a)),
    by simp⟩

theorem pairwise_entries (T : Shields.BoundedSkewSSYT (Shields.rect 1 p) ⊥ a) :
    (List.ofFn fun j : Fin p => (⟨T 0 j, entry_lt a p T j⟩ : Fin a)).Pairwise (· ≤ ·) := by
  rw [List.pairwise_ofFn]
  intro i j hij
  change T 0 i ≤ T 0 j
  exact T.1.row_weak hij (by simp [Shields.mem_rect, j.isLt]) (YoungDiagram.notMem_bot _)

theorem sort_symOfTableau (T : Shields.BoundedSkewSSYT (Shields.rect 1 p) ⊥ a) :
    (symOfTableau a p T).1.sort (· ≤ ·) =
      List.ofFn fun j : Fin p => (⟨T 0 j, entry_lt a p T j⟩ : Fin a) := by
  change Multiset.sort (((List.ofFn fun j : Fin p => (⟨T 0 j, entry_lt a p T j⟩ : Fin a) :
    List (Fin a)) : Multiset (Fin a))) _ = _
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (pairwise_entries a p T)

/-- One-row tableaux with entries below `a` are the multisets of size `p` on `a` letters. -/
def tableauEquivSym : Shields.BoundedSkewSSYT (Shields.rect 1 p) ⊥ a ≃ Sym (Fin a) p where
  toFun := symOfTableau a p
  invFun := tableauOfSym a p
  left_inv T := by
    refine Shields.BoundedSkewSSYT.ext fun i j => ?_
    rw [tableauOfSym_apply, sortWord, sort_symOfTableau]
    by_cases hi : i = 0
    · subst hi
      simp only [ite_true, List.map_ofFn]
      by_cases hj : j < p
      · rw [List.getD_eq_getElem _ _ (by simpa using hj)]
        simp
      · rw [List.getD_eq_default _ _ (by simpa using hj)]
        refine (T.zeros ?_).symm
        simp [Shields.mem_skewCells, Shields.mem_rect]
        omega
    · simp only [hi, ↓reduceIte]
      refine (T.zeros ?_).symm
      simp [Shields.mem_skewCells, Shields.mem_rect]
      omega
  right_inv s := by
    refine Subtype.ext ?_
    change ((List.ofFn fun j : Fin p => (⟨(tableauOfSym a p s) 0 j, entry_lt a p _ j⟩ : Fin a))
      : Multiset (Fin a)) = s.1
    have : (List.ofFn fun j : Fin p => (⟨(tableauOfSym a p s) 0 j, entry_lt a p _ j⟩ : Fin a))
        = s.1.sort (· ≤ ·) := by
      apply List.ext_getElem
      · simp [Multiset.length_sort]
      · intro k h1 h2
        simp only [List.getElem_ofFn, tableauOfSym_apply, ite_true]
        apply Fin.ext
        simp only [sortWord]
        rw [List.getD_eq_getElem _ _ (by simpa [sortWord] using h2)]
        simp
    rw [this, Multiset.sort_eq]

end OneRow

/-! ### The alphabet of `a` independent variables -/

/-- The alphabet `x_0, …, x_{a-1}` of `a` independent variables of `MvPolynomial (Fin a) ℚ`,
zero beyond. -/
noncomputable def varAlphabet (a : ℕ) : ℕ → MvPolynomial (Fin a) ℚ :=
  fun i => if h : i < a then X ⟨i, h⟩ else 0

theorem varAlphabet_val {a : ℕ} (i : Fin a) : varAlphabet a i = X i := by
  simp [varAlphabet, i.isLt]

/-- **The tableau definition of `h_p` agrees with `hsymm`.**  A one-row tableau is the weakly
increasing word of a multiset. -/
theorem completeHom_varAlphabet (a p : ℕ) :
    Shields.completeHom a p (varAlphabet a) = hsymm (Fin a) ℚ p := by
  rw [Shields.completeHom, Shields.skewSchur, hsymm]
  refine Fintype.sum_equiv (tableauEquivSym a p) _ _ fun T => ?_
  change _ = (((List.ofFn fun j : Fin p => (⟨T 0 j, entry_lt a p T j⟩ : Fin a) :
    List (Fin a)) : Multiset (Fin a)).map X).prod
  rw [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn]
  have : Shields.skewCells (Shields.rect 1 p) ⊥ = Finset.range 1 ×ˢ Finset.range p := by
    rw [Shields.skewCells_bot]; rfl
  rw [Finset.prod_congr this (fun c _ => rfl), Finset.prod_product, Finset.range_one,
    Finset.prod_singleton, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact varAlphabet_val ⟨T 0 j, entry_lt a p T j⟩

/-- **The tableau definition of `e_q` agrees with `esymm`.** -/
theorem elemHom_varAlphabet (a q : ℕ) :
    Shields.elemHom a q (varAlphabet a) = esymm (Fin a) ℚ q := by
  rw [Shields.elemHom_eq_sum_powersetCard, esymm]
  symm
  refine Finset.sum_bij (fun t _ => t.map Fin.valEmbedding) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_powersetCard] at ht ⊢
    refine ⟨?_, by simpa using ht.2⟩
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hx
    simp
  · intro t _ t' _ h
    exact Finset.map_injective _ h
  · intro S hS
    rw [Finset.mem_powersetCard] at hS
    refine ⟨S.attachFin (fun i hi => Finset.mem_range.mp (hS.1 hi)), ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, by simpa using hS.2⟩
    · ext x
      simp only [Finset.mem_map, Finset.mem_attachFin, Fin.valEmbedding_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, Finset.mem_range.mp (hS.1 hx)⟩, hx, rfl⟩
  · intro t _
    rw [Finset.prod_map]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [varAlphabet_val]

/-! ### The two evaluations of `Λ` -/

section Evaluation

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- **Evaluation at the complete alphabet.**  The `ℚ`-algebra map `Λ → R` sending `h_k` to the
complete homogeneous polynomial `h_k(x₀, …, x_{b-1})`. -/
noncomputable def evalComplete (b : ℕ) (x : ℕ → R) : Lambda →ₐ[ℚ] R :=
  aeval fun k : ℕ+ => Shields.completeHom b k x

/-- **Evaluation at the elementary alphabet.**  The `ℚ`-algebra map `Λ → R` sending `h_k` to the
elementary polynomial `e_k(x₀, …, x_{a-1})`. -/
noncomputable def evalElem (a : ℕ) (x : ℕ → R) : Lambda →ₐ[ℚ] R :=
  aeval fun k : ℕ+ => Shields.elemHom a k x

theorem evalComplete_hPos (b : ℕ) (x : ℕ → R) (k : ℕ) :
    evalComplete b x (hPos k) = Shields.completeHom b k x := by
  by_cases hk : 0 < k
  · have h := hPos_pnat ⟨k, hk⟩
    simp only [PNat.mk_coe] at h
    rw [h]
    exact aeval_X (fun k : ℕ+ => Shields.completeHom b k x) (⟨k, hk⟩ : ℕ+)
  · obtain rfl : k = 0 := by omega
    simp [Shields.completeHom_zero]

theorem evalElem_hPos (a : ℕ) (x : ℕ → R) (k : ℕ) :
    evalElem a x (hPos k) = Shields.elemHom a k x := by
  by_cases hk : 0 < k
  · have h := hPos_pnat ⟨k, hk⟩
    simp only [PNat.mk_coe] at h
    rw [h]
    exact aeval_X (fun k : ℕ+ => Shields.elemHom a k x) (⟨k, hk⟩ : ℕ+)
  · obtain rfl : k = 0 := by omega
    simp [Shields.elemHom_zero]

theorem evalComplete_hh (b : ℕ) (x : ℕ → R) (j : ℤ) :
    evalComplete b x (hh j) = if j < 0 then 0 else Shields.completeHom b j.toNat x := by
  unfold hh
  split_ifs with h
  · simp
  · exact evalComplete_hPos b x _

theorem evalElem_hh (a : ℕ) (x : ℕ → R) (j : ℤ) :
    evalElem a x (hh j) = if j < 0 then 0 else Shields.elemHom a j.toNat x := by
  unfold hh
  split_ifs with h
  · simp
  · exact evalElem_hPos a x _

/-! ### The dual Jacobi--Trudi identity -/

omit [Algebra ℚ R] in
theorem completeHom_zero_alphabet_of_pos {p : ℕ} (hp : 0 < p) (x : ℕ → R) :
    Shields.completeHom 0 p x = 0 := by
  refine Shields.skewSchur_eq_zero_of_lt_skewColLen (j := 0) x ?_
  rw [Shields.skewColLen, Shields.colLen_rect_of_lt hp, Shields.colLen_bot]
  omega

omit [Algebra ℚ R] in
theorem superHom_zero_even (a m : ℕ) (β α : ℕ → R) :
    Shields.superHom 0 a m β α = Shields.elemHom a m α := by
  rw [Shields.superHom, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
  · rw [Shields.completeHom_zero, one_mul, Nat.sub_zero]
  · intro p _ hp
    rw [completeHom_zero_alphabet_of_pos (Nat.pos_of_ne_zero hp), zero_mul]

omit [Algebra ℚ R] in
/-- **The dual Jacobi--Trudi identity.**  For a skew shape `λ / μ` inside `m` rows,
`det [e_{λ_u - μ_v - u + v}]_{u,v < m} = s_{λ'/μ'}(α)` in `a` variables. -/
theorem dualJacobiTrudi (a m : ℕ) (α : ℕ → R) (lam mu : YoungDiagram) (hmu : mu ≤ lam)
    (hrow : ∀ i, m ≤ i → lam.rowLen i = 0) :
    Shields.jacobiTrudiDet (fun k => Shields.elemHom a k α) lam mu m
      = Shields.skewSchur lam.transpose mu.transpose a α := by
  rw [← Shields.superSkewSchur_zero_even (fun _ => 0) α hmu]
  exact Shields.jacobiTrudiDet_eq_superSkewSchur
    (fun k => (superHom_zero_even a k (fun _ => 0) α).symm) hmu hrow

theorem Profile.evalComplete_schur {n : ℕ} (b : ℕ) (x : ℕ → R) (P : Profile n) :
    evalComplete b x P.schur = Shields.skewSchur P.lam P.mu b x :=
  Profile.aeval_schur_eq_skewSchur b x P

/-- **The second Jacobi--Trudi identity for a profile.**  Evaluating `s_P` at the elementary
alphabet in `a` variables gives the skew Schur polynomial of the transposed shape
`λ' / μ'`. -/
theorem Profile.evalElem_schur {n : ℕ} (a : ℕ) (x : ℕ → R) (P : Profile n) :
    evalElem a x P.schur = Shields.skewSchur P.lam.transpose P.mu.transpose a x := by
  rw [← dualJacobiTrudi a (n + 1) x P.lam P.mu P.mu_le_lam fun i hi => P.rowLen_lam_of_le hi]
  rw [Profile.schur, AlgHom.map_det, Shields.jacobiTrudiDet]
  congr 1
  ext u v
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, evalElem_hh,
    Shields.jtCoeff, Profile.rowLen_lam, Profile.rowLen_mu]
  have h1 := P.xi_pos u
  have h2 := P.zeta_nonneg v
  have h3 := P.zeta_nonneg u
  split_ifs with ha hb hb
  · omega
  · rfl
  · congr 2
    omega
  · omega

end Evaluation

/-! ### Newton--Girard and the involution `ι` -/

open AlgebraicCombinatorics.SymmetricPolynomials in
/-- **`ι` after evaluation.**  In `a` independent variables the involution `ι` of `Λ`, which is
defined by `ι(h_j) = e_j` through the recursion `elem`, sends the evaluation of `h_k` at the
complete alphabet to the elementary polynomial: `evalComplete (ι h_k) = e_k`.  The input is the
Newton--Girard identity `∑ (-1)^j e_j h_{n-j} = 0` of `Vendor.AlgebraicCombinatorics`. -/
theorem evalComplete_elem (a k : ℕ) :
    evalComplete a (varAlphabet a) (elem k) = esymm (Fin a) ℚ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | m
    · simp [elem]
    · have hNG := newtonGirard_eh (K := ℚ) (N := a) (m + 1) (by omega)
      rw [Finset.sum_range_succ, Nat.sub_self, h_zero, mul_one] at hNG
      rw [elem_succ, map_sum]
      have e1 : ∀ i ∈ Finset.range (m + 1),
          evalComplete a (varAlphabet a) ((-1) ^ (m + i) * elem i * hPos (m + 1 - i))
            = (-1) ^ m * ((-1) ^ i * esymm (Fin a) ℚ i * hsymm (Fin a) ℚ (m + 1 - i)) := by
        intro i hi
        have hi : i < m + 1 := Finset.mem_range.mp hi
        rw [map_mul, map_mul, ih i hi, evalComplete_hPos, completeHom_varAlphabet]
        simp only [map_pow, map_neg, map_one]
        rw [pow_add]
        ring
      rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
      have e2 : (-1 : MvPolynomial (Fin a) ℚ) ^ m * (-1) ^ m = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
      have e3 : ∑ i ∈ Finset.range (m + 1),
          (-1 : MvPolynomial (Fin a) ℚ) ^ i * esymm (Fin a) ℚ i * hsymm (Fin a) ℚ (m + 1 - i)
          = (-1) ^ m * esymm (Fin a) ℚ (m + 1) := by
        have : (-1 : MvPolynomial (Fin a) ℚ) ^ (m + 1) = -(-1) ^ m := by rw [pow_succ]; ring
        rw [this] at hNG
        linear_combination hNG
      rw [e3]
      linear_combination (esymm (Fin a) ℚ (m + 1)) * e2

/-- `evalComplete ∘ ι = evalElem` at the alphabet of `a` independent variables. -/
theorem evalComplete_comp_schurInvolution (a : ℕ) :
    (evalComplete a (varAlphabet a)).comp schurInvolution = evalElem a (varAlphabet a) := by
  apply MvPolynomial.algHom_ext
  intro k
  rw [AlgHom.comp_apply, schurInvolution_X, evalComplete_elem]
  exact (by rw [evalElem, aeval_X, elemHom_varAlphabet])

theorem evalComplete_schurInvolution (a : ℕ) (f : Lambda) :
    evalComplete a (varAlphabet a) (schurInvolution f) = evalElem a (varAlphabet a) f :=
  congrArg (fun g : Lambda →ₐ[ℚ] _ => g f) (evalComplete_comp_schurInvolution a)

open AlgebraicCombinatorics.SymmetricPolynomials in
/-- **Evaluations at independent variables separate `Λ`.**  A function of `Λ` is determined by
its values `evalComplete a x` at the alphabets of `a` independent variables, `a` arbitrary:
every element involves finitely many `h_k`, and `h_1, …, h_a` are algebraically independent in
`a` variables. -/
theorem eq_of_evalComplete_eq {f g : Lambda}
    (h : ∀ a, evalComplete a (varAlphabet a) f = evalComplete a (varAlphabet a) g) : f = g := by
  rw [← sub_eq_zero]
  set d : Lambda := f - g with hd
  have hd0 : ∀ a, evalComplete a (varAlphabet a) d = 0 := by
    intro a
    rw [hd, map_sub, h a, sub_self]
  set N : ℕ := d.vars.sup fun k : ℕ+ => (k : ℕ) with hN
  let φ : Fin N → ℕ+ := fun j => ⟨j + 1, Nat.succ_pos _⟩
  have hφ : Function.Injective φ := by
    intro i j hij
    exact Fin.ext (by simpa [φ] using congrArg PNat.val hij)
  have hsub : ↑d.vars ⊆ Set.range φ := by
    intro k hk
    have hkN : (k : ℕ) ≤ N := Finset.le_sup (f := fun k : ℕ+ => (k : ℕ)) (Finset.mem_coe.mp hk)
    exact ⟨⟨k - 1, by have := k.pos; omega⟩, PNat.eq (by simp [φ]; have := k.pos; omega)⟩
  obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range d φ hφ hsub
  have h0 := hd0 N
  rw [← hq, evalComplete, aeval_rename] at h0
  have hind := hsymm_algebraicIndependent (K := ℚ) (N := N)
  rw [algebraicIndependent_iff_injective_aeval] at hind
  have : q = 0 := by
    apply hind
    rw [map_zero, ← h0]
    have hfun : (fun j : Fin N => hsymm (Fin N) ℚ (j + 1))
        = (fun k : ℕ+ => Shields.completeHom N (k : ℕ) (varAlphabet N)) ∘ φ := by
      funext j
      exact (completeHom_varAlphabet N (j + 1)).symm
    rw [hfun]
  rw [← hq, this, map_zero]

end SkewJacobiNegative.Gluing
