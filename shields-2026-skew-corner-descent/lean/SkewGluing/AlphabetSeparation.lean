import SkewGluing.SchurBridge
import Vendor.AlgebraicCombinatorics.SymmetricFunctions.Definitions

/-!
# Finite alphabets separate symmetric functions

TODO-COPIED from `skew-factor-gluing/lean/SkewGluing/DualEvaluation.lean`.
Supports `shields-2026-skew-corner-descent.tex`, «Corner cofactors and common cores»
(`sec:corner`, `lem:cofactor`). One-row tableaux identify the complete homogeneous
polynomials, and algebraic independence separates the abstract generator ring. Sorry-free.
-/

namespace SkewGluing

open MvPolynomial

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

/-- Specialization to a finite complete homogeneous alphabet. -/
noncomputable def evalComplete {R : Type*} [CommRing R] [Algebra ℚ R]
    (b : ℕ) (x : ℕ → R) : Lambda →ₐ[ℚ] R :=
  aeval fun k : ℕ+ => Shields.completeHom b k x

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

end SkewGluing
