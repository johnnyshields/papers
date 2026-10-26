/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/RibbonSchur.lean
import Shields.Combinatorics.Young.LGVTableau
import SkewRibbonCoarsenings.PartsAndCuts

/-!
# The ribbon Schur function, defined independently of the coarsening polynomial

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:algebra` (the ribbon Schur
function `r_β` that `eq:ribbon-expansion` expands).

The ribbon of a composition `β = (β₁, …, β_ℓ)` of weight `n` is the skew shape `λ/μ` with rows of
lengths `β₁, …, β_ℓ` (top to bottom) in which consecutive rows share exactly one column:
`λ_u = n - (β₁ + ⋯ + β_u) + u` and `μ_u = n - (β₁ + ⋯ + β_{u+1}) + u`.  The ribbon Schur
function `r_β ∈ Λ_ℤ = ℤ[h₁, h₂, …]` (`ribbonParts`, and `ribbon` for a cut set) is the
Jacobi–Trudi determinant `det [h_{λ_u - μ_v - u + v}]` of that skew shape, evaluated in the
independent generators `h_j` of `Lam` (the standard definition of a skew Schur function in `Λ`).
It involves neither `G` nor the sign twist `𝒜`.

`ribbonParts_bridge` ties it to the tableau definition: for every finite alphabet of `b` variables,
the ring homomorphism `h_j ↦ h_j(x₁, …, x_b)` sends `r_β` to the skew Schur polynomial
`Shields.skewSchur` of the ribbon shape, the sum over semistandard skew tableaux.  The recursion
`r_{(a,b,…)} = h_a r_{(b,…)} - r_{(a+b,…)}` is read off the first column of the determinant.
Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

/-! ### Young diagrams from a row-length function -/

/-- The Young diagram whose row `i < m` has length `f i` (for `f` weakly decreasing on `[0, m)`);
rows `i ≥ m` are empty. -/
def ydOfFun (m : ℕ) (f : ℕ → ℕ) : YoungDiagram where
  cells := (range m).biUnion fun i' => range (i' + 1) ×ˢ range (f i')
  isLowerSet := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hle hmem
    obtain ⟨hi, hj⟩ := Prod.mk_le_mk.mp hle
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_product, Finset.mem_range] at hmem ⊢
    obtain ⟨k, hk, h1, h2⟩ := hmem
    exact ⟨k, hk, by omega, by omega⟩

lemma mem_ydOfFun {m : ℕ} {f : ℕ → ℕ} {i j : ℕ} :
    (i, j) ∈ ydOfFun m f ↔ ∃ k, i ≤ k ∧ k < m ∧ j < f k := by
  rw [← YoungDiagram.mem_cells]
  simp only [ydOfFun, Finset.mem_biUnion, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, h1, h2⟩; exact ⟨k, by omega, hk, h2⟩
  · rintro ⟨k, h1, hk, h2⟩; exact ⟨k, hk, by omega, h2⟩

lemma rowLen_ydOfFun {m : ℕ} {f : ℕ → ℕ} (hf : ∀ i j, i ≤ j → j < m → f j ≤ f i) {i : ℕ}
    (hi : i < m) : (ydOfFun m f).rowLen i = f i := by
  apply le_antisymm
  · by_contra h
    have h' : f i < (ydOfFun m f).rowLen i := not_le.mp h
    have := YoungDiagram.mem_iff_lt_rowLen.mpr h'
    obtain ⟨k, h1, h2, h3⟩ := mem_ydOfFun.mp this
    have := hf i k h1 h2
    omega
  · by_contra h
    have h' : (ydOfFun m f).rowLen i < f i := not_le.mp h
    have : (i, (ydOfFun m f).rowLen i) ∈ ydOfFun m f := mem_ydOfFun.mpr ⟨i, le_rfl, hi, h'⟩
    have := YoungDiagram.mem_iff_lt_rowLen.mp this
    omega

lemma rowLen_ydOfFun_of_le {m : ℕ} {f : ℕ → ℕ} {i : ℕ} (hi : m ≤ i) :
    (ydOfFun m f).rowLen i = 0 := by
  by_contra h
  have : (i, 0) ∈ ydOfFun m f := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  obtain ⟨k, h1, h2, _⟩ := mem_ydOfFun.mp this
  omega

lemma ydOfFun_le {m : ℕ} {f g : ℕ → ℕ} (h : ∀ k, k < m → f k ≤ g k) :
    ydOfFun m f ≤ ydOfFun m g := by
  rintro ⟨i, j⟩ hc
  obtain ⟨k, h1, h2, h3⟩ := mem_ydOfFun.mp hc
  exact mem_ydOfFun.mpr ⟨k, h1, h2, lt_of_lt_of_le h3 (h k h2)⟩

/-! ### Partial sums of a list of parts -/

/-- The partial sum `β₁ + ⋯ + β_i` of a list of parts. -/
def pSum (l : List ℕ) (i : ℕ) : ℕ := (l.take i).sum

@[simp] lemma pSum_zero (l : List ℕ) : pSum l 0 = 0 := by simp [pSum]

lemma pSum_cons_succ (a : ℕ) (l : List ℕ) (i : ℕ) : pSum (a :: l) (i + 1) = a + pSum l i := by
  simp [pSum]

lemma pSum_length (l : List ℕ) : pSum l l.length = l.sum := by simp [pSum]

lemma pSum_le_sum (l : List ℕ) (i : ℕ) : pSum l i ≤ l.sum := by
  unfold pSum
  conv_rhs => rw [← List.take_append_drop i l]
  rw [List.sum_append]
  omega

lemma pSum_add_le : ∀ (l : List ℕ), IsParts l → ∀ {i j : ℕ}, i ≤ j → j ≤ l.length →
    pSum l i + (j - i) ≤ pSum l j
  | [], _, i, j, hij, hj => by
    have : j = 0 := by simpa using hj
    subst this
    have : i = 0 := by omega
    subst this
    simp
  | a :: l, hl, i, j, hij, hj => by
    have ha : 0 < a := hl a (by simp)
    have hl' : IsParts l := isParts_tail hl
    cases i with
    | zero =>
      cases j with
      | zero => simp
      | succ j =>
        have := pSum_add_le l hl' (Nat.zero_le j) (by simpa using hj)
        rw [pSum_cons_succ]
        simp at this ⊢
        omega
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have := pSum_add_le l hl' (Nat.le_of_succ_le_succ hij) (by simpa using hj)
        rw [pSum_cons_succ, pSum_cons_succ]
        omega

/-! ### The ribbon shape -/

/-- The outer shape `λ` of the ribbon of the composition `β`: row `u` has length
`n - (β₁ + ⋯ + β_u) + u`, for `u < ℓ(β)`. -/
def ribbonLam (β : List ℕ) : YoungDiagram :=
  ydOfFun β.length fun u => β.sum - pSum β u + u

/-- The inner shape `μ` of the ribbon of the composition `β`: row `u` has length
`n - (β₁ + ⋯ + β_{u+1}) + u`, for `u < ℓ(β)`. -/
def ribbonMu (β : List ℕ) : YoungDiagram :=
  ydOfFun β.length fun v => β.sum - pSum β (v + 1) + v

lemma rowLen_ribbonLam {β : List ℕ} (hβ : IsParts β) {u : ℕ} (hu : u < β.length) :
    (ribbonLam β).rowLen u = β.sum - pSum β u + u := by
  refine rowLen_ydOfFun (fun i j hij hj => ?_) hu
  have h1 := pSum_add_le β hβ hij hj.le
  have h2 := pSum_le_sum β j
  omega

lemma rowLen_ribbonMu {β : List ℕ} (hβ : IsParts β) {u : ℕ} (hu : u < β.length) :
    (ribbonMu β).rowLen u = β.sum - pSum β (u + 1) + u := by
  refine rowLen_ydOfFun (fun i j hij hj => ?_) hu
  have h1 : pSum β (i + 1) + (j - i) ≤ pSum β (j + 1) := by
    have := pSum_add_le β hβ (Nat.succ_le_succ hij) hj
    simpa [Nat.succ_sub_succ] using this
  have h2 := pSum_le_sum β (j + 1)
  omega

lemma ribbonMu_le_ribbonLam {β : List ℕ} (hβ : IsParts β) : ribbonMu β ≤ ribbonLam β := by
  refine ydOfFun_le fun k hk => ?_
  have h1 : pSum β k + 1 ≤ pSum β (k + 1) := by
    have := pSum_add_le β hβ (Nat.le_succ k) hk
    simpa using this
  omega

/-- The ribbon has row `u` of skew length `β_{u+1} = (β₁ + ⋯ + β_{u+1}) - (β₁ + ⋯ + β_u)`. -/
theorem ribbon_rowLen_sub {β : List ℕ} (hβ : IsParts β) {u : ℕ} (hu : u < β.length) :
    (ribbonLam β).rowLen u - (ribbonMu β).rowLen u = pSum β (u + 1) - pSum β u := by
  rw [rowLen_ribbonLam hβ hu, rowLen_ribbonMu hβ hu]
  have h1 := pSum_add_le β hβ (Nat.le_succ u) hu
  have h2 := pSum_le_sum β (u + 1)
  omega

/-- Consecutive rows of the ribbon share exactly one column: `λ_{u+1} = μ_u + 1`. -/
theorem ribbon_overlap {β : List ℕ} (hβ : IsParts β) {u : ℕ} (hu : u + 1 < β.length) :
    (ribbonLam β).rowLen (u + 1) = (ribbonMu β).rowLen u + 1 := by
  rw [rowLen_ribbonLam hβ hu, rowLen_ribbonMu hβ (by omega)]
  omega

/-- The ribbon Schur function `r_β ∈ Λ_ℤ` of a list of parts: the Jacobi–Trudi determinant
`det [h_{λ_u - μ_v - u + v}]_{0 ≤ u, v < ℓ}` of the ribbon shape `λ/μ` in the independent
generators `h_j` (`hgen`, `h_0 = 1`, `h_j = 0` for `j < 0`).  The empty composition gives `1`. -/
noncomputable def ribbonParts (β : List ℕ) : Lam :=
  Shields.jacobiTrudiDet hgen (ribbonLam β) (ribbonMu β) β.length

/-! ### The bridge to semistandard skew tableaux -/

/-- The ring homomorphism `Λ_ℤ → ℤ[x₀, x₁, …]` sending `h_j` to the complete homogeneous
symmetric polynomial `h_j(x₀, …, x_{b-1})`, written as the skew Schur polynomial of the row
`(j)` (`Shields.completeHom`). -/
noncomputable def evalAlphabet (b : ℕ) : Lam →+* MvPolynomial ℕ ℤ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℤ →+* MvPolynomial ℕ ℤ)
    fun j : ℕ+ => Shields.completeHom b (j : ℕ) (MvPolynomial.X : ℕ → MvPolynomial ℕ ℤ)

lemma evalAlphabet_hgen (b j : ℕ) :
    evalAlphabet b (hgen j) = Shields.completeHom b j (MvPolynomial.X : ℕ → MvPolynomial ℕ ℤ) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hgen, Shields.completeHom_zero]
  · have h1 : hgen j = MvPolynomial.X (Nat.toPNat j hj) := by simp [hgen, hj]; rfl
    rw [h1, evalAlphabet, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    rfl

/-- Bridge: the ribbon Schur function is the skew Schur polynomial of the ribbon shape.  For
every number `b` of variables, the image of `r_β` under `h_j ↦ h_j(x₀, …, x_{b-1})` is
`Shields.skewSchur (ribbonLam β) (ribbonMu β) b x`, the generating function of the semistandard
tableaux of the ribbon shape with entries `< b` (Shields' tableau definition, independent of
the determinant).  It rests on the skew Jacobi–Trudi identity `Shields.jacobiTrudiDet_eq_skewSchur`
for the even alphabet. -/
theorem ribbonParts_bridge {β : List ℕ} (hβ : IsParts β) (b : ℕ) :
    evalAlphabet b (ribbonParts β)
      = Shields.skewSchur (ribbonLam β) (ribbonMu β) b (MvPolynomial.X : ℕ → MvPolynomial ℕ ℤ) := by
  rw [← Shields.jacobiTrudiDet_eq_skewSchur (b := b) (m := β.length)
    (MvPolynomial.X : ℕ → MvPolynomial ℕ ℤ) (ribbonLam β) (ribbonMu β) (ribbonMu_le_ribbonLam hβ)
    (fun i hi => rowLen_ydOfFun_of_le hi)]
  unfold ribbonParts Shields.jacobiTrudiDet
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro u v
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  unfold Shields.jtCoeff
  split_ifs
  · exact evalAlphabet_hgen b _
  · exact map_zero _

/-! ### The first-column recursion -/

/-- The Hessenberg determinant `det [h_{Q_u - Q_{v+1}}]_{0 ≤ u, v < m}` of a decreasing
sequence `Q`, with `h_j = 0` for `j < 0`: the ribbon determinant in terms of the row ends. -/
noncomputable def hessDet (Q : ℕ → ℕ) (m : ℕ) : Lam :=
  (Matrix.of fun u v : Fin m => if Q (v + 1) ≤ Q u then hgen (Q u - Q (v + 1)) else 0).det

lemma hgen_zero : hgen 0 = 1 := by simp [hgen]

lemma hessDet_zero (Q : ℕ → ℕ) : hessDet Q 0 = 1 := by simp [hessDet]

lemma hessDet_one (Q : ℕ → ℕ) :
    hessDet Q 1 = if Q 1 ≤ Q 0 then hgen (Q 0 - Q 1) else 0 := by
  simp [hessDet, Matrix.det_unique]

lemma hessDet_congr {Q Q' : ℕ → ℕ} {m : ℕ} (h : ∀ k, k ≤ m → Q k = Q' k) :
    hessDet Q m = hessDet Q' m := by
  unfold hessDet
  congr 1
  ext u v
  simp only [Matrix.of_apply]
  rw [h u (by omega), h (v + 1) (by omega)]

lemma succAbove_one_val {m : ℕ} (i : Fin (m + 1)) :
    ((Fin.succAbove (1 : Fin (m + 2)) i : Fin (m + 2)) : ℕ)
      = if (i : ℕ) = 0 then 0 else (i : ℕ) + 1 := by
  by_cases h : (i : ℕ) = 0
  · have : i = 0 := Fin.ext h
    subst this
    simp
  · rw [if_neg h, Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
    simp

/-- Expansion of the Hessenberg determinant along its first column (sizes `m + 2`). -/
theorem hessDet_succ_succ (Q : ℕ → ℕ) (m : ℕ) (hQ : ∀ i j, i < j → j ≤ m + 2 → Q j < Q i) :
    hessDet Q (m + 2) = hgen (Q 0 - Q 1) * hessDet (fun k => Q (k + 1)) (m + 1)
      - hessDet (fun k => if k = 0 then Q 0 else Q (k + 1)) (m + 1) := by
  unfold hessDet
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have h3 : ∑ i : Fin m, (-1 : Lam) ^ ((i.succ.succ : Fin (m + 2)) : ℕ) *
      (Matrix.of fun u v : Fin (m + 2) =>
        if Q (v + 1) ≤ Q u then hgen (Q u - Q (v + 1)) else 0) i.succ.succ 0 *
      ((Matrix.of fun u v : Fin (m + 2) =>
        if Q (v + 1) ≤ Q u then hgen (Q u - Q (v + 1)) else 0).submatrix
        (Fin.succAbove i.succ.succ) Fin.succ).det = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have : (Matrix.of fun u v : Fin (m + 2) =>
        if Q (v + 1) ≤ Q u then hgen (Q u - Q (v + 1)) else 0) i.succ.succ 0 = 0 := by
      simp only [Matrix.of_apply, Fin.val_zero, Fin.val_succ, zero_add]
      have := hQ 1 (i + 2) (by omega) (by omega)
      exact ite_eq_right_iff.mpr
        (fun h => absurd h (by rw [show (i : ℕ) + 1 + 1 = i + 2 by ring]; omega))
    rw [this]; simp
  rw [h3, add_zero]
  have e0 : (Matrix.of fun u v : Fin (m + 2) =>
      if Q (v + 1) ≤ Q u then hgen (Q u - Q (v + 1)) else 0).submatrix
      (Fin.succAbove (0 : Fin (m + 2))) Fin.succ
      = Matrix.of fun u v : Fin (m + 1) =>
          if (fun k => Q (k + 1)) (v + 1) ≤ (fun k => Q (k + 1)) u
          then hgen ((fun k => Q (k + 1)) u - (fun k => Q (k + 1)) (v + 1)) else 0 := by
    ext i j
    simp [Fin.succAbove_zero]
  have e1 : (Matrix.of fun u v : Fin (m + 2) =>
      if Q (v + 1) ≤ Q u then hgen (Q u - Q (v + 1)) else 0).submatrix
      (Fin.succAbove (Fin.succ (0 : Fin (m + 1)))) Fin.succ
      = Matrix.of fun u v : Fin (m + 1) =>
          if (fun k => if k = 0 then Q 0 else Q (k + 1)) (v + 1)
              ≤ (fun k => if k = 0 then Q 0 else Q (k + 1)) u
          then hgen ((fun k => if k = 0 then Q 0 else Q (k + 1)) u
              - (fun k => if k = 0 then Q 0 else Q (k + 1)) (v + 1)) else 0 := by
    ext i j
    have := succAbove_one_val i
    simp only [Fin.succ_zero_eq_one] at this ⊢
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.val_succ, this]
    by_cases hi : (i : ℕ) = 0 <;> simp [hi]
  have a00 : (Matrix.of fun u v : Fin (m + 2) =>
      if Q (v + 1) ≤ Q u then hgen (Q u - Q (v + 1)) else 0) 0 0 = hgen (Q 0 - Q 1) := by
    have := hQ 0 1 (by omega) (by omega)
    simp [this.le]
  have a10 : (Matrix.of fun u v : Fin (m + 2) =>
      if Q (v + 1) ≤ Q u then hgen (Q u - Q (v + 1)) else 0) (Fin.succ 0) 0 = 1 := by
    simp [hgen_zero]
  rw [e0, e1, a00, a10]
  simp
  ring

lemma ribbonParts_eq_hessDet {β : List ℕ} (hβ : IsParts β) :
    ribbonParts β = hessDet (fun k => β.sum - pSum β k) β.length := by
  unfold ribbonParts Shields.jacobiTrudiDet hessDet
  congr 1
  ext u v
  simp only [Matrix.of_apply]
  rw [rowLen_ribbonLam hβ u.isLt, rowLen_ribbonMu hβ v.isLt]
  have h1 := pSum_le_sum β u
  have h2 := pSum_le_sum β (v + 1)
  unfold Shields.jtCoeff
  have e1 : (β.sum - pSum β u + u + v) - (β.sum - pSum β (v + 1) + v + u)
      = (β.sum - pSum β u) - (β.sum - pSum β (v + 1)) := by omega
  have e2 : (β.sum - pSum β (v + 1) + v + u ≤ β.sum - pSum β u + u + v)
      ↔ β.sum - pSum β (v + 1) ≤ β.sum - pSum β u := by omega
  simp only [e2, e1]

@[simp] lemma ribbonParts_nil : ribbonParts [] = 1 := by
  simp [ribbonParts, Shields.jacobiTrudiDet]

lemma ribbonParts_singleton {a : ℕ} (ha : 0 < a) : ribbonParts [a] = hgen a := by
  rw [ribbonParts_eq_hessDet (fun x hx => by simp at hx; omega)]
  simp [hessDet_one, pSum]

/-- The first-column recursion of the ribbon Schur function:
`r_{(a,b,…)} = h_a · r_{(b,…)} - r_{(a+b,…)}`. -/
theorem ribbonParts_cons_cons {a b : ℕ} {l : List ℕ} (h : IsParts (a :: b :: l)) :
    ribbonParts (a :: b :: l) = hgen a * ribbonParts (b :: l) - ribbonParts ((a + b) :: l) := by
  have hb : IsParts (b :: l) := isParts_tail h
  have hab : IsParts ((a + b) :: l) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have := head_pos h; omega
    · exact hb x (List.mem_cons_of_mem _ hx)
  have ha : 0 < a := head_pos h
  rw [ribbonParts_eq_hessDet h, ribbonParts_eq_hessDet hb, ribbonParts_eq_hessDet hab]
  have hlen : (a :: b :: l).length = l.length + 2 := by simp
  rw [hlen, show (b :: l).length = l.length + 1 by simp,
    show ((a + b) :: l).length = l.length + 1 by simp]
  have hsum : (a :: b :: l).sum = a + (b :: l).sum := by simp
  have hsum' : ((a + b) :: l).sum = a + (b :: l).sum := by simp; omega
  have hQ : ∀ i j, i < j → j ≤ l.length + 2 →
      (a :: b :: l).sum - pSum (a :: b :: l) j < (a :: b :: l).sum - pSum (a :: b :: l) i := by
    intro i j hij hj
    have h1 := pSum_add_le (a :: b :: l) h hij.le (by simpa using hj)
    have h2 := pSum_le_sum (a :: b :: l) j
    omega
  rw [hessDet_succ_succ _ _ hQ]
  have hpb : (b :: l).sum ≥ b := by simp
  have e0 : (a :: b :: l).sum - pSum (a :: b :: l) 0 - ((a :: b :: l).sum - pSum (a :: b :: l) 1)
      = a := by
    simp [pSum] <;> omega
  rw [e0]
  refine congrArg₂ (· - ·) (congrArg₂ (· * ·) rfl (hessDet_congr fun k _ => ?_))
    (hessDet_congr fun k hk => ?_)
  · rw [pSum_cons_succ]
    omega
  · rcases k with _ | k
    · simp [hsum']
    · rw [if_neg (by omega)]
      simp only [pSum_cons_succ]
      omega

end SkewRibbonCoarsenings
