/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/Unsigned.lean
import SkewRibbonCoarsenings.LiteralFactor

/-!
# Unsigned composition as substitution

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:algebra`
(`prop:unsigned` with `eq:seam`, `eq:substitution`, `eq:Psi-laws`, `eq:projection`, `eq:split`,
and `cor:reversal-suffices`).

`Psi_G` is `eq:substitution`, `Psi_compCuts` and `Psi_revCuts` are `eq:Psi-laws`, `proj` is the
ring homomorphism `π_p` of `eq:projection` and `proj_Psi` is `eq:split`.  The identities are
integral (`Lam = ℤ[h₁, h₂, …]`) and hold verbatim over any commutative coefficient ring.
`reversal_suffices` is `cor:reversal-suffices`, for the right-nested composition product
`compProd` of a list of compositions.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset MvPolynomial

lemma G_empty (n : ℕ) : G n ∅ = hgen n := by
  simp [G, gaps]

lemma compCuts_isCutSet {m : ℕ} {A : Finset ℕ} {p : ℕ} {E : Finset ℕ} (hp : 0 < p)
    (hA : IsCutSet m A) (hE : IsCutSet p E) : IsCutSet (m * p) (compCuts m A p E) := by
  intro x hx
  rw [mem_compCuts] at hx
  rcases hx with ⟨y, hy, rfl⟩ | ⟨j, hj, e, he, rfl⟩
  · have := Finset.mem_Ioo.mp (hA hy)
    refine Finset.mem_Ioo.mpr ⟨Nat.mul_pos hp this.1, ?_⟩
    rw [mul_comm m p]
    exact Nat.mul_lt_mul_of_pos_left this.2 hp
  · have := Finset.mem_Ioo.mp (hE he)
    refine Finset.mem_Ioo.mpr ⟨by omega, ?_⟩
    calc j * p + e < j * p + p := by omega
      _ = (j + 1) * p := by ring
      _ ≤ m * p := Nat.mul_le_mul_right _ hj

lemma nearPowerCuts_isCutSet {n : ℕ} {E : Finset ℕ} (hE : IsCutSet n E) (j : ℕ) :
    IsCutSet (j * n) (nearPowerCuts n E j) := by
  intro x hx
  rw [mem_nearPowerCuts] at hx
  obtain ⟨i, hi, e, he, rfl⟩ := hx
  have := Finset.mem_Ioo.mp (hE he)
  refine Finset.mem_Ioo.mpr ⟨by omega, ?_⟩
  calc i * n + e < i * n + n := by omega
    _ = (i + 1) * n := by ring
    _ ≤ j * n := Nat.mul_le_mul_right _ hi

lemma concatCuts_eq_insert (n : ℕ) (S S' : Finset ℕ) :
    concatCuts n S S' = insert n (nearCuts n S S') := by
  simp only [concatCuts, nearCuts]
  rw [Finset.union_right_comm, Finset.union_comm _ {n}]
  rfl

lemma compCuts_empty (j p : ℕ) (E : Finset ℕ) : compCuts j ∅ p E = nearPowerCuts p E j := by
  simp [compCuts, nearPowerCuts]

lemma compCuts_insert (m : ℕ) (y : ℕ) (A : Finset ℕ) (p : ℕ) (E : Finset ℕ) :
    compCuts m (insert y A) p E = insert (p * y) (compCuts m A p E) := by
  simp only [compCuts, Finset.image_insert, Finset.insert_union]

/-- Splitting the outer composition at its last cut `m'`: the composition product of the whole
is the near-concatenation of the product of the head with the near-power of the inner factor. -/
lemma compCuts_split {m' m : ℕ} (h : m' ≤ m) (A1 : Finset ℕ) (p : ℕ) (E : Finset ℕ) :
    compCuts m A1 p E
      = nearCuts (m' * p) (compCuts m' A1 p E) (nearPowerCuts p E (m - m')) := by
  obtain ⟨t, rfl⟩ : ∃ t, m = m' + t := ⟨m - m', by omega⟩
  rw [Nat.add_sub_cancel_left]
  ext x
  simp only [nearCuts, mem_compCuts, mem_nearPowerCuts, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨y, hy, rfl⟩ | ⟨j, hj, e, he, rfl⟩)
    · exact Or.inl (Or.inl ⟨y, hy, rfl⟩)
    · by_cases hjm : j < m'
      · exact Or.inl (Or.inr ⟨j, hjm, e, he, rfl⟩)
      · refine Or.inr ⟨(j - m') * p + e, ⟨j - m', by omega, e, he, rfl⟩, ?_⟩
        have : m' * p + (j - m') * p = j * p := by
          rw [← Nat.add_mul]; congr 1; omega
        omega
  · rintro ((⟨y, hy, rfl⟩ | ⟨j, hj, e, he, rfl⟩) | ⟨z, ⟨i, hi, e, he, rfl⟩, rfl⟩)
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨j, by omega, e, he, rfl⟩
    · refine Or.inr ⟨m' + i, by omega, e, he, ?_⟩
      have : (m' + i) * p = m' * p + i * p := by ring
      omega

/-- `eq:substitution`: `Ψ_ε(G_α) = G_{α ∘ ε}`, with `α` of weight `m` and cut set `A`, and the
inner composition `ε` of weight `n > 0` and cut set `E`.

**Differs from the paper's route.**  Induction on the number of cuts of `α`, splitting off its
last cut with `eq:seam` and `compCuts_split`, instead of grouping the coarsenings of `α ∘ ε` by
their retained outer seams. -/
theorem Psi_G (n : ℕ) (E : Finset ℕ) (hn : 0 < n) (hE : IsCutSet n E) :
    ∀ (m : ℕ) (A : Finset ℕ), IsCutSet m A →
      Psi n E (G m A) = G (m * n) (compCuts m A n E) := by
  have hPsi : ∀ j : ℕ, Psi n E (hgen j) = G (j * n) (nearPowerCuts n E j) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [hgen, G, gaps, nearPowerCuts]
    · have h1 : hgen j = MvPolynomial.X (Nat.toPNat j hj) := by simp [hgen, hj]; rfl
      rw [h1, Psi, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      rfl
  intro m A
  obtain ⟨c, hc⟩ : ∃ c, A.card = c := ⟨_, rfl⟩
  induction c generalizing m A with
  | zero =>
    intro _
    rw [Finset.card_eq_zero] at hc
    subst hc
    rw [G_empty, hPsi, compCuts_empty]
  | succ c ih =>
    intro hA
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    set m' := A.max' hne with hm'
    have hm'A : m' ∈ A := Finset.max'_mem A hne
    have hm'b := Finset.mem_Ioo.mp (hA hm'A)
    set A1 := A.erase m' with hA1
    have hA1m : IsCutSet m' A1 := by
      intro x hx
      have hxA := Finset.mem_of_mem_erase hx
      have hxm : x ≠ m' := Finset.ne_of_mem_erase hx
      have := Finset.le_max' A x hxA
      exact Finset.mem_Ioo.mpr ⟨(Finset.mem_Ioo.mp (hA hxA)).1, lt_of_le_of_ne this hxm⟩
    have hA1m2 : IsCutSet m A1 := fun x hx => Finset.mem_Ioo.mpr
      ⟨(Finset.mem_Ioo.mp (hA1m hx)).1, by have := (Finset.mem_Ioo.mp (hA1m hx)).2; omega⟩
    have hAins : A = insert m' A1 := (Finset.insert_erase hm'A).symm
    have hAeq : A = concatCuts m' A1 ∅ := by
      rw [concatCuts_eq_insert, hAins]
      simp [nearCuts]
    have hcard : A1.card = c := by rw [hA1, Finset.card_erase_of_mem hm'A]; omega
    have hseam := G_concat_cuts m' (m - m') A1 ∅ hm'b.1 (by omega) hA1m (fun x hx => by simp at hx)
    rw [show m' + (m - m') = m by omega, ← hAeq, G_empty] at hseam
    have hnc : nearCuts m' A1 ∅ = A1 := by simp [nearCuts]
    rw [hnc] at hseam
    rw [hseam, map_add, map_mul, ih m' A1 hcard hA1m, ih m A1 hcard hA1m2, hPsi]
    have hN : IsCutSet (m' * n) (compCuts m' A1 n E) := compCuts_isCutSet hn hA1m hE
    have hN' : IsCutSet ((m - m') * n) (nearPowerCuts n E (m - m')) :=
      nearPowerCuts_isCutSet hE _
    have hmm : 0 < m - m' := by omega
    have hseam2 := G_concat_cuts (m' * n) ((m - m') * n) (compCuts m' A1 n E)
      (nearPowerCuts n E (m - m')) (Nat.mul_pos hm'b.1 hn) (Nat.mul_pos hmm hn) hN hN'
    have hnear : nearCuts (m' * n) (compCuts m' A1 n E) (nearPowerCuts n E (m - m'))
        = compCuts m A1 n E := (compCuts_split hm'b.2.le A1 n E).symm
    have hconc : concatCuts (m' * n) (compCuts m' A1 n E) (nearPowerCuts n E (m - m'))
        = compCuts m A n E := by
      rw [concatCuts_eq_insert, hnear, hAins, compCuts_insert, mul_comm n m']
    rw [hnear, hconc, show m' * n + (m - m') * n = m * n by
      rw [← Nat.add_mul]; congr 1; omega] at hseam2
    rw [hseam2]

/-- `nearPowerCuts` commutes with reversal: `(ε^{⊙ j})* = (ε*)^{⊙ j}` at the level of cut sets. -/
lemma revCuts_nearPowerCuts {n : ℕ} {E : Finset ℕ} (hE : IsCutSet n E) (j : ℕ) :
    revCuts (j * n) (nearPowerCuts n E j) = nearPowerCuts n (revCuts n E) j := by
  ext x
  rw [revCuts_mem]
  simp only [mem_nearPowerCuts, revCuts_mem]
  constructor
  · rintro ⟨y, ⟨i, hi, e, he, rfl⟩, rfl⟩
    have hen := Finset.mem_Ioo.mp (hE he)
    obtain ⟨t, rfl⟩ : ∃ t, j = i + 1 + t := ⟨j - (i + 1), by omega⟩
    refine ⟨t, by omega, n - e, ⟨e, he, rfl⟩, ?_⟩
    have : (i + 1 + t) * n = i * n + n + t * n := by ring
    omega
  · rintro ⟨i, hi, z, ⟨e, he, rfl⟩, rfl⟩
    have hen := Finset.mem_Ioo.mp (hE he)
    obtain ⟨t, rfl⟩ : ∃ t, j = i + 1 + t := ⟨j - (i + 1), by omega⟩
    refine ⟨t * n + e, ⟨t, by omega, e, he, rfl⟩, ?_⟩
    have : (i + 1 + t) * n = i * n + n + t * n := by ring
    omega

lemma ringHom_ext_Lam {R : Type*} [CommRing R] (f g : Lam →+* R)
    (h : ∀ j : ℕ+, f (MvPolynomial.X j) = g (MvPolynomial.X j)) : f = g := by
  apply MvPolynomial.ringHom_ext
  · intro r
    have : (MvPolynomial.C r : Lam) = (r : Lam) := by simp
    rw [this, map_intCast, map_intCast]
  · exact h

lemma hgen_pnat (j : ℕ+) : hgen (j : ℕ) = MvPolynomial.X j := by
  simp only [hgen, j.pos, dite_true]
  rfl

lemma Psi_hgen (n : ℕ) (E : Finset ℕ) (j : ℕ) :
    Psi n E (hgen j) = G (j * n) (nearPowerCuts n E j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hgen, G, gaps, nearPowerCuts]
  · have h1 : hgen j = MvPolynomial.X (Nat.toPNat j hj) := by simp [hgen, hj]; rfl
    rw [h1, Psi, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    rfl

/-- `eq:Psi-laws`, first identity: `Ψ_{α ∘ ε} = Ψ_ε Ψ_α`, for `α` of weight `m` with cut set `A`
and `ε` of weight `p > 0` with cut set `E`. -/
theorem Psi_compCuts {m p : ℕ} {A E : Finset ℕ} (hp : 0 < p) (hA : IsCutSet m A)
    (hE : IsCutSet p E) : Psi (m * p) (compCuts m A p E) = (Psi p E).comp (Psi m A) := by
  apply ringHom_ext_Lam
  intro j
  rw [← hgen_pnat, RingHom.comp_apply, Psi_hgen, Psi_hgen,
    Psi_G p E hp hE (j * m) _ (nearPowerCuts_isCutSet hA j), nearPowerCuts_compCuts,
    mul_assoc]

/-- `eq:Psi-laws`, second identity: `Ψ_{ε*} = Ψ_ε`. -/
theorem Psi_revCuts {n : ℕ} {E : Finset ℕ} (hE : IsCutSet n E) :
    Psi n (revCuts n E) = Psi n E := by
  apply ringHom_ext_Lam
  intro j
  rw [← hgen_pnat, Psi_hgen, Psi_hgen, ← revCuts_nearPowerCuts hE]
  exact G_revCuts _ _ (nearPowerCuts_isCutSet hE j)

/-- `eq:projection`: the ring homomorphism `π_p`, `h_j ↦ h_{j/p}` if `p ∣ j`, and `0`
otherwise. -/
noncomputable def proj (p : ℕ) : Lam →+* Lam :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℤ →+* Lam)
    (fun j : ℕ+ => if p ∣ (j : ℕ) then hgen ((j : ℕ) / p) else 0)

lemma proj_hgen (p j : ℕ) : proj p (hgen j) = if p ∣ j then hgen (j / p) else 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hgen, proj]
  · have h1 : hgen j = MvPolynomial.X (Nat.toPNat j hj) := by simp [hgen, hj]; rfl
    rw [h1, proj, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    rfl

/-- The least retained cut is a block length. -/
lemma min_mem_gaps {n : ℕ} {T : Finset ℕ} (hT : T.Nonempty) : T.min' hT ∈ gaps n T := by
  unfold gaps
  rw [Multiset.mem_map]
  refine ⟨T.min' hT, ?_, ?_⟩
  · simp [Finset.min'_mem]
  · have : T.filter (· < T.min' hT) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      rw [Finset.mem_filter] at hx
      exact absurd hx.2 (not_lt.mpr (Finset.min'_le T x hx.1))
    rw [this]; simp

/-- `eq:split`: `π_p Ψ_ε = id`, for the inner composition of weight `p > 0` with cut set `E`. -/
theorem proj_Psi {p : ℕ} {E : Finset ℕ} (hp : 0 < p) (hE : IsCutSet p E) :
    (proj p).comp (Psi p E) = RingHom.id Lam := by
  apply ringHom_ext_Lam
  intro j
  rw [← hgen_pnat, RingHom.comp_apply, Psi_hgen, RingHom.id_apply]
  have hj := j.pos
  unfold G
  rw [map_sum, Finset.sum_eq_single ∅]
  · have hdvd : p ∣ (j : ℕ) * p := dvd_mul_left p _
    rw [gaps_empty, Multiset.map_singleton, Multiset.prod_singleton, proj_hgen _ _]
    simp [hdvd, Nat.mul_div_cancel _ hp]
  · intro T hT hne
    have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    rw [Finset.mem_powerset] at hT
    have hmem : T.min' hTne ∈ nearPowerCuts p E (j : ℕ) := hT (Finset.min'_mem T hTne)
    have hnd : ¬ p ∣ T.min' hTne := by
      obtain ⟨i, _, e, he, hx⟩ := mem_nearPowerCuts.mp hmem
      have he' := Finset.mem_Ioo.mp (hE he)
      rw [← hx]
      intro hd
      have : p ∣ e := (Nat.dvd_add_right (dvd_mul_left p i)).mp hd
      exact absurd (Nat.le_of_dvd he'.1 this) (by omega)
    rw [map_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_zero
    rw [Multiset.mem_map]
    refine ⟨T.min' hTne, min_mem_gaps hTne, ?_⟩
    simp [Function.comp, proj_hgen _ _, hnd]
  · intro h
    exact absurd (Finset.empty_mem_powerset _) h

/-- `prop:unsigned`, cut-set form: `eq:seam`, `eq:substitution`, `eq:Psi-laws` and `eq:split`
for compositions given by weights and cut sets (`α`: weight `m`, cuts `A`; `ε`: weight `p > 0`,
cuts `E`; `β`: weight `n'`, cuts `S'`; `α`, `β` of positive weight for the seam identity). -/
theorem prop_unsigned :
    (∀ (m n' : ℕ) (A S' : Finset ℕ), 0 < m → 0 < n' → IsCutSet m A → IsCutSet n' S' →
      G (m + n') (concatCuts m A S') = G m A * G n' S' + G (m + n') (nearCuts m A S')) ∧
    (∀ (m p : ℕ) (A E : Finset ℕ), 0 < p → IsCutSet m A → IsCutSet p E →
      Psi p E (G m A) = G (m * p) (compCuts m A p E)) ∧
    (∀ (m p : ℕ) (A E : Finset ℕ), 0 < p → IsCutSet m A → IsCutSet p E →
      Psi (m * p) (compCuts m A p E) = (Psi p E).comp (Psi m A)) ∧
    (∀ (p : ℕ) (E : Finset ℕ), IsCutSet p E → Psi p (revCuts p E) = Psi p E) ∧
    (∀ (p : ℕ) (E : Finset ℕ), 0 < p → IsCutSet p E → (proj p).comp (Psi p E) = RingHom.id Lam) :=
  ⟨fun _ _ _ _ hm hn' hA hS' => G_concat_cuts _ _ _ _ hm hn' hA hS',
    fun _ p _ _ hp hA hE => Psi_G p _ hp hE _ _ hA,
    fun _ _ _ _ hp hA hE => Psi_compCuts hp hA hE,
    fun _ _ hE => Psi_revCuts hE,
    fun _ _ hp hE => proj_Psi hp hE⟩

/-! ### `cor:reversal-suffices` -/

/-- The substitution homomorphism `Ψ_ε` of a composition given as a list of parts. -/
noncomputable def PsiParts (ε : List ℕ) : Lam →+* Lam := Psi ε.sum (partsCuts ε)

/-- `G_α = Ψ_α(h₁)`: evaluation of the substitution at `h₁`. -/
lemma Gparts_eq_PsiParts_h1 (α : List ℕ) : Gparts α = PsiParts α (hgen 1) := by
  rw [PsiParts, Psi_hgen, Gparts]
  simp only [one_mul]
  rw [show nearPowerCuts α.sum (partsCuts α) 1 = partsCuts α by
    simp [nearPowerCuts]]

/-- `eq:substitution`, list form: `Ψ_ε(G_α) = G_{α ∘ ε}`. -/
theorem PsiParts_Gparts {α ε : List ℕ} (hα : IsParts α) (hε : IsParts ε) (hε0 : ε ≠ []) :
    PsiParts ε (Gparts α) = Gparts (compose α ε) := by
  have hp := sum_pos_of_ne_nil hε hε0
  rw [PsiParts, Gparts, Psi_G _ _ hp (partsCuts_isCutSet hε) _ _ (partsCuts_isCutSet hα),
    Gparts, sum_compose, partsCuts_compose hα hε0]

/-- `eq:Psi-laws`, list form: `Ψ_{α ∘ ε} = Ψ_ε Ψ_α`. -/
theorem PsiParts_compose {α ε : List ℕ} (hα : IsParts α) (hε : IsParts ε) (hε0 : ε ≠ []) :
    PsiParts (compose α ε) = (PsiParts ε).comp (PsiParts α) := by
  have hp := sum_pos_of_ne_nil hε hε0
  rw [PsiParts, PsiParts, PsiParts, sum_compose, partsCuts_compose hα hε0]
  exact Psi_compCuts hp (partsCuts_isCutSet hα) (partsCuts_isCutSet hε)

/-- `eq:Psi-laws`, list form: `Ψ_{ε*} = Ψ_ε`. -/
theorem PsiParts_reverse {ε : List ℕ} (hε : IsParts ε) :
    PsiParts ε.reverse = PsiParts ε := by
  rw [PsiParts, PsiParts, List.sum_reverse, partsCuts_reverse hε]
  exact Psi_revCuts (partsCuts_isCutSet hε)

/-- `G_{α*} = G_α` for a list of parts. -/
theorem Gparts_reverse {α : List ℕ} (hα : IsParts α) : Gparts α.reverse = Gparts α := by
  rw [Gparts, Gparts, List.sum_reverse, partsCuts_reverse hα]
  exact G_revCuts _ _ (partsCuts_isCutSet hα)

/-- Reverse a factor when the flag is set. -/
def revIf (b : Bool) (α : List ℕ) : List ℕ := if b then α.reverse else α

lemma isParts_revIf {b : Bool} {α : List ℕ} (h : IsParts α) : IsParts (revIf b α) := by
  cases b
  · simpa [revIf] using h
  · intro x hx; exact h x (List.mem_reverse.mp (by simpa [revIf] using hx))

lemma revIf_ne_nil {b : Bool} {α : List ℕ} (h : α ≠ []) : revIf b α ≠ [] := by
  cases b <;> simpa [revIf] using h

lemma PsiParts_revIf {b : Bool} {α : List ℕ} (h : IsParts α) :
    PsiParts (revIf b α) = PsiParts α := by
  cases b
  · rfl
  · exact PsiParts_reverse h

lemma isParts_compProd : ∀ αs : List (List ℕ), (∀ α ∈ αs, IsParts α ∧ α ≠ []) →
    IsParts (compProd αs) ∧ compProd αs ≠ []
  | [], _ => ⟨fun a ha => by simp [compProd] at ha; omega, by simp [compProd]⟩
  | α :: αs, h => by
    obtain ⟨h1, h2⟩ := isParts_compProd αs (fun x hx => h x (List.mem_cons_of_mem _ hx))
    obtain ⟨h3, h4⟩ := h α (by simp)
    exact ⟨isParts_compose h1, compose_ne_nil h4 h2 h3⟩

/-- The substitution of a composition product only depends on the factors up to reversal:
`Ψ_{α₁^{s₁} ∘ ⋯ ∘ α_r^{s_r}} = Ψ_{α₁ ∘ ⋯ ∘ α_r}`, by `eq:Psi-laws` applied successively. -/
theorem PsiParts_compProd_revIf : ∀ (αs : List (List ℕ)), (∀ α ∈ αs, IsParts α ∧ α ≠ []) →
    ∀ fl : List Bool, fl.length = αs.length →
    PsiParts (compProd (List.zipWith revIf fl αs)) = PsiParts (compProd αs)
  | [], _, fl, hlen => by
    have : fl = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst this; rfl
  | α :: αs, h, fl, hlen => by
    cases fl with
    | nil => simp at hlen
    | cons b fl =>
      have hlen' : fl.length = αs.length := by simpa using hlen
      have h' : ∀ x ∈ αs, IsParts x ∧ x ≠ [] := fun x hx => h x (List.mem_cons_of_mem _ hx)
      obtain ⟨hα, hα0⟩ := h α (by simp)
      obtain ⟨hC, hC0⟩ := isParts_compProd αs h'
      have hC' := isParts_compProd (List.zipWith revIf fl αs) (by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        simp only [List.getElem_zipWith]
        have := h' (αs[i]'(by simpa [hlen'] using hi)) (List.getElem_mem _)
        exact ⟨isParts_revIf this.1, revIf_ne_nil this.2⟩)
      simp only [List.zipWith_cons_cons, compProd]
      rw [PsiParts_compose (isParts_revIf hα) hC'.1 hC'.2, PsiParts_compose hα hC hC0,
        PsiParts_revIf hα, PsiParts_compProd_revIf αs h' fl hlen']

/-- `cor:reversal-suffices`.  Let `β = α₁ ∘ α₂ ∘ ⋯ ∘ α_r` be a composition factorization
(`compProd`, right-nested, which is no restriction since `∘` is associative).  Reversing any
specified factors preserves `G`: for any flags `s`, `G_{α₁^{s₁} ∘ ⋯ ∘ α_r^{s_r}} = G_β`.
The proof uses only `eq:Psi-laws` and the evaluation `G_β = Ψ_β(h₁)`; no recognition theorem. -/
theorem reversal_suffices (αs : List (List ℕ)) (hα : ∀ α ∈ αs, IsParts α ∧ α ≠ [])
    (fl : List Bool) (hlen : fl.length = αs.length) :
    Gparts (compProd (List.zipWith revIf fl αs)) = Gparts (compProd αs) := by
  rw [Gparts_eq_PsiParts_h1, Gparts_eq_PsiParts_h1, PsiParts_compProd_revIf αs hα fl hlen]

end SkewRibbonCoarsenings
