/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/Recognition.lean
import SkewRibbonCoarsenings.Coordinates
import SkewRibbonCoarsenings.LocalAlternative

/-!
# Recognition by descent

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:recognition`
(`thm:coarse`, `eq:coarse-certificate`, `eq:coefficient-grid`, `rem:shallow-induction`,
`prop:budget`, `cor:modular-budget`).

A factor-reversal witness (`FactorWitness`) is a pair of factorizations
`β = δ₁ ∘ ⋯ ∘ δ_s`, `γ = ε₁ ∘ ⋯ ∘ ε_s` with `ε_i ∈ {δ_i, δ_i*}`.  Compositions are given by
their weight and cut set; the factorization is a list of factors written as lists of parts
(`compProd δs` is the right-nested product of `PartsAndCuts`), and the second side is
`compProd (List.zipWith revIf fl δs)` for a list `fl` of reversal flags, the form in which
`reversal_suffices` is stated.

Everything is conditional on the single interface `LocalAlternative H` of `LocalAlternative.lean`
(`prop:local-alternative`), carried as the explicit hypothesis `hLA`.
`coarse_recognition_of_budget` proves `thm:coarse` once for an arbitrary budget `H` monotone under
divisibility (`prop:budget`), and `coarse_recognition` specializes it to `Ω(n) + 2`.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

/-! ### Scaling a cut set by `p` -/

lemma sup_image_mul_left (p : ℕ) (U : Finset ℕ) : (U.image (p * ·)).sup id = p * U.sup id := by
  rw [Finset.sup_image]
  induction U using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sup_insert, ← ih, mul_max_of_nonneg]

/-- The block lengths of the coarsening retaining the scaled cuts `p T` of weight `m p` are `p`
times the block lengths of the coarsening retaining `T` of weight `m`. -/
lemma gaps_scale {p : ℕ} (hp : 0 < p) (m : ℕ) (T : Finset ℕ) :
    gaps (m * p) (T.image (p * ·)) = (gaps m T).map (p * ·) := by
  have hinj : Function.Injective (p * · : ℕ → ℕ) := fun a b h => Nat.eq_of_mul_eq_mul_left hp h
  have h1 : insert (m * p) (T.image (p * ·)) = (insert m T).image (p * ·) := by
    rw [Finset.image_insert, mul_comm m p]
  unfold gaps
  rw [h1, Finset.image_val_of_injOn hinj.injOn, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  simp only [Function.comp_apply]
  have h2 : ((T.image (p * ·)).filter (· < p * x)) = (T.filter (· < x)).image (p * ·) := by
    rw [Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro a _
    exact Nat.mul_lt_mul_left hp
  rw [h2, sup_image_mul_left, Nat.mul_sub]

/-- If every block length of a coarsening is divisible by `p`, so is every retained cut. -/
lemma dvd_of_dvd_gaps {p : ℕ} : ∀ (T : Finset ℕ) {n : ℕ}, IsCutSet n T →
    (∀ g ∈ gaps n T, p ∣ g) → ∀ t ∈ T, p ∣ t := by
  intro T
  induction T using Finset.induction_on_max with
  | empty => intro n _ _ t ht; simp at ht
  | insert a s ha ih =>
    intro n hT hg t ht
    have han : a < n := (Finset.mem_Ioo.mp (hT (Finset.mem_insert_self a s))).2
    have hsum := sum_gaps hT
    have hpn : p ∣ n := by
      rw [← hsum]
      exact Multiset.dvd_sum hg
    rw [gaps_insert_max han ha] at hg
    have hna : p ∣ n - a := hg _ (Multiset.mem_cons_self _ _)
    have hpa : p ∣ a := by
      have := Nat.dvd_sub hpn hna
      rwa [show n - (n - a) = a by omega] at this
    rcases Finset.mem_insert.mp ht with rfl | hts
    · exact hpa
    · refine ih ?_ (fun g hg' => hg g (Multiset.mem_cons_of_mem hg')) t hts
      intro x hx
      exact Finset.mem_Ioo.mpr ⟨(Finset.mem_Ioo.mp (hT (Finset.mem_insert_of_mem hx))).1, ha x hx⟩

/-- `eq:coefficient-grid`, general form: for `β = δ ∘ ε` with outer cut set `A` of weight `m` and
inner cut set `E` of weight `p`, the coefficient of `h_{pμ}` in `G_β` is the coefficient of `h_μ`
in `G_δ`, for every multiset `μ`. -/
theorem mult_scale {m p : ℕ} {A E : Finset ℕ} (hp : 0 < p) (hA : IsCutSet m A) (hE : IsCutSet p E)
    (lam : Multiset ℕ) :
    mult (m * p) (compCuts m A p E) (lam.map (p * ·)) = mult m A lam := by
  have hinj : Function.Injective (p * · : ℕ → ℕ) := fun a b h => Nat.eq_of_mul_eq_mul_left hp h
  have hSc : IsCutSet (m * p) (compCuts m A p E) := compCuts_isCutSet hp hA hE
  unfold mult
  refine (Finset.card_bij (fun T0 _ => T0.image (p * ·)) ?_ ?_ ?_).symm
  · intro T0 hT0
    rw [Finset.mem_filter, Finset.mem_powerset] at hT0 ⊢
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact mem_compCuts.mpr (Or.inl ⟨a, hT0.1 ha, rfl⟩)
    · rw [gaps_scale hp, hT0.2]
  · intro T0 _ T1 _ h
    exact Finset.image_injective hinj h
  · intro T hT
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    have hTc : IsCutSet (m * p) T := fun x hx => hSc (hT.1 hx)
    have hdvd : ∀ t ∈ T, p ∣ t := by
      refine dvd_of_dvd_gaps T hTc fun g hg => ?_
      rw [hT.2] at hg
      obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hg
      exact dvd_mul_right p y
    have himg : (T.image (· / p)).image (p * ·) = T := by
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨z, ⟨t, ht, rfl⟩, rfl⟩
        rwa [Nat.mul_div_cancel' (hdvd t ht)]
      · intro hx
        exact ⟨x / p, ⟨x, hx, rfl⟩, Nat.mul_div_cancel' (hdvd x hx)⟩
    have hsubA : T.image (· / p) ⊆ A := by
      intro y hy
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
      have := hT.1 ht
      rw [← Nat.mul_div_cancel' (hdvd t ht)] at this
      exact (mem_compCuts_of_dvd hp hE _).mp this
    refine ⟨T.image (· / p), ?_, himg⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hsubA, ?_⟩
    have h := hT.2
    rw [← himg, gaps_scale hp] at h
    exact Multiset.map_injective hinj h

/-! ### Reversal and equality of the inventories at the level of multiplicities -/

lemma mult_eq_of_G_eq {n : ℕ} (hn : 0 < n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') (h : G n S = G n S') {lam : Multiset ℕ} (hlam : ∀ x ∈ lam, 0 < x) :
    mult n S lam = mult n S' lam := by
  have h1 := coeff_G hn hS lam hlam
  have h2 := coeff_G hn hS' lam hlam
  rw [h] at h1
  exact_mod_cast h1.symm.trans h2

lemma mult_revCuts {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S) {lam : Multiset ℕ}
    (hlam : ∀ x ∈ lam, 0 < x) : mult n (revCuts n S) lam = mult n S lam :=
  mult_eq_of_G_eq hn (revCuts_isCutSet hS) hS (G_revCuts n S hS) hlam

lemma distinctExceptPair_map_mul {p : ℕ} (hp : 0 < p) {lam : Multiset ℕ}
    (h : DistinctExceptPair lam) : DistinctExceptPair (lam.map (p * ·)) := by
  have hinj : Function.Injective (p * · : ℕ → ℕ) := fun a b h => Nat.eq_of_mul_eq_mul_left hp h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun j => ?_, ?_⟩
  · by_cases hj : ∃ i, p * i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [Multiset.count_map_eq_count' (p * ·) lam hinj i]
      exact h1 i
    · rw [Multiset.count_eq_zero_of_notMem]
      · omega
      · intro hmem
        obtain ⟨y, _, hy⟩ := Multiset.mem_map.mp hmem
        exact hj ⟨y, hy⟩
  · refine le_trans (Finset.card_le_card ?_) ((Finset.card_image_le (f := (p * ·))).trans h2)
    intro j hj
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hj
    obtain ⟨hjm, hjc⟩ := hj
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hjm
    rw [Multiset.count_map_eq_count' (p * ·) lam hinj y] at hjc
    exact Finset.mem_image.mpr ⟨y, by simp [hy, hjc], rfl⟩

/-! ### Certificates lift through the grid and through reversal -/

lemma CoarseCertificate.scale {H : ℕ → ℕ} {m p : ℕ} {A A' E : Finset ℕ} {lam : Multiset ℕ}
    (hp : 0 < p) (hA : IsCutSet m A) (hA' : IsCutSet m A') (hE : IsCutSet p E)
    (hH : H m ≤ H (m * p)) (h : CoarseCertificate H m A A' lam) :
    CoarseCertificate H (m * p) (compCuts m A p E) (compCuts m A' p E) (lam.map (p * ·)) := by
  obtain ⟨hpos, hsum, hcard, hdiff, hd⟩ := h
  refine ⟨?_, ?_, ?_, ?_, distinctExceptPair_map_mul hp hd⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    exact Nat.mul_pos hp (hpos y hy)
  · have := Multiset.sum_map_mul_left (a := p) (s := lam) (f := id)
    simp only [id, Multiset.map_id'] at this
    rw [this, hsum, mul_comm]
  · rw [Multiset.card_map]
    exact hcard.trans hH
  · rw [mult_scale hp hA hE, mult_scale hp hA' hE]
    exact hdiff

lemma CoarseCertificate.rev_right {H : ℕ → ℕ} {n : ℕ} {S S' : Finset ℕ} {lam : Multiset ℕ}
    (hn : 0 < n) (hS' : IsCutSet n S') (h : CoarseCertificate H n S S' lam) :
    CoarseCertificate H n S (revCuts n S') lam := by
  obtain ⟨hpos, hsum, hcard, hdiff, hd⟩ := h
  refine ⟨hpos, hsum, hcard, ?_, hd⟩
  rw [mult_revCuts hn hS' hpos]
  exact hdiff

/-! ### Factorizations of compositions as lists of factors -/

lemma nearPow_one_part (a : ℕ) : nearPow [1] (a + 1) = [a + 1] := by
  induction a with
  | zero => rfl
  | succ a ih => rw [nearPow_succ, ih]; rfl

/-- `α ∘ (1) = α`. -/
lemma compose_one_right {α : List ℕ} (hα : IsParts α) : compose α [1] = α := by
  induction α with
  | nil => simp [compose]
  | cons a α ih =>
    have ha : 0 < a := hα a (by simp)
    obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    rw [compose_cons, nearPow_one_part, ih (isParts_tail hα)]
    rfl

lemma compProd_singleton {δ : List ℕ} (hδ : IsParts δ) : compProd [δ] = δ := by
  show compose δ [1] = δ
  exact compose_one_right hδ

lemma compProd_append_singleton {ε : List ℕ} (hε : IsParts ε) :
    ∀ l : List (List ℕ), (∀ α ∈ l, IsParts α ∧ α ≠ []) →
      compProd (l ++ [ε]) = compose (compProd l) ε
  | [], _ => by
    rw [List.nil_append, compProd_singleton hε]
    simp [compProd, compose, nearPow, nearConcat]
  | α :: l, h => by
    have h' : ∀ x ∈ l, IsParts x ∧ x ≠ [] := fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨hα, _⟩ := h α (by simp)
    rw [List.cons_append]
    show compose α (compProd (l ++ [ε])) = compose (compose α (compProd l)) ε
    rw [compProd_append_singleton hε l h', compose_assoc hα (isParts_compProd l h').1 hε]

lemma compProd_reverse :
    ∀ l : List (List ℕ), (∀ α ∈ l, IsParts α ∧ α ≠ []) →
      (compProd l).reverse = compProd (l.map List.reverse)
  | [], _ => rfl
  | α :: l, h => by
    have h' : ∀ x ∈ l, IsParts x ∧ x ≠ [] := fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨hα, _⟩ := h α (by simp)
    show (compose α (compProd l)).reverse = compose α.reverse (compProd (l.map List.reverse))
    rw [compose_reverse hα (isParts_compProd l h').1, compProd_reverse l h']

lemma zipWith_revIf_not : ∀ (fl : List Bool) (δs : List (List ℕ)), fl.length = δs.length →
    List.zipWith revIf (fl.map (!·)) δs = (List.zipWith revIf fl δs).map List.reverse
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | b :: fl, δ :: δs, h => by
    have h' : fl.length = δs.length := by simpa using h
    simp only [List.map_cons, List.zipWith_cons_cons]
    rw [zipWith_revIf_not fl δs h']
    congr 1
    cases b <;> simp [revIf]

lemma sum_revIf (b : Bool) (α : List ℕ) : (revIf b α).sum = α.sum := by
  cases b <;> simp [revIf]

lemma sum_compProd_revIf : ∀ (fl : List Bool) (δs : List (List ℕ)), fl.length = δs.length →
    (compProd (List.zipWith revIf fl δs)).sum = (compProd δs).sum
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | b :: fl, δ :: δs, h => by
    have h' : fl.length = δs.length := by simpa using h
    simp only [List.zipWith_cons_cons, compProd, sum_compose, sum_revIf]
    rw [sum_compProd_revIf fl δs h']

/-- A factor-reversal witness for the compositions of weight `n` with cut sets `S, S'`:
factorizations `β = δ₁ ∘ ⋯ ∘ δ_s` and `γ = ε₁ ∘ ⋯ ∘ ε_s` with `ε_i ∈ {δ_i, δ_i*}`
(`thm:main-structure`, third statement).  The factors are nonempty lists of positive parts, the
list `fl` records which factors are reversed on the second side, and `compProd` is the right-nested
composition product (`∘` is associative). -/
def FactorWitness (n : ℕ) (S S' : Finset ℕ) : Prop :=
  ∃ (δs : List (List ℕ)) (fl : List Bool), (∀ δ ∈ δs, IsParts δ ∧ δ ≠ []) ∧
    fl.length = δs.length ∧ (compProd δs).sum = n ∧ partsCuts (compProd δs) = S ∧
    partsCuts (compProd (List.zipWith revIf fl δs)) = S'

/-- A factor witness preserves the complete inventory (`cor:reversal-suffices`). -/
theorem FactorWitness.G_eq {n : ℕ} {S S' : Finset ℕ} (h : FactorWitness n S S') :
    G n S = G n S' := by
  obtain ⟨δs, fl, hδ, hfl, hs, hc, hc'⟩ := h
  have := reversal_suffices δs hδ fl hfl
  rw [Gparts, Gparts, sum_compProd_revIf fl δs hfl, hs, hc, hc'] at this
  exact this.symm

/-- A factor witness gives equality of the substitution maps (`eq:Psi-laws`). -/
theorem FactorWitness.Psi_eq {n : ℕ} {S S' : Finset ℕ} (h : FactorWitness n S S') :
    Psi n S = Psi n S' := by
  obtain ⟨δs, fl, hδ, hfl, hs, hc, hc'⟩ := h
  have := PsiParts_compProd_revIf δs hδ fl hfl
  rw [PsiParts, PsiParts, sum_compProd_revIf fl δs hfl, hs, hc, hc'] at this
  exact this.symm

lemma FactorWitness.one_le {n : ℕ} {S S' : Finset ℕ} (h : FactorWitness n S S') : 1 ≤ n := by
  obtain ⟨δs, fl, hδ, hfl, hs, hc, hc'⟩ := h
  have := sum_pos_of_ne_nil (isParts_compProd δs hδ).1 (isParts_compProd δs hδ).2
  omega

lemma FactorWitness.refl {n : ℕ} (hn : 1 ≤ n) {S : Finset ℕ} (hS : IsCutSet n S) :
    FactorWitness n S S := by
  obtain ⟨l, hl, hls, hlc⟩ := exists_parts_of_isCutSet n S hS
  have hl0 : l ≠ [] := by rintro rfl; simp at hls; omega
  refine ⟨[l], [false], by simpa using ⟨hl, hl0⟩, rfl, ?_, ?_, ?_⟩
  · rw [compProd_singleton hl]; exact hls
  · rw [compProd_singleton hl]; exact hlc
  · simp only [List.zipWith_cons_cons, List.zipWith_nil_left, revIf, Bool.false_eq_true,
      if_false]
    rw [compProd_singleton hl]; exact hlc

lemma FactorWitness.rev_self {n : ℕ} (hn : 1 ≤ n) {S : Finset ℕ} (hS : IsCutSet n S) :
    FactorWitness n S (revCuts n S) := by
  obtain ⟨l, hl, hls, hlc⟩ := exists_parts_of_isCutSet n S hS
  have hl0 : l ≠ [] := by rintro rfl; simp at hls; omega
  have hlr : IsParts l.reverse := fun x hx => hl x (List.mem_reverse.mp hx)
  refine ⟨[l], [true], by simpa using ⟨hl, hl0⟩, rfl, ?_, ?_, ?_⟩
  · rw [compProd_singleton hl]; exact hls
  · rw [compProd_singleton hl]; exact hlc
  · simp only [List.zipWith_cons_cons, List.zipWith_nil_left, revIf, if_true]
    rw [compProd_singleton hlr, partsCuts_reverse hl, hls, hlc]

/-- Reversing every factor on the second side; the order of the factor list is not reversed
(`(α ∘ ε)* = α* ∘ ε*`). -/
lemma FactorWitness.flip {n : ℕ} {S S'' : Finset ℕ} (h : FactorWitness n S S'') :
    FactorWitness n S (revCuts n S'') := by
  obtain ⟨δs, fl, hδ, hfl, hs, hc, hc'⟩ := h
  have hz : ∀ x ∈ List.zipWith revIf fl δs, IsParts x ∧ x ≠ [] := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [List.getElem_zipWith]
    have := hδ (δs[i]'(by simpa [← hfl] using hi)) (List.getElem_mem _)
    exact ⟨isParts_revIf this.1, revIf_ne_nil this.2⟩
  refine ⟨δs, fl.map (!·), hδ, by simpa using hfl, hs, hc, ?_⟩
  rw [zipWith_revIf_not fl δs hfl, ← compProd_reverse _ hz,
    partsCuts_reverse (isParts_compProd _ hz).1, ← hc', sum_compProd_revIf fl δs hfl, hs]

/-- Composition with a common literal inner factor `ε`: a witness for the outer pair gives a witness
for the products (the factor `ε` is appended to the factor list). -/
lemma FactorWitness.comp {m p : ℕ} {A A' E : Finset ℕ} (hp : 0 < p) (hE : IsCutSet p E)
    (h : FactorWitness m A A') : FactorWitness (m * p) (compCuts m A p E) (compCuts m A' p E) := by
  obtain ⟨δs, fl, hδ, hfl, hs, hc, hc'⟩ := h
  obtain ⟨ε, hε, hεs, hεc⟩ := exists_parts_of_isCutSet p E hE
  have hε0 : ε ≠ [] := by rintro rfl; simp at hεs; omega
  have hz : ∀ x ∈ List.zipWith revIf fl δs, IsParts x ∧ x ≠ [] := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [List.getElem_zipWith]
    have := hδ (δs[i]'(by simpa [← hfl] using hi)) (List.getElem_mem _)
    exact ⟨isParts_revIf this.1, revIf_ne_nil this.2⟩
  have hδ' : ∀ δ ∈ δs ++ [ε], IsParts δ ∧ δ ≠ [] := by
    intro δ hδm
    rcases List.mem_append.mp hδm with h1 | h1
    · exact hδ δ h1
    · rw [List.mem_singleton.mp h1]; exact ⟨hε, hε0⟩
  have hzip : List.zipWith revIf (fl ++ [false]) (δs ++ [ε]) =
      List.zipWith revIf fl δs ++ [ε] := by
    rw [List.zipWith_append hfl]
    simp [revIf]
  refine ⟨δs ++ [ε], fl ++ [false], hδ', by simp [hfl], ?_, ?_, ?_⟩
  · rw [compProd_append_singleton hε δs hδ, sum_compose, hs, hεs]
  · rw [compProd_append_singleton hε δs hδ, partsCuts_compose (isParts_compProd δs hδ).1 hε0, hs,
      hεs, hc, hεc]
  · rw [hzip, compProd_append_singleton hε _ hz,
      partsCuts_compose (isParts_compProd _ hz).1 hε0, sum_compProd_revIf fl δs hfl, hs, hεs, hc',
      hεc]

/-! ### `thm:coarse` and `prop:budget` -/

/-- `prop:budget` (`thm:coarse` with an arbitrary budget `H` monotone under divisibility), at the
level of cut sets: for compositions of weight `n ≥ 1` either they have a factor-reversal witness
and equal substitution maps, or there is a coarse certificate with at most `H n` blocks
(`eq:coarse-certificate`).

The proof is the strong induction on `n` of the paper, with the outer pair of weight `n / p` and the
coefficient grid `mult_scale` (`eq:coefficient-grid`).  **Differs from the paper's route.**  The
equality of the substitution maps is not carried through the induction: it is recovered at the end
from the witness by `eq:Psi-laws` (`FactorWitness.Psi_eq`), and the witness for the outer pair is
extended by appending the common inner factor (`FactorWitness.comp`) and reversed on the second side
by `FactorWitness.flip`. -/
theorem coarse_recognition_of_budget {H : ℕ → ℕ} (hH : MonotoneDvd H)
    (hLA : LocalAlternative H) :
    ∀ (n : ℕ), 1 ≤ n → ∀ (S S' : Finset ℕ), IsCutSet n S → IsCutSet n S' →
      (FactorWitness n S S' ∧ Psi n S = Psi n S') ∨ ∃ lam, CoarseCertificate H n S S' lam := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn S S' hS hS'
    rcases hLA n S S' hS hS' with h | h | ⟨p, d, A, A', E, S'', hp3, hpd, hpdle, hdn, hdlt, hA, hA', hE, hSeq, hor, hS''eq, -⟩ |
        ⟨lam, hc⟩
    · subst h
      have := FactorWitness.refl hn hS
      exact Or.inl ⟨this, this.Psi_eq⟩
    · subst h
      have := FactorWitness.rev_self hn hS
      exact Or.inl ⟨this, this.Psi_eq⟩
    · have hpn : p ∣ n := hpd.trans hdn
      have hpn' : p < n := by omega
      have hS'eq : S' = compCuts (n / p) A' p E ∨ revCuts n S' = compCuts (n / p) A' p E := by
        rcases hor with h | h
        · exact Or.inl (h ▸ hS''eq)
        · exact Or.inr (h ▸ hS''eq)
      have hp : 0 < p := by omega
      obtain ⟨m, hm⟩ : ∃ m, n / p = m := ⟨_, rfl⟩
      have hnm : n = m * p := by rw [← hm]; exact (Nat.div_mul_cancel hpn).symm
      rw [hm] at hSeq hS'eq hA hA'
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp at hnm; omega
        · exact h
      have hmn : m < n := by
        rw [hnm]
        nlinarith
      have hdvd : m ∣ n := ⟨p, hnm⟩
      have key : FactorWitness n S (compCuts m A' p E) ∨
          ∃ lam, CoarseCertificate H n S (compCuts m A' p E) lam := by
        rcases ih m hmn hm1 A A' hA hA' with ⟨hw, _⟩ | ⟨lam, hc⟩
        · left
          rw [hSeq, hnm]
          exact hw.comp hp hE
        · right
          refine ⟨lam.map (p * ·), ?_⟩
          rw [hSeq, hnm]
          exact CoarseCertificate.scale hp hA hA' hE (hnm ▸ hH m n hm1 hn hdvd) hc
      have hcomp : IsCutSet n (compCuts m A' p E) := by
        rw [hnm]; exact compCuts_isCutSet hp hA' hE
      rcases hS'eq with h | h
      · rw [h]
        rcases key with hw | hc
        · exact Or.inl ⟨hw, hw.Psi_eq⟩
        · exact Or.inr hc
      · have hS'r : S' = revCuts n (compCuts m A' p E) := by
          rw [← h, revCuts_revCuts hS']
        rw [hS'r]
        rcases key with hw | ⟨lam, hc⟩
        · have := hw.flip
          exact Or.inl ⟨this, this.Psi_eq⟩
        · exact Or.inr ⟨lam, hc.rev_right hn hcomp⟩
    · exact Or.inr ⟨lam, hc⟩

/-- The alternatives of `thm:coarse` are exclusive: a factor witness preserves the complete
inventory (`cor:reversal-suffices`), while a certificate is a nonzero coefficient difference. -/
theorem factorWitness_not_certificate {H : ℕ → ℕ} {n : ℕ} {S S' : Finset ℕ}
    (hn : 1 ≤ n) (hS : IsCutSet n S) (hS' : IsCutSet n S') (hw : FactorWitness n S S')
    (lam : Multiset ℕ) : ¬ CoarseCertificate H n S S' lam := by
  rintro ⟨hpos, _, _, hdiff, _⟩
  have := mult_eq_of_G_eq (by omega) hS hS' hw.G_eq hpos
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdiff
  rw [this] at hdiff
  omega

/-- `prop:budget`: for an arbitrary budget `H` monotone under divisibility that satisfies the local
alternative `prop:local-alternative`, `thm:coarse` holds with `H n` in place of `Ω(n) + 2`:
exactly one of the two alternatives holds. -/
theorem budget_recognition {H : ℕ → ℕ} (hH : MonotoneDvd H) (hLA : LocalAlternative H)
    {n : ℕ} (hn : 1 ≤ n) {S S' : Finset ℕ} (hS : IsCutSet n S) (hS' : IsCutSet n S') :
    Xor (FactorWitness n S S' ∧ Psi n S = Psi n S') (∃ lam, CoarseCertificate H n S S' lam) := by
  rcases coarse_recognition_of_budget hH hLA n hn S S' hS hS' with h | h
  · exact Or.inl ⟨h, fun ⟨lam, hc⟩ => factorWitness_not_certificate hn hS hS' h.1 lam hc⟩
  · refine Or.inr ⟨h, fun hw => ?_⟩
    obtain ⟨lam, hc⟩ := h
    exact factorWitness_not_certificate hn hS hS' hw.1 lam hc

/-- `thm:coarse` (`eq:coarse-certificate`): for compositions `β, γ` of weight `n` (cut sets
`S, S'`), either they have a factor-reversal witness and `Ψ_β = Ψ_γ`, or some `λ ⊢ n` satisfies
`ℓ(λ) ≤ Ω(n) + 2` and `m_β(λ) - m_γ(λ) ∈ {-2, -1, 1, 2}`, with distinct parts except possibly one
repeated pair.  The alternatives are exclusive.  Conditional on `prop:local-alternative` for the
budget `Ω(n) + 2`. -/
theorem coarse_recognition (hLA : LocalAlternativeOmega) {n : ℕ} (hn : 1 ≤ n) {S S' : Finset ℕ}
    (hS : IsCutSet n S) (hS' : IsCutSet n S') :
    Xor (FactorWitness n S S' ∧ Psi n S = Psi n S')
      (∃ lam, CoarseCertificate (fun n => ArithmeticFunction.cardFactors n + 2) n S S' lam) :=
  budget_recognition monotoneDvd_omega hLA hn hS hS'

/-! ### `cor:modular-budget` -/

/-- `cor:modular-budget`: under a budget `H` as in `prop:budget`, ordinary inventory coefficients
through `H(n)` modulo any integer `q ≥ 3` determine the complete inventory.  A nonzero discrepancy
of magnitude one or two is nonzero modulo `q`, and the exact integer alternative is applied; no
labeled factorial is inverted. -/
theorem modular_budget {H : ℕ → ℕ} (hH : MonotoneDvd H) (hLA : LocalAlternative H) {q : ℕ}
    (hq : 3 ≤ q) {n : ℕ} (hn : 1 ≤ n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') :
    (∀ lam : Multiset ℕ, (∀ x ∈ lam, 0 < x) → lam.sum = n → Multiset.card lam ≤ H n →
        (q : ℤ) ∣ (mult n S lam : ℤ) - mult n S' lam) ↔ G n S = G n S' := by
  constructor
  · intro hmod
    rcases budget_recognition hH hLA hn hS hS' with ⟨⟨hw, _⟩, _⟩ | ⟨⟨lam, hpos, hsum, hcard, hdiff, _⟩, _⟩
    · exact hw.G_eq
    · exfalso
      have hD : (mult n S lam : ℤ) - mult n S' lam ≠ 0 := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdiff
        omega
      refine not_dvd_of_abs_le_two hD ?_ hq (hmod lam hpos hsum hcard)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdiff
      rcases hdiff with h | h | h | h <;> rw [h] <;> norm_num
  · intro h lam hpos _ _
    rw [mult_eq_of_G_eq (by omega) hS hS' h hpos]
    simp

/-! ### `rem:shallow-induction` -/

/-- `rem:shallow-induction`, first half: for `β = δ ∘ ε` and `η = ζ ∘ ε` with a common literal
inner factor of weight `p`, `eq:coefficient-grid` transfers a shallow congruence of the products to
the outer pair: if the ordinary coefficients of `G_β` and `G_η` agree at every `λ ⊢ mp` with fewer
than `s` parts, then those of `G_δ` and `G_ζ` agree at every `μ ⊢ m` with fewer than `s` parts. -/
theorem shallow_transfer {m p s : ℕ} {A A' E : Finset ℕ} (hp : 0 < p) (hA : IsCutSet m A)
    (hA' : IsCutSet m A') (hE : IsCutSet p E)
    (h : ∀ lam : Multiset ℕ, (∀ x ∈ lam, 0 < x) → lam.sum = m * p → Multiset.card lam < s →
      mult (m * p) (compCuts m A p E) lam = mult (m * p) (compCuts m A' p E) lam) :
    ∀ mu : Multiset ℕ, (∀ x ∈ mu, 0 < x) → mu.sum = m → Multiset.card mu < s →
      mult m A mu = mult m A' mu := by
  intro mu hpos hsum hcard
  rw [← mult_scale hp hA hE, ← mult_scale hp hA' hE]
  refine h _ ?_ ?_ (by rwa [Multiset.card_map])
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    exact Nat.mul_pos hp (hpos y hy)
  · have := Multiset.sum_map_mul_left (a := p) (s := mu) (f := id)
    simp only [id, Multiset.map_id'] at this
    rw [this, hsum, mul_comm]

/-- `rem:shallow-induction`, second half: under a budget `H` as in `prop:budget`, a shallow
congruence of the products `β = δ ∘ ε`, `η = ζ ∘ ε` through degree `H(mp)` (fewer than `H(mp) + 1`
blocks) gives, by `eq:coefficient-grid` and the smaller-weight theorem, full equality of the outer
inventories `G_δ = G_ζ`. -/
theorem shallow_induction {H : ℕ → ℕ} (hH : MonotoneDvd H) (hLA : LocalAlternative H) {m p : ℕ}
    {A A' E : Finset ℕ} (hm : 1 ≤ m) (hp : 0 < p) (hA : IsCutSet m A) (hA' : IsCutSet m A')
    (hE : IsCutSet p E)
    (h : ∀ lam : Multiset ℕ, (∀ x ∈ lam, 0 < x) → lam.sum = m * p → Multiset.card lam ≤ H (m * p) →
      mult (m * p) (compCuts m A p E) lam = mult (m * p) (compCuts m A' p E) lam) :
    G m A = G m A' := by
  have hsh := shallow_transfer (s := H (m * p) + 1) hp hA hA' hE
    (fun lam hpos hsum hcard => h lam hpos hsum (by omega))
  by_contra hne
  rcases budget_recognition hH hLA hm hA hA' with ⟨⟨hw, _⟩, _⟩ | ⟨⟨lam, hpos, hsum, hcard, hdiff, _⟩, _⟩
  · exact hne hw.G_eq
  · have hle : H m ≤ H (m * p) := hH m (m * p) hm (Nat.mul_pos hm hp) ⟨p, rfl⟩
    have := hsh lam hpos hsum (by omega)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdiff
    omega

end SkewRibbonCoarsenings
