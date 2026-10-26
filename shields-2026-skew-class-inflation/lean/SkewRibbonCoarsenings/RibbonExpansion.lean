/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/RibbonExpansion.lean
import SkewRibbonCoarsenings.RibbonSchur
import SkewRibbonCoarsenings.DepthDefs

/-!
# The ribbon expansion and ribbon equality

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:algebra` (`eq:ribbon-expansion`
and the equivalence of ribbon equality with equality of coarsening inventories stated after it).

`ribbon n S` is the ribbon Schur function of the composition of weight `n` with cut set `S`: the
Jacobi–Trudi determinant of the ribbon shape (`RibbonSchur`), independent of `G` and of the sign
twist.  `negH` is the ring homomorphism `𝒜`, `h_j ↦ -h_j`.

* `ribbon_expansion` (`eq:ribbon-expansion`): `r_β = (-1)^{ℓ(β)} 𝒜(G_β)`, with `ℓ(β) = |S| + 1`.
  It is proved from the first-column recursion `r_{(a,b,…)} = h_a r_{(b,…)} - r_{(a+b,…)}` of the
  determinant, which gives the signed coarsening sum `signedCoarsening`, and then the sign twist.
* `totalDegree_G`: the top ordinary degree of `G_β` is `ℓ(β)`.
* `ribbon_eq_iff`: equality of ribbon functions of the same weight is equivalent to equality of
  inventories; `card_eq_of_ribbon_eq` gives the intermediate equality of lengths.

Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset MvPolynomial

/-! ### The sign twist `𝒜` -/

/-- The ring homomorphism `𝒜 : Λ_ℤ → Λ_ℤ`, `𝒜(h_j) = -h_j` for `j ≥ 1`. -/
noncomputable def negH : Lam →+* Lam :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℤ →+* Lam) (fun j : ℕ+ => -MvPolynomial.X j)

lemma negH_X (j : ℕ+) : negH (MvPolynomial.X j) = -MvPolynomial.X j := by
  simp [negH]

/-- `𝒜(h_j) = -h_j` for `j ≥ 1`. -/
lemma negH_hgen {j : ℕ} (hj : 0 < j) : negH (hgen j) = -hgen j := by
  have h : hgen j = MvPolynomial.X (Nat.toPNat j hj) := by simp [hgen, hj]; rfl
  rw [h, negH_X]

/-- `𝒜` is an involution. -/
lemma negH_negH (p : Lam) : negH (negH p) = p := by
  have h : negH.comp negH = RingHom.id Lam := by
    apply ringHom_ext_Lam
    intro j
    simp [RingHom.comp_apply, negH_X]
  simpa using RingHom.congr_fun h p

lemma negH_injective : Function.Injective negH := fun p q h => by
  rw [← negH_negH p, ← negH_negH q, h]

/-- `𝒜` multiplies a product of `k` positive-index generators by `(-1)^k`. -/
lemma neg_one_pow_add_two {R : Type*} [Ring R] (k : ℕ) : (-1 : R) ^ (k + 2) = (-1) ^ k := by
  rw [pow_add]; simp

lemma negH_prod_hgen (M : Multiset ℕ) (hM : ∀ x ∈ M, 0 < x) :
    negH ((M.map hgen).prod) = (-1 : Lam) ^ (Multiset.card M) * (M.map hgen).prod := by
  induction M using Multiset.induction with
  | empty => simp
  | cons a M ih =>
    have ha : 0 < a := hM a (Multiset.mem_cons_self _ _)
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, negH_hgen ha,
      ih (fun x hx => hM x (Multiset.mem_cons_of_mem hx)), Multiset.card_cons, pow_succ]
    ring

/-! ### The signed coarsening sum -/

/-- The signed coarsening sum `∑_{T ⊆ S} (-1)^{|S| - |T|} h_{gaps T}` of the composition of
weight `n` with cut set `S`. -/
noncomputable def signedCoarsening (n : ℕ) (S : Finset ℕ) : Lam :=
  ∑ T ∈ S.powerset, (-1 : Lam) ^ (S.card + T.card) * ((gaps n T).map hgen).prod

lemma image_add_injective (a : ℕ) : Function.Injective (a + · : ℕ → ℕ) :=
  fun x y h => by simpa using h

lemma notMem_image_add {a n' : ℕ} {S' : Finset ℕ} (hS' : IsCutSet n' S') :
    a ∉ S'.image (a + ·) := by
  intro h
  obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp h
  have := (Finset.mem_Ioo.mp (hS' hx)).1
  omega

/-- The first-column recursion for the signed coarsening sum, on cut sets: the composition
`(a, b, …)` has cuts `{a} ∪ (a + S')` with `S'` the cuts of `(b, …)`, and `(a+b, …)` has cuts
`a + S'`. -/
lemma signed_shift (a n' : ℕ) (hn' : 0 < n') (S' : Finset ℕ) (hS' : IsCutSet n' S') :
    signedCoarsening (a + n') (insert a (S'.image (a + ·)))
      = hgen a * signedCoarsening n' S' - signedCoarsening (a + n') (S'.image (a + ·)) := by
  set S'' := S'.image (a + ·) with hS''
  have hcard : S''.card = S'.card := Finset.card_image_of_injective _ (image_add_injective a)
  have haS : a ∉ S'' := notMem_image_add hS'
  have hcardI : (insert a S'').card = S''.card + 1 := Finset.card_insert_of_notMem haS
  have hA : ∑ T ∈ S''.powerset, (-1 : Lam) ^ ((insert a S'').card + T.card)
        * ((gaps (a + n') T).map hgen).prod
      = -signedCoarsening (a + n') S'' := by
    unfold signedCoarsening
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [hcardI, show S''.card + 1 + T.card = (S''.card + T.card) + 1 by ring, pow_succ]
    ring
  have hB : ∑ T ∈ S''.powerset, (-1 : Lam) ^ ((insert a S'').card + (insert a T).card)
        * ((gaps (a + n') (insert a T)).map hgen).prod
      = hgen a * signedCoarsening n' S' := by
    symm
    unfold signedCoarsening
    rw [Finset.mul_sum]
    refine Finset.sum_nbij' (fun T' => T'.image (a + ·)) (fun T => T.image (· - a))
      ?_ ?_ ?_ ?_ ?_
    · intro T' hT'
      rw [Finset.mem_powerset] at hT' ⊢
      exact Finset.image_subset_image hT'
    · intro T hT
      rw [Finset.mem_powerset] at hT ⊢
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (hT hx)
      simpa using hz
    · intro T' _
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨a + x, ⟨x, hx, rfl⟩, by omega⟩
    · intro T hT
      rw [Finset.mem_powerset] at hT
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        have hzT : z ∈ S'' := hT hz
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hzT
        simpa using hz
      · intro hx
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp (hT hx)
        exact ⟨a + w - a, ⟨a + w, hx, rfl⟩, by omega⟩
    · intro T' hT'
      rw [Finset.mem_powerset] at hT'
      have hT'c : IsCutSet n' T' := fun x hx => hS' (hT' hx)
      have hnot : a ∉ T'.image (a + ·) := notMem_image_add hT'c
      have hc' : (T'.image (a + ·)).card = T'.card :=
        Finset.card_image_of_injective _ (image_add_injective a)
      have hg : gaps (a + n') (insert a (T'.image (a + ·))) = {a} + gaps n' T' := by
        have := gaps_glue a n' ∅ T' (by simp) hn'
          (fun x hx => Finset.mem_Ioo.mp (hT'c hx))
        rw [gaps_empty] at this
        rw [← this]
        congr 1
        ext x
        simp [or_comm]
      rw [Finset.card_insert_of_notMem hnot, hc', hcardI, hcard, hg, Multiset.map_add,
        Multiset.prod_add]
      simp only [Multiset.map_singleton, Multiset.prod_singleton]
      rw [show S'.card + 1 + (T'.card + 1) = (S'.card + T'.card) + 2 by ring, pow_add]
      norm_num
      ring
  have key : signedCoarsening (a + n') (insert a S'')
      = (∑ T ∈ S''.powerset, (-1 : Lam) ^ ((insert a S'').card + T.card)
          * ((gaps (a + n') T).map hgen).prod)
        + ∑ T ∈ S''.powerset, (-1 : Lam) ^ ((insert a S'').card + (insert a T).card)
          * ((gaps (a + n') (insert a T)).map hgen).prod :=
    Finset.sum_powerset_insert haS _
  rw [key, hA, hB]
  ring

lemma card_partsCuts : ∀ (β : List ℕ), IsParts β → β ≠ [] → (partsCuts β).card + 1 = β.length
  | [], _, h => absurd rfl h
  | [a], _, _ => by simp
  | a :: b :: l, hβ, _ => by
    have hb : IsParts (b :: l) := isParts_tail hβ
    have ih := card_partsCuts (b :: l) hb (by simp)
    rw [partsCuts_cons a (by simp : b :: l ≠ []), Finset.card_insert_of_notMem]
    · rw [Finset.card_image_of_injective _ (image_add_injective a)]
      simp only [List.length_cons] at ih ⊢
      omega
    · exact notMem_image_add (partsCuts_isCutSet hb)

lemma partsCuts_cons_cons_merge (a b : ℕ) (l : List ℕ) :
    partsCuts ((a + b) :: l) = (partsCuts (b :: l)).image (a + ·) := by
  have h : ((a + b) :: l) = nearConcat [a] (b :: l) := rfl
  rw [h, partsCuts_nearConcat]
  simp [nearCuts]

/-- The ribbon determinant is the signed coarsening sum. -/
theorem ribbonParts_eq_signed :
    ∀ (β : List ℕ), IsParts β → ribbonParts β = signedCoarsening β.sum (partsCuts β) := by
  intro β
  induction' hlen : β.length using Nat.strong_induction_on with k ih generalizing β
  intro hβ
  match β, hβ, hlen with
  | [], _, _ => simp [signedCoarsening, gaps, hgen]
  | [a], hβ, _ =>
    have ha : 0 < a := head_pos hβ
    rw [ribbonParts_singleton ha]
    simp [signedCoarsening, gaps_empty]
  | a :: b :: l, hβ, hlen =>
    have hb : IsParts (b :: l) := isParts_tail hβ
    have hab : IsParts ((a + b) :: l) := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · have := head_pos hβ; omega
      · exact hb x (List.mem_cons_of_mem _ hx)
    have hk1 := ih (b :: l).length (by simp at hlen ⊢; omega) (b :: l) rfl hb
    have hk2 := ih ((a + b) :: l).length (by simp at hlen ⊢; omega) ((a + b) :: l) rfl hab
    rw [ribbonParts_cons_cons hβ, hk1, hk2, partsCuts_cons_cons_merge]
    have hpos : 0 < (b :: l).sum := by
      have := head_pos hb
      simp only [List.sum_cons]; omega
    have hsum1 : ((a + b) :: l).sum = a + (b :: l).sum := by simp; omega
    have hsum2 : (a :: b :: l).sum = a + (b :: l).sum := by simp
    rw [hsum1, hsum2, partsCuts_cons a (by simp : b :: l ≠ []),
      signed_shift a _ hpos _ (partsCuts_isCutSet hb)]

/-! ### Cut-set form of the ribbon -/

open Classical in
/-- The composition (list of parts) of weight `n` with cut set `S`, when `S` is a cut set. -/
noncomputable def cutsParts (n : ℕ) (S : Finset ℕ) : List ℕ :=
  if h : IsCutSet n S then Classical.choose (exists_parts_of_isCutSet n S h) else []

lemma cutsParts_spec {n : ℕ} {S : Finset ℕ} (h : IsCutSet n S) :
    IsParts (cutsParts n S) ∧ (cutsParts n S).sum = n ∧ partsCuts (cutsParts n S) = S := by
  unfold cutsParts
  rw [dif_pos h]
  exact Classical.choose_spec (exists_parts_of_isCutSet n S h)

/-- The ribbon Schur function `r_β ∈ Λ_ℤ` of the composition `β` of weight `n` with cut set `S`:
the Jacobi–Trudi determinant of its ribbon shape (`ribbonParts`). -/
noncomputable def ribbon (n : ℕ) (S : Finset ℕ) : Lam := ribbonParts (cutsParts n S)

lemma ribbon_partsCuts {l : List ℕ} (hl : IsParts l) : ribbon l.sum (partsCuts l) = ribbonParts l := by
  have h := cutsParts_spec (partsCuts_isCutSet hl)
  have : cutsParts l.sum (partsCuts l) = l := partsCuts_injective h.1 hl h.2.1 h.2.2
  rw [ribbon, this]

/-- The ribbon Schur function is the signed coarsening sum. -/
theorem ribbon_eq_signed {n : ℕ} {S : Finset ℕ} (hS : IsCutSet n S) :
    ribbon n S = signedCoarsening n S := by
  obtain ⟨h1, h2, h3⟩ := cutsParts_spec hS
  rw [ribbon, ribbonParts_eq_signed _ h1, h2, h3]

/-- `eq:ribbon-expansion`, in the form of its proof: the signed coarsening sum is
`(-1)^{ℓ(β)} 𝒜(G_β)`. -/
theorem signedCoarsening_eq {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S) :
    signedCoarsening n S = (-1 : Lam) ^ (S.card + 1) * negH (G n S) := by
  unfold signedCoarsening G
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hT' : IsCutSet n T := fun x hx => hS ((Finset.mem_powerset.mp hT) hx)
  rw [negH_prod_hgen _ (gaps_pos hn hT'), card_gaps hT']
  rw [← mul_assoc, ← pow_add, show S.card + 1 + (T.card + 1) = (S.card + T.card) + 2 by ring,
    neg_one_pow_add_two]

/-- `eq:ribbon-expansion`: `r_β = (-1)^{ℓ(β)} 𝒜(G_β)` with `𝒜(h_j) = -h_j`, for the composition of
weight `n ≥ 1` with cut set `S` (so `ℓ(β) = |S| + 1`).  The ribbon Schur function is the
Jacobi–Trudi determinant of the ribbon shape, defined without reference to `G`; the identity is
the first-column recursion of that determinant together with the coarsening sum `G`. -/
theorem ribbon_expansion {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S) :
    ribbon n S = (-1 : Lam) ^ (S.card + 1) * negH (G n S) := by
  rw [ribbon_eq_signed hS, signedCoarsening_eq hn hS]

/-- `eq:ribbon-expansion`, list form: `r_β = (-1)^{ℓ(β)} 𝒜(G_β)` for a nonempty list of parts. -/
theorem ribbonParts_expansion {β : List ℕ} (hβ : IsParts β) (hne : β ≠ []) :
    ribbonParts β = (-1 : Lam) ^ β.length * negH (Gparts β) := by
  rw [← ribbon_partsCuts hβ, ribbon_expansion (sum_pos_of_ne_nil hβ hne) (partsCuts_isCutSet hβ),
    ← card_partsCuts β hβ hne]
  rfl

/-! ### Coefficients and the top ordinary degree -/

lemma coeff_prod_hgen (M : Multiset ℕ) (d : ℕ+ →₀ ℕ) :
    ((M.map hgen).prod).coeff d = if Multiset.toFinsupp (posParts M) = d then 1 else 0 := by
  rw [prod_hgen_eq, prod_X_eq_monomial, MvPolynomial.coeff_monomial]

lemma degree_gapsMon {n : ℕ} (hn : 0 < n) {T : Finset ℕ} (hT : IsCutSet n T) :
    (Multiset.toFinsupp (posParts (gaps n T))).degree = T.card + 1 := by
  rw [degree_toFinsupp, card_posParts (gaps_pos hn hT), card_gaps hT]

lemma card_le_of_mem_powerset {S T : Finset ℕ} (hT : T ∈ S.powerset) : T.card ≤ S.card :=
  Finset.card_le_card (Finset.mem_powerset.mp hT)

/-- Above degree `|S| + 1` every coefficient of `G` vanishes. -/
lemma coeff_G_of_degree_gt {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S)
    {d : ℕ+ →₀ ℕ} (hd : S.card + 1 < d.degree) : (G n S).coeff d = 0 := by
  unfold G
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun T hT => ?_
  have hT' : IsCutSet n T := fun x hx => hS ((Finset.mem_powerset.mp hT) hx)
  rw [coeff_prod_hgen, if_neg]
  intro h
  have := degree_gapsMon hn hT'
  rw [h] at this
  have := card_le_of_mem_powerset hT
  omega

/-- Above degree `|S| + 1` every coefficient of the signed coarsening sum vanishes. -/
lemma coeff_signed_of_degree_gt {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S)
    {d : ℕ+ →₀ ℕ} (hd : S.card + 1 < d.degree) : (signedCoarsening n S).coeff d = 0 := by
  unfold signedCoarsening
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun T hT => ?_
  have hT' : IsCutSet n T := fun x hx => hS ((Finset.mem_powerset.mp hT) hx)
  have hc : (-1 : Lam) ^ (S.card + T.card) = MvPolynomial.C ((-1 : ℤ) ^ (S.card + T.card)) := by
    simp
  rw [hc, MvPolynomial.coeff_C_mul, coeff_prod_hgen, if_neg, mul_zero]
  intro h
  have := degree_gapsMon hn hT'
  rw [h] at this
  have := card_le_of_mem_powerset hT
  omega

/-- The coefficient of `h_λ` in the signed coarsening sum is `(-1)^{|S| + ℓ(λ) - 1} m_β(λ)`. -/
theorem coeff_signed {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S) (lam : Multiset ℕ)
    (hlam : ∀ x ∈ lam, 0 < x) :
    (signedCoarsening n S).coeff (Multiset.toFinsupp (posParts lam))
      = (-1 : ℤ) ^ (S.card + Multiset.card lam + 1) * (mult n S lam : ℤ) := by
  unfold signedCoarsening
  rw [MvPolynomial.coeff_sum]
  have key : ∀ T ∈ S.powerset,
      ((-1 : Lam) ^ (S.card + T.card) * ((gaps n T).map hgen).prod).coeff
          (Multiset.toFinsupp (posParts lam))
        = if gaps n T = lam then (-1 : ℤ) ^ (S.card + Multiset.card lam + 1) else 0 := by
    intro T hT
    have hT' : IsCutSet n T := fun x hx => hS ((Finset.mem_powerset.mp hT) hx)
    have hc : (-1 : Lam) ^ (S.card + T.card) = MvPolynomial.C ((-1 : ℤ) ^ (S.card + T.card)) := by
      simp
    rw [hc, MvPolynomial.coeff_C_mul, coeff_prod_hgen]
    have hiff : Multiset.toFinsupp (posParts (gaps n T)) = Multiset.toFinsupp (posParts lam)
        ↔ gaps n T = lam := by
      constructor
      · intro h
        have h1 := Multiset.toFinsupp.injective h
        rw [← map_val_posParts (gaps_pos hn hT'), h1, map_val_posParts hlam]
      · intro h; rw [h]
    by_cases h : gaps n T = lam
    · have hcard : Multiset.card lam = T.card + 1 := by rw [← h]; exact card_gaps hT'
      rw [if_pos (hiff.mpr h), if_pos h, mul_one, hcard,
        show S.card + (T.card + 1) + 1 = (S.card + T.card) + 2 by ring, neg_one_pow_add_two]
    · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl key, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mult]
  ring

/-- A polynomial with no monomial of degree above `k` and a nonzero monomial of degree `k` has
total degree `k`. -/
lemma totalDegree_eq_of {p : Lam} {k : ℕ} (hle : ∀ d : ℕ+ →₀ ℕ, k < d.degree → p.coeff d = 0)
    (hex : ∃ d : ℕ+ →₀ ℕ, d.degree = k ∧ p.coeff d ≠ 0) : p.totalDegree = k := by
  apply le_antisymm
  · unfold MvPolynomial.totalDegree
    refine Finset.sup_le fun d hd => ?_
    by_contra hlt
    have hlt' : k < d.degree := not_le.mp hlt
    exact (MvPolynomial.mem_support_iff.mp hd) (hle d hlt')
  · obtain ⟨d, hd, hne⟩ := hex
    have := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)
    rw [← hd]
    exact this

lemma mult_self_pos {n : ℕ} {S : Finset ℕ} : 0 < mult n S (gaps n S) := by
  unfold mult
  exact Finset.card_pos.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset_self S, rfl⟩⟩

/-- The top ordinary degree of `G_β` is `ℓ(β)` (the sentence after `eq:ribbon-expansion`):
`deg_h G_β = |S| + 1`.  The unique coarsening retaining every cut contributes `h_{β₁} ⋯ h_{β_ℓ}`
with coefficient `m_β(β) ≥ 1`, and every other coarsening has fewer blocks. -/
theorem totalDegree_G {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S) :
    (G n S).totalDegree = S.card + 1 := by
  apply totalDegree_eq_of (fun d hd => coeff_G_of_degree_gt hn hS hd)
  refine ⟨Multiset.toFinsupp (posParts (gaps n S)), degree_gapsMon hn hS, ?_⟩
  rw [coeff_G hn hS _ (gaps_pos hn hS)]
  exact_mod_cast (mult_self_pos (n := n) (S := S)).ne'

/-- The top ordinary degree of the ribbon Schur function is `ℓ(β)` as well. -/
theorem totalDegree_ribbon {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S) :
    (ribbon n S).totalDegree = S.card + 1 := by
  rw [ribbon_eq_signed hS]
  apply totalDegree_eq_of (fun d hd => coeff_signed_of_degree_gt hn hS hd)
  refine ⟨Multiset.toFinsupp (posParts (gaps n S)), degree_gapsMon hn hS, ?_⟩
  rw [coeff_signed hn hS _ (gaps_pos hn hS), card_gaps hS]
  have hm : (mult n S (gaps n S) : ℤ) ≠ 0 := by exact_mod_cast (mult_self_pos (n := n) (S := S)).ne'
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hm

/-- Equal inventories have equal lengths: `|S| = |S'|`. -/
theorem card_eq_of_G_eq {n : ℕ} (hn : 0 < n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') (h : G n S = G n S') : S.card = S'.card := by
  have h1 := totalDegree_G hn hS
  have h2 := totalDegree_G hn hS'
  rw [h] at h1
  omega

/-- `eq:ribbon-expansion`, first half of the equivalence: equality of ribbon Schur functions
implies equal lengths. -/
theorem card_eq_of_ribbon_eq {n : ℕ} (hn : 0 < n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') (h : ribbon n S = ribbon n S') : S.card = S'.card := by
  have h1 := totalDegree_ribbon hn hS
  have h2 := totalDegree_ribbon hn hS'
  rw [h] at h1
  omega

/-- `eq:ribbon-expansion`: equality of ribbon Schur functions of compositions of the same weight
holds if and only if their coarsening inventories are equal, `r_β = r_γ ↔ G_β = G_γ`.  Equal
ribbon functions have equal lengths (top ordinary degree), and then the sign twist `𝒜` cancels;
conversely equal inventories have equal lengths. -/
theorem ribbon_eq_iff {n : ℕ} (hn : 0 < n) {S S' : Finset ℕ} (hS : IsCutSet n S)
    (hS' : IsCutSet n S') : ribbon n S = ribbon n S' ↔ G n S = G n S' := by
  constructor
  · intro h
    have hc := card_eq_of_ribbon_eq hn hS hS' h
    rw [ribbon_expansion hn hS, ribbon_expansion hn hS', hc] at h
    have hne : ((-1 : Lam) ^ (S'.card + 1)) ≠ 0 := pow_ne_zero _ (by simp)
    exact negH_injective (mul_left_cancel₀ hne h)
  · intro h
    have hc := card_eq_of_G_eq hn hS hS' h
    rw [ribbon_expansion hn hS, ribbon_expansion hn hS', hc, h]

/-- `eq:ribbon-expansion`, list form of `ribbon_eq_iff`: ribbon equality of two compositions of the
same weight is equality of inventories. -/
theorem ribbonParts_eq_iff {β γ : List ℕ} (hβ : IsParts β) (hγ : IsParts γ) (hne : β ≠ [])
    (hsum : β.sum = γ.sum) : ribbonParts β = ribbonParts γ ↔ Gparts β = Gparts γ := by
  have hn := sum_pos_of_ne_nil hβ hne
  have hS := partsCuts_isCutSet hβ
  have hS' : IsCutSet β.sum (partsCuts γ) := by rw [hsum]; exact partsCuts_isCutSet hγ
  rw [← ribbon_partsCuts hβ, ← ribbon_partsCuts hγ, ← hsum, ribbon_eq_iff hn hS hS']
  rw [Gparts, Gparts, ← hsum]

/-! ### Values at the coefficient of `h_n` -/

lemma mult_singleton {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S) (k : ℕ) :
    mult n S {k} = if k = n then 1 else 0 := by
  unfold mult
  by_cases hk : k = n
  · subst hk
    rw [if_pos rfl, Finset.card_eq_one]
    refine ⟨∅, ?_⟩
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · rintro ⟨hT, hg⟩
      have hT' : IsCutSet k T := fun x hx => hS (hT hx)
      have := card_gaps hT'
      rw [hg] at this
      simp at this
      exact this
    · rintro rfl
      exact ⟨Finset.empty_subset _, gaps_empty k⟩
  · rw [if_neg hk, Finset.card_eq_zero]
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.notMem_empty, iff_false, not_and]
    intro hT hg
    have hT' : IsCutSet n T := fun x hx => hS (hT hx)
    have hsum := sum_gaps hT'
    rw [hg] at hsum
    simp at hsum
    exact hk hsum

/-- The coefficient of `h_k` in the ribbon Schur function of weight `n`: `(-1)^{ℓ(β) - 1}` at
`k = n` and zero otherwise.  In terms of `eq:ribbon-expansion` the coefficient of `h_n` in `G_β`
is `1`, so that of `r_β` is `(-1)^{ℓ(β)} · (-1)`. -/
theorem coeff_ribbon_single {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S) {k : ℕ}
    (hk : 0 < k) :
    (ribbon n S).coeff (Finsupp.single (Nat.toPNat k hk) 1) = if k = n then (-1 : ℤ) ^ S.card else 0 := by
  rw [ribbon_eq_signed hS]
  have h1 : Finsupp.single (Nat.toPNat k hk) 1 = Multiset.toFinsupp (posParts {k}) := by
    rw [show ({k} : Multiset ℕ) = k ::ₘ 0 from rfl, posParts_cons_pos hk]
    simp [posParts, Multiset.toFinsupp_singleton]
  rw [h1, coeff_signed hn hS {k} (by simpa using hk), mult_singleton hn hS]
  by_cases h : k = n
  · rw [if_pos h, if_pos h]
    simp only [Multiset.card_singleton, Nat.cast_one, mul_one]
    rw [show S.card + 1 + 1 = S.card + 2 by ring, neg_one_pow_add_two]
  · rw [if_neg h, if_neg h]
    simp

/-- Every coefficient of the ribbon Schur function is the signed coefficient of `G`:
`[h^d] r_β = (-1)^{ℓ(β) + deg_h d} [h^d] G_β`, where `ℓ(β) = |S| + 1` and `deg_h d` is the
ordinary degree of the monomial.  This is `eq:ribbon-expansion` read monomial by monomial. -/
theorem coeff_ribbon {n : ℕ} (hn : 0 < n) {S : Finset ℕ} (hS : IsCutSet n S) (d : ℕ+ →₀ ℕ) :
    (ribbon n S).coeff d = (-1 : ℤ) ^ (S.card + 1 + d.degree) * (G n S).coeff d := by
  rw [ribbon_eq_signed hS]
  unfold signedCoarsening G
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hT' : IsCutSet n T := fun x hx => hS ((Finset.mem_powerset.mp hT) hx)
  have hc : (-1 : Lam) ^ (S.card + T.card) = MvPolynomial.C ((-1 : ℤ) ^ (S.card + T.card)) := by
    simp
  rw [hc, MvPolynomial.coeff_C_mul, coeff_prod_hgen]
  by_cases h : Multiset.toFinsupp (posParts (gaps n T)) = d
  · have hd : d.degree = T.card + 1 := by rw [← h]; exact degree_gapsMon hn hT'
    rw [if_pos h, hd, mul_one, mul_one,
      show S.card + 1 + (T.card + 1) = (S.card + T.card) + 2 by ring, neg_one_pow_add_two]
  · rw [if_neg h]
    simp

end SkewRibbonCoarsenings
