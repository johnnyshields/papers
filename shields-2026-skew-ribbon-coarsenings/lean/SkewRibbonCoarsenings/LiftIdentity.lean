/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.OddInvariant
import SkewRibbonCoarsenings.Coordinates

/-!
# The lift identity, the extraction, and the unit witness

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:depth`
(`thm:lift`: `eq:lift-difference`, `eq:lift-extraction`, and the exact-degree clause).

`lift_difference` expands the two alternative seams of the lifted roots with `eq:seam` and the
associativity of `⊙` on cut sets.  `pderiv_G` records that a composition of weight `t` has the term
`h_t` exactly once and no other term involving `h_k` for `k ≥ t`; `lift_extraction` is the double
derivative identity, and `lift_first_differs` the exact-degree clause with an ordinary unit
witness.  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open MvPolynomial Finset

lemma near_assoc (a b : ℕ) (A B C : Finset ℕ) :
    nearCuts (a + b) (nearCuts a A B) C = nearCuts a A (nearCuts b B C) := by
  ext x
  simp only [nearCuts, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ((h | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a + y - a, Or.inl (by simpa using hy), by omega⟩
    · exact Or.inr ⟨b + y, Or.inr ⟨y, hy, rfl⟩, by omega⟩
  · rintro (h | ⟨y, (hy | ⟨z, hz, rfl⟩), rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨y, hy, rfl⟩)
    · exact Or.inr ⟨z, hz, by omega⟩

lemma concat_near_left (a b : ℕ) (A B C : Finset ℕ) :
    nearCuts (a + b) (concatCuts a A B) C = concatCuts a A (nearCuts b B C) := by
  ext x
  simp only [nearCuts, concatCuts, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro (((h | rfl) | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨y, Or.inl hy, rfl⟩
    · exact Or.inr ⟨b + y, Or.inr ⟨y, hy, rfl⟩, by omega⟩
  · rintro ((h | rfl) | ⟨y, (hy | ⟨z, hz, rfl⟩), rfl⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr rfl))
    · exact Or.inl (Or.inr ⟨y, hy, rfl⟩)
    · exact Or.inr ⟨z, hz, by omega⟩

lemma near_concat_right (a b : ℕ) (A B C : Finset ℕ) :
    nearCuts a A (concatCuts b B C) = concatCuts (a + b) (nearCuts a A B) C := by
  ext x
  simp only [nearCuts, concatCuts, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro (h | ⟨y, ((hy | rfl) | ⟨z, hz, rfl⟩), rfl⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨y, hy, rfl⟩))
    · exact Or.inl (Or.inr (by omega))
    · exact Or.inr ⟨z, hz, by omega⟩
  · rintro (((h | ⟨y, hy, rfl⟩) | h) | ⟨y, hy, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y, Or.inl (Or.inl hy), rfl⟩
    · exact Or.inr ⟨b, Or.inl (Or.inr rfl), by omega⟩
    · exact Or.inr ⟨b + y, Or.inr ⟨y, hy, rfl⟩, by omega⟩

/-! ### The lift identity -/

lemma liftE_eq_word (w : ℕ) (R S : Finset ℕ) : liftE w R S = wordCuts w R S 0 2 := by
  rw [liftE_eq, wordBd_empty]

lemma nearCuts_S_E (w : ℕ) (R S : Finset ℕ) :
    nearCuts w S (liftE w R S) = wordCuts w R S 1 3 := by
  have h := wordCuts_add w R S 1 1 2
  rw [wordCuts_one, if_neg (by decide), one_mul,
    wordCuts_congr (p := 1 + 1) (p' := 0) (by omega)] at h
  rw [liftE_eq_word]
  exact h.symm

lemma nearCuts_R_SE (w : ℕ) (R S : Finset ℕ) :
    nearCuts w R (wordCuts w R S 1 3) = wordCuts w R S 0 4 := by
  have h := wordCuts_add w R S 0 1 3
  rw [wordCuts_one, if_pos (by decide), one_mul, zero_add] at h
  exact h.symm

lemma nearCuts_E_R (w : ℕ) (R S : Finset ℕ) :
    nearCuts (2 * w) (liftE w R S) R = wordCuts w R S 0 3 := by
  have h := wordCuts_add w R S 0 2 1
  rw [wordCuts_one, if_pos (by decide)] at h
  rw [liftE_eq_word]
  exact h.symm

lemma nearCuts_RSR_S (w : ℕ) (R S : Finset ℕ) :
    nearCuts (3 * w) (wordCuts w R S 0 3) S = wordCuts w R S 0 4 := by
  have h := wordCuts_add w R S 0 3 1
  rw [wordCuts_one, if_neg (by decide)] at h
  exact h.symm

/-- `eq:lift-difference` (the seam expansion): the two lifted inventories differ by
`G_E (G_R G_{S ⊙ R ⊙ S} - G_{R ⊙ S ⊙ R} G_S)`, where `S ⊙ R ⊙ S = Alt_1(S,R)` and
`R ⊙ S ⊙ R = Alt_1(R,S)`.  Only `eq:seam` and the associativity of `⊙` are used. -/
theorem lift_difference {w : ℕ} {R S : Finset ℕ} (hw : 0 < w) (hR : IsCutSet w R)
    (hS : IsCutSet w S) :
    G (6 * w) (liftR w R S) - G (6 * w) (liftS w R S) =
      G (2 * w) (liftE w R S) *
        (G w R * G ((2 * 1 + 1) * w) (altCuts w S R 1) -
          G ((2 * 1 + 1) * w) (altCuts w R S 1) * G w S) := by
  have hE : IsCutSet (2 * w) (liftE w R S) := by
    have := isCutSet_nearCuts hR hS
    rwa [two_mul]
  have hEw : IsCutSet (w + w) (liftE w R S) := by rwa [← two_mul]
  have hF : IsCutSet (w + w) (liftF w R S) := isCutSet_concatCuts hw hw hR hS
  have h2w : 0 < 2 * w := by omega
  -- the seam expansions of the two lifted roots
  have hFE : IsCutSet (2 * w + 2 * w) (nearCuts (2 * w) (liftF w R S) (liftE w R S)) :=
    isCutSet_nearCuts (by rwa [two_mul]) hE
  have hEF : IsCutSet (2 * w + 2 * w) (nearCuts (2 * w) (liftE w R S) (liftF w R S)) :=
    isCutSet_nearCuts hE (by rwa [two_mul])
  have hR' : G (6 * w) (liftR w R S) =
      G (2 * w) (liftE w R S) * G (4 * w) (nearCuts (2 * w) (liftF w R S) (liftE w R S)) +
        G (6 * w) (nearCuts (2 * w) (liftE w R S) (nearCuts (2 * w) (liftF w R S) (liftE w R S))) := by
    have := G_concat_cuts (2 * w) (4 * w) (liftE w R S)
      (nearCuts (2 * w) (liftF w R S) (liftE w R S)) h2w (by omega) hE
      (by rw [show 4 * w = 2 * w + 2 * w by ring]; exact hFE)
    rw [show 2 * w + 4 * w = 6 * w by ring] at this
    exact this
  have hS' : G (6 * w) (liftS w R S) =
      G (4 * w) (nearCuts (2 * w) (liftE w R S) (liftF w R S)) * G (2 * w) (liftE w R S) +
        G (6 * w) (nearCuts (4 * w) (nearCuts (2 * w) (liftE w R S) (liftF w R S)) (liftE w R S)) := by
    have := G_concat_cuts (4 * w) (2 * w) (nearCuts (2 * w) (liftE w R S) (liftF w R S))
      (liftE w R S) (by omega) h2w
      (by rw [show 4 * w = 2 * w + 2 * w by ring]; exact hEF) hE
    rw [show 4 * w + 2 * w = 6 * w by ring] at this
    exact this
  have hnear : nearCuts (4 * w) (nearCuts (2 * w) (liftE w R S) (liftF w R S)) (liftE w R S) =
      nearCuts (2 * w) (liftE w R S) (nearCuts (2 * w) (liftF w R S) (liftE w R S)) := by
    rw [show 4 * w = 2 * w + 2 * w by ring]
    exact near_assoc _ _ _ _ _
  -- the inner seam expansions
  have hFEeq : nearCuts (2 * w) (liftF w R S) (liftE w R S) =
      concatCuts w R (wordCuts w R S 1 3) := by
    unfold liftF
    rw [show 2 * w = w + w by ring, concat_near_left, nearCuts_S_E]
  have hEFeq : nearCuts (2 * w) (liftE w R S) (liftF w R S) =
      concatCuts (3 * w) (wordCuts w R S 0 3) S := by
    unfold liftF
    rw [near_concat_right, show 2 * w + w = 3 * w by ring, nearCuts_E_R]
  have hw3 : IsCutSet (3 * w) (wordCuts w R S 0 3) := isCutSet_wordCuts hR hS 0 3
  have hw3' : IsCutSet (3 * w) (wordCuts w R S 1 3) := isCutSet_wordCuts hR hS 1 3
  have hA : G (4 * w) (concatCuts w R (wordCuts w R S 1 3)) =
      G w R * G (3 * w) (wordCuts w R S 1 3) + G (4 * w) (wordCuts w R S 0 4) := by
    have := G_concat_cuts w (3 * w) R (wordCuts w R S 1 3) hw (by omega) hR hw3'
    rw [show w + 3 * w = 4 * w by ring, nearCuts_R_SE] at this
    exact this
  have hB : G (4 * w) (concatCuts (3 * w) (wordCuts w R S 0 3) S) =
      G (3 * w) (wordCuts w R S 0 3) * G w S + G (4 * w) (wordCuts w R S 0 4) := by
    have := G_concat_cuts (3 * w) w (wordCuts w R S 0 3) S (by omega) hw hw3 hS
    rw [show 3 * w + w = 4 * w by ring, nearCuts_RSR_S] at this
    exact this
  rw [hR', hS', hnear, hFEeq, hEFeq, hA, hB, altCuts_eq_wordCuts, altCuts_eq_wordCuts]
  have e1 : wordCuts w S R 0 (2 * 1 + 1) = wordCuts w R S 1 3 := by
    rw [← wordCuts_swap]
  have e2 : wordCuts w R S 0 (2 * 1 + 1) = wordCuts w R S 0 3 := rfl
  rw [e1, e2, show (2 * 1 + 1) * w = 3 * w by ring]
  ring

/-! ### Extraction -/

lemma pderiv_hgen_pnat (k : ℕ+) (t : ℕ) (ht : 0 < t) :
    pderiv k (hgen t) = if (k : ℕ) = t then 1 else 0 := by
  rw [hgen, dif_pos ht]
  by_cases h : (k : ℕ) = t
  · have : k = ⟨t, ht⟩ := PNat.eq h
    subst this
    rw [if_pos h]
    exact pderiv_X_self _
  · rw [if_neg h]
    exact pderiv_X_of_ne (by intro e; apply h; rw [← e]; rfl)

/-- A composition of weight `t` has the term `h_t` exactly once and no other term involving `h_t`
(or any `h_k` with `k ≥ t`): for `k ≥ t`, `∂_{h_k} G_β = 1` if `k = t` and `0` otherwise. -/
theorem pderiv_G {t : ℕ} (ht : 0 < t) {S : Finset ℕ} (hS : IsCutSet t S) (k : ℕ+)
    (hk : t ≤ (k : ℕ)) : pderiv k (G t S) = if (k : ℕ) = t then 1 else 0 := by
  have hq := G_sub_mem_supported ht hS
  have hk0 : pderiv k (G t S - hgen t) = 0 := by
    apply pderiv_eq_zero_of_notMem_vars
    intro hv
    have := (MvPolynomial.mem_supported.mp hq) hv
    simp only [Set.mem_setOf_eq] at this
    omega
  have := pderiv_hgen_pnat k t ht
  rw [map_sub] at hk0
  rw [sub_eq_zero.mp hk0, this]

/-- `h_t` occurs in `G_β` with coefficient one, and no other monomial of `G_β` involves `h_t`:
the exact form of "a composition of weight `t` has the term `h_t` once and no other term
containing `h_t`". -/
theorem G_eq_hgen_add {t : ℕ} (ht : 0 < t) {S : Finset ℕ} (hS : IsCutSet t S) :
    ∃ q : Lam, G t S = hgen t + q ∧ ∀ k : ℕ+, t ≤ (k : ℕ) → pderiv k q = 0 := by
  refine ⟨G t S - hgen t, by ring, fun k hk => ?_⟩
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  have := (MvPolynomial.mem_supported.mp (G_sub_mem_supported ht hS)) hv
  simp only [Set.mem_setOf_eq] at this
  omega

lemma pderiv_G_of_lt {t : ℕ} (ht : 0 < t) {S : Finset ℕ} (hS : IsCutSet t S) (k : ℕ+)
    (hk : t < (k : ℕ)) : pderiv k (G t S) = 0 := by
  rw [pderiv_G ht hS k hk.le, if_neg hk.ne']

lemma pderiv_G_self {t : ℕ} (ht : 0 < t) {S : Finset ℕ} (hS : IsCutSet t S) (k : ℕ+)
    (hk : (k : ℕ) = t) : pderiv k (G t S) = 1 := by
  rw [pderiv_G ht hS k hk.ge, if_pos hk]

/-- `eq:lift-extraction`: `∂_{h_{2w}} ∂_{h_{3w}} (G_{R'} - G_{S'}) = G_R - G_S`. -/
theorem lift_extraction {w : ℕ} {R S : Finset ℕ} (hw : 0 < w) (hR : IsCutSet w R)
    (hS : IsCutSet w S) :
    pderiv ⟨2 * w, by omega⟩ (pderiv ⟨3 * w, by omega⟩
      (G (6 * w) (liftR w R S) - G (6 * w) (liftS w R S))) = G w R - G w S := by
  have hE : IsCutSet (2 * w) (liftE w R S) := by
    have := isCutSet_nearCuts hR hS
    rwa [two_mul]
  have hA := isCutSet_altCuts hR hS 1
  have hB := isCutSet_altCuts hS hR 1
  rw [lift_difference hw hR hS]
  set k2 : ℕ+ := ⟨2 * w, by omega⟩
  set k3 : ℕ+ := ⟨3 * w, by omega⟩
  have hw0 : 0 < (2 * 1 + 1) * w := by omega
  -- derivative in `h_{3w}`
  have d3 : pderiv k3 (G (2 * w) (liftE w R S) *
        (G w R * G ((2 * 1 + 1) * w) (altCuts w S R 1) -
          G ((2 * 1 + 1) * w) (altCuts w R S 1) * G w S)) =
      G (2 * w) (liftE w R S) * (G w R - G w S) := by
    have e1 : pderiv k3 (G (2 * w) (liftE w R S)) = 0 :=
      pderiv_G_of_lt (by omega) hE k3 (by simp [k3]; omega)
    have e2 : pderiv k3 (G w R) = 0 := pderiv_G_of_lt hw hR k3 (by simp [k3]; omega)
    have e3 : pderiv k3 (G w S) = 0 := pderiv_G_of_lt hw hS k3 (by simp [k3]; omega)
    have e4 : pderiv k3 (G ((2 * 1 + 1) * w) (altCuts w S R 1)) = 1 :=
      pderiv_G_self hw0 hB k3 (by simp [k3])
    have e5 : pderiv k3 (G ((2 * 1 + 1) * w) (altCuts w R S 1)) = 1 :=
      pderiv_G_self hw0 hA k3 (by simp [k3])
    simp only [pderiv_mul, map_sub, e1, e2, e3, e4, e5, smul_eq_mul]
    ring
  rw [d3]
  have f1 : pderiv k2 (G (2 * w) (liftE w R S)) = 1 :=
    pderiv_G_self (by omega) hE k2 rfl
  have f2 : pderiv k2 (G w R) = 0 := pderiv_G_of_lt hw hR k2 (by simp [k2]; omega)
  have f3 : pderiv k2 (G w S) = 0 := pderiv_G_of_lt hw hS k2 (by simp [k2]; omega)
  simp only [pderiv_mul, map_sub, f1, f2, f3, smul_eq_mul]
  ring

/-! ### The exact-degree clause -/

/-- A positive natural number as an element of `ℕ+`. -/
def pnOf (n : ℕ) (h : 0 < n) : ℕ+ := ⟨n, h⟩

lemma toFinsupp_cons_pnat (a : ℕ+) (M : Multiset ℕ+) :
    Multiset.toFinsupp (a ::ₘ M) = Multiset.toFinsupp M + Finsupp.single a 1 := by
  rw [← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton, add_comm]

lemma degree_toFinsupp (M : Multiset ℕ+) :
    Finsupp.degree (Multiset.toFinsupp M) = Multiset.card M := by
  have h := Multiset.toFinsupp_sum_eq M
  rw [Finsupp.degree_apply]
  exact h

lemma card_posParts {l : Multiset ℕ} (hl : ∀ x ∈ l, 0 < x) :
    Multiset.card (posParts l) = Multiset.card l := by
  rw [← map_val_posParts hl, Multiset.card_map, map_val_posParts hl]

lemma toFinsupp_posParts_add {w : ℕ} (hw : 0 < w) (lam : Multiset ℕ) :
    Multiset.toFinsupp (posParts (lam + {2 * w, 3 * w})) =
      Multiset.toFinsupp (posParts lam) + Finsupp.single (pnOf (2 * w) (by omega)) 1 +
        Finsupp.single (pnOf (3 * w) (by omega)) 1 := by
  have e : lam + {2 * w, 3 * w} = (2 * w) ::ₘ (3 * w) ::ₘ lam := by
    rw [Multiset.insert_eq_cons, Multiset.add_comm, Multiset.cons_add, Multiset.singleton_add]
  rw [e, posParts_cons_pos (by omega), posParts_cons_pos (by omega), toFinsupp_cons_pnat,
    toFinsupp_cons_pnat]
  have h2 : Nat.toPNat (2 * w) (by omega) = pnOf (2 * w) (by omega) := rfl
  have h3 : Nat.toPNat (3 * w) (by omega) = pnOf (3 * w) (by omega) := rfl
  rw [h2, h3]
  abel

/-- `thm:lift`, the exact-degree clause: if `OA_s(R,S)` holds (`s ≥ 2`) and `G_R - G_S` has a
nonzero coefficient at `h_λ` with `λ ⊢ w` of length `s`, then `G_{R'} - G_{S'}` has no monomial of
ordinary degree `< s + 2` and its coefficient at `h_{sort(λ ∪ {2w, 3w})}` (of ordinary degree
`s + 2`) is the same integer, so it is nonzero; in particular, a coefficient `±1` (an ordinary
unit witness) is transported unchanged.  `OA_s(R,S)` at `j = 0` already gives that `G_R - G_S`
has no monomial of ordinary degree `< s`, so `s` is the first degree of difference. -/
theorem lift_witness {w : ℕ} {R S : Finset ℕ} (hw : 0 < w) (hR : IsCutSet w R)
    (hS : IsCutSet w S) {s : ℕ} (hs : 2 ≤ s) (hOA : OA w R S s)
    (lam : Multiset ℕ) (hpos : ∀ x ∈ lam, 0 < x) (hle : ∀ x ∈ lam, x ≤ w)
    (hcard : Multiset.card lam = s) :
    ordGE s (G w R - G w S) ∧
    ordGE (s + 2) (G (6 * w) (liftR w R S) - G (6 * w) (liftS w R S)) ∧
    (G (6 * w) (liftR w R S) - G (6 * w) (liftS w R S)).coeff
        (Multiset.toFinsupp (posParts (lam + {2 * w, 3 * w}))) =
      (G w R - G w S).coeff (Multiset.toFinsupp (posParts lam)) ∧
    Finsupp.degree (Multiset.toFinsupp (posParts (lam + {2 * w, 3 * w}))) = s + 2 := by
  have h0 : ordGE s (G w R - G w S) := by
    have := OA_iff.mp hOA 0
    simpa [altCuts] using this
  have h1 : ordGE (s + 2) (G (6 * w) (liftR w R S) - G (6 * w) (liftS w R S)) := by
    have := OA_iff.mp (OA_lift hw hR hS hs hOA) 0
    simpa [altCuts] using this
  refine ⟨h0, h1, ?_, ?_⟩
  · have hext := lift_extraction hw hR hS
    rw [toFinsupp_posParts_add hw lam]
    set P := G (6 * w) (liftR w R S) - G (6 * w) (liftS w R S)
    set m := Multiset.toFinsupp (posParts lam)
    set k2 : ℕ+ := pnOf (2 * w) (by omega) with hk2
    set k3 : ℕ+ := pnOf (3 * w) (by omega) with hk3
    have hext : pderiv k2 (pderiv k3 P) = G w R - G w S := hext
    have hm2 : m k2 = 0 := by
      simp only [m, Multiset.toFinsupp_apply]
      rw [Multiset.count_eq_zero]
      intro hk
      have := Multiset.mem_map_of_mem (fun x : ℕ+ => (x : ℕ)) hk
      rw [map_val_posParts hpos] at this
      have := hle _ this
      simp [k2, pnOf] at this
      omega
    have hm3 : m k3 = 0 := by
      simp only [m, Multiset.toFinsupp_apply]
      rw [Multiset.count_eq_zero]
      intro hk
      have := Multiset.mem_map_of_mem (fun x : ℕ+ => (x : ℕ)) hk
      rw [map_val_posParts hpos] at this
      have := hle _ this
      simp [k3, pnOf] at this
      omega
    have c2 := MvPolynomial.coeff_pderiv (i := k2) (pderiv k3 P) m
    have c3 := MvPolynomial.coeff_pderiv (i := k3) P (m + Finsupp.single k2 1)
    rw [hext, c3] at c2
    have hk32 : (Finsupp.single k2 1 : ℕ+ →₀ ℕ) k3 = 0 := by
      rw [Finsupp.single_apply, if_neg]
      intro e
      have := congrArg (fun x : ℕ+ => (x : ℕ)) e
      simp [k2, k3, pnOf] at this
      omega
    simp only [Finsupp.add_apply, hm2, hm3, hk32] at c2
    simpa using c2.symm
  · rw [toFinsupp_posParts_add hw lam, map_add, map_add, degree_toFinsupp,
      Finsupp.degree_single, Finsupp.degree_single, card_posParts hpos, hcard]

/-- `thm:lift`, exact-degree clause with an ordinary unit witness.  Let `OA_s(R,S)` hold for
`s ≥ 2`, let `G_R - G_S` first differ in degree `s` (no monomial of ordinary degree `< s`, and a
nonzero coefficient at a partition `λ ⊢ w` of length `s`) with a unit witness, i.e. the coefficient
at `h_λ` is `1` or `-1`.  Then `G_{R'} - G_{S'}` first differs in degree `s + 2` (no monomial of
ordinary degree `< s + 2`, and a nonzero coefficient at a monomial of ordinary degree `s + 2`), and
has the same unit witness at `sort(λ ∪ {2w, 3w})`. -/
theorem lift_first_differs {w : ℕ} {R S : Finset ℕ} (hw : 0 < w) (hR : IsCutSet w R)
    (hS : IsCutSet w S) {s : ℕ} (hs : 2 ≤ s) (hOA : OA w R S s)
    (lam : Multiset ℕ) (hpos : ∀ x ∈ lam, 0 < x) (hsum : lam.sum = w)
    (hcard : Multiset.card lam = s)
    (hunit : ((G w R - G w S).coeff (Multiset.toFinsupp (posParts lam)) = 1 ∨
      (G w R - G w S).coeff (Multiset.toFinsupp (posParts lam)) = -1)) :
    (ordGE s (G w R - G w S) ∧
      (G w R - G w S).coeff (Multiset.toFinsupp (posParts lam)) ≠ 0) ∧
    (ordGE (s + 2) (G (6 * w) (liftR w R S) - G (6 * w) (liftS w R S)) ∧
      Finsupp.degree (Multiset.toFinsupp (posParts (lam + {2 * w, 3 * w}))) = s + 2 ∧
      (G (6 * w) (liftR w R S) - G (6 * w) (liftS w R S)).coeff
        (Multiset.toFinsupp (posParts (lam + {2 * w, 3 * w}))) =
      (G w R - G w S).coeff (Multiset.toFinsupp (posParts lam)) ∧
      ((G (6 * w) (liftR w R S) - G (6 * w) (liftS w R S)).coeff
        (Multiset.toFinsupp (posParts (lam + {2 * w, 3 * w}))) = 1 ∨
      (G (6 * w) (liftR w R S) - G (6 * w) (liftS w R S)).coeff
        (Multiset.toFinsupp (posParts (lam + {2 * w, 3 * w}))) = -1)) := by
  have hle : ∀ x ∈ lam, x ≤ w := fun x hx => hsum ▸ Multiset.le_sum_of_mem hx
  obtain ⟨h0, h1, hc, hd⟩ := lift_witness hw hR hS hs hOA lam hpos hle hcard
  refine ⟨⟨h0, ?_⟩, h1, hd, hc, ?_⟩
  · rcases hunit with h | h <;> rw [h] <;> norm_num
  · rw [hc]; exact hunit

/-- `thm:lift`, all clauses together: for `s ≥ 2`, `OA_s(R,S)` implies `OA_{s+2}(R',S')`
(`eq:OA-lift`); the extraction identity `eq:lift-extraction` holds; and, if `OA_s(R,S)` holds and
`G_R - G_S` first differs in degree `s` with an ordinary unit witness at `λ ⊢ w`, then
`G_{R'} - G_{S'}` first differs in degree `s + 2` with the same unit witness at
`sort(λ ∪ {2w, 3w})`. -/
theorem thm_lift {w : ℕ} {R S : Finset ℕ} (hw : 0 < w) (hR : IsCutSet w R)
    (hS : IsCutSet w S) {s : ℕ} (hs : 2 ≤ s) :
    (OA w R S s → OA (6 * w) (liftR w R S) (liftS w R S) (s + 2)) ∧
    pderiv ⟨2 * w, by omega⟩ (pderiv ⟨3 * w, by omega⟩
      (G (6 * w) (liftR w R S) - G (6 * w) (liftS w R S))) = G w R - G w S ∧
    (OA w R S s → ∀ lam : Multiset ℕ, (∀ x ∈ lam, 0 < x) → lam.sum = w →
      Multiset.card lam = s →
      ((G w R - G w S).coeff (Multiset.toFinsupp (posParts lam)) = 1 ∨
        (G w R - G w S).coeff (Multiset.toFinsupp (posParts lam)) = -1) →
      (ordGE s (G w R - G w S) ∧
        (G w R - G w S).coeff (Multiset.toFinsupp (posParts lam)) ≠ 0) ∧
      (ordGE (s + 2) (G (6 * w) (liftR w R S) - G (6 * w) (liftS w R S)) ∧
        Finsupp.degree (Multiset.toFinsupp (posParts (lam + {2 * w, 3 * w}))) = s + 2 ∧
        (G (6 * w) (liftR w R S) - G (6 * w) (liftS w R S)).coeff
          (Multiset.toFinsupp (posParts (lam + {2 * w, 3 * w}))) =
        (G w R - G w S).coeff (Multiset.toFinsupp (posParts lam)))) := by
  refine ⟨fun h => OA_lift hw hR hS hs h, lift_extraction hw hR hS, ?_⟩
  intro hOA lam hpos hsum hcard hunit
  obtain ⟨a, b⟩ := lift_first_differs hw hR hS hs hOA lam hpos hsum hcard hunit
  exact ⟨a, b.1, b.2.1, b.2.2.1⟩

end SkewRibbonCoarsenings
