/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.NoEscape
import SkewJacobiNegative.Overlaps.RowOverlaps

/-!
# The number of index minus one entries is a Schur invariant

Formalizes the counting identity at the head of the proof of
`lem:zero-free-bijection` in `shields-2026-skew-class-inflation.tex`.  An entry
of the full Jacobi--Trudi board has index \(-1\) exactly when it sits at
distance \(k-1\ge2\) below the diagonal and the \(k\) consecutive rows it spans
share \(k-2\) columns.  The number of such entries is therefore the sum over
\(k\ge3\) of the multiplicity of \(k-2\) in the row overlap multiset, which is
read from the Schur function.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.Overlaps

namespace Profile

variable {n : ℕ}

/-- Every entry on or above the first subdiagonal of the full board has nonnegative index. -/
theorem index_nonneg_of_le_succ (P : Profile n) (i j : Fin (n + 1))
    (h : i.val ≤ j.val + 1) :
    0 ≤ P.xi i - P.zeta j := by
  rcases Nat.lt_or_ge j.val i.val with hlt | hge
  · have hi : i.val = j.val + 1 := by omega
    have hj : j.val < n := by omega
    have e := P.xi_succ_sub_zeta_castSucc ⟨j.val, hj⟩
    have e1 : (⟨j.val, hj⟩ : Fin n).succ = i := Fin.ext (by simp [hi])
    have e2 : (⟨j.val, hj⟩ : Fin n).castSucc = j := Fin.ext (by simp)
    rw [e1, e2] at e
    omega
  · have hij : i ≤ j := hge
    have h1 : P.xi j ≤ P.xi i := P.xi_strictAnti.antitone hij
    have h2 := P.xi_sub_zeta j
    have h3 := P.r_pos j
    omega

/-- The number of full board entries of index minus one. -/
def negOneCount (P : Profile n) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun p =>
    P.toBetaRows.xi p.1 - P.toBetaRows.zeta p.2 = -1).card

theorem negOneCount_eq_zero_iff (P : Profile n) :
    P.negOneCount = 0 ↔ ∀ i j : Fin (n + 1), P.xi i - P.zeta j ≠ -1 := by
  unfold negOneCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i j
    have := h (x := (i.val, j.val)) (by simp only [Finset.mem_product, Finset.mem_range]; omega)
    rwa [Gluing.Profile.toBetaRows_xi, Gluing.Profile.toBetaRows_zeta] at this
  · intro h p hp
    have hp1 : p.1 < n + 1 := by simpa using (Finset.mem_product.mp hp).1
    have hp2 : p.2 < n + 1 := by simpa using (Finset.mem_product.mp hp).2
    have := h ⟨p.1, hp1⟩ ⟨p.2, hp2⟩
    have e1 := Gluing.Profile.toBetaRows_xi P ⟨p.1, hp1⟩
    have e2 := Gluing.Profile.toBetaRows_zeta P ⟨p.2, hp2⟩
    simp only at e1 e2
    rw [e1, e2]
    exact this

/-- Entries of index minus one lie at least two steps below the diagonal. -/
theorem two_le_of_index_neg_one (P : Profile n) {i j : ℕ} (hi : i < n + 1) (hj : j < n + 1)
    (h : P.toBetaRows.xi i - P.toBetaRows.zeta j = -1) : j + 2 ≤ i := by
  by_contra hc
  have := Profile.index_nonneg_of_le_succ P ⟨i, hi⟩ ⟨j, hj⟩ (by simp only; omega)
  have e1 := Gluing.Profile.toBetaRows_xi P ⟨i, hi⟩
  have e2 := Gluing.Profile.toBetaRows_zeta P ⟨j, hj⟩
  simp only at e1 e2 this
  omega

/-- The count of index minus one entries, as a sum of overlap multiplicities. -/
theorem negOneCount_eq_sum (P : Profile n) :
    P.negOneCount = ∑ d ∈ Finset.Icc 2 n,
      Multiset.count (d - 1) (Gluing.Profile.rowOverlapPartition P (d + 1)) := by
  classical
  set B := P.toBetaRows with hB
  have hfib : ∀ d ∈ Finset.Icc 2 n,
      Multiset.count (d - 1) (Gluing.Profile.rowOverlapPartition P (d + 1)) =
        ((Finset.range (n + 1 - d)).filter fun j => B.xi (j + d) - B.zeta j = -1).card := by
    intro d hd
    have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hd).1
    rw [Gluing.Profile.rowOverlapPartition, BetaRows.overlaps, Multiset.count_map]
    simp only [Nat.add_sub_cancel]
    change (Finset.filter (fun j => d - 1 = B.overlap d j) (Finset.range (n + 1 - d))).card = _
    congr 1
    apply Finset.filter_congr
    intro j _
    simp only [BetaRows.overlap]
    constructor
    · intro h
      omega
    · intro h
      omega
  rw [Finset.sum_congr rfl hfib, ← Finset.card_sigma]
  unfold negOneCount
  apply Finset.card_bij' (fun p _ => (⟨p.1 - p.2, p.2⟩ : (_ : ℕ) × ℕ))
    (fun s _ => (s.2 + s.1, s.2))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    have h2 := Profile.two_le_of_index_neg_one P hp.1.1 hp.1.2 hp.2
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
    have : p.2 + (p.1 - p.2) = p.1 := by omega
    rw [this]; exact hp.2
  · intro s hs
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range,
      Finset.mem_product] at hs ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    exact hs.2.2
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    have h2 := Profile.two_le_of_index_neg_one P hp.1.1 hp.1.2 hp.2
    ext <;> simp <;> omega
  · intro s _
    ext <;> simp

/-- Schur-equal connected profiles have equally many entries of index minus one. -/
theorem negOneCount_eq_of_profileSchur_eq {P Q : Profile n}
    (h : profileSchur P = profileSchur Q) : P.negOneCount = Q.negOneCount := by
  rw [negOneCount_eq_sum, negOneCount_eq_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [Gluing.Profile.rowOverlapPartition_eq_of_schur_eq 
    ((profileSchur_eq_inherited P).symm.trans (h.trans (profileSchur_eq_inherited Q))) (d + 1)]

end Profile
end SkewClassInflation
