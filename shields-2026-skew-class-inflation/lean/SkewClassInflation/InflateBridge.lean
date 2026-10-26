/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.ProfileWords
import SkewClassInflation.CellProfiles
import SkewGluing.Coding

/-!
# From zero-freeness of an inflated board to the words of the diagram

Formalizes the first paragraph of the proof of `lem:inflate-chart` in
`shields-2026-skew-class-inflation.tex`: the diagram words
\(A_k=\ell_{k-1}-\ell_k\), \(B_k=h_{k-1}-h_k\) of a connected skew diagram agree on the internal
steps with the membership words of its beta lists, so that zero-freeness of the inflated board
is the vanishing of \(B_T(j)A_T(j+1)\) on the diagram words of \(T\).  At width zero the coding
of the composite then forces \(A_V(1)=B_V(q-1)=0\) on the inner.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

theorem lt_card_filter_iff {m : ℕ} (f : Fin m → Prop) [DecidablePred f]
    (hf : ∀ i j : Fin m, i ≤ j → f j → f i) (j : Fin m) :
    f j ↔ j.val < (Finset.univ.filter f).card := by
  constructor
  · intro hj
    have h : Finset.Iic j ⊆ Finset.univ.filter f := fun i hi => by
      simp only [Finset.mem_Iic] at hi
      simp [hf i j hi hj]
    have := Finset.card_le_card h
    simp only [Fin.card_Iic] at this
    omega
  · intro hj
    by_contra hnj
    have h : Finset.univ.filter f ⊆ Finset.Iio j := fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_Iio]
      by_contra hij
      exact hnj (hf j i (not_lt.mp hij) hi)
    have := Finset.card_le_card h
    simp only [Fin.card_Iio] at this
    omega

namespace Profile

variable {n : ℕ}

theorem mem_diag_profileCells (P : Profile n) (a k : ℤ) :
    (a, a + k) ∈ profileCells P ↔
      ∃ j : Fin (n + 1), (j.val : ℤ) = a ∧ P.zeta j ≤ k ∧ k < P.xi j := by
  rw [mem_profileCells]
  constructor
  · rintro ⟨j, h1, h2, h3⟩
    exact ⟨j, h1, by omega, by omega⟩
  · rintro ⟨j, h1, h2, h3⟩
    exact ⟨j, h1, by omega, by omega⟩

/-- The rows whose column beta exceeds `k` form an initial segment. -/
theorem lt_zeta_iff (P : Profile n) (k : ℤ) (j : Fin (n + 1)) :
    k < P.zeta j ↔ j.val < (Finset.univ.filter fun i : Fin (n + 1) => k < P.zeta i).card :=
  lt_card_filter_iff (fun i => k < P.zeta i)
    (fun _ _ hij hj => lt_of_lt_of_le hj (P.zeta_strictAnti.antitone hij)) j

/-- The rows whose row beta exceeds `k` form an initial segment. -/
theorem lt_xi_iff (P : Profile n) (k : ℤ) (j : Fin (n + 1)) :
    k < P.xi j ↔ j.val < (Finset.univ.filter fun i : Fin (n + 1) => k < P.xi i).card :=
  lt_card_filter_iff (fun i => k < P.xi i)
    (fun _ _ hij hj => lt_of_lt_of_le hj (P.xi_strictAnti.antitone hij)) j

/-- The first and last rows of the diagonal of content `k` of the cell diagram. -/
theorem diag_profileCells (P : Profile n) {k : ℤ} (h0 : 0 ≤ k) (h1 : k < P.xi 0) :
    SkewGluing.diagLo (profileCells P) k =
        ((Finset.univ.filter fun i : Fin (n + 1) => k < P.zeta i).card : ℤ) ∧
      SkewGluing.diagHi (profileCells P) k =
        ((Finset.univ.filter fun i : Fin (n + 1) => k < P.xi i).card : ℤ) - 1 := by
  set s := (Finset.univ.filter fun i : Fin (n + 1) => k < P.zeta i).card with hs
  set t := (Finset.univ.filter fun i : Fin (n + 1) => k < P.xi i).card with ht
  have hsn : s < n + 1 := by
    have := (P.lt_zeta_iff k (Fin.last n)).not
    rw [P.zeta_last] at this
    have h2 : ¬ k < 0 := by omega
    have := this.mp h2
    simp only [Fin.val_last, not_lt] at this
    have h3 := Finset.card_le_univ (Finset.univ.filter fun i : Fin (n + 1) => k < P.zeta i)
    simp only [Fintype.card_fin] at h3
    omega
  have hst : s < t := by
    set j : Fin (n + 1) := ⟨s, hsn⟩ with hj
    have : k < P.xi j := by
      by_cases h : s = 0
      · have e : j = 0 := Fin.ext (by simp [hj, h])
        rw [e]; exact h1
      · have hn : s - 1 < n := by omega
        set i : Fin n := ⟨s - 1, hn⟩
        have hi1 : i.castSucc = (⟨s - 1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
        have hi2 : i.succ = j := Fin.ext (by simp [i, hj]; omega)
        have a1 : k < P.zeta i.castSucc := (P.lt_zeta_iff k _).mpr (by simp [i]; omega)
        have a2 := P.xi_succ_sub_zeta_castSucc i
        rw [hi2] at a2
        have : (0 : ℤ) ≤ P.g i := by positivity
        omega
    have := (P.lt_xi_iff k j).mp this
    simpa [hj] using this
  have htn : t ≤ n + 1 := by
    have h3 := Finset.card_le_univ (Finset.univ.filter fun i : Fin (n + 1) => k < P.xi i)
    simpa using h3
  constructor
  · apply SkewGluing.diagLo_eq_of
    · rw [mem_diag_profileCells]
      refine ⟨⟨s, hsn⟩, rfl, ?_, ?_⟩
      · by_contra hc
        have := (P.lt_zeta_iff k ⟨s, hsn⟩).mp (not_le.mp hc)
        simp only at this
        omega
      · exact (P.lt_xi_iff k _).mpr hst
    · intro i hi
      obtain ⟨j, hj1, hj2, hj3⟩ := (mem_diag_profileCells P i k).mp hi
      subst hj1
      by_contra hc
      have := (P.lt_zeta_iff k j).mpr (by omega)
      omega
  · apply SkewGluing.diagHi_eq_of
    · rw [mem_diag_profileCells]
      refine ⟨⟨t - 1, by omega⟩, by simp; omega, ?_, ?_⟩
      · by_contra hc
        have := (P.lt_zeta_iff k ⟨t - 1, by omega⟩).mp (not_le.mp hc)
        simp at this
        omega
      · exact (P.lt_xi_iff k _).mpr (by simp; omega)
    · intro i hi
      obtain ⟨j, hj1, hj2, hj3⟩ := (mem_diag_profileCells P i k).mp hi
      subst hj1
      have := (P.lt_xi_iff k j).mp hj3
      omega

theorem card_filter_eq_ite {m : ℕ} {g : Fin m → ℤ} (hg : Function.Injective g) (k : ℤ) :
    ((Finset.univ.filter fun i : Fin m => g i = k).card : ℤ) =
      if ∃ i, g i = k then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    have : (Finset.univ.filter fun i : Fin m => g i = k) = {i} := by
      ext i'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h' => hg (h'.trans hi.symm), fun h' => h' ▸ hi⟩
    rw [this]; simp
  · have : (Finset.univ.filter fun i : Fin m => g i = k) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _ hi
      exact h ⟨i, hi⟩
    rw [this]; simp

theorem card_lt_sub {m : ℕ} (g : Fin m → ℤ) (k : ℤ) :
    ((Finset.univ.filter fun i : Fin m => k - 1 < g i).card : ℤ) -
        (Finset.univ.filter fun i : Fin m => k < g i).card =
      (Finset.univ.filter fun i : Fin m => g i = k).card := by
  have hsplit : (Finset.univ.filter fun i : Fin m => k - 1 < g i) =
      (Finset.univ.filter fun i : Fin m => k < g i) ∪
        Finset.univ.filter fun i : Fin m => g i = k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.univ.filter fun i : Fin m => k < g i)
      (Finset.univ.filter fun i : Fin m => g i = k) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  push_cast
  ring

/-- **The words of the cell diagram.**  On the internal steps `1 ≤ k < N`, the diagram word
`A_k = ℓ_{k-1} - ℓ_k` of the cell diagram is the membership word of the column beta list. -/
theorem bitA_profileCells (P : Profile n) {k : ℤ} (h1 : 1 ≤ k) (h2 : k < P.xi 0) :
    SkewGluing.bitA (profileCells P) k = wordA P k := by
  unfold SkewGluing.bitA wordA
  rw [(diag_profileCells P (by omega) (by omega)).1, (diag_profileCells P (by omega) h2).1,
    card_lt_sub P.zeta k]
  exact card_filter_eq_ite P.zeta_strictAnti.injective k

/-- On the internal steps, the diagram word `B_k = h_{k-1} - h_k` is the membership word of the
row beta list. -/
theorem bitB_profileCells (P : Profile n) {k : ℤ} (h1 : 1 ≤ k) (h2 : k < P.xi 0) :
    SkewGluing.bitB (profileCells P) k = wordB P k := by
  unfold SkewGluing.bitB wordB
  rw [(diag_profileCells P (by omega) (by omega)).2, (diag_profileCells P (by omega) h2).2]
  have := card_lt_sub P.xi k
  have h3 := card_filter_eq_ite P.xi_strictAnti.injective k
  rw [← h3, ← this]
  ring

theorem minContent_profileCells (P : Profile n) : SkewGluing.minContent (profileCells P) = 0 := by
  have hne : (profileCells P).Nonempty :=
    (SkewGluing.isConnectedSkew_iff_diagonal.mp (profileCells_connected P)).1
  have h := profileCells_contents P
  have hc := SkewGluing.minContent_mem hne
  have h0 : (0 : ℤ) ∈ SkewGluing.contents (profileCells P) := by
    rw [h, Finset.mem_Icc]; have := P.xi_pos 0; omega
  have := SkewGluing.minContent_le h0
  rw [h, Finset.mem_Icc] at hc
  omega

/-- The membership words of a profile are supported in the internal range. -/
theorem wordB_support (P : Profile n) {m : ℤ} (h : wordB P m = 1) : 1 ≤ m ∧ m ≤ P.xi 0 := by
  unfold wordB at h
  by_cases hx : ∃ i, P.xi i = m
  · obtain ⟨i, hi⟩ := hx
    have h1 := P.xi_pos i
    have h2 := P.xi_strictAnti.antitone (Fin.zero_le i)
    omega
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' hx)] at h; exact absurd h (by norm_num)

theorem wordA_support (P : Profile n) {m : ℤ} (h : wordA P m = 1) : 0 ≤ m ∧ m < P.xi 0 := by
  unfold wordA at h
  by_cases hx : ∃ i, P.zeta i = m
  · obtain ⟨i, hi⟩ := hx
    have h1 := P.zeta_nonneg i
    have h2 := P.zeta_strictAnti.antitone (Fin.zero_le i)
    have h3 := P.xi_sub_zeta 0
    have h4 := P.r_pos 0
    omega
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' hx)] at h; exact absurd h (by norm_num)

/-- **Zero-freeness of the inflated board in the words of the diagram.**  The inflation of a
profile is zero-free exactly when `B(j) A(j + 1) = 0` on the internal steps of the diagram words
of its cell diagram. -/
theorem zeroFree_inflate_one_iff_diagram (P : Profile n) :
    (inflate 1 P).ZeroFree ↔ ∀ j : ℤ, 1 ≤ j → j + 1 < P.xi 0 →
      SkewGluing.bitB (profileCells P) j * SkewGluing.bitA (profileCells P) (j + 1) = 0 := by
  rw [zeroFree_inflate_one_iff]
  have hB01 : ∀ m, wordB P m = 0 ∨ wordB P m = 1 := by
    intro m; unfold wordB; split_ifs <;> simp
  have hA01 : ∀ m, wordA P m = 0 ∨ wordA P m = 1 := by
    intro m; unfold wordA; split_ifs <;> simp
  constructor
  · intro h j h1 h2
    rw [bitB_profileCells P h1 (by omega), bitA_profileCells P (by omega) h2]
    exact h j
  · intro h m
    by_contra hm
    have hb : wordB P m = 1 := by
      rcases hB01 m with h' | h' <;> rcases hA01 (m + 1) with h'' | h'' <;> simp_all
    have ha : wordA P (m + 1) = 1 := by
      rcases hB01 m with h' | h' <;> rcases hA01 (m + 1) with h'' | h'' <;> simp_all
    have s1 := wordB_support P hb
    have s2 := wordA_support P ha
    have := h m s1.1 (by omega)
    rw [bitB_profileCells P s1.1 (by omega), bitA_profileCells P (by omega) s2.2, hb, ha] at this
    simp at this

end Profile

/-- **`lem:inflate-chart`, first step, on an arbitrary position of the chart.**  If the chart
`T` is a translate of the cell diagram of the profile `P`, the inflated board is zero-free exactly
when `B_T(j) A_T(j + 1) = 0` for the diagram words of `T`, on the internal steps. -/
theorem zeroFree_inflate_one_iff_words {n : ℕ} (P : Profile n) {T : SkewGluing.Diagram}
    {v : ℤ × ℤ} (hT : T = SkewGluing.translate v (profileCells P)) :
    (Profile.inflate 1 P).ZeroFree ↔ ∀ j : ℤ, 1 ≤ j → j + 1 < (SkewGluing.span T : ℤ) →
      SkewGluing.wordB T j * SkewGluing.wordA T (j + 1) = 0 := by
  have hc := profileCells_connected P
  have hspan : (SkewGluing.span T : ℤ) = P.xi 0 := by
    rw [hT, SkewGluing.span_translate]; exact profileCells_span P
  have hw : ∀ j : ℤ, 1 ≤ j → j < P.xi 0 →
      SkewGluing.wordA T j = SkewGluing.bitA (profileCells P) j ∧
        SkewGluing.wordB T j = SkewGluing.bitB (profileCells P) j := by
    intro j h1 h2
    have e1 : j < (SkewGluing.span (profileCells P) : ℤ) := by rw [profileCells_span]; exact h2
    rw [hT, SkewGluing.wordA_translate hc v h1 e1, SkewGluing.wordB_translate hc v h1 e1]
    unfold SkewGluing.wordA SkewGluing.wordB
    rw [Profile.minContent_profileCells]
    simp only [zero_add, and_self]
  rw [Profile.zeroFree_inflate_one_iff_diagram, hspan]
  constructor
  · intro h j h1 h2
    rw [(hw j h1 (by omega)).2, (hw (j + 1) (by omega) h2).1]
    exact h j h1 h2
  · intro h j h1 h2
    have := h j h1 h2
    rw [(hw j h1 (by omega)).2, (hw (j + 1) (by omega) h2).1] at this
    exact this

/-! ### A connected diagram that is not a row has a one in each word -/

section NotRow

open SkewGluing

/-- A single row: every cell lies in one row. -/
def IsRowDiagram (D : Diagram) : Prop := ∃ a : ℤ, ∀ x ∈ D, x.1 = a

variable {D : Diagram}

theorem wordA_zero_of_ne_one (hD : IsConnectedSkew D) {j : ℤ} (h1 : 1 ≤ j)
    (h2 : j < (span D : ℤ)) (hne : SkewGluing.wordA D j ≠ 1) : bitA D (minContent D + j - 1 + 1) = 0 ∧
      diagLo D (minContent D + j - 1) = diagLo D (minContent D + j) := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hsp := span_eq_of_isConnectedSkew hD
  have hc := hs.contents_eq
  have := (hs.2.2.2.1 (minContent D + j) (by rw [hc, Finset.mem_Icc]; omega)
    (by rw [hc, Finset.mem_Icc]; omega)).1
  unfold SkewGluing.wordA at hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  have e : minContent D + j - 1 + 1 = minContent D + j := by ring
  rw [e]
  unfold bitA at this hne ⊢
  constructor <;> omega

/-- A connected skew diagram that is not a row has a one in its word `A`. -/
theorem exists_wordA_one (hD : IsConnectedSkew D) (hrow : ¬ IsRowDiagram D) :
    ∃ j : ℤ, 1 ≤ j ∧ j < (span D : ℤ) ∧ SkewGluing.wordA D j = 1 := by
  by_contra hno
  push Not at hno
  apply hrow
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hsp := span_eq_of_isConnectedSkew hD
  have hc := hs.contents_eq
  have hne := hs.1
  have hle : minContent D ≤ maxContent D := minContent_le (maxContent_mem hne)
  have hconst : ∀ k, minContent D ≤ k → k ≤ maxContent D →
      diagLo D k = diagLo D (minContent D) := by
    intro k hk
    induction k, hk using Int.leInduction with
    | base => intro _; rfl
    | succ n hn ih =>
      intro hn1
      have := (wordA_zero_of_ne_one hD (j := n + 1 - minContent D) (by omega) (by omega)
        (hno _ (by omega) (by omega))).2
      have e : minContent D + (n + 1 - minContent D) = n + 1 := by ring
      rw [e] at this
      have e2 : n + 1 - 1 = n := by ring
      rw [e2] at this
      rw [← this]
      exact ih (by omega)
  have hend0 := hs.2.2.2.2 (minContent D) (minContent_mem hne) (Or.inl (by
    rw [hc, Finset.mem_Icc]; omega))
  refine ⟨diagLo D (minContent D), fun x hx => ?_⟩
  obtain ⟨i, j'⟩ := x
  have hk : j' - i ∈ contents D := content_mem_contents hx
  have hk' := hk
  rw [hc, Finset.mem_Icc] at hk'
  have e : (i, j') = (i, i + (j' - i)) := by ext <;> simp
  rw [e] at hx
  have h1 := diagLo_le (k := j' - i) hx (by ring)
  have h2 := le_diagHi (k := j' - i) hx (by ring)
  have h3 := (hs.diagHi_anti (a := minContent D) (b := j' - i) (minContent_mem hne) hk
    (by omega)).1
  have h4 := hconst (j' - i) hk'.1 hk'.2
  change i = _
  omega

theorem wordB_zero_of_ne_one (hD : IsConnectedSkew D) {j : ℤ} (h1 : 1 ≤ j)
    (h2 : j < (span D : ℤ)) (hne : SkewGluing.wordB D j ≠ 1) :
      diagHi D (minContent D + j - 1) = diagHi D (minContent D + j) := by
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hsp := span_eq_of_isConnectedSkew hD
  have hc := hs.contents_eq
  have := (hs.2.2.2.1 (minContent D + j) (by rw [hc, Finset.mem_Icc]; omega)
    (by rw [hc, Finset.mem_Icc]; omega)).2
  unfold SkewGluing.wordB at hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  unfold bitB at this hne
  omega

/-- A connected skew diagram that is not a row has a one in its word `B`. -/
theorem exists_wordB_one (hD : IsConnectedSkew D) (hrow : ¬ IsRowDiagram D) :
    ∃ j : ℤ, 1 ≤ j ∧ j < (span D : ℤ) ∧ SkewGluing.wordB D j = 1 := by
  by_contra hno
  push Not at hno
  apply hrow
  have hs := isConnectedSkew_iff_diagonal.mp hD
  have hsp := span_eq_of_isConnectedSkew hD
  have hc := hs.contents_eq
  have hne := hs.1
  have hle : minContent D ≤ maxContent D := minContent_le (maxContent_mem hne)
  have hconst : ∀ k, minContent D ≤ k → k ≤ maxContent D →
      diagHi D k = diagHi D (minContent D) := by
    intro k hk
    induction k, hk using Int.leInduction with
    | base => intro _; rfl
    | succ n hn ih =>
      intro hn1
      have := wordB_zero_of_ne_one hD (j := n + 1 - minContent D) (by omega) (by omega)
        (hno _ (by omega) (by omega))
      have e3 : minContent D + (n + 1 - minContent D) - 1 = n := by ring
      have e : minContent D + (n + 1 - minContent D) = n + 1 := by ring
      rw [e3, e] at this
      rw [← this]
      exact ih (by omega)
  have hend0 := hs.2.2.2.2 (minContent D) (minContent_mem hne) (Or.inl (by
    rw [hc, Finset.mem_Icc]; omega))
  have hend1 := hs.2.2.2.2 (maxContent D) (maxContent_mem hne) (Or.inr (by
    rw [hc, Finset.mem_Icc]; omega))
  refine ⟨diagHi D (minContent D), fun x hx => ?_⟩
  obtain ⟨i, j'⟩ := x
  have hk : j' - i ∈ contents D := content_mem_contents hx
  have hk' := hk
  rw [hc, Finset.mem_Icc] at hk'
  have e : (i, j') = (i, i + (j' - i)) := by ext <;> simp
  rw [e] at hx
  have h1 := diagLo_le (k := j' - i) hx (by ring)
  have h2 := le_diagHi (k := j' - i) hx (by ring)
  have h3 := (hs.diagLo_anti (a := j' - i) (b := maxContent D) hk (maxContent_mem hne)
    hk'.2).1
  have h4 := hconst (j' - i) hk'.1 hk'.2
  have h5 := hconst (maxContent D) hle le_rfl
  change i = _
  omega

end NotRow

/-! ### Width zero: the constraints on the inner -/

namespace Width0

open SkewGluing SkewGluing.MarkedInner

variable {ω : MarkedInner} {D : Diagram}

/-- For the empty mark the words of the composite repeat the words of the inner on every block. -/
theorem wordAB_block (h : ω.IsLegalEmpty) (hD : IsConnectedSkew D) {j a : ℤ} (hj0 : 0 ≤ j)
    (hj : j < (span D : ℤ)) (ha1 : 1 ≤ a) (ha : a < ω.period) :
    SkewGluing.wordA (ω.compose D) (j * ω.period + a) = SkewGluing.wordA ω.E a ∧
      SkewGluing.wordB (ω.compose D) (j * ω.period + a) = SkewGluing.wordB ω.E a := by
  have hc := h.classRows hD
  have hmin := h.minContent_compose' hD
  have hsp := span_eq_of_isConnectedSkew hD
  have hw := h.width_zero
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ (minContent D + j) a :=
    Or.inl ⟨by omega, by omega⟩
  have hk : j * ω.period + a = ((minContent D + j) - minContent D) * ω.period + a := by ring
  have hne : a ≠ 0 := by omega
  constructor
  · rw [hc.wordA_class' hmin hk (by omega) ha hv (fun h0 => absurd h0 hne)]
    unfold classBitLo SkewGluing.wordA bitA
    simp only [hne, ite_false, MarkedInner.oRowLo, MarkedInner.lo]
    have e : minContent ω.E + (a - 1) = minContent ω.E + a - 1 := by ring
    rw [e]
    ring
  · rw [hc.wordB_class' hmin hk (by omega) ha hv (fun h0 => absurd h0 hne)]
    unfold classBitHi SkewGluing.wordB bitB
    simp only [hne, ite_false, MarkedInner.oRowHi, MarkedInner.hi]
    have e : minContent ω.E + (a - 1) = minContent ω.E + a - 1 := by ring
    rw [e]
    ring

/-- **Width zero, the constraints on the inner** (`lem:inflate-chart`, second assertion).  Let
the composite `T = D ∘_∅ V` of a connected outer with a one in each word satisfy
`B_T(j) A_T(j + 1) = 0`.  Then `A_V(1) = 0` and `B_V(q - 1) = 0`, for a period `q ≥ 2`.  The
joining step `jq` reads the bits of the outer, and the steps next to it read the first and last
bits of the inner. -/
theorem inner_constraints (h : ω.IsLegalEmpty) (hD : IsConnectedSkew D) (hq2 : 2 ≤ ω.period)
    (hAD : ∃ j : ℤ, 1 ≤ j ∧ j < (span D : ℤ) ∧ SkewGluing.wordA D j = 1)
    (hBD : ∃ j : ℤ, 1 ≤ j ∧ j < (span D : ℤ) ∧ SkewGluing.wordB D j = 1)
    (hz : ∀ j : ℤ, 1 ≤ j → j + 1 < (span (ω.compose D) : ℤ) →
      SkewGluing.wordB (ω.compose D) j * SkewGluing.wordA (ω.compose D) (j + 1) = 0) :
    SkewGluing.wordA ω.E 1 = 0 ∧ SkewGluing.wordB ω.E (ω.period - 1) = 0 := by
  have hsF := h.span_compose_eq hD
  have hsp := span_eq_of_isConnectedSkew hD
  have hq := h.period_pos
  constructor
  · obtain ⟨j, hj1, hj2, hj3⟩ := hBD
    have j1 := (h.joining hD hj1 hj2).2
    have j2 := (wordAB_block h hD (j := j) (a := 1) (by omega) hj2 le_rfl (by omega)).1
    have := hz (j * ω.period) (by nlinarith) (by
      rw [hsF]
      have : j + 1 ≤ maxContent D - minContent D + 1 := by omega
      nlinarith)
    rw [j1, hj3, one_mul, j2] at this
    exact this
  · obtain ⟨j, hj1, hj2, hj3⟩ := hAD
    have j1 := (h.joining hD hj1 hj2).1
    have j2 := (wordAB_block h hD (j := j - 1) (a := ω.period - 1) (by omega) (by omega)
      (by omega) (by omega)).2
    have e : (j - 1) * ω.period + (ω.period - 1) = j * ω.period - 1 := by ring
    rw [e] at j2
    have := hz (j * ω.period - 1) (by nlinarith) (by
      rw [hsF]
      have : j ≤ maxContent D - minContent D := by omega
      nlinarith)
    rw [j2, show j * ω.period - 1 + 1 = j * ω.period by ring, j1, hj3, mul_one] at this
    exact this

/-- **Width zero, from zero-freeness of the inflated chart.**  If the composite `T = D ∘_∅ V` of a
connected outer that is not a row with a legal empty mark of period `q ≥ 2` is a translate of the
cell diagram of `P` and the inflated board `I(T)` is zero-free, then `A_V(1) = B_V(q - 1) = 0`. -/
theorem inner_constraints_of_zeroFree (h : ω.IsLegalEmpty) (hD : IsConnectedSkew D)
    (hrow : ¬ IsRowDiagram D) (hq2 : 2 ≤ ω.period) {n : ℕ} {P : Profile n} {v : ℤ × ℤ}
    (hT : ω.compose D = SkewGluing.translate v (profileCells P))
    (hz : (Profile.inflate 1 P).ZeroFree) :
    SkewGluing.wordA ω.E 1 = 0 ∧ SkewGluing.wordB ω.E (ω.period - 1) = 0 :=
  inner_constraints h hD hq2 (exists_wordA_one hD hrow) (exists_wordB_one hD hrow)
    ((zeroFree_inflate_one_iff_words P hT).mp hz)

end Width0

/-! ### Positive width, case (a): the private bits of the inner -/

namespace PosWidthA

open SkewGluing SkewGluing.MarkedInner

variable {ω : MarkedInner} {D : Diagram}

theorem hex_a (hca : ω.case = .a) :
    ω.ordT = 0 := (ordT_eq_zero_iff (by simp [AttachCase.IsMixed, hca])).mpr hca

/-- Off the exceptional residue `t`, the word `A` of the composite repeats the word `A` of the
inner on the block of the outer diagonal `J`. -/
theorem blockA (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hca : ω.case = .a) {s t : ℤ}
    (hph : ω.IsPhases s t) {J a : ℤ} (hJ1 : minContent D ≤ J) (hJ2 : J ≤ maxContent D)
    (ha1 : 1 ≤ a) (haq : a < ω.period) (hat : a ≠ t) :
    SkewGluing.wordA (ω.compose D) ((J - minContent D) * ω.period + a) =
      SkewGluing.wordA ω.E a := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hz := hex_a hca
  have hc := ord_classRows h hD hmix
  have hmin := h.minContent_compose' hD
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a := Or.inl ⟨hJ1, hJ2⟩
  rw [hc.wordA_class' hmin rfl (by omega) haq hv (fun h0 => by omega),
    ord_classBitLo h hD hmix hph (by omega) haq hv (fun h0 => by omega)
      ⟨fun _ => hat, fun h1 => by omega⟩]
  have hne : a ≠ 0 := by omega
  simp only [hne, ite_false]
  unfold SkewGluing.wordA bitA MarkedInner.lo
  have e : minContent ω.E + (a - 1) = minContent ω.E + a - 1 := by ring
  rw [e]

/-- Off the exceptional residue `s`, the word `B` of the composite repeats the word `B` of the
inner on the block of the outer diagonal `J`. -/
theorem blockB (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hca : ω.case = .a) {s t : ℤ}
    (hph : ω.IsPhases s t) {J a : ℤ} (hJ1 : minContent D ≤ J) (hJ2 : J ≤ maxContent D)
    (ha1 : 1 ≤ a) (haq : a < ω.period) (has : a ≠ s) :
    SkewGluing.wordB (ω.compose D) ((J - minContent D) * ω.period + a) =
      SkewGluing.wordB ω.E a := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hz := hex_a hca
  have hc := ord_classRows h hD hmix
  have hmin := h.minContent_compose' hD
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J a := Or.inl ⟨hJ1, hJ2⟩
  rw [hc.wordB_class' hmin rfl (by omega) haq hv (fun h0 => by omega),
    ord_classBitHi h hD hmix hph (by omega) haq hv (fun h0 => by omega)
      ⟨fun _ => has, fun h1 => by omega⟩]
  have hne : a ≠ 0 := by omega
  simp only [hne, ite_false]
  unfold SkewGluing.wordB bitB MarkedInner.hi
  have e : minContent ω.E + (a - 1) = minContent ω.E + a - 1 := by ring
  rw [e]

/-- At the first slot of the exceptional residue `s`, the word `B` of the composite is the word
`B` of the inner plus the word `B` of the outer. -/
theorem slotB (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hca : ω.case = .a) {s t : ℤ}
    (hph : ω.IsPhases s t) {J : ℤ} (hJ1 : minContent D + 1 ≤ J) (hJ2 : J ≤ maxContent D) :
    SkewGluing.wordB (ω.compose D) ((J - minContent D) * ω.period + s) =
      SkewGluing.wordB ω.E s + bitB D J := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hz := hex_a hca
  have hc := ord_classRows h hD hmix
  have hmin := h.minContent_compose' hD
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hq := h.width_lt_period
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J s := Or.inl ⟨by omega, hJ2⟩
  have hv' := validClass_pred hv
  rw [hc.wordB_class' hmin rfl (by omega) (by omega) hv (fun h0 => by omega)]
  have hs0 : s ≠ 0 := by omega
  unfold classBitHi
  simp only [hs0, ite_false]
  rw [ordHi_formula h hD hmix hph (by omega) hv', ordHi_formula h hD hmix hph (by omega) hv]
  unfold ordGHi
  simp only [hz, ite_true]
  unfold SkewGluing.wordB bitB MarkedInner.hi
  have e : minContent ω.E + s - 1 = minContent ω.E + (s - 1) := by ring
  rw [e]
  unfold ValidClass at hv
  split_ifs <;> omega

/-- At the residue zero with `t ≠ 0` the word `A` of the composite is one. -/
theorem resA_one (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hca : ω.case = .a) {s t : ℤ}
    (hph : ω.IsPhases s t) (ht0 : t ≠ 0) {J : ℤ} (hJ1 : minContent D + 1 ≤ J)
    (hJ2 : J ≤ maxContent D) :
    SkewGluing.wordA (ω.compose D) ((J - minContent D) * ω.period) = 1 := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hz := hex_a hca
  have hc := ord_classRows h hD hmix
  have hmin := h.minContent_compose' hD
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J 0 := Or.inl ⟨by omega, hJ2⟩
  have := hc.wordA_class' hmin (J := J) (a := 0) (k := (J - minContent D) * ω.period)
    (by ring) le_rfl (by omega) hv (fun _ => hJ1)
  rw [this, ord_classBitLo h hD hmix hph le_rfl (by omega) hv (fun _ => hJ1)
    ⟨fun _ => fun hh => ht0 hh.symm, fun h1 => by omega⟩]
  simp

/-- At the residue zero with `t = 0` the word `A` of the composite is the word `A` of the outer. -/
theorem resA_zero (h : ω.IsLegalNonempty) (hD : IsConnectedSkew D) (hca : ω.case = .a) {s t : ℤ}
    (hph : ω.IsPhases s t) (ht0 : t = 0) {J : ℤ} (hJ1 : minContent D + 1 ≤ J)
    (hJ2 : J ≤ maxContent D) :
    SkewGluing.wordA (ω.compose D) ((J - minContent D) * ω.period) = bitA D J := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hz := hex_a hca
  have hc := ord_classRows h hD hmix
  have hmin := h.minContent_compose' hD
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hcaps := (ord_E_facts h hmix).2
  have hv : ValidClass (minContent D) (maxContent D) ω.widthZ J 0 := Or.inl ⟨by omega, hJ2⟩
  rw [hc.wordA_class' hmin (J := J) (a := 0) (k := (J - minContent D) * ω.period)
    (by ring) le_rfl (by omega) hv (fun _ => hJ1)]
  unfold classBitLo
  simp only [ite_true]
  have hv' := validClass_prev (ω.period - 1) hv hJ1
  rw [ordLo_formula h hD hmix hph (by omega) hv', ordLo_formula h hD hmix hph le_rfl hv]
  unfold ValidClass at hv
  have hc1 := hcaps
  unfold dLo dHi at hc1
  simp only [zero_add] at hc1
  have hp : (J - 1) * ω.rowShift = J * ω.rowShift - ω.rowShift := by ring
  unfold ordGLo bitA
  simp only [hz, ite_true]
  split_ifs <;> omega

/-- In case (a) with a nonempty lower tail, the private diagonal `w` of the inner has
`B(w) = 1`. -/
theorem wordB_w_one (h : ω.IsLegalNonempty) (hca : ω.case = .a) {s t : ℤ}
    (hph : ω.IsPhases s t) (hsw : s < ω.widthZ) : SkewGluing.wordB ω.E ω.widthZ = 1 := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hz := hex_a hca
  have hw := h.width_pos
  have hcaps := (ord_E_facts h hmix).2
  have o := (ord_offsets h hmix hph (b := ω.widthZ - 1) (by omega) le_rfl).1 hz
  unfold dLo dHi at o hcaps
  have hc1 := hcaps.1 hz
  have hbin := h.1.1.1
  have hs := isConnectedSkew_iff_diagonal.mp hbin
  have hwq := h.width_lt_period
  have hspan := h.1.1.span_eq
  have hspan' := span_eq_of_isConnectedSkew hbin
  have hwz : ω.widthZ = (ω.width : ℤ) := rfl
  have hc := hs.contents_eq
  have hb := (hs.2.2.2.1 (minContent ω.E + ω.widthZ) (by
      rw [hc, Finset.mem_Icc]; omega)
    (by rw [hc, Finset.mem_Icc]; omega)).2
  unfold SkewGluing.wordB bitB
  unfold MarkedInner.hi at hc1 o
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  unfold bitB at hb
  have e : minContent ω.E + ω.widthZ - 1 = minContent ω.E + (ω.widthZ - 1) := by ring
  rw [e] at hb ⊢
  have := o.2.2.1 (by omega)
  omega

/-- **Positive width, case (a): the private bits of the inner** (`lem:inflate-chart`, first
assertion).  Let `ω` be a legal ordinary mark of case (a) with `0 < w` and `w + 1 < q`, and `D` a
connected outer with a one in each word.  If the composite `T = D ∘_ω E` satisfies
`B_T(j) A_T(j + 1) = 0`, then the private diagonals of the inflated inner are singletons:
`A_E(w + 1) = 0` and `B_E(q - 1) = 0`. -/
theorem private_bits (h : ω.IsLegalNonempty) (hca : ω.case = .a) (hD : IsConnectedSkew D)
    (hwq : ω.widthZ + 1 < ω.period)
    (hAD : ∃ j : ℤ, 1 ≤ j ∧ j < (span D : ℤ) ∧ SkewGluing.wordA D j = 1)
    (hBD : ∃ j : ℤ, 1 ≤ j ∧ j < (span D : ℤ) ∧ SkewGluing.wordB D j = 1)
    (hz : ∀ j : ℤ, 1 ≤ j → j + 1 < (span (ω.compose D) : ℤ) →
      SkewGluing.wordB (ω.compose D) j * SkewGluing.wordA (ω.compose D) (j + 1) = 0) :
    SkewGluing.wordA ω.E (ω.widthZ + 1) = 0 ∧ SkewGluing.wordB ω.E (ω.period - 1) = 0 := by
  obtain ⟨s, t, hph⟩ := h.exists_phases
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hw := h.width_pos
  have hsF := h.span_compose_eq hD
  have hsp := span_eq_of_isConnectedSkew hD
  have hmM : minContent D ≤ maxContent D := minContent_le (maxContent_mem hD.2.1)
  obtain ⟨jA, hjA1, hjA2, hjA3⟩ := hAD
  obtain ⟨jB, hjB1, hjB2, hjB3⟩ := hBD
  constructor
  · by_cases hsw : s < ω.widthZ
    · have hB1 := wordB_w_one h hca hph hsw
      have b1 := blockB h hD hca hph (J := minContent D) le_rfl hmM (a := ω.widthZ) (by omega)
        (by omega) (by omega)
      have a1 := blockA h hD hca hph (J := minContent D) le_rfl hmM (a := ω.widthZ + 1)
        (by omega) (by omega) (by omega)
      have := hz ((minContent D - minContent D) * ω.period + ω.widthZ) (by simp; omega) (by
        rw [hsF]; simp; nlinarith)
      rw [b1, hB1, one_mul, show (minContent D - minContent D) * ω.period + ω.widthZ + 1 =
        (minContent D - minContent D) * ω.period + (ω.widthZ + 1) by ring, a1] at this
      exact this
    · have hseq : s = ω.widthZ := by omega
      have s1 := slotB h hD hca hph (J := minContent D + jB) (by omega) (by omega)
      have a1 := blockA h hD hca hph (J := minContent D + jB) (by omega) (by omega)
        (a := ω.widthZ + 1) (by omega) (by omega) (by omega)
      have hpos : 0 ≤ SkewGluing.wordB ω.E s := by
        have hbin := h.1.1.1
        have hs := isConnectedSkew_iff_diagonal.mp hbin
        have hc := hs.contents_eq
        have hspan := h.1.1.span_eq
        have hspan' := span_eq_of_isConnectedSkew hbin
        have hwz : ω.widthZ = (ω.width : ℤ) := rfl
        have := (hs.2.2.2.1 (minContent ω.E + s) (by rw [hc, Finset.mem_Icc]; omega)
          (by rw [hc, Finset.mem_Icc]; omega)).2
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        unfold SkewGluing.wordB
        omega
      have hbD : bitB D (minContent D + jB) = 1 := hjB3
      have hx : 1 ≤ (minContent D + jB - minContent D) * ω.period + s := by nlinarith
      have := hz ((minContent D + jB - minContent D) * ω.period + s) hx (by
        rw [hsF]; nlinarith)
      rw [s1, show (minContent D + jB - minContent D) * ω.period + s + 1 =
        (minContent D + jB - minContent D) * ω.period + (ω.widthZ + 1) by rw [hseq]; ring, a1]
        at this
      have h2 : SkewGluing.wordB ω.E s + bitB D (minContent D + jB) ≠ 0 := by omega
      exact (mul_eq_zero.mp this).resolve_left h2
  · by_cases ht0 : t = 0
    · have r1 := resA_zero h hD hca hph ht0 (J := minContent D + jA) (by omega) (by omega)
      have b1 := blockB h hD hca hph (J := minContent D + jA - 1) (by omega) (by omega)
        (a := ω.period - 1) (by omega) (by omega) (by omega)
      have hA1 : bitA D (minContent D + jA) = 1 := hjA3
      have e : (minContent D + jA - 1 - minContent D) * ω.period + (ω.period - 1) =
          (minContent D + jA - minContent D) * ω.period - 1 := by ring
      rw [e] at b1
      have := hz ((minContent D + jA - minContent D) * ω.period - 1) (by nlinarith) (by
        rw [hsF]; nlinarith)
      rw [b1, show (minContent D + jA - minContent D) * ω.period - 1 + 1 =
        (minContent D + jA - minContent D) * ω.period by ring, r1, hA1, mul_one] at this
      exact this
    · have r1 := resA_one h hD hca hph ht0 (J := minContent D + 1) (by omega) (by omega)
      have b1 := blockB h hD hca hph (J := minContent D) le_rfl hmM
        (a := ω.period - 1) (by omega) (by omega) (by omega)
      have := hz ((minContent D - minContent D) * ω.period + (ω.period - 1)) (by simp; omega) (by
        rw [hsF]; simp; nlinarith)
      rw [b1, show (minContent D - minContent D) * ω.period + (ω.period - 1) + 1 =
        (minContent D + 1 - minContent D) * ω.period by ring, r1, mul_one] at this
      exact this

end PosWidthA

end SkewClassInflation
