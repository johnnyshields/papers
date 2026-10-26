import SkewGluing.SmallOverlap.WordsEq

/-!
# The singleton root of period `g`, case (b)

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the singleton construction in the case of two vertical
attachments.

`exists_singletonRoot_b`: a connected skew diagram `F` of span `M g + 1` whose boundary words
satisfy the singleton coding `eq:gluing-singleton` of case (b) at period `g`, with the end bits and
the private drift of a width-one root, has a proper root of period `g` and width one in case (b).

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace SmallOverlap

/-- **`lem:gluing-small`, the singleton construction, case (b).**  A connected skew `F` of span
`M g + 1` whose boundary words satisfy `eq:gluing-singleton` of case (b) at period `g`, with the end
bits `1` and the private drift of a width-one root, has a proper root of period `g`, width one and
case (b): the inner is `fromBits (g + 1)` of the first `g - 1` bits and the terminal bit `1`, the
outer is read from `1 - B_{jg}` and `1 - A_{jg+1}`.  **Differs from the paper's route.**  The paper
obtains case (b) from case (a) by antitransposition; here it is constructed directly. -/
theorem exists_singletonRoot_b {F : Diagram} (hF : IsConnectedSkew F) {g M : ℕ} (hg : 2 ≤ g)
    (hM : 2 ≤ M) (hN : span F = M * g + 1)
    (htab : SingletonTable (span F - 1) g .b (wordA F) (wordB F))
    (hA1 : wordA F 1 = 1) (hB1 : wordB F 1 = 1) (hAN : wordA F ((M * g : ℕ) : ℤ) = 1)
    (hBN : wordB F ((M * g : ℕ) : ℤ) = 1) (hpen : heightWord (wA F) (wB F) (g - 1) = 1) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧ χ.period = g ∧ χ.ω.width = 1 ∧
      χ.ω.case = .b := by
  obtain ⟨hA, hB, hAg, -⟩ := htab
  have hL : span F - 1 = M * g := by omega
  have hA' : PeriodWords.PeriodExcept (M * g) g {1} (wordA F) := by simpa [hL] using hA
  have hB' : PeriodWords.PeriodExcept (M * g) g {0} (wordB F) := by simpa [hL] using hB
  have hgp : 0 < g := by omega
  have hbd := isBitData_of_isConnectedSkew hF
  -- the inner
  have hinner : SingletonInnerData g (innerBits F g 1 (wA F)) (innerBits F g 1 (wB F)) :=
    SingletonInnerData.of_F hF hg hN (by omega) (Or.inr rfl) (by rw [hA1, hB1]) hpen
  have hcb : CaseBits .b (innerBits F g 1 (wA F) 1) (innerBits F g 1 (wA F) g) := by
    refine ⟨?_, by simp [innerBits]⟩
    simp only [innerBits, show (1 : ℕ) ≠ g by omega, ite_false, wA]
    simpa using hA1
  -- constants of the classes
  have hA0 : ∀ j : ℕ, 1 ≤ j → j ≤ M → wordA F ((j * g : ℕ) : ℤ) = 1 := by
    intro j hj1 hj2
    have hx := periodExcept_eq_of_dvd hA' hgp (x := (g : ℤ)) (y := ((j * g : ℕ) : ℤ)) (by omega)
      (by push_cast; nlinarith) (by push_cast; nlinarith) ⟨(j - 1 : ℤ), by push_cast; ring⟩
      (by simp)
    rw [← hx]; exact hAg
  have hB1j : ∀ j : ℕ, j + 1 ≤ M → wordB F ((j * g + 1 : ℕ) : ℤ) = 1 := by
    intro j hj
    have hx := periodExcept_eq_of_dvd hB' hgp (x := 1) (y := ((j * g + 1 : ℕ) : ℤ)) (by omega)
      (by push_cast; nlinarith) (by push_cast; nlinarith) ⟨j, by push_cast; ring⟩
      (by rw [Int.emod_eq_of_lt (by omega) (by omega)]; simp)
    rw [← hx]; exact hB1
  -- the outer
  obtain ⟨fA, hfA⟩ : ∃ fA : ℕ → ℤ, fA = fun j => 1 - wordB F ((j * g : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨fB, hfB⟩ : ∃ fB : ℕ → ℤ, fB = fun j => 1 - wordA F ((j * g + 1 : ℕ) : ℤ) := ⟨_, rfl⟩
  have houter : IsBitData M fA fB := by
    refine outer_isBitData hF hg hM hN hA hB (by simp) (by simp) (by rw [hA1, hB1])
      hpen (by rw [hAN, hBN]) ?_ ?_
    · intro j hj1 hj2
      have h1 : 1 ≤ j * g := by nlinarith
      have h2 : j * g < M * g := Nat.mul_lt_mul_of_pos_right (by omega) hgp
      refine ⟨?_, ?_⟩
      · rw [hfA]
        have h3 : wordB F ((j * g : ℕ) : ℤ) = 0 ∨ wordB F ((j * g : ℕ) : ℤ) = 1 :=
          (hbd.2.1 (j * g) h1 (by omega)).2
        simp only
        omega
      · rw [hfB]
        have h3 : wordA F ((j * g + 1 : ℕ) : ℤ) = 0 ∨ wordA F ((j * g + 1 : ℕ) : ℤ) = 1 :=
          (hbd.2.1 (j * g + 1) (by omega) (by omega)).1
        simp only
        omega
    · intro j hj1 hj2
      rw [hfA, hfB]
      simp only
      rw [hA0 j hj1 (by omega), hB1j j hj2]
      ring
  have hD'c : IsConnectedSkew (fromBits M fA fB) := isConnectedSkew_fromBits houter
  have hD'sp : span (fromBits M fA fB) = M := span_fromBits houter
  have hlegal := hinner.isLegalNonempty .b hcb
  have hwZ := hinner.widthZ .b
  have hph := hlegal.isPhases_one hwZ
  have hper := hinner.singletonMark_period .b
  have hspan' : span ((singletonMark (fromBits (g + 1) (innerBits F g 1 (wA F))
      (innerBits F g 1 (wB F))) .b).compose (fromBits M fA fB)) = M * g + 1 := by
    have := hinner.span_compose .b hcb hD'c
    rw [hD'sp] at this
    exact_mod_cast this
  obtain ⟨pA, pB⟩ := hlegal.gluing_coding_periodic hD'c hph
  have hpt : (singletonMark (fromBits (g + 1) (innerBits F g 1 (wA F))
      (innerBits F g 1 (wB F))) .b).period.toNat = g := by rw [hper]; simp
  rw [hpt, hspan'] at pA pB
  simp only [holesA, holesB, singletonMark, Nat.add_sub_cancel] at pA pB
  have hmD : minContent (fromBits M fA fB) = 0 := minContent_fromBits houter
  have wD'A : ∀ j : ℕ, 1 ≤ j → j < M → wordA (fromBits M fA fB) (j : ℤ) = fA j := by
    intro j hj1 hj2
    have := bitA_fromBits houter (k := j) hj1 hj2
    rw [hmD] at this
    simpa [wordA, hmD] using this
  have wD'B : ∀ j : ℕ, 1 ≤ j → j < M → wordB (fromBits M fA fB) (j : ℤ) = fB j := by
    intro j hj1 hj2
    have := bitB_fromBits houter (k := j) hj1 hj2
    rw [hmD] at this
    simpa [wordB, hmD] using this
  have hDA : ∀ j : ℤ, 1 ≤ j → j < M → wordA (fromBits M fA fB) j = 1 - wordB F (j * g) := by
    intro j hj1 hj2
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = n := ⟨j.toNat, by omega⟩
    rw [wD'A n (by omega) (by omega), hfA]
    simp
  have hDB : ∀ j : ℤ, 1 ≤ j → j < M → wordB (fromBits M fA fB) j = 1 - wordA F (j * g + 1) := by
    intro j hj1 hj2
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = n := ⟨j.toNat, by omega⟩
    rw [wD'B n (by omega) (by omega), hfB]
    simp
  have hfirst : ∀ x : ℤ, 1 ≤ x → x < g →
      wordA ((singletonMark (fromBits (g + 1) (innerBits F g 1 (wA F))
        (innerBits F g 1 (wB F))) .b).compose (fromBits M fA fB)) x = wordA F x ∧
      wordB ((singletonMark (fromBits (g + 1) (innerBits F g 1 (wA F))
        (innerBits F g 1 (wB F))) .b).compose (fromBits M fA fB)) x = wordB F x := by
    intro x hx1 hx2
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, x = n := ⟨x.toNat, by omega⟩
    obtain ⟨e1, e2⟩ := hinner.compose_first .b hcb hD'c (x := n) (by omega) (by omega)
    simp only [innerBits, show n ≠ g by omega, ite_false, wA, wB] at e1 e2
    exact ⟨e1, e2⟩
  have hall := words_eq_b hg hM hlegal rfl hwZ hper hD'c hD'sp hspan' hfirst hDA hDB hA' hB' hAg
    (by simpa using hBN)
  have hcc := hlegal.1.isConnectedSkew_compose hD'c
  obtain ⟨v, hv⟩ := eq_translate_of_bits hcc hF (by rw [hspan', hN]) (fun k hk1 hk2 => by
      have := (hall k (by omega) (by rw [hspan'] at hk2; omega)).1
      exact this) (fun k hk1 hk2 => by
      have := (hall k (by omega) (by rw [hspan'] at hk2; omega)).2
      exact this)
  refine ⟨⟨fromBits M fA fB, singletonMark (fromBits (g + 1) (innerBits F g 1 (wA F))
    (innerBits F g 1 (wB F))) .b⟩, ⟨hD'c, ?_, ?_, hlegal.1⟩, ⟨v, hv⟩, ?_, ?_, rfl⟩
  · change 2 ≤ (fromBits M fA fB).card
    have := card_ge_span (D := fromBits M fA fB); omega
  · change 2 ≤ (fromBits (g + 1) (innerBits F g 1 (wA F)) (innerBits F g 1 (wB F))).card
    have := card_ge_span (D := fromBits (g + 1) (innerBits F g 1 (wA F)) (innerBits F g 1 (wB F)))
    have h2 := span_fromBits hinner.bits
    omega
  · exact hper
  · have := hinner.singletonMark_width .b
    exact this

end SmallOverlap
end SkewGluing
