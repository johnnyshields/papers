/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/MixedFold/Root.lean`. -/
import GluingCore.MarkTransfer
import GluingCore.MixedFold.Glue

/-!
# The period-`g` root as a chart

Formalizes `shields-2026-skew-factor-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`: "the composition is literally the parent").

`MixFoldFold.exists_chart` assembles the proof: from the word data `MixFoldFold` of a connected skew
parent `F`, the mark `mixFoldMark G g p` on the inner `G` (`MixFoldFold.diag`, legal by
`MixFoldDiag.legal`) and the outer `D = mixFoldOuter` of `eq:gluing-mixed-inverse` form a proper
legal chart of period `g`, width `v` and case (d) with `D ∘ G` a translate of `F`.  The composite is
compared with `F` on its bit words: the first window (`normalize_compose_first`), the last window
(`normalize_compose_last`), the interface `eq:gluing-interface`, and the caps `eq:gluing-caps` give
the hypotheses of `MixFoldFold.eq_words`.

Sorry-free.
-/

namespace GluingCore

open PeriodWords

theorem mixFold_two_le_card_of_span {D : Diagram} {n : ℕ} (h : n ≤ span D) : n ≤ D.card :=
  h.trans (Finset.card_image_le (s := D) (f := content))

namespace MixFoldFold

variable {F : Diagram} {g M v : ℕ} {α β : ℤ}

set_option maxHeartbeats 1600000 in
-- the assembly is one long chain of linear-arithmetic steps over many cast hypotheses
theorem exists_chart (hFc : IsConnectedSkew F)
    (hF : MixFoldFold (wordA F) (wordB F) (span F) g M v α β) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧ χ.ω.period.toNat = g ∧ χ.ω.case = .d ∧
      χ.ω.width = v := by
  have hbd : IsBitData (span F) (fun k : ℕ => wordA F k) (fun k : ℕ => wordB F k) :=
    isBitData_of_isConnectedSkew hFc
  have hdiag := hF.diag hbd
  obtain ⟨hleg, hph⟩ := hdiag.legal
  have hGbd := hF.isBitData hbd
  have hD'bd := hF.isBitData_outer hbd
  have hD'c : IsConnectedSkew (mixFoldOuter (wordA F) g M α β) := isConnectedSkew_fromBits hD'bd
  have hGc : IsConnectedSkew (mixFoldInner (wordA F) (wordB F) g M v) :=
    isConnectedSkew_fromBits hGbd
  have hspD' : span (mixFoldOuter (wordA F) g M α β) = M := span_fromBits hD'bd
  have hspG : span (mixFoldInner (wordA F) (wordB F) g M v) = g + v := span_fromBits hGbd
  have hvg := hF.hvg
  have hv0 := hF.hv0
  have hM := hF.hM
  have hα0 := hF.hα
  have hαβ := hF.hαβ
  have hβv := hF.hβv
  have hNN := hF.hN
  have hgpos : 0 < g := by omega
  have hNz : (span F : ℤ) = (M : ℤ) * g + v := by exact_mod_cast hNN
  have hMgz : (2 : ℤ) * g ≤ (M : ℤ) * g := by
    have : (2 : ℤ) ≤ M := by exact_mod_cast hM
    nlinarith
  set p := bitsLo (mixFoldGB (wordB F) g M v) g with hp
  set ω := mixFoldMark (mixFoldInner (wordA F) (wordB F) g M v) g p with hω
  set D' := mixFoldOuter (wordA F) g M α β with hD'
  have hper : ω.period = (g : ℤ) := MixFoldDiag.period_eq
  have hwid : ω.width = v := hdiag.width_eq
  have hwidZ : ω.widthZ = v := by unfold MarkedInner.widthZ; rw [hwid]
  have hCc : IsConnectedSkew (ω.compose D') := hleg.isConnectedSkew_compose hD'c
  have hspanC : span (ω.compose D') = span F := by
    have := MarkedInner.span_compose hD'c hleg.1
    rw [hspD', hper, hwid] at this
    have h2 : (span (ω.compose D') : ℤ) = ((M * g + v : ℕ) : ℤ) := by push_cast; linarith
    have := Nat.cast_injective h2
    omega
  have hspanCz : (span (ω.compose D') : ℤ) = (span F : ℤ) := by rw [hspanC]
  have hptoNat : ω.period.toNat = g := by rw [hper]; simp
  -- the coding of the composite
  obtain ⟨hPA, hPB⟩ := hleg.gluing_coding_periodic hD'c hph
  rw [hptoNat, hspanC] at hPA hPB
  have hPA' : PeriodExcept (span F - 1) g {α, β} (wordA (ω.compose D')) := by
    simpa [holesA, hω, mixFoldMark] using hPA
  have hPB' : PeriodExcept (span F - 1) g ∅ (wordB (ω.compose D')) := by
    simpa [holesB, hω, mixFoldMark] using hPB
  obtain ⟨cp1, cp2, cp3, cp4, cp5, cp6⟩ := hleg.caps_d hD'c rfl hph
  rw [hspanCz, hwidZ] at cp3 cp4
  rw [hwidZ] at cp5
  rw [hper] at cp6
  -- the first window
  have hfirstwin := fun (x : ℤ × ℤ) (hx : content x ≤ ω.period - 1) =>
    hleg.normalize_compose_first (Or.inr rfl) hD'c (x := x) hx
  have hfirst : ∀ k : ℤ, 1 ≤ k → k ≤ (g : ℤ) - 1 →
      wordA (ω.compose D') k = wordA F k ∧ wordB (ω.compose D') k = wordB F k := by
    intro k hk1 hk2
    have hw := mixFold_word_first hCc hGc (c := (g : ℤ) - 1)
      (fun x hx => hfirstwin x (by rw [hper]; exact hx)) hk1 hk2 (by rw [hspanCz]; omega)
      (by rw [hspG]; push_cast; omega)
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
    have h1 : 1 ≤ n := by omega
    have h2 : n + 1 ≤ g := by omega
    have hA : bitA (mixFoldInner (wordA F) (wordB F) g M v)
        (minContent (mixFoldInner (wordA F) (wordB F) g M v) + (n : ℤ)) =
        mixFoldGA (wordA F) g M v n := bitA_fromBits hGbd h1 (by omega)
    have hB : bitB (mixFoldInner (wordA F) (wordB F) g M v)
        (minContent (mixFoldInner (wordA F) (wordB F) g M v) + (n : ℤ)) =
        mixFoldGB (wordB F) g M v n := bitB_fromBits hGbd h1 (by omega)
    obtain ⟨f1, f2⟩ := hF.first_words h1 h2
    refine ⟨hw.1.trans (Eq.trans hA f1), hw.2.trans (Eq.trans hB f2)⟩
  -- the last window gives `A_{M g}`
  have hAmg : 1 ≤ α → wordA (ω.compose D') g = 1 := by
    intro hα1
    have hmaxD : maxContent D' = (M : ℤ) - 1 := maxContent_fromBits hD'bd
    have hminD : minContent D' = 0 := minContent_fromBits hD'bd
    have hlastwin := fun (x : ℤ × ℤ)
        (hx : (maxContent D' - minContent D') * ω.period + ω.widthZ ≤ content x) =>
      hleg.normalize_compose_last (Or.inr rfl) hD'c (x := x) hx
    have hcu : content ((maxContent D' - minContent D') • ω.v) = ((M : ℤ) - 1) * g := by
      rw [MarkedInner.content_smul, hmaxD, hminD]
      have : content ω.v = ω.period := rfl
      rw [this, hper]; ring
    have hMg := mixFold_word_last hCc hGc (c := ((M : ℤ) - 1) * g + v)
      (u := (maxContent D' - minContent D') • ω.v)
      (fun x hx => hlastwin x (by rw [hmaxD, hminD, hper, hwidZ]; simpa using hx))
      (k := (M : ℤ) * g) (by nlinarith) (by nlinarith) (by rw [hspanCz]; push_cast [hNN]; omega)
      (by rw [hcu]; nlinarith) (by rw [hcu, hspG]; push_cast; nlinarith)
    rw [hcu] at hMg
    have e : (M : ℤ) * g - ((M : ℤ) - 1) * g = g := by ring
    rw [e] at hMg
    obtain ⟨-, -, -, -, s5, -, -⟩ := hF.GA_slots
    have hA : bitA (mixFoldInner (wordA F) (wordB F) g M v)
        (minContent (mixFoldInner (wordA F) (wordB F) g M v) + (g : ℤ)) =
        mixFoldGA (wordA F) g M v g := bitA_fromBits hGbd (k := g) (by omega) (by omega)
    have hper2 := mixFold_periodExcept_mul hPA' (M - 1) (g : ℤ) (by omega) (by
      have h1 : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
      have h2 : ((span F - 1 : ℕ) : ℤ) = (span F : ℤ) - 1 := by omega
      rw [h1, h2, hNz]; nlinarith) (by
      rw [Int.emod_self]
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
    have e2 : (g : ℤ) + ((M - 1 : ℕ) : ℤ) * g = (M : ℤ) * g := by
      have : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
      rw [this]; ring
    rw [e2] at hper2
    rw [hper2, hMg]
    refine (Eq.trans hA s5).trans ?_
    simp [hα1]
  -- the interface
  have hint : ∀ j : ℕ, 1 ≤ j → j < M →
      wordA (ω.compose D') ((j : ℤ) * g + α) = wordA F ((j : ℤ) * g + α) ∧
        wordA (ω.compose D') ((j : ℤ) * g + β) = wordA F ((j : ℤ) * g + β) := by
    intro j hj1 hj2
    have hi := hleg.interface_d hD'c rfl hph (j := (j : ℤ)) (by exact_mod_cast hj1)
      (by rw [hspD']; exact_mod_cast hj2)
    rw [hper] at hi
    have hA := bitA_fromBits hD'bd hj1 hj2
    have hB := bitB_fromBits hD'bd hj1 hj2
    have eA : wordA D' (j : ℤ) = wordA F ((j : ℤ) * g + α) := hA
    have eB : wordB D' (j : ℤ) = 1 - wordA F ((j : ℤ) * g + β) := hB
    refine ⟨hi.1.trans eA, ?_⟩
    rw [hi.2, eB]; ring
  have hwords := hF.eq_words hPA' hPB' hfirst (fun h => cp1 h) cp2 cp3 cp4 cp6 hAmg hint
  obtain ⟨t, ht⟩ := eq_translate_of_bits hCc hFc hspanC
    (fun k hk1 hk2 => (hwords k (by exact_mod_cast hk1) (by
      rw [hspanC] at hk2; have : ((k : ℕ) : ℤ) + 1 ≤ span F := by exact_mod_cast hk2
      omega)).1)
    (fun k hk1 hk2 => (hwords k (by exact_mod_cast hk1) (by
      rw [hspanC] at hk2; have : ((k : ℕ) : ℤ) + 1 ≤ span F := by exact_mod_cast hk2
      omega)).2)
  refine ⟨⟨D', ω⟩, ⟨hD'c, ?_, ?_, hleg.1⟩, ⟨t, ht⟩, ?_, rfl, hwid⟩
  · have := mixFold_two_le_card_of_span (D := D') (n := 2) (by rw [hspD']; exact hM)
    exact this
  · have := mixFold_two_le_card_of_span (D := ω.E) (n := 2) (by
      change 2 ≤ span (mixFoldInner (wordA F) (wordB F) g M v)
      rw [hspG]; omega)
    exact this
  · exact hptoNat

end MixFoldFold

end GluingCore
