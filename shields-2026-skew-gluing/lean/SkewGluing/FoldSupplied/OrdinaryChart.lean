import SkewGluing.FoldSupplied.OrdinarySlotBigB
import SkewGluing.FoldSupplied.Lift

/-!
# `ge:ordinary-fold`: the chart of the supplied inner

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:ordinary-fold`).

`FoldSupplied.OrdCtx.exists_chart` builds, from the facts `OrdCtx` about the two boundary words of
an ordinary inner of period `r` and width `v` (classes of the native lists constant off the classes
of the contacts, `g ∣ r`, `2 ≤ g < r`), a proper legal chart of the inner of period `g`:

* at `v ≡ 0 (mod g)` its mark is the horizontal empty mark;
* otherwise its width is `a = v mod g`; the mark has type (a) when `v < g` or
  `t mod g ≤ s mod g`, and type (b) when `g ≤ v` and `s mod g < t mod g`.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open OrdinaryDrift OrdinaryFold SmallOverlap

variable {A B : ℕ → ℤ} {r v s t g : ℕ}

namespace OrdCtx

theorem exists_chart (c : OrdCtx A B r v s t g) {F : Diagram} (hF : IsConnectedSkew F)
    (hsp : span F = r + v) (hFA : ∀ k : ℕ, 1 ≤ k → k < r + v → wordA F k = A k)
    (hFB : ∀ k : ℕ, 1 ≤ k → k < r + v → wordB F k = B k) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧ χ.period = g ∧
      (v % g = 0 → χ.ω.W = ∅) ∧
      (0 < v % g → χ.ω.W.Nonempty ∧ χ.ω.width = v % g ∧
        ((v < g ∨ t % g ≤ s % g) → χ.ω.case = .a) ∧
        (g ≤ v → s % g < t % g → χ.ω.case = .b)) := by
  have hg := c.g_pos
  by_cases hv0 : v % g = 0
  · obtain ⟨R, hR⟩ := c.gr
    have hgv : g ∣ v := Nat.dvd_of_mod_eq_zero hv0
    have hEW := c.h.emptyWords c.g2 ⟨R, hR⟩ hgv c.glt c.hC c.hB
    obtain ⟨χ, hχ, hχF, hper, hW⟩ := EmptyWords.exists_root hEW hF hsp hFA hFB
    exact ⟨χ, hχ, hχF, hper, fun _ => hW, fun h => by omega⟩
  · have ha : 0 < v % g := by omega
    by_cases hvg : v < g
    · have hSW := c.slotWords_small hvg
      obtain ⟨χ, hχ, hχF, hper, hcase, hW, hwid⟩ := SlotWords.exists_root hSW hF hsp hFA hFB
      exact ⟨χ, hχ, hχF, hper, fun h => absurd h hv0,
        fun _ => ⟨hW, hwid, fun _ => hcase, fun h => by omega⟩⟩
    · have hvg' : g ≤ v := by omega
      by_cases hts : t % g ≤ s % g
      · have hSW := c.slotWords_a_big ha hvg' hts
        obtain ⟨χ, hχ, hχF, hper, hcase, hW, hwid⟩ := SlotWords.exists_root hSW hF hsp hFA hFB
        exact ⟨χ, hχ, hχF, hper, fun h => absurd h hv0,
          fun _ => ⟨hW, hwid, fun _ => hcase, fun _ h => by omega⟩⟩
      · have hst : s % g < t % g := by omega
        have hSW := c.slotWords_b_big ha hvg' hst
        have hF' := isConnectedSkew_antitranspose hF
        obtain ⟨χ', hχ', hχF', hper, hcase, hW, hwid⟩ := SlotWords.exists_root hSW hF'
          (by rw [span_antitranspose, hsp])
          (fun k hk1 hk2 => by
            rw [ordFold_wordA_antitranspose hF (by exact_mod_cast hk1) (by
              rw [hsp]; exact_mod_cast hk2), hFB k hk1 hk2])
          (fun k hk1 hk2 => by
            rw [ordFold_wordB_antitranspose hF (by exact_mod_cast hk1) (by
              rw [hsp]; exact_mod_cast hk2), hFA k hk1 hk2])
        have hord : ¬ χ'.ω.case.IsMixed := by simp [hcase, AttachCase.IsMixed]
        refine ⟨χ'.at, hχ'.at hW, ?_, ?_, fun h => absurd h hv0, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
        · have := Chart.IsChartOf.at hχ' hord hχF'
          rwa [antitranspose_antitranspose] at this
        · rw [Chart.at_period]; exact hper
        · exact antitranspose_nonempty_iff.mpr hW
        · change χ'.ω.anti.width = v % g
          rw [MarkedInner.width_anti]; exact hwid
        · intro h; omega
        · intro _ _
          change χ'.ω.case.anti = .b
          simp [hcase, AttachCase.anti]

end OrdCtx

end FoldSupplied
end SkewGluing
