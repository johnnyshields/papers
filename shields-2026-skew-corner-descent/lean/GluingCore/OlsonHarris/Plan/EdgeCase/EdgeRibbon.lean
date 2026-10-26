-- TODO-COPIED from skew-factor-gluing/lean/SkewGluing/OlsonHarris/Plan/EdgeCase/EdgeRibbon.lean
import GluingCore.OlsonHarris.Plan.Defs
import GluingCore.OlsonHarris.Plan.EdgeCase.TFun
import GluingCore.OlsonHarris.Plan.EdgeCase.Ribbons
import GluingCore.OlsonHarris.Plan.EdgeCase.EdgeRibbon.Model
import GluingCore.OlsonHarris.Plan.EdgeCase.EdgeRibbon.Data
import GluingCore.OlsonHarris.Plan.EdgeCase.EdgeRibbon.Lift

/-!
# The ribbons removable on the left from a composite (ordinary mark of case (a))

Formalizes `shields-2026-skew-factor-gluing.tex`, «Charts and the common-factor graph»
(`sec:gluing`, `eq:gluing-offsets`, `def:gluing-graph`): thesis Thm. 5.4.1 and Lemmas 5.4.2 and
5.4.5 (`OlsonHarris2024HopfApplications`), in the form `leftRibbons_copies_proof`: the ribbons of
size `m q` removable on the left from `D ∘_ω E` are exactly the lifts `A ∘ K↑(E)` of the ribbons
`A` of size `m` removable on the left from the connected outer diagram `D`, the lift is injective,
and `ht (A ∘ K↑(E)) = m h(E) + ht A` modulo two, with `h(E) = |v₁|`.

**Differs from the paper's route.**  The thesis argues with loose end ribbons (Thm. 5.4.1) and
Lemma 5.2.7; here the northwest border word of `D ∘_ω E` is computed from the diagonal classes of
the composite (`EdgeRibbon.BorderModel`): it is the key-ribbon word of `E`, joined by the bits of
`D` at the offset `t` of the upper middle tail, and a segment of `m q` contents that is removable
on the left starts at that offset (`EdgeRibbon.BorderModel.removable_iff`), the two ends being
handled by the end caps of the mark.

Sorry-free.
-/

set_option linter.style.openClassical false

namespace GluingCore

namespace Plan

open scoped Classical

open GluingCore.MarkedInner

namespace EdgeRibbon

/-- The border model and the key ribbon of a legal mark of case (a) and a connected outer. -/
theorem exists_model {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .a) {C : Diagram}
    (hC : IsConnectedSkew C) :
    ∃ t : ℤ, ∃ fLo fHi : ℤ → ℤ → ℤ,
      BorderModel (ω.compose C) (minContent ω.E) ω.period ω.widthZ t (minContent C)
        (maxContent C) ω.rowShift (diagLo C) ω.lo fLo fHi ∧
      keyRibbon ω = segment ω.E (minContent ω.E + t) ω.period.toNat := by
  have hq := hω.period_pos
  have hsp := span_eq_of_isConnectedSkew hω.1.1
  have hwf := hω.1.span_eq
  have hmodel : ∃ t : ℤ, ∃ fLo fHi : ℤ → ℤ → ℤ,
      BorderModel (ω.compose C) (minContent ω.E) ω.period ω.widthZ t (minContent C)
        (maxContent C) ω.rowShift (diagLo C) ω.lo fLo fHi ∧
      maxContent ω.middle = minContent ω.E + ω.period + t - 1 := by
    by_cases hW : ω.W = ∅
    · exact borderModel_empty ⟨hω, hW⟩ hC
    · exact borderModel_nonempty ⟨hω, Finset.nonempty_iff_ne_empty.mpr hW⟩ hc hC
  obtain ⟨t, fLo, fHi, hM, hmax⟩ := hmodel
  refine ⟨t, fLo, fHi, hM, keyRibbon_eq_segment hω.1.1 hmax hM.t0 hq ?_⟩
  have hw : ω.widthZ = (ω.width : ℤ) := rfl
  have := hM.t0
  rcases hM.tw with h1 | ⟨h1, h2⟩ <;> omega

end EdgeRibbon

/-- **The ribbons of size `m q` removable on the left from a composite** (thesis Lemma 5.4.5 (1)
with Lemma 5.2.9): they are the lifts `A ∘ K↑(E)` of the ribbons `A` of size `m` removable on the
left from the outer diagram, the lift is injective, and `ht (A ∘ K↑(E)) = m h(E) + ht A` with
`h(E) ≡ |v₁|`.  **Differs from the paper's route.**  The border word of the composite is
computed from its diagonal classes instead of arguing with loose end ribbons. -/
theorem leftRibbons_copies_proof {ω : MarkedInner} (hω : ω.IsLegal) (hc : ω.case = .a)
    {C : Diagram} (hC : IsConnectedSkew C) {m : ℕ} (hm : 0 < m) :
    leftRibbons (MarkedInner.copies ω C) (m * ω.period.toNat) =
        (leftRibbons C m).image (liftRibbon ω C) ∧
      Set.InjOn (liftRibbon ω C) (leftRibbons C m : Set Diagram) ∧
      ∀ A ∈ leftRibbons C m,
        ribbonSign (liftRibbon ω C A) = (-1) ^ (m * ω.v.1.natAbs) * ribbonSign A := by
  have hord : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hc]
  have hq := hω.period_pos
  rw [← MarkedInner.compose_eq_copies hord hC.2.1]
  obtain ⟨t, fLo, fHi, hM, hkey⟩ := EdgeRibbon.exists_model hω hc hC
  have hF : IsConnectedSkew (ω.compose C) := hω.isConnectedSkew_compose hC
  have hFs := isConnectedSkew_iff_diagonal.mp hF
  have hCs := isConnectedSkew_iff_diagonal.mp hC
  have hqn : ((ω.period.toNat : ℕ) : ℤ) = ω.period := Int.toNat_of_nonneg hq.le
  have hN : (((m * ω.period.toNat : ℕ)) : ℤ) = m * ω.period := by push_cast; rw [hqn]
  have hNpos : 0 < m * ω.period.toNat := Nat.mul_pos hm (by omega)
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have key : ∀ Y, Y ∈ leftRibbons (ω.compose C) (m * ω.period.toNat) ↔
      ∃ j₀ : ℤ, minContent C ≤ j₀ ∧ j₀ + m - 1 ≤ maxContent C ∧
        (j₀ = minContent C ∨ diagLo C (j₀ - 1) - diagLo C j₀ = 1) ∧
        (j₀ + m - 1 = maxContent C ∨ diagLo C (j₀ + m - 1) - diagLo C (j₀ + m) = 0) ∧
        Y = segment (ω.compose C) (minContent ω.E + t + j₀ * ω.period) (m * ω.period.toNat) := by
    intro Y
    rw [mem_leftRibbons_iff_segment hF hNpos]
    constructor
    · rintro ⟨k₀, h1, h2, h3, h4, rfl⟩
      rw [hN] at h2 h4
      obtain ⟨j₀, a1, a2, a3, a4, hk⟩ := (hM.removable_iff hmZ).mp ⟨h1, h2, h3, h4⟩
      exact ⟨j₀, a1, a2, a3, a4, by rw [hk]⟩
    · rintro ⟨j₀, a1, a2, a3, a4, rfl⟩
      obtain ⟨h1, h2, h3, h4⟩ := (hM.removable_iff hmZ).mpr ⟨j₀, a1, a2, a3, a4, rfl⟩
      exact ⟨_, h1, by rw [hN]; exact h2, h3, by rw [hN]; exact h4, rfl⟩
  have keyC : ∀ Y, Y ∈ leftRibbons C m ↔
      ∃ j₀ : ℤ, minContent C ≤ j₀ ∧ j₀ + m - 1 ≤ maxContent C ∧
        (j₀ = minContent C ∨ diagLo C (j₀ - 1) - diagLo C j₀ = 1) ∧
        (j₀ + m - 1 = maxContent C ∨ diagLo C (j₀ + m - 1) - diagLo C (j₀ + m) = 0) ∧
        Y = segment C j₀ m := by
    intro Y
    rw [mem_leftRibbons_iff_segment hC hm]
    exact Iff.rfl
  refine ⟨?_, ?_, ?_⟩
  · ext Y
    rw [key, Finset.mem_image]
    constructor
    · rintro ⟨j₀, a1, a2, a3, a4, rfl⟩
      exact ⟨segment C j₀ m, (keyC _).mpr ⟨j₀, a1, a2, a3, a4, rfl⟩,
        EdgeRibbon.liftRibbon_segment hc hM hkey a1 a2⟩
    · rintro ⟨A, hA, rfl⟩
      obtain ⟨j₀, a1, a2, a3, a4, rfl⟩ := (keyC A).mp hA
      exact ⟨j₀, a1, a2, a3, a4, EdgeRibbon.liftRibbon_segment hc hM hkey a1 a2⟩
  · intro A hA B hB hAB
    obtain ⟨j₀, a1, a2, -, -, rfl⟩ := (keyC A).mp (Finset.mem_coe.mp hA)
    obtain ⟨j₁, b1, b2, -, -, rfl⟩ := (keyC B).mp (Finset.mem_coe.mp hB)
    rw [EdgeRibbon.liftRibbon_segment hc hM hkey a1 a2,
      EdgeRibbon.liftRibbon_segment hc hM hkey b1 b2] at hAB
    have hc2 := congrArg contents hAB
    rw [contents_segment, contents_segment] at hc2
    have hmem1 : minContent ω.E + t + j₀ * ω.period ∈
        Finset.Ico (minContent ω.E + t + j₀ * ω.period)
          (minContent ω.E + t + j₀ * ω.period + ((m * ω.period.toNat : ℕ) : ℤ)) := by
      rw [Finset.mem_Ico, hN]
      constructor
      · exact le_rfl
      · nlinarith
    have hmem2 : minContent ω.E + t + j₁ * ω.period ∈
        Finset.Ico (minContent ω.E + t + j₁ * ω.period)
          (minContent ω.E + t + j₁ * ω.period + ((m * ω.period.toNat : ℕ) : ℤ)) := by
      rw [Finset.mem_Ico, hN]
      constructor
      · exact le_rfl
      · nlinarith
    rw [hc2] at hmem1
    rw [← hc2] at hmem2
    rw [Finset.mem_Ico] at hmem1 hmem2
    have : j₀ * ω.period = j₁ * ω.period := by omega
    have := mul_right_cancel₀ hq.ne' this
    rw [this]
  · intro A hA
    obtain ⟨j₀, a1, a2, a3, a4, rfl⟩ := (keyC A).mp hA
    rw [EdgeRibbon.liftRibbon_segment hc hM hkey a1 a2]
    obtain ⟨h1, h2, -, -⟩ := (hM.removable_iff hmZ).mpr ⟨j₀, a1, a2, a3, a4, rfl⟩
    have hH1 := ribbonHeight_segment hFs hNpos h1 (by rw [hN]; exact h2)
    have hH2 := ribbonHeight_segment hCs hm a1 a2
    have hse := hM.diagLo_start_end (j₀ := j₀) (n := m) a1 hmZ a2
    rw [hN] at hH1
    have hp : ω.rowShift = ω.v.1 := rfl
    rw [hp] at hse
    unfold ribbonSign
    rw [← pow_add, neg_one_pow_eq_pow_mod_two (n := ribbonHeight _),
      neg_one_pow_eq_pow_mod_two (n := m * ω.v.1.natAbs + ribbonHeight _)]
    congr 1
    have hX : ((m * ω.v.1.natAbs : ℕ) : ℤ) = (m : ℤ) * ((ω.v.1.natAbs : ℕ) : ℤ) := by
      push_cast; ring
    rcases Int.natAbs_eq ω.v.1 with hv | hv
    · have e : (m : ℤ) * ω.v.1 = ((m * ω.v.1.natAbs : ℕ) : ℤ) := by rw [hX]; nth_rw 1 [hv]
      omega
    · have e : (m : ℤ) * ω.v.1 = -((m * ω.v.1.natAbs : ℕ) : ℤ) := by rw [hX]; nth_rw 1 [hv]; ring
      omega

end Plan

end GluingCore
