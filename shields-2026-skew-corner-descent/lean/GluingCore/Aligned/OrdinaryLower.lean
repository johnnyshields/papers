/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/OrdinaryLower.lean`. -/
import GluingCore.Aligned.OrdinaryEdge
import GluingCore.Aligned.LowerAssemble

/-!
# Ordinary charts: the lower mark and the edge displacement

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, ordinary `ω` and ordinary `η`).

* `exists_lowerMark_ordinary_proof` (`b > 0`): the lower mark `μ` on `V` with copy
  `Z = V ∩ (V - z)`, `L_ω(z) = v_η`.  The legality of `μ` reads the diagonals of `η` at the
  private residue `w`, where `E` has a singleton diagonal (`Aligned/LowerBridge.lean`,
  `Aligned/LowerGlue.lean`), and checks the legality clauses on `V` (`Aligned/LowerLegal.lean`).
* `ordinary_edge_displacement_proof` (`b = 0`): `Aligned/OrdinaryEdge.lean`.

Sorry-free.
-/

namespace GluingCore

namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

/-- **`lem:gluing-aligned`, ordinary lower marks (legality).**  For an ordinary `ω`, an ordinary
`η` on `U = V ∘_ω E` of displacement content `a q` and `a < N_V` (that is, `b > 0`), there is a
legal ordinary mark `μ` on `V`, namely `Z = V ∩ (V - z)` with `L_ω(z) = v_η`, with
`v_η = L_ω(v_μ)` and the case of `η` the product of those of `ω` and `μ`.

**Differs from the paper's route.**  Maximality (I) of `μ` is immediate for a lower copy that is
the full intersection `V ∩ (V - z)`, so no copy-union argument is made; the attachments are read
from the sides of the tails of `V` against `V - z` (a southeast tail when `η` and `ω` have the
same case) and, without a tail, from the lower end caps of `η`. -/
theorem exists_lowerMark_ordinary_proof (hω : ω.IsLegal) (hord : ¬ ω.case.IsMixed)
    (hV : IsConnectedSkew V) (hη : η.IsLegal) (hηord : ¬ η.case.IsMixed)
    (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    (hpos : a < (span V : ℤ)) :
    ∃ μ : MarkedInner, μ.IsLegal ∧ μ.E = V ∧ ¬ μ.case.IsMixed ∧ η.v = ω.lat μ.v ∧
      η.ordSign = ω.ordSign * μ.ordSign := by
  have C : LowerChart ω η V a := ⟨hω, hord, hV, hη, hηord, hU, ha, hpos⟩
  refine ⟨muOf V (zOf ω η a) (lowerCase ω η), C.isLegal_lowerMark, rfl,
    lowerCase_not_mixed ω η, ?_, ?_⟩
  · exact (lat_zOf ω η ha).symm
  · have h1 := ordSign_mul_self ω
    have h2 := ordSign_mul_self η
    have h3 : ω.ordSign = 1 ∨ ω.ordSign = -1 := by unfold ordSign; split_ifs <;> simp
    have h4 : η.ordSign = 1 ∨ η.ordSign = -1 := by unfold ordSign; split_ifs <;> simp
    have hμ : (muOf V (zOf ω η a) (lowerCase ω η)).ordSign =
        if η.ordSign = ω.ordSign then 1 else -1 := by
      have key : ∀ cs : AttachCase, (muOf V (zOf ω η a) cs).ordSign =
          if cs = .b then -1 else 1 := fun cs => rfl
      rw [key]
      unfold lowerCase
      by_cases h : η.ordSign = ω.ordSign
      · simp [h]
      · simp [h]
    rw [hμ]
    by_cases h : η.ordSign = ω.ordSign
    · simp [h]
    · have : η.ordSign = -ω.ordSign := by omega
      simp [this]

end MarkedInner

/-! ### Checked examples -/

open MarkedInner in
/-- The lower mark of the chart `(7) = (3) ∘_ω (3)` with the case-(a) row mark `η` of period four:
`z = (0, 2)`, and `μ` is the legal case-(a) mark of width one on `(3)`. -/
example : zOf rowInnerThree
    ⟨compose (skewOf [3] []) rowInnerThree, ∅, (0, 4), .a⟩ 2 = (0, 2) ∧
    (muOf (skewOf [3] []) (0, 2) .a).IsLegal := by
  refine ⟨by decide +kernel, by decide +kernel⟩

end GluingCore
