import SkewGluing.Aligned.InnerFactor.Core

/-!
# The inner factor of a divisible chart: assembly

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`prop:gluing-divisible`).

`perData_of_charts` reads the repetition of `D ∘_ω E` off the two windows of the coarse chart
`C ∘_η B`; `exists_inner_factor_core` builds the inner factor `V` from it and identifies `B`
with `V ∘_ω E` by the two-window uniqueness of `lem:gluing-local` (3), for `ω` not of case (c).

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace MarkedInner

variable {ω η : MarkedInner} {D C : Diagram}

theorem perData_of_charts (hω : ω.IsLegal) (hη : η.IsLegal) (hD : IsConnectedSkew D)
    (hC : IsConnectedSkew C) {u : ℤ × ℤ}
    (hFG : ω.compose D = translate u (η.compose C)) {a b Δ : ℤ} (ha : 2 ≤ a) (hb : 0 ≤ b)
    (hba : b < a) (hΔ : 0 ≤ Δ) (hQ : η.period = a * ω.period)
    (hw' : η.widthZ = b * ω.period + ω.widthZ) (hr : (span D : ℤ) = a + b + Δ)
    (hΔq : Δ * ω.period = ((span C : ℤ) - 1) * η.period) :
    PerData ω D a b Δ (η.origin C (ne C) - η.origin C (sw C)) := by
  have hCne := hC.2.1
  have hG : (η.compose C).Nonempty := by
    obtain ⟨d, hd⟩ := id hCne
    obtain ⟨y, hy⟩ := hη.1.1.2.1
    exact ⟨y + η.origin C d, (mem_compose hCne).mpr
      (Or.inl ⟨d, hd, mem_translate.mpr (by simpa using hy)⟩)⟩
  have hM1 := hω.minContent_compose hD
  have hM2 := hη.minContent_compose hC
  have hM3 : minContent (ω.compose D) = minContent (η.compose C) + content u := by
    rw [hFG, minContent_translate hG]
  have hspD := span_eq_of_isConnectedSkew hD
  have hspC := span_eq_of_isConnectedSkew hC
  have hτ := content_ne_sub_sw_origin η hC
  have e1 : (minContent D + b) * ω.period = minContent D * ω.period + b * ω.period := by ring
  have e2 : (minContent D + a) * ω.period = minContent D * ω.period + a * ω.period := by ring
  unfold widthZ at hw'
  refine ⟨hω, hD, by omega, hb, hba, hΔ, by omega, ?_, ?_⟩
  · rw [hτ]
    have : maxContent C - minContent C = (span C : ℤ) - 1 := by omega
    rw [this, ← hΔq]
  · intro x h0 h1
    have hcu : content (x - u) = content x - content u := content_sub x u
    have hwz : η.widthZ = (η.width : ℤ) := rfl
    have hwz2 : ω.widthZ = (ω.width : ℤ) := rfl
    have hc := hη.compose_repeat hC (y := x - u)
      (by rw [hcu, hwz]; rw [hwz2] at h0; linarith)
      (by rw [hcu]; linarith)
    have e : x - u + (η.origin C (ne C) - η.origin C (sw C)) =
        x + (η.origin C (ne C) - η.origin C (sw C)) - u := by abel
    rw [e] at hc
    rw [hFG, mem_translate, mem_translate]
    exact hc

end MarkedInner

end SkewGluing
