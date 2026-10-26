-- TODO-COPIED: skew-factor-gluing/lean/SkewGluing/Coding/Reversal.lean
import SkewGluing.Coding.Empty

/-!
# Case (c) of `lem:gluing-coding`, by rotation

Formalizes `shields-2026-skew-factor-gluing.tex`, «Diagonal geometry» (`lem:gluing-coding`,
`eq:gluing-holes`, `eq:gluing-caps`: "case (c) is obtained by antitransposition").

**Differs from the paper's route.**  The paper obtains case (c) from case (d) by antitransposition;
here the rotation `D ∘_ω E = (D* ∘_{ω*} E*)*` of `compose_rotate_c` is used, which reverses
the boundary words and exchanges `A` and `B`: `A_k(F*) = B_{N-k}(F)` and
`B_k(F*) = A_{N-k}(F)`.  The
phases of `ω*` are `(s*, t*) = (w - t, w - s)`, so the holes `{t*, s*}` of `A` for `ω*` become the
holes `{t, s}` of `B` for `ω`.

Sorry-free.
-/

namespace SkewGluing

/-! ### Reversal of boundary words -/

theorem wordA_rotate {G : Diagram} (hG : IsConnectedSkew G) (k : ℤ) :
    wordA (rotate G) k = wordB G ((span G : ℤ) - k) := by
  have hne := hG.2.1
  have hsp := span_eq_of_isConnectedSkew hG
  unfold wordA wordB bitA bitB
  rw [minContent_rotate hne]
  rw [show -maxContent G + k - 1 = -(maxContent G - k + 1) by ring,
    show -maxContent G + k = -(maxContent G - k) by ring, diagLo_rotate, diagLo_rotate]
  have e4 : maxContent G - k + 1 = minContent G + ((span G : ℤ) - k) := by omega
  have e5 : maxContent G - k = minContent G + ((span G : ℤ) - k) - 1 := by omega
  rw [e4, e5]
  ring

theorem wordB_rotate {G : Diagram} (hG : IsConnectedSkew G) (k : ℤ) :
    wordB (rotate G) k = wordA G ((span G : ℤ) - k) := by
  have hne := hG.2.1
  have hsp := span_eq_of_isConnectedSkew hG
  unfold wordA wordB bitA bitB
  rw [minContent_rotate hne]
  rw [diagHi_rotate, diagHi_rotate]
  have e1 : -(-maxContent G + k - 1) = maxContent G - k + 1 := by ring
  have e2 : -(-maxContent G + k) = maxContent G - k := by ring
  rw [e1, e2]
  have e4 : maxContent G - k + 1 = minContent G + ((span G : ℤ) - k) := by omega
  have e5 : maxContent G - k = minContent G + ((span G : ℤ) - k) - 1 := by omega
  rw [e4, e5]
  ring

/-- Reversal of a word with period `p` except at the residues `S`. -/
theorem periodExcept_reverse {L p : ℕ} {S S' : Finset ℤ} {f g : ℤ → ℤ} {N : ℤ}
    (hN : N = (L : ℤ) + 1) (hg : ∀ k, g k = f (N - k)) (hf : PeriodWords.PeriodExcept L p S f)
    (hres : ∀ x : ℤ, x % (p : ℤ) ∉ S' → (N - x - p) % (p : ℤ) ∉ S) :
    PeriodWords.PeriodExcept L p S' g := by
  intro x hx hS
  rw [Finset.mem_Icc] at hx
  have hy : N - x - p ∈ Finset.Icc (1 : ℤ) ((L : ℤ) - p) := by
    rw [Finset.mem_Icc]
    omega
  have := hf (N - x - p) hy (hres x hS)
  rw [hg x, hg (x + p)]
  have e : N - x - p + p = N - x := by ring
  rw [e] at this
  rw [show N - (x + p) = N - x - p by ring]
  exact this.symm

theorem emod_reflect {q w x c : ℤ} (hc0 : 0 ≤ c) (hcq : c < q) (hwc : 0 ≤ w - c)
    (hwq : w - c < q) (h : (w - x) % q = w - c) : x % q = c := by
  have h1 : (w - x) ≡ (w - c) [ZMOD q] := by
    unfold Int.ModEq
    rw [h, Int.emod_eq_of_lt hwc hwq]
  have h2 : -x ≡ -c [ZMOD q] := by
    have := h1.add_left_cancel' w
    simpa [sub_eq_add_neg] using this
  have h3 : x ≡ c [ZMOD q] := by simpa using h2.neg
  unfold Int.ModEq at h3
  rw [h3, Int.emod_eq_of_lt hc0 hcq]

namespace MarkedInner

variable {ω : MarkedInner} {D : Diagram}

/-- The phases of the rotated mark: `(s*, t*) = (w - t, w - s)`. -/
theorem IsLegalNonempty.isPhases_rotate (h : ω.IsLegalNonempty) {s t : ℤ} (hph : ω.IsPhases s t) :
    ω.rotate.IsPhases (ω.widthZ - t) (ω.widthZ - s) := by
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph
  rw [IsPhases, widthZ_rotate]
  refine ⟨by omega, by omega, by omega, by omega, fun b hb0 hb1 => ?_, fun b hb0 hb1 => ?_⟩
  · have e := hT (ω.widthZ - 1 - b) (by omega) (by omega)
    have d1 := h.dLo_rotate (ω.widthZ - 1 - b)
    have d2 := h.dHi_rotate (ω.widthZ - 1 - b)
    rw [show ω.widthZ - 1 - (ω.widthZ - 1 - b) = b by ring] at d1 d2
    unfold TailLower
    unfold TailUpper at e
    rw [d1, d2]
    omega
  · have e := hS (ω.widthZ - 1 - b) (by omega) (by omega)
    have d1 := h.dLo_rotate (ω.widthZ - 1 - b)
    have d2 := h.dHi_rotate (ω.widthZ - 1 - b)
    rw [show ω.widthZ - 1 - (ω.widthZ - 1 - b) = b by ring] at d1 d2
    unfold TailUpper
    unfold TailLower at e
    rw [d1, d2]
    omega

end MarkedInner

end SkewGluing
