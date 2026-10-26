import SkewGluing.FoldSupplied.JWords
import SkewGluing.MixedFold

/-!
# The boundary words of a case-(d) marked inner

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:mixed-fold`) and «Diagonal geometry» (`lem:gluing-local`, `eq:gluing-caps`): the
facts about the two boundary words of the inner `J = ω.E` of a legal case-(d) mark of period `r`,
width `v` and phases `t < s` that the mixed residue fold consumes.

`MixWords A B r v s t` collects them for the words `A = wordA J`, `B = wordB J`: bit data of span
`r + v`; the copy relation `A_{r+b} = A_b - [b = s] - [b = t]`, `B_{r+b} = B_b` of the upper copy
against the lower; the bits at the ends of the private band `A_v = [s = v]`, `B_v = 1`,
`A_r = [t ≥ 1]`, `B_r = 0`; the two singleton heights `H_v = H_{r-1} = 1`; and positivity of the
mark heights `H_z ≥ 1 + [s ≤ z]`.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open MarkedInner

/-- The facts about the boundary words of the inner of a case-(d) mark. -/
structure MixWords (A B : ℤ → ℤ) (r v s t : ℕ) : Prop where
  v_pos : 1 ≤ v
  v_lt : v < r
  s_pos : 1 ≤ s
  s_le : s ≤ v
  t_lt : t < s
  bits : ∀ k : ℤ, 1 ≤ k → k ≤ ((r + v : ℕ) : ℤ) - 1 →
    (A k = 0 ∨ A k = 1) ∧ (B k = 0 ∨ B k = 1)
  pos : ∀ n : ℕ, n < r + v → 0 < mixFold_ht A B n
  last : mixFold_ht A B (r + v - 1) = 1
  copyA : ∀ b : ℕ, 1 ≤ b → b < v →
    A ((r : ℤ) + b) = A b - (if b = s then 1 else 0) - (if b = t then 1 else 0)
  copyB : ∀ b : ℕ, 1 ≤ b → b < v → B ((r : ℤ) + b) = B b
  A_v : A v = if s = v then 1 else 0
  B_v : B v = 1
  A_r : A r = if 1 ≤ t then 1 else 0
  B_r : B r = 0
  sing_v : mixFold_ht A B v = 1
  sing_r : mixFold_ht A B (r - 1) = 1
  mpos : ∀ z, z < v → 1 + (if s ≤ z then 1 else 0) ≤ mixFold_ht A B z

variable {ω : MarkedInner}

theorem mixFold_ht_wordE (h : ω.IsLegalNonempty) (n : ℕ) :
    mixFold_ht (wordA ω.E) (wordB ω.E) n = ω.hi n - ω.lo n + 1 := by
  unfold mixFold_ht
  exact heightWord_E h n

theorem IsLegalNonempty.mixWords (h : ω.IsLegalNonempty) (hcd : ω.case = .d) {s t : ℤ}
    (hph : ω.IsPhases s t) :
    MixWords (wordA ω.E) (wordB ω.E) ω.period.toNat ω.width s.toNat t.toNat := by
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hspan := h.span_eq
  have hlt := h.phases_lt (Or.inr hcd) hph
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hr : ((ω.period.toNat : ℕ) : ℤ) = ω.period := Int.toNat_of_nonneg (by omega)
  have hv : ((ω.width : ℕ) : ℤ) = ω.widthZ := rfl
  have hsN : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg (by omega)
  have htN : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg (by omega)
  have hbd := isBitData_of_isConnectedSkew h.isConnectedSkew_E
  have hspanN : span ω.E = ω.period.toNat + ω.width := by
    have : (span ω.E : ℤ) = ((ω.period.toNat + ω.width : ℕ) : ℤ) := by
      rw [hspan]; push_cast; omega
    exact_mod_cast this
  rw [hspanN] at hbd
  have hoff : ∀ b : ℤ, 0 ≤ b → b ≤ ω.widthZ - 1 →
      ω.dHi b = 0 ∧ -1 ≤ ω.dLo b ∧ ω.dLo b ≤ 1 ∧ (b < t → ω.dLo b < 0) ∧
        (t ≤ b → 0 ≤ ω.dLo b) ∧ (s ≤ b → 0 < ω.dLo b) ∧ (b < s → ω.dLo b ≤ 0) :=
    fun b h0 h1 => d_E_facts h hcd hph h0 h1
  have hlo : ∀ a : ℤ, ω.lo (a + ω.period) = ω.lo a + ω.rowShift + ω.dLo a := by
    intro a; unfold dLo; ring
  have hhi : ∀ a : ℤ, ω.hi (a + ω.period) = ω.hi a + ω.rowShift + ω.dHi a := by
    intro a; unfold dHi; ring
  obtain ⟨⟨cH1, cH2, cH3⟩, ⟨cU1, cU2, cU3⟩⟩ := d_caps h hcd
  have hH := mixFold_ht_wordE h
  set r := ω.period.toNat with hrdef
  set v := ω.width with hvdef
  have hrz : (r : ℤ) = ω.period := hr
  have hvz : (v : ℤ) = ω.widthZ := hv
  have hs' : s.toNat = s.toNat := rfl
  -- the copy relations
  have hcopyA : ∀ b, 1 ≤ b → b < v →
      wordA ω.E ((r : ℤ) + b) = wordA ω.E (b : ℤ) - (if b = s.toNat then 1 else 0) -
        (if b = t.toNat then 1 else 0) := by
    intro b hb1 hb2
    have ha1 := hoff ((b : ℤ) - 1) (by omega) (by omega)
    have ha2 := hoff (b : ℤ) (by omega) (by omega)
    have l1 := hlo ((b : ℤ) - 1)
    have l2 := hlo (b : ℤ)
    have c1 : (r : ℤ) + b - 1 = (b : ℤ) - 1 + ω.period := by omega
    have c2 : (r : ℤ) + b = (b : ℤ) + ω.period := by omega
    rw [wordA_E, wordA_E, c1, c2, l1, l2]
    split_ifs with hbs hbt hbt <;> omega
  have hcopyB : ∀ b, 1 ≤ b → b < v → wordB ω.E ((r : ℤ) + b) = wordB ω.E (b : ℤ) := by
    intro b hb1 hb2
    have ha1 := hoff ((b : ℤ) - 1) (by omega) (by omega)
    have ha2 := hoff (b : ℤ) (by omega) (by omega)
    have l1 := hhi ((b : ℤ) - 1)
    have l2 := hhi (b : ℤ)
    have c1 : (r : ℤ) + b - 1 = (b : ℤ) - 1 + ω.period := by omega
    have c2 : (r : ℤ) + b = (b : ℤ) + ω.period := by omega
    rw [wordB_E, wordB_E, c1, c2, l1, l2]
    omega
  refine ⟨by omega, by omega, by omega, by omega, by omega, fun k hk1 hk2 => ?_, ?_, ?_,
    fun b hb1 hb2 => hcopyA b hb1 hb2, fun b hb1 hb2 => hcopyB b hb1 hb2, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · obtain ⟨k', rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
    exact hbd.2.1 k' (by omega) (by omega)
  · exact fun n hn => hbd.2.2.1 n hn
  · exact hbd.2.2.2
  · rw [wordA_E, hvz]
    have := hoff (ω.widthZ - 1) (by omega) (by omega)
    split_ifs with hsv <;> omega
  · rw [wordB_E, hvz]; omega
  · rw [wordA_E, hrz]
    have := hoff 0 (by omega) (by omega)
    split_ifs with ht0 <;> omega
  · rw [wordB_E, hrz]; omega
  · rw [hH, hvz]
    have := h.lo_w_eq_hi_w
    omega
  · have e : (((r - 1 : ℕ)) : ℤ) = ω.period - 1 := by omega
    rw [hH, e]
    have := h.lo_pred_period_eq_hi
    omega
  · intro z hz
    rw [hH]
    obtain ⟨r0, c0, c1, c2, c3⟩ := h.W_row (a := (z : ℤ)) (by omega) (by omega)
    have h1 := hhi (z : ℤ)
    have h3 := hlo (z : ℤ)
    have h2 := hoff (z : ℤ) (by omega) (by omega)
    split_ifs with hsz <;> omega

end FoldSupplied
end SkewGluing
