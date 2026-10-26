import SkewGluing.FoldSupplied.Basics
import SkewGluing.OrdinaryFold
import SkewGluing.Coding

/-!
# The boundary words of an ordinary marked inner

Formalizes `shields-2026-skew-gluing.tex`, «Residue folds with one exceptional class in
each word» (`ge:ordinary-fold`) and «Diagonal geometry» (`lem:gluing-local`,
`eq:gluing-caps`): the facts about the two boundary words of the inner `J = ω.E` of a legal
case-(a) mark of period `r`, width `v` and phases `s`, `t` that the ordinary residue fold consumes.

`OrdWords A B r v s t` collects them for the words `A = wordA J`, `B = wordB J`: bit data of span
`r + v`; the copy relation `A_{r+b} = A_b - [b = t]`, `B_{r+b} = B_b + [b = s]` of the upper copy
against the lower; the caps `A_t = 1`, `B_s = 0`; the bits at the ends of the private band
`A_v = 0`, `B_v = [s < v]`, `A_r = [t ≥ 1]`, `B_r = 0`; the four singleton heights; and positivity of
the mark heights `H_z ≥ 1 + [s ≤ z]`.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

open MarkedInner OrdinaryDrift

/-- The facts about the boundary words of the inner of an ordinary case-(a) mark. -/
structure OrdWords (A B : ℕ → ℤ) (r v s t : ℕ) : Prop where
  v_pos : 1 ≤ v
  v_lt : v < r
  s_pos : 1 ≤ s
  s_le : s ≤ v
  t_lt : t < v
  words : WordData A B (r + v)
  copyA : ∀ b, 1 ≤ b → b < v → A (r + b) = A b - if b = t then 1 else 0
  copyB : ∀ b, 1 ≤ b → b < v → B (r + b) = B b + if b = s then 1 else 0
  capA : 1 ≤ t → A t = 1
  capB : B s = 0
  A_v : A v = 0
  B_v : B v = if s < v then 1 else 0
  A_r : A r = if 1 ≤ t then 1 else 0
  B_r : B r = 0
  sing_v : heightWord A B v = 1
  sing_r : heightWord A B (r - 1) = 1
  mpos : ∀ z, z < v → 1 + (if s ≤ z then 1 else 0) ≤ heightWord A B z

variable {ω : MarkedInner}

theorem wordA_E (ω : MarkedInner) (k : ℤ) : wordA ω.E k = ω.lo (k - 1) - ω.lo k := by
  unfold wordA bitA MarkedInner.lo
  have e : minContent ω.E + k - 1 = minContent ω.E + (k - 1) := by ring
  rw [e]

theorem wordB_E (ω : MarkedInner) (k : ℤ) : wordB ω.E k = ω.hi (k - 1) - ω.hi k := by
  unfold wordB bitB MarkedInner.hi
  have e : minContent ω.E + k - 1 = minContent ω.E + (k - 1) := by ring
  rw [e]

theorem heightWord_E (h : ω.IsLegalNonempty) (n : ℕ) :
    heightWord (fun k : ℕ => wordA ω.E k) (fun k : ℕ => wordB ω.E k) n = ω.hi n - ω.lo n + 1 := by
  induction n with
  | zero =>
    simp only [heightWord, Finset.range_zero, Finset.sum_empty, add_zero, Nat.cast_zero]
    have := h.lo_zero
    omega
  | succ n ih =>
    rw [heightWord_succ, ih, wordA_E, wordB_E]
    push_cast
    simp only [add_sub_cancel_right]
    ring

theorem IsLegalNonempty.ordWords (h : ω.IsLegalNonempty) (hca : ω.case = .a) {s t : ℤ}
    (hph : ω.IsPhases s t) :
    OrdWords (fun k : ℕ => wordA ω.E k) (fun k : ℕ => wordB ω.E k) ω.period.toNat ω.width
      s.toNat t.toNat := by
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hT := (ordT_eq_zero_iff hmix).mpr hca
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hspan := h.span_eq
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hr : ((ω.period.toNat : ℕ) : ℤ) = ω.period := Int.toNat_of_nonneg (by omega)
  have hv : ((ω.width : ℕ) : ℤ) = ω.widthZ := rfl
  have hsN : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg (by omega)
  have htN : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg (by omega)
  have hbd := isBitData_of_isConnectedSkew h.isConnectedSkew_E
  have hspanN : span ω.E = ω.period.toNat + ω.width := by
    have : (span ω.E : ℤ) = ((ω.period.toNat + ω.width : ℕ) : ℤ) := by rw [hspan]; push_cast; omega
    exact_mod_cast this
  rw [hspanN] at hbd
  have hLH := (h.attach.1 hca).1
  have hUH := (h.attach.1 hca).2
  obtain ⟨lc1, lc2, lc3⟩ := h.lower_caps_H hLH
  obtain ⟨uc1, uc2, uc3⟩ := h.upper_caps_H hUH
  have hoff : ∀ b : ℤ, 0 ≤ b → b ≤ ω.widthZ - 1 →
      (b < t → ω.dLo b = -1) ∧ (t ≤ b → ω.dLo b = 0) ∧
      (s ≤ b → ω.dHi b = -1) ∧ (b < s → ω.dHi b = 0) :=
    fun b h0 h1 => (ord_offsets h hmix hph h0 h1).1 hT
  have hlo : ∀ a : ℤ, ω.lo (a + ω.period) = ω.lo a + ω.rowShift + ω.dLo a := by
    intro a; unfold dLo; ring
  have hhi : ∀ a : ℤ, ω.hi (a + ω.period) = ω.hi a + ω.rowShift + ω.dHi a := by
    intro a; unfold dHi; ring
  -- the position casts
  have wA : ∀ k : ℕ, wordA ω.E (k : ℤ) = ω.lo ((k : ℤ) - 1) - ω.lo (k : ℤ) := fun k => wordA_E ω k
  have wB : ∀ k : ℕ, wordB ω.E (k : ℤ) = ω.hi ((k : ℤ) - 1) - ω.hi (k : ℤ) := fun k => wordB_E ω k
  have hH := heightWord_E h
  set r := ω.period.toNat with hrdef
  set v := ω.width with hvdef
  have hrz : (r : ℤ) = ω.period := hr
  have hvz : (v : ℤ) = ω.widthZ := hv
  have hA1 := hbd.2.1
  have hcopyA : ∀ b, 1 ≤ b → b < v →
      wordA ω.E ((r + b : ℕ) : ℤ) = wordA ω.E (b : ℤ) - if b = t.toNat then 1 else 0 := by
    intro b hb1 hb2
    have ha1 := hoff ((b : ℤ) - 1) (by omega) (by omega)
    have ha2 := hoff (b : ℤ) (by omega) (by omega)
    have l1 := hlo ((b : ℤ) - 1)
    have l2 := hlo (b : ℤ)
    have c1 : ((r + b : ℕ) : ℤ) - 1 = (b : ℤ) - 1 + ω.period := by push_cast; omega
    have c2 : ((r + b : ℕ) : ℤ) = (b : ℤ) + ω.period := by push_cast; omega
    rw [wordA_E, wordA_E, c1, c2, l1, l2]
    split_ifs with hbt
    · have : (b : ℤ) = t := by omega
      omega
    · omega
  have hcopyB : ∀ b, 1 ≤ b → b < v →
      wordB ω.E ((r + b : ℕ) : ℤ) = wordB ω.E (b : ℤ) + if b = s.toNat then 1 else 0 := by
    intro b hb1 hb2
    have ha1 := hoff ((b : ℤ) - 1) (by omega) (by omega)
    have ha2 := hoff (b : ℤ) (by omega) (by omega)
    have l1 := hhi ((b : ℤ) - 1)
    have l2 := hhi (b : ℤ)
    have c1 : ((r + b : ℕ) : ℤ) - 1 = (b : ℤ) - 1 + ω.period := by push_cast; omega
    have c2 : ((r + b : ℕ) : ℤ) = (b : ℤ) + ω.period := by push_cast; omega
    rw [wordB_E, wordB_E, c1, c2, l1, l2]
    split_ifs with hbt
    · have : (b : ℤ) = s := by omega
      omega
    · omega
  have hbits := hbd.2.1
  refine ⟨by omega, by omega, by omega, by omega, by omega, ⟨hbd.2.1, hbd.2.2.1, hbd.2.2.2⟩,
    fun b hb1 hb2 => hcopyA b hb1 hb2, fun b hb1 hb2 => hcopyB b hb1 hb2, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro ht
    have h1 := hcopyA t.toNat ht (by omega)
    simp only [ite_true] at h1
    have b1 : wordA ω.E ((r + t.toNat : ℕ) : ℤ) = 0 ∨ wordA ω.E ((r + t.toNat : ℕ) : ℤ) = 1 :=
      (hbits (r + t.toNat) (by omega) (by omega)).1
    have b2 : wordA ω.E ((t.toNat : ℕ) : ℤ) = 0 ∨ wordA ω.E ((t.toNat : ℕ) : ℤ) = 1 :=
      (hbits t.toNat ht (by omega)).1
    show wordA ω.E ((t.toNat : ℕ) : ℤ) = 1
    omega
  · show wordB ω.E ((s.toNat : ℕ) : ℤ) = 0
    by_cases hsv : s.toNat < v
    · have h1 := hcopyB s.toNat (by omega) hsv
      simp only [ite_true] at h1
      have b1 : wordB ω.E ((r + s.toNat : ℕ) : ℤ) = 0 ∨ wordB ω.E ((r + s.toNat : ℕ) : ℤ) = 1 :=
        (hbits (r + s.toNat) (by omega) (by omega)).2
      have b2 : wordB ω.E ((s.toNat : ℕ) : ℤ) = 0 ∨ wordB ω.E ((s.toNat : ℕ) : ℤ) = 1 :=
        (hbits s.toNat (by omega) (by omega)).2
      omega
    · have hsv' : s.toNat = v := by omega
      rw [hsv', wordB_E, hvz]
      have := hoff (ω.widthZ - 1) (by omega) (by omega)
      omega
  · change wordA ω.E (v : ℤ) = 0
    rw [wordA_E, hvz]; omega
  · change wordB ω.E (v : ℤ) = _
    rw [wordB_E, hvz]
    have := hoff (ω.widthZ - 1) (by omega) (by omega)
    split_ifs with hsv
    · omega
    · omega
  · change wordA ω.E (r : ℤ) = _
    rw [wordA_E, hrz]
    have := hoff 0 (by omega) (by omega)
    split_ifs with ht0
    · omega
    · omega
  · change wordB ω.E (r : ℤ) = 0
    rw [wordB_E, hrz]; omega
  · change heightWord (fun k : ℕ => wordA ω.E k) (fun k : ℕ => wordB ω.E k) v = 1
    rw [hH, hvz]
    have := h.lo_w_eq_hi_w
    omega
  · change heightWord (fun k : ℕ => wordA ω.E k) (fun k : ℕ => wordB ω.E k) (r - 1) = 1
    rw [hH]
    have e : (((r - 1 : ℕ)) : ℤ) = ω.period - 1 := by omega
    rw [e]
    have := h.lo_pred_period_eq_hi
    omega
  · intro z hz
    change 1 + (if s.toNat ≤ z then 1 else 0) ≤
      heightWord (fun k : ℕ => wordA ω.E k) (fun k : ℕ => wordB ω.E k) z
    rw [hH]
    obtain ⟨r0, c0, c1, c2, c3⟩ := h.W_row (a := (z : ℤ)) (by omega) (by omega)
    have h1 := hhi (z : ℤ)
    have h2 := hoff (z : ℤ) (by omega) (by omega)
    split_ifs with hsz
    · omega
    · omega

end FoldSupplied
end SkewGluing
