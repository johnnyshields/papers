import SkewGluing.FoldSupplied.MixedBits
import SkewGluing.FoldSupplied.Lift
import SkewGluing.FoldSupplied.Ordinary

/-!
# `ge:mixed-fold`: the word data of the folded root of a case-(d) inner

Formalizes `shields-2026-skew-gluing.tex`, «The mixed residue fold in every width range»
(`ge:mixed-fold`): from the case-(d) word facts `MixWords` of a legal inner `J = ω.E` of period
`r`, width `v` and phases `t < s`, and the class conditions of the lemma (every residue class of
the native row list modulo `g` is full or empty, and so is every class of the native column list
outside the residues of `t` and `s`), the word data `MixFoldFold` of the period-`g` root of `J`
(`MixCtx.foldData`): period off the two projected contacts `α < β`, the caps, the singleton heights
at `a`, `g - 1` and `N - g`, and the block relation, for `a = v mod g` and `M = r / g + v / g`.

Sorry-free.
-/

namespace SkewGluing
namespace FoldSupplied

variable {E : Diagram} {r v s t g : ℕ}

namespace MixCtx

theorem foldData (h : MixCtx (wordA E) (wordB E) r v s t g) (hspan : span E = r + v) :
    MixFoldFold (wordA E) (wordB E) (span E) g (r / g + v / g) (v % g)
      ((min (t % g) (s % g) : ℕ) : ℤ) ((max (t % g) (s % g) : ℕ) : ℤ) := by
  have hg := h.g_pos
  have hr := h.r_eq
  have hvpos := h.w.v_pos
  have hvr := h.w.v_lt
  have hglt := h.glt
  have hm2 := h.m_ge_two
  have hts := h.w.t_lt
  have hsv := h.w.s_le
  have hne := h.win.1
  have hsdm := Nat.div_add_mod' s g
  have htdm := Nat.div_add_mod' t g
  have hvdm := Nat.div_add_mod' v g
  obtain ⟨ea, eb, ec, ed, ee, ef⟩ := h.end_facts
  have ha := h.a_pos
  have hτ := Nat.mod_lt t hg
  have hσ := Nat.mod_lt s hg
  have haL := Nat.mod_lt v hg
  set a := v % g with ha_def
  set τ := t % g with hτ_def
  set σ := s % g with hσ_def
  set d := v / g with hd_def
  set m := r / g with hm_def
  have hm2' : 2 ≤ m := hm2
  have hmg : m * g = r := hr.symm
  have hdg : d * g + a = v := hvdm
  have hMg : (m + d) * g = r + d * g := by rw [add_mul, hmg]
  have hN : r + v = (m + d) * g + a := by rw [hMg]; omega
  have hbitAt : ∀ n : ℕ, 1 ≤ n → n < r + v → wordA E (n : ℤ) = mnA (wordA E) n := by
    intro n h1 _; unfold mnA; simp [show n ≠ 0 by omega]
  have hbitBt : ∀ n : ℕ, 1 ≤ n → n < r + v → wordB E (n : ℤ) = mnB (wordB E) n := by
    intro n h1 _; unfold mnB; simp [show n ≠ 0 by omega]
  -- periodicity of A, B in natural numbers
  have perA : ∀ n : ℕ, 1 ≤ n → n + g < r + v → n % g ≠ τ → n % g ≠ σ →
      wordA E (n : ℤ) = wordA E ((n + g : ℕ) : ℤ) := by
    intro n h1 h2 h3 h4
    rw [hbitAt n h1 (by omega), hbitAt (n + g) (by omega) h2,
      h.mnA_mod (by omega) h3 h4, h.mnA_mod h2 (by simpa using h3) (by simpa using h4)]
    simp
  have perB : ∀ n : ℕ, 1 ≤ n → n + g < r + v →
      wordB E (n : ℤ) = wordB E ((n + g : ℕ) : ℤ) := by
    intro n h1 h2
    rw [hbitBt n h1 (by omega), hbitBt (n + g) (by omega) h2,
      h.mnB_mod (by omega), h.mnB_mod h2]
    simp
  have hclass : ∀ (x : ℤ) (n : ℕ), x = n → x % (g : ℤ) = ((n % g : ℕ) : ℤ) := by
    intro x n hx; rw [hx]; exact (Int.natCast_mod n g).symm
  -- the terminal caps
  have hdiv : ∀ x : ℕ, x = d * g + x % g ↔ x / g = d := by
    intro x
    have := Nat.div_add_mod' x g
    constructor
    · intro e
      have : x / g * g = d * g := by omega
      exact Nat.eq_of_mul_eq_mul_right hg this
    · intro e; rw [← e]; omega
  have term : ∀ e : ℕ, (e = τ ∨ e = σ) → e < a → wordA E (((m + d) * g + e : ℕ) : ℤ) = 0 := by
    intro e he hea
    have hb : d * g + e < v := by omega
    have hpos : 1 ≤ (m + d) * g + e := by rw [hMg]; omega
    have e1 : (m + d) * g + e = r + (d * g + e) := by rw [hMg]; omega
    have hmode : (d * g + e) % g = e := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt (by omega)
    rw [hbitAt _ hpos (by omega), e1, h.mnA_upper hb]
    rcases he with he | he
    · have bt : mnA (wordA E) (d * g + e) = if t / g = d then 1 else 0 := by rw [he]; exact ed
      have c1 : d * g + e ≠ s := fun c => hne (by
        have : (d * g + e) % g = s % g := by rw [c]
        omega)
      rw [bt]
      by_cases hc : t / g = d
      · have : d * g + e = t := by have := (hdiv t).mpr hc; omega
        rw [if_pos hc, if_neg c1, if_pos this]; norm_num
      · have : d * g + e ≠ t := fun c => hc ((hdiv t).mp (by omega))
        rw [if_neg hc, if_neg c1, if_neg this]; norm_num
    · have bt : mnA (wordA E) (d * g + e) = if s / g = d then 1 else 0 := by rw [he]; exact ee
      have c1 : d * g + e ≠ t := fun c => hne (by
        have : (d * g + e) % g = t % g := by rw [c]
        omega)
      rw [bt]
      by_cases hc : s / g = d
      · have : d * g + e = s := by have := (hdiv s).mpr hc; omega
        rw [if_pos hc, if_pos this, if_neg c1]; norm_num
      · have : d * g + e ≠ s := fun c => hc ((hdiv s).mp (by omega))
        rw [if_neg hc, if_neg this, if_neg c1]; norm_num
  obtain ⟨f1, f2, f3⟩ := h.first
  obtain ⟨hne', hwin⟩ := h.win
  have hrv : 0 < r + v := by omega
  have mn1 : ∀ n : ℕ, 1 ≤ n → mnA (wordA E) n = wordA E (n : ℤ) := by
    intro n h1; unfold mnA; simp [show n ≠ 0 by omega]
  have key : ∀ α0 β0 : ℕ, α0 < β0 → ((α0 = τ ∧ β0 = σ) ∨ (α0 = σ ∧ β0 = τ)) →
      MixFoldFold (wordA E) (wordB E) (span E) g (m + d) a (α0 : ℤ) (β0 : ℤ) := by
    intro α0 β0 hlt hset
    have hα0τσ : α0 = τ ∨ α0 = σ := by rcases hset with ⟨x, _⟩ | ⟨x, _⟩ <;> omega
    have hβ0τσ : β0 = τ ∨ β0 = σ := by rcases hset with ⟨_, x⟩ | ⟨_, x⟩ <;> omega
    have hβa : β0 ≤ a := by rcases hβ0τσ with e | e <;> omega
    have hαa : α0 < a := by omega
    have hαg : α0 < g := by omega
    have hβg : β0 < g := by omega
    have hmodα : α0 % g = α0 := Nat.mod_eq_of_lt hαg
    have hmodβ : β0 % g = β0 := Nat.mod_eq_of_lt hβg
    have hsetE : ∀ P : ℕ → Prop, P τ → P σ → P α0 ∧ P β0 := by
      intro P p1 p2; rcases hset with ⟨x, y⟩ | ⟨x, y⟩ <;> subst x <;> subst y <;> exact ⟨‹_›, ‹_›⟩
    have cA0 : mnA (wordA E) α0 = 1 := by rcases hα0τσ with e | e <;> rw [e] <;> assumption
    have cB0 : mnA (wordA E) β0 = 1 := by rcases hβ0τσ with e | e <;> rw [e] <;> assumption
    have hβ1 : 1 ≤ β0 := by omega
    rw [hspan]
    refine ⟨hN, ha, haL, ?_, by exact_mod_cast Nat.zero_le α0, by exact_mod_cast hlt, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans hm2 (Nat.le_add_right _ _)
    · exact_mod_cast hβa
    · -- perB
      intro x hx _
      rw [Finset.mem_Icc] at hx
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ x by omega)
      have := perB n (by omega) (by omega)
      rw [show ((n : ℤ) + (g : ℤ)) = ((n + g : ℕ) : ℤ) by push_cast; ring]
      exact this
    · -- perA
      intro x h1 h2 h3 h4
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ x by omega)
      have e1 : ((n : ℤ)) % (g : ℤ) = ((n % g : ℕ) : ℤ) := (Int.natCast_mod n g).symm
      have c1 : n % g ≠ τ := by
        intro c; apply h3; rw [e1, c]
        rcases hset with ⟨x, y⟩ | ⟨x, y⟩ <;> omega
      have c2 : n % g ≠ σ := by
        intro c; apply h4; rw [e1, c]
        rcases hset with ⟨x, y⟩ | ⟨x, y⟩ <;> omega
      have := perA n (by omega) (by omega) c1 c2
      rw [show ((n : ℤ) + (g : ℤ)) = ((n + g : ℕ) : ℤ) by push_cast; ring]
      exact this
    · intro h1; rw [← mn1 _ (by omega)]; exact cA0
    · rw [← mn1 _ hβ1]; exact cB0
    · have := term α0 hα0τσ hαa
      exact_mod_cast this
    · intro hb
      have := term β0 hβ0τσ (by exact_mod_cast hb)
      exact_mod_cast this
    · -- Bv
      have e1 := h.mnB_mod (i := v) (by omega)
      have e2 : mnB (wordB E) v = 1 := by
        rw [← hbitBt v hvpos (by omega)]; exact h.w.B_v
      rw [hbitBt a ha (by omega), ← e1, e2]
    · -- Bg
      have e1 := h.mnB_mod (i := g) (by omega)
      rw [Nat.mod_self] at e1
      have e2 : mnB (wordB E) 0 = 0 := by simp [mnB]
      rw [hbitBt g hg (by omega), e1, e2]
    · -- Hv
      rw [mixFold_ht_eq_Sg]; exact ec
    · -- Hg
      rw [mixFold_ht_eq_Sg, show g - 1 + 1 = g by omega]; exact f3
    · -- HNg
      have hM1 : (m + d - 1) * g + g = (m + d) * g := by
        rw [← Nat.succ_mul]; congr 1
        exact Nat.sub_add_cancel (le_trans (by norm_num : 1 ≤ 2) (le_trans hm2' (Nat.le_add_right m d)))
      have hMle : (m + d) * g ≤ r + v := by omega
      have w := hwin ((m + d - 1) * g) ((m + d - 1) * g + τ) ((m + d - 1) * g + σ) (by omega)
        (by omega) (by omega) (mod_blk hτ) (by omega) (by omega) (mod_blk hσ)
      have sa := Sg_add (wordA E) (wordB E) ((m + d - 1) * g) g
      rw [hM1, w, ef] at sa
      have sb := h.sg_block (j := m + d - 1) (z := a) haL (by omega)
      rw [if_pos ea, if_pos eb] at sb
      rw [mixFold_ht_eq_Sg, show r + v - g + 1 = (m + d - 1) * g + a + 1 by omega, sb]
      linarith
    · -- block
      have sb := h.sg_block (j := 1) (z := a) haL (by omega)
      rw [if_pos ea, if_pos eb, one_mul] at sb
      rw [f3] at sb
      have q : ∀ e : ℕ, wordA E ((g : ℤ) + (e : ℤ)) = mnA (wordA E) (g + e) := by
        intro e
        rw [mn1 _ (by omega)]
        push_cast; ring_nf
      rw [mixFold_ht_eq_Sg, mixFold_ht_eq_Sg]
      rcases hset with ⟨x, y⟩ | ⟨x, y⟩
      · subst x; subst y
        rw [q, q]
        linarith
      · subst x; subst y
        rw [q, q]
        linarith
    · -- Amg
      intro h1
      have h1' : 1 ≤ α0 := by exact_mod_cast h1
      have hτ1 : 1 ≤ τ := by rcases hset with ⟨x, y⟩ | ⟨x, y⟩ <;> omega
      have hσ1 : 1 ≤ σ := by rcases hset with ⟨x, y⟩ | ⟨x, y⟩ <;> omega
      have hbm : ((m + d : ℕ) : ℤ) * (g : ℤ) = (((m + d) * g : ℕ) : ℤ) := by push_cast; ring
      have hb : d * g < v := by omega
      have hz : d * g % g = 0 := Nat.mul_mod_left d g
      rw [hbm, ← mn1 _ (by rw [hMg]; omega), hMg, h.mnA_upper hb,
        h.mnA_mod (i := d * g) (by omega) (by rw [hz]; omega) (by rw [hz]; omega), hz]
      have n1 : d * g ≠ s := fun e => by
        have : d * g % g = s % g := by rw [e]
        omega
      have n2 : d * g ≠ t := fun e => by
        have : d * g % g = t % g := by rw [e]
        omega
      rw [if_neg n1, if_neg n2]
      simp [mnA]
    · -- Av
      intro hb
      have hb' : β0 < a := by exact_mod_cast hb
      have hτb : τ ≤ β0 := by rcases hset with ⟨x, y⟩ | ⟨x, y⟩ <;> omega
      have hσb : σ ≤ β0 := by rcases hset with ⟨x, y⟩ | ⟨x, y⟩ <;> omega
      have e1 := h.mnA_mod (i := v) (by omega) (by omega) (by omega)
      have e2 : wordA E (v : ℤ) = 0 := by
        rw [h.w.A_v, if_neg]
        intro e
        have : s % g = v % g := by rw [e]
        omega
      rw [← mn1 a ha, ← e1, mn1 v hvpos, e2]
  have hlt : min τ σ < max τ σ := by omega
  exact key _ _ hlt (by omega)

end MixCtx

end FoldSupplied
end SkewGluing
