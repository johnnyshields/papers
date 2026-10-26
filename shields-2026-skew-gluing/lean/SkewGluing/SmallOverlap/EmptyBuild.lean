import SkewGluing.SmallOverlap.Blocks
import SkewGluing.SmallOverlap.EmptyRoot

/-!
# The period-`g` empty root

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-small`), the construction for an empty root: the inner is the first `g`
diagonals, the outer is read from the block starts, and the empty composition reproduces the
boundary words.

* `exists_emptyRoot_of_blockData`: a connected skew diagram whose boundary words have the block
  data of period `g` has a proper root of period `g` and width zero.

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

namespace SmallOverlap

theorem card_ge_span {D : Diagram} : span D ≤ D.card := by
  unfold span contents
  exact Finset.card_image_le

/-- The empty composition of the first `g` diagonals with the block starts reproduces `F`,
the shared core of `exists_emptyRoot_of_blockData`. -/
theorem emptyRoot_core {F : Diagram} (hF : IsConnectedSkew F) {g : ℕ} {a b : ℕ → ℤ}
    (ha : ∀ k : ℕ, a k = wordA F k) (hb : ∀ k : ℕ, b k = wordB F k)
    (hbd : BlockData g (span F) a b) {E' D' : Diagram} (hE' : E' = fromBits g a b)
    (hD' : D' = fromBits (span F / g) (BlockData.outerA g a) (BlockData.outerA g b))
    {ω' : MarkedInner} (hω' : ω' = MarkedInner.mk E' ∅ (vH E') .a) :
    IsConnectedSkew E' ∧ IsConnectedSkew D' ∧ ω'.IsLegal ∧ ω'.period = g ∧
      ∃ t, F = translate t (ω'.compose D') := by
  have hg := hbd.two_le
  have hinner := hbd.bits_inner
  have houter := hbd.isBitData_outer
  have hE'c : IsConnectedSkew E' := by rw [hE']; exact isConnectedSkew_fromBits hinner
  have hD'c : IsConnectedSkew D' := by rw [hD']; exact isConnectedSkew_fromBits houter
  have hE'sp : span E' = g := by rw [hE']; exact span_fromBits hinner
  have hD'sp : span D' = span F / g := by rw [hD']; exact span_fromBits houter
  obtain ⟨M, hM⟩ := hbd.dvd
  have hNg : span F / g = M := by rw [hM]; exact Nat.mul_div_cancel_left M (by omega)
  have hM2 : 2 ≤ M := by
    by_contra hcon
    have : g * M ≤ g * 1 := Nat.mul_le_mul_left g (by omega)
    have := hbd.lt
    omega
  have hleg : ω'.IsLegal := by rw [hω']; exact isLegal_emptyMark hE'c
  have hωE : ω'.E = E' := by rw [hω']
  have hemp : ω'.IsLegalEmpty := ⟨hleg, by rw [hω']⟩
  have hper : ω'.period = g := by
    have := hemp.span_eq
    rw [hωE, hE'sp] at this
    omega
  have hG := hemp.isConnectedSkew_compose hD'c
  have hGsp : (span (ω'.compose D') : ℤ) = span F := by
    rw [hemp.span_compose_eq hD'c, hper]
    have := span_eq_of_isConnectedSkew hD'c
    rw [hD'sp, hNg] at this
    rw [hM, show ((g * M : ℕ) : ℤ) = (g : ℤ) * M by push_cast; rfl]
    have h2 : (maxContent D' - minContent D' + 1 : ℤ) = M := by omega
    rw [h2]; ring
  refine ⟨hE'c, hD'c, hleg, hper, ?_⟩
  have hmD : minContent D' = 0 := by rw [hD']; exact minContent_fromBits houter
  have hcl := hemp.classRows hD'c
  have hminG := hemp.minContent_compose' hD'c
  have hper' := hemp.periodExcept hD'c
  rw [hper] at hper'
  have hspG : span (ω'.compose D') = span F := by exact_mod_cast hGsp
  rw [hspG] at hper'
  have hgp : 0 < g := by omega
  have hfirstA : ∀ c : ℕ, 1 ≤ c → c < g → wordA (ω'.compose D') c = a c := by
    intro c hc1 hcg
    have hv : ValidClass (minContent D') (maxContent D') ω'.widthZ (minContent D') (c : ℤ) :=
      Or.inl ⟨le_rfl, by have := minContent_le (maxContent_mem hD'c.2.1); omega⟩
    have e1 := hcl.wordA_class' (by simp [hminG, hmD]) (J := minContent D') (a := (c : ℤ))
      (k := c) (by rw [hper]; ring) (by omega) (by rw [hper]; omega) hv (fun h => by omega)
    rw [e1]
    unfold classBitLo
    have hc0 : (c : ℤ) ≠ 0 := by omega
    simp only [hc0, ite_false]
    have h1 : bitA E' (minContent E' + c) = a c := by
      rw [hE']; exact bitA_fromBits hinner (k := c) hc1 hcg
    have e2 : ω'.lo ((c : ℤ) - 1) - ω'.lo c = bitA E' (minContent E' + c) := by
      unfold MarkedInner.lo bitA
      rw [hωE]
      congr 2
      ring
    omega
  have hfirstB : ∀ c : ℕ, 1 ≤ c → c < g → wordB (ω'.compose D') c = b c := by
    intro c hc1 hcg
    have hv : ValidClass (minContent D') (maxContent D') ω'.widthZ (minContent D') (c : ℤ) :=
      Or.inl ⟨le_rfl, by have := minContent_le (maxContent_mem hD'c.2.1); omega⟩
    have e1 := hcl.wordB_class' (by simp [hminG, hmD]) (J := minContent D') (a := (c : ℤ))
      (k := c) (by rw [hper]; ring) (by omega) (by rw [hper]; omega) hv (fun h => by omega)
    rw [e1]
    unfold classBitHi
    have hc0 : (c : ℤ) ≠ 0 := by omega
    simp only [hc0, ite_false]
    have h1 : bitB E' (minContent E' + c) = b c := by
      rw [hE']; exact bitB_fromBits hinner (k := c) hc1 hcg
    have e2 : ω'.hi ((c : ℤ) - 1) - ω'.hi c = bitB E' (minContent E' + c) := by
      unfold MarkedInner.hi bitB
      rw [hωE]
      congr 2
      ring
    omega
  have hkey : ∀ k : ℕ, 1 ≤ k → k < span F →
      wordA (ω'.compose D') k = wordA F k ∧ wordB (ω'.compose D') k = wordB F k := by
    intro k hk1 hk2
    have hkN : k < g * M := by rw [← hM]; exact hk2
    by_cases hc : k % g = 0
    · obtain ⟨j, hj⟩ : ∃ j, k = j * g := ⟨k / g, by
        have := Nat.div_add_mod k g
        rw [hc, Nat.mul_comm] at this; omega⟩
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0; simp at hj; omega
        · exact h0
      have hjM : j < M := by
        by_contra hcon
        have : M * g ≤ j * g := Nat.mul_le_mul_right g (by omega)
        rw [Nat.mul_comm g M] at hkN
        omega
      obtain ⟨hjA, hjB⟩ := hemp.joining hD'c (j := (j : ℤ)) (by omega) (by omega)
      rw [hper] at hjA hjB
      have e : ((k : ℕ) : ℤ) = (j : ℤ) * g := by rw [hj]; push_cast; ring
      rw [e, hjA, hjB]
      have hbA : bitA D' (minContent D' + j) = BlockData.outerA g a j := by
        rw [hD']; exact bitA_fromBits houter (k := j) hj1 (by rw [hNg]; exact hjM)
      have hbB : bitB D' (minContent D' + j) = BlockData.outerA g b j := by
        rw [hD']; exact bitB_fromBits houter (k := j) hj1 (by rw [hNg]; exact hjM)
      have ejg : (j : ℤ) * g = ((j * g : ℕ) : ℤ) := by push_cast; ring
      refine ⟨?_, ?_⟩
      · rw [ejg, ← ha]; exact hbA
      · rw [ejg, ← hb]; exact hbB
    · obtain ⟨c, hcdef⟩ : ∃ c, c = k % g := ⟨_, rfl⟩
      have hc1 : 1 ≤ c := by omega
      have hcg : c < g := hcdef ▸ Nat.mod_lt _ hgp
      have hk' : k = (k / g) * g + c := by
        have := Nat.div_add_mod k g
        rw [Nat.mul_comm] at this; omega
      have hFa := (hbd.periodic.eq_of_lt (j := k / g) hc1 hcg (by omega))
      rw [← hk'] at hFa
      have hdvd : (g : ℤ) ∣ (k : ℤ) - c := ⟨(k / g : ℕ), by
        have : (k : ℤ) = ((k / g : ℕ) : ℤ) * g + c := by exact_mod_cast hk'
        push_cast at this ⊢; linarith⟩
      have hnS : (c : ℤ) % ((g : ℕ) : ℤ) ∉ ({0} : Finset ℤ) := by
        rw [Int.emod_eq_of_lt (by omega) (by omega)]
        simp only [Finset.mem_singleton]
        omega
      have hgn : ((g : ℤ)).toNat = g := by omega
      rw [hgn] at hper'
      have hA := periodExcept_eq_of_dvd hper'.1 hgp (x := (c : ℤ)) (y := (k : ℤ)) (by omega)
        (by omega) (by omega) hdvd hnS
      have hB := periodExcept_eq_of_dvd hper'.2 hgp (x := (c : ℤ)) (y := (k : ℤ)) (by omega)
        (by omega) (by omega) hdvd hnS
      refine ⟨?_, ?_⟩
      · rw [← hA, hfirstA c hc1 hcg, ← ha k, ← hFa.1]
      · rw [← hB, hfirstB c hc1 hcg, ← hb k, ← hFa.2]
  obtain ⟨v, hv⟩ := eq_translate_of_bits hG hF hspG
    (fun k hk1 hk2 => by
      have := (hkey k hk1 (hspG ▸ hk2)).1
      unfold wordA at this
      exact this)
    (fun k hk1 hk2 => by
      have := (hkey k hk1 (hspG ▸ hk2)).2
      unfold wordB at this
      exact this)
  exact ⟨v, hv⟩

/-- **`lem:gluing-small`, the empty-root construction.**  Let `F` be connected skew whose
boundary words have period `g` except at the multiples of `g`, with `g ∣ N`, `2 ≤ g < N`.  Then
`F` has a proper root of period `g` and width zero: the inner `E` is the first `g` diagonals, and
the outer is read from the bits and heights at the multiples of `g`. -/
theorem exists_emptyRoot_of_blockData {F : Diagram} (hF : IsConnectedSkew F) {g : ℕ}
    (hbd : BlockData g (span F) (fun k : ℕ => wordA F k) (fun k : ℕ => wordB F k)) :
    ∃ χ : Chart, χ.IsProperLegal ∧ χ.IsChartOf F ∧ χ.period = g ∧ χ.ω.W = ∅ := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℤ, a = fun k : ℕ => wordA F k := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℤ, b = fun k : ℕ => wordB F k := ⟨_, rfl⟩
  rw [← ha, ← hb] at hbd
  obtain ⟨E', hE'⟩ : ∃ E' : Diagram, E' = fromBits g a b := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : Diagram,
    D' = fromBits (span F / g) (BlockData.outerA g a) (BlockData.outerA g b) := ⟨_, rfl⟩
  obtain ⟨ω', hω'⟩ : ∃ ω' : MarkedInner, ω' = MarkedInner.mk E' ∅ (vH E') .a := ⟨_, rfl⟩
  obtain ⟨hE'c, hD'c, hleg, hper, hF'⟩ := emptyRoot_core hF (fun k => by rw [ha])
    (fun k => by rw [hb]) hbd hE' hD' hω'
  have hg := hbd.two_le
  have hE'sp : span E' = g := hE' ▸ span_fromBits hbd.bits_inner
  have hD'sp : span D' = span F / g := hD' ▸ span_fromBits hbd.isBitData_outer
  obtain ⟨M, hM⟩ := hbd.dvd
  have hNg : span F / g = M := by rw [hM]; exact Nat.mul_div_cancel_left M (by omega)
  have hM2 : 2 ≤ M := by
    by_contra hcon
    have : g * M ≤ g * 1 := Nat.mul_le_mul_left g (by omega)
    have := hbd.lt
    omega
  refine ⟨⟨D', ω'⟩, ⟨hD'c, ?_, ?_, hleg⟩, hF', hper, by rw [hω']⟩
  · change 2 ≤ D'.card
    have := card_ge_span (D := D'); omega
  · have hωE : ω'.E = E' := by rw [hω']
    have := card_ge_span (D := ω'.E); rw [hωE] at this ⊢
    change 2 ≤ E'.card
    omega

end SmallOverlap
end SkewGluing
