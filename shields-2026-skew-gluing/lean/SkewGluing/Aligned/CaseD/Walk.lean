import SkewGluing.Aligned.CaseD.Empty

/-!
# Aligned marks, case (d): the walk

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-walk-signs`).

The height of `U = V ∘_ω E` on every diagonal is read off the interleaved profile `f(2J) = S_J - 1`,
`f(2J + 1) = M_J` of `V` (`HU_interleaved`), and the northwest offset of `η` is the difference
`δ_k = f(k) - f(k + 2a)` (`eta_dLo_walk`).  `walk_signs` is `eq:gluing-walk-signs`; `walk_level`
and `exists_theta` read the level `θ` off the walk `g_0, k_0, g_1, k_1, …`.

Sorry-free.
-/

namespace SkewGluing
namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

/-- The interleaved profile of `eq:gluing-walk-signs`: `f(2J) = S_J - 1`, `f(2J + 1) = M_J`
(the paper's `S_J` shifted by one, which does not change the differences `δ_k`). -/
def profIL (D : Diagram) (k : ℤ) : ℤ :=
  if k % 2 = 0 then profS D (k / 2) - 1 else profM D (k / 2)

theorem profIL_even (D : Diagram) (J : ℤ) : profIL D (2 * J) = profS D J - 1 := by
  unfold profIL
  have h1 : (2 * J) % 2 = 0 := by omega
  have h2 : (2 * J) / 2 = J := by omega
  rw [h1, h2]; simp

theorem profIL_odd (D : Diagram) (J : ℤ) : profIL D (2 * J + 1) = profM D J := by
  unfold profIL
  have h1 : ¬ ((2 * J + 1) % 2 = 0) := by omega
  have h2 : (2 * J + 1) / 2 = J := by omega
  rw [h2]; simp only [h1]; simp

/-- The selector of a marked residue `α`: the profile index `2J + κ_α` read by the diagonal. -/
def selK (s t α : ℤ) : ℤ := if α < t then -1 else if α < s then 0 else 1

/-- The part of the height of `U` on the residue `α` that does not depend on `V`. -/
def constU (ω : MarkedInner) (α : ℤ) : ℤ :=
  if α < ω.widthZ then Om ω α else height ω.E (minContent ω.E + α) - 1

theorem HU_interleaved (h : ω.IsLegalNonempty) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    {s t : ℤ} (hph : ω.IsPhases s t) (hlt : t < s) {i α : ℤ} (hi0 : 0 ≤ i)
    (hi1 : i ≤ (span V : ℤ)) (hα0 : 0 ≤ α) (hα1 : α < ω.period)
    (hiN : i = (span V : ℤ) → α < ω.widthZ) :
    HU ω V (i * ω.period + α) =
      constU ω α + profIL V (2 * (minContent V + i) + selK s t α) := by
  have hq := h.width_lt_period
  have hsp := aligned_span_eq hV
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph
  have hph' : ω.IsPhases s t := ⟨hs1, hs2, ht1, ht2, hS, hT⟩
  by_cases hi : i < (span V : ℤ)
  · have := HU_class h hd hV hph' hlt hi0 hi hα0 hα1
    rw [this]
    unfold constU selK
    by_cases hw : α < ω.widthZ
    · simp only [hw, ↓reduceIte]
      by_cases h2 : α < t
      · simp only [h2, ↓reduceIte]
        have e : 2 * (minContent V + i) + -1 = 2 * (minContent V + i - 1) + 1 := by ring
        rw [e, profIL_odd]
      · by_cases h3 : α < s
        · simp only [h2, h3, ↓reduceIte]
          rw [add_zero, profIL_even]
        · simp only [h2, h3, ↓reduceIte]
          rw [profIL_odd]
    · have h2 : ¬ α < t := by omega
      have h3 : ¬ α < s := by omega
      simp only [hw, h2, h3, ↓reduceIte]
      rw [profIL_odd]; ring
  · have hiN' : i = (span V : ℤ) := by omega
    have hw := hiN hiN'
    subst hiN'
    have e : ((span V : ℤ)) * ω.period + α = α + (span V : ℤ) * ω.period := by ring
    rw [e, HU_last h hd hV hph' hlt hα0 hw]
    unfold constU selK
    simp only [hw, ↓reduceIte]
    have em : minContent V + (span V : ℤ) = maxContent V + 1 := by omega
    rw [em]
    by_cases h2 : α < t
    · simp only [h2, ↓reduceIte]
      have e2 : 2 * (maxContent V + 1) + -1 = 2 * maxContent V + 1 := by ring
      rw [e2, profIL_odd, aligned_profM_last hV]
    · by_cases h3 : α < s
      · simp only [h2, h3, ↓reduceIte]
        simp only [add_zero]; rw [profIL_even, aligned_profS_eq_one (by omega)]
        simp
      · simp only [h2, h3, ↓reduceIte]
        rw [profIL_odd, aligned_profM_eq_zero (by omega)]

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

/-- The difference `δ_k = f(k) - f(k + 2a)` of the interleaved profile of `V`. -/
def walkDelta (V : Diagram) (a k : ℤ) : ℤ := profIL V k - profIL V (k + 2 * a)

/-- The profile index `2 (m + ⌊x/q⌋) + κ_{x mod q}` sampled by the diagonal `x` of `U`. -/
def sampleIdx (ω : MarkedInner) (V : Diagram) (s t x : ℤ) : ℤ :=
  2 * (minContent V + x / ω.period) + selK s t (x % ω.period)

theorem eta_dLo_walk (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    {s t : ℤ} (hph : ω.IsPhases s t) (hlt : t < s) {x : ℤ} (h0 : 0 ≤ x)
    (h1 : x ≤ η.widthZ - 1) :
    η.dLo x = walkDelta V a (sampleIdx ω V s t x) := by
  have hl := aligned_legalNonempty hω hd
  have hq := hl.width_lt_period
  have hw0 := hl.width_pos
  have hq0 : 0 < ω.period := by omega
  have hap := eta_pos hω hV hη hU ha
  have hwe := eta_width_eq hω hV hη hU ha
  have hwz : η.widthZ = ((span V : ℤ) - a) * ω.period + ω.widthZ := by
    have : η.widthZ = (η.width : ℤ) := rfl
    rw [this, hwe]; rfl
  have hdm := Int.mul_ediv_add_emod x ω.period
  have hm0 := Int.emod_nonneg x hq0.ne'
  have hm1 := Int.emod_lt_of_pos x hq0
  set i := x / ω.period with hi
  set α := x % ω.period with hα
  have hi0 : 0 ≤ i := Int.ediv_nonneg h0 hq0.le
  have hib : i ≤ (span V : ℤ) - a := by
    by_contra hne
    have : (span V : ℤ) - a + 1 ≤ i := by omega
    have := mul_le_mul_of_nonneg_right this hq0.le
    nlinarith
  have hαb : i = (span V : ℤ) - a → α < ω.widthZ := by
    intro he
    rw [he] at hdm
    nlinarith
  rw [eta_dLo hω hd hV hη hU ha h0 h1]
  have e1 : x = i * ω.period + α := by linarith
  have e2 : x + a * ω.period = (i + a) * ω.period + α := by rw [e1]; ring
  rw [e2]
  have r1 := HU_interleaved hl hd hV hph hlt (i := i) (α := α) hi0 (by omega) hm0 hm1
    (by intro he; omega)
  have r2 := HU_interleaved hl hd hV hph hlt (i := i + a) (α := α) (by omega) (by omega) hm0 hm1
    (by intro he; exact hαb (by omega))
  have r1' : ω.HU V x = ω.constU α + profIL V (2 * (minContent V + i) + selK s t α) := by
    rw [e1]; exact r1
  rw [r1', r2]
  unfold walkDelta sampleIdx
  rw [← hi, ← hα]
  have e3 : 2 * (minContent V + (i + a)) + selK s t α =
      2 * (minContent V + i) + selK s t α + 2 * a := by ring
  rw [e3]
  ring

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

theorem selK_mono {s t α α' : ℤ} (h : α ≤ α') : selK s t α ≤ selK s t α' := by
  unfold selK
  split_ifs <;> omega

theorem selK_bounds (s t α : ℤ) : -1 ≤ selK s t α ∧ selK s t α ≤ 1 := by
  unfold selK
  split_ifs <;> omega

theorem sampleIdx_mono (hq0 : 0 < ω.period) {s t : ℤ} {x x' : ℤ}
    (hxx : x ≤ x') : sampleIdx ω V s t x ≤ sampleIdx ω V s t x' := by
  unfold sampleIdx
  have h1 := Int.mul_ediv_add_emod x ω.period
  have h2 := Int.emod_nonneg x hq0.ne'
  have h3 := Int.emod_lt_of_pos x hq0
  have h1' := Int.mul_ediv_add_emod x' ω.period
  have h2' := Int.emod_nonneg x' hq0.ne'
  have h3' := Int.emod_lt_of_pos x' hq0
  have hdiv : x / ω.period ≤ x' / ω.period := Int.ediv_le_ediv hq0 hxx
  have hb1 := selK_bounds s t (x % ω.period)
  have hb2 := selK_bounds s t (x' % ω.period)
  rcases lt_or_eq_of_le hdiv with hlt | heq
  · omega
  · rw [heq]
    have : x % ω.period ≤ x' % ω.period := by
      have : ω.period * (x / ω.period) + x % ω.period ≤ ω.period * (x' / ω.period) +
          x' % ω.period := by linarith
      rw [heq] at this; omega
    have := selK_mono (s := s) (t := t) this
    omega

theorem eta_dLo_mono (hl : η.IsLegalNonempty)
    (hdHi : ∀ x, 0 ≤ x → x ≤ η.widthZ - 1 → η.dHi x = 0) {x x' : ℤ} (h0 : 0 ≤ x)
    (hxx : x ≤ x') (h1 : x' ≤ η.widthZ - 1) : η.dLo x ≤ η.dLo x' := by
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph
  have a1 := hl.thin_lower x h0 (by omega)
  have a2 := hl.thin_lower x' (by omega) h1
  have a3 := hl.thin_upper (a := x) h0 (by omega)
  have a4 := hl.thin_upper (a := x') (by omega) h1
  have d1 := hdHi x h0 (by omega)
  have d2 := hdHi x' (by omega) h1
  have s1 := hS x h0 (by omega)
  have s2 := hS x' (by omega) h1
  have t1 := hT x h0 (by omega)
  have t2 := hT x' (by omega) h1
  unfold TailLower at s1 s2
  unfold TailUpper at t1 t2
  by_contra hcon
  have hcon := not_le.mp hcon
  by_cases hx : 0 < η.dLo x
  · have : s ≤ x := s1.mp (Or.inl hx)
    have := s2.mpr (by omega)
    omega
  · have hx0 : η.dLo x = 0 := by omega
    have hx' : η.dLo x' < 0 := by omega
    have : x' < t := t2.mp (Or.inl hx')
    have := t1.mpr (by omega)
    omega

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

theorem selK_at_t {s t : ℤ} (hlt : t < s) : selK s t t = 0 := by
  unfold selK; split_ifs <;> omega

theorem selK_at_s {s t : ℤ} (hlt : t < s) : selK s t s = 1 := by
  unfold selK; split_ifs <;> omega

theorem selK_ge {s t α : ℤ} (hlt : t < s) (h : s ≤ α) : selK s t α = 1 := by
  unfold selK; split_ifs <;> omega

/-- A profile index of the marked band is sampled by a marked diagonal of `U`. -/
theorem exists_sample (hl : ω.IsLegalNonempty) {s t : ℤ} (hph : ω.IsPhases s t) (hlt : t < s)
    {b k : ℤ} (hk0 : 2 * minContent V ≤ k) (hk1 : k ≤ 2 * minContent V + 2 * b + 1)
    (hlast : k = 2 * minContent V + 2 * b + 1 → s < ω.widthZ) :
    ∃ x, 0 ≤ x ∧ x ≤ b * ω.period + ω.widthZ - 1 ∧ sampleIdx ω V s t x = k := by
  have hq := hl.width_lt_period
  have hw := hl.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph
  have hq0 : 0 < ω.period := by omega
  set r := k - 2 * minContent V with hr
  set i := r / 2 with hi
  have hi0 : 0 ≤ i := by omega
  have hib : i ≤ b := by omega
  rcases Int.emod_two_eq_zero_or_one r with hpar | hpar
  · -- an even index: the residue `t`
    refine ⟨i * ω.period + t, by nlinarith, ?_, ?_⟩
    · nlinarith
    · have hdm := aligned_divmod_eq (j := i) hq0 ht1 (by omega : t < ω.period)
      unfold sampleIdx
      rw [hdm.1, hdm.2, selK_at_t hlt]
      omega
  · by_cases hib' : i < b
    · refine ⟨i * ω.period + ω.widthZ, by nlinarith, ?_, ?_⟩
      · nlinarith
      · have hdm := aligned_divmod_eq (j := i) hq0 (by omega : 0 ≤ ω.widthZ) hq
        unfold sampleIdx
        rw [hdm.1, hdm.2, selK_ge hlt hs2]
        omega
    · have hieq : i = b := by omega
      have hs : s < ω.widthZ := hlast (by omega)
      refine ⟨i * ω.period + s, by nlinarith, ?_, ?_⟩
      · rw [hieq]; omega
      · have hdm := aligned_divmod_eq (j := i) hq0 (by omega : 0 ≤ s) (by omega : s < ω.period)
        unfold sampleIdx
        rw [hdm.1, hdm.2, selK_at_s hlt]
        omega

end MarkedInner
end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

private theorem profS_ge_one (hV : IsConnectedSkew V) (J : ℤ) : 1 ≤ profS V J := by
  by_cases h : minContent V + 1 ≤ J ∧ J ≤ maxContent V
  · rw [aligned_profS_eq h]
    have hb := D_bits hV h.1 h.2
    have hs := isConnectedSkew_iff_diagonal.mp hV
    have hJ : J ∈ contents V := hs.mem_contents_iff.mpr ⟨by omega, h.2⟩
    have hJ1 : J - 1 ∈ contents V := hs.mem_contents_iff.mpr ⟨by omega, by omega⟩
    have l1 := diagLo_le_diagHi hJ1
    omega
  · rw [aligned_profS_eq_one h]

/-- **`eq:gluing-walk-signs`.**  Put `b = N_V - a`.  On the profile indices `k` of the marked band,
`2m ≤ k ≤ 2m + 2b + 1` (`m` the least content of `V`), the differences `δ_k = f(k) - f(k + 2a)` of
the interleaved profile lie in `{-1, 0, 1}`, are monotone (so of the form `- ⋯ - 0 ⋯ 0 + ⋯ +`),
`δ` at the first index is `≤ 0` and `δ` at the last index is `1`. -/
theorem walk_signs (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    (∀ k, 2 * minContent V ≤ k → k ≤ 2 * minContent V + 2 * ((span V : ℤ) - a) + 1 →
        -1 ≤ walkDelta V a k ∧ walkDelta V a k ≤ 1) ∧
    (∀ k k', 2 * minContent V ≤ k → k ≤ k' →
        k' ≤ 2 * minContent V + 2 * ((span V : ℤ) - a) + 1 →
        walkDelta V a k ≤ walkDelta V a k') ∧
    walkDelta V a (2 * minContent V) ≤ 0 ∧
    walkDelta V a (2 * minContent V + 2 * ((span V : ℤ) - a) + 1) = 1 := by
  have hl := aligned_legalNonempty hω hd
  have hq := hl.width_lt_period
  have hw0 := hl.width_pos
  have hq0 : 0 < ω.period := by omega
  have hap := eta_pos hω hV hη hU ha
  have hle := eta_le_span hω hV hη hU ha
  have hηl := eta_legalNonempty hω hd hV hη hU ha
  have hwe := eta_width_eq hω hV hη hU ha
  have hwz : η.widthZ = ((span V : ℤ) - a) * ω.period + ω.widthZ := by
    have : η.widthZ = (η.width : ℤ) := rfl
    rw [this, hwe]; rfl
  have hdHi : ∀ x, 0 ≤ x → x ≤ η.widthZ - 1 → η.dHi x = 0 :=
    fun x h0 h1 => eta_dHi_zero hω hd hV hη hU ha h0 h1
  obtain ⟨s, t, hph⟩ := hl.exists_phases
  have hlt := hl.phases_lt (Or.inr hd) hph
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hph
  have hph' : ω.IsPhases s t := ⟨hs1, hs2, ht1, ht2, hS, hT⟩
  set b := (span V : ℤ) - a with hb
  have hb0 : 0 ≤ b := by omega
  -- the last odd index
  have hlastv : walkDelta V a (2 * minContent V + 2 * b + 1) = 1 := by
    have hx0 : 0 ≤ b * ω.period + ω.widthZ := by nlinarith
    have hxr : b * ω.period + ω.widthZ ≤ (span V : ℤ) * ω.period + ω.widthZ - 1 := by
      nlinarith
    have hH := HU_interleaved hl hd hV hph' hlt (i := b) (α := ω.widthZ) hb0 (by omega)
      (by omega) hq (by intro he; omega)
    have hsing : HU ω V (b * ω.period + ω.widthZ) = 1 := by
      have h1 := eta_lo_hi_height hω hV hU (η.widthZ)
      have h2 := hηl.lo_w_eq_hi_w
      rw [hwz] at h1 h2
      omega
    have hcu : constU ω ω.widthZ = 0 := by
      unfold constU
      have := hl.lo_w_eq_hi_w
      have e : height ω.E (minContent ω.E + ω.widthZ) = 1 := by
        unfold height; unfold lo hi at this; omega
      simp [e]
    rw [hcu, selK_ge hlt hs2, zero_add] at hH
    rw [hsing, profIL_odd] at hH
    unfold walkDelta
    have e1 : 2 * minContent V + 2 * b + 1 = 2 * (minContent V + b) + 1 := by ring
    have e2 : 2 * (minContent V + b) + 1 + 2 * a = 2 * (maxContent V + 1) + 1 := by
      have := aligned_span_eq hV; omega
    have e3 : ¬ (minContent V ≤ maxContent V + 1 ∧ maxContent V + 1 ≤ maxContent V) := by omega
    rw [e1, e2, profIL_odd, profIL_odd, aligned_profM_eq_zero e3]
    omega
  -- samples
  have hsamp : ∀ k, 2 * minContent V ≤ k → k ≤ 2 * minContent V + 2 * b + 1 →
      k ≠ 2 * minContent V + 2 * b + 1 →
      ∃ x, 0 ≤ x ∧ x ≤ η.widthZ - 1 ∧ sampleIdx ω V s t x = k ∧
        η.dLo x = walkDelta V a k := by
    intro k hk0 hk1 hne
    obtain ⟨x, hx0, hx1, hx2⟩ := exists_sample (V := V) hl hph' hlt (b := b) hk0 hk1
      (fun h => absurd h hne)
    refine ⟨x, hx0, by rw [hwz]; exact hx1, hx2, ?_⟩
    rw [eta_dLo_walk hω hd hV hη hU ha hph' hlt hx0 (by rw [hwz]; exact hx1), hx2]
  have hbound : ∀ k, 2 * minContent V ≤ k → k ≤ 2 * minContent V + 2 * b + 1 →
      -1 ≤ walkDelta V a k ∧ walkDelta V a k ≤ 1 := by
    intro k hk0 hk1
    by_cases hne : k = 2 * minContent V + 2 * b + 1
    · rw [hne, hlastv]; omega
    · obtain ⟨x, hx0, hx1, -, hx3⟩ := hsamp k hk0 hk1 hne
      have a1 := hηl.thin_lower x hx0 hx1
      have a3 := hηl.thin_upper (a := x) hx0 hx1
      rw [← hx3]; omega
  refine ⟨hbound, ?_, ?_, hlastv⟩
  · intro k k' hk0 hkk hk1
    by_cases hne' : k' = 2 * minContent V + 2 * b + 1
    · rw [hne', hlastv]
      exact (hbound k hk0 (by omega)).2
    · have hne : k ≠ 2 * minContent V + 2 * b + 1 := by omega
      obtain ⟨x, hx0, hx1, hx2, hx3⟩ := hsamp k hk0 (by omega) hne
      obtain ⟨x', hx0', hx1', hx2', hx3'⟩ := hsamp k' (by omega) hk1 hne'
      rw [← hx3, ← hx3']
      rcases lt_or_eq_of_le hkk with hlt' | heq
      · have hxx : x ≤ x' := by
          by_contra hc
          have := sampleIdx_mono (ω := ω) (V := V) (s := s) (t := t) hq0 (le_of_lt (not_le.mp hc))
          omega
        exact eta_dLo_mono hηl hdHi hx0 hxx hx1'
      · subst heq
        have : x = x' ∨ True := Or.inr trivial
        rw [hx3, hx3']
  · unfold walkDelta
    have e1 : 2 * minContent V + 2 * a = 2 * (minContent V + a) := by ring
    rw [e1, profIL_even, profIL_even]
    have p1 : profS V (minContent V) = 1 := aligned_profS_eq_one (by omega)
    have p2 := profS_ge_one hV (minContent V + a)
    omega

end MarkedInner
end SkewGluing

namespace SkewGluing

/-- **The walk lemma of `lem:gluing-aligned` (case (d)).**  Let `D₁, …, D_L ∈ {-1, 0, 1}` be
nondecreasing (`- ⋯ - 0 ⋯ 0 + ⋯ +`) and let the walk `W₀, …, W_L` have the increments
`W_{n+1} - W_n = (-1)^{n+1} D_{n+1}`.  Then some level `θ` lies at one end of every step:
`W_n = θ` or `W_{n+1} = θ` for `n < L`. -/
theorem walk_level (L : ℕ) (W D : ℕ → ℤ) (hD : ∀ i, 1 ≤ i → i ≤ L → -1 ≤ D i ∧ D i ≤ 1)
    (hmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ L → D i ≤ D j)
    (hev : ∀ n, n + 1 ≤ L → n % 2 = 0 → W (n + 1) = W n - D (n + 1))
    (hod : ∀ n, n + 1 ≤ L → n % 2 = 1 → W (n + 1) = W n + D (n + 1)) :
    ∃ θ : ℤ, ∀ n, n + 1 ≤ L → W n = θ ∨ W (n + 1) = θ := by
  classical
  -- `p` is the length of the negative portion
  have hexp : ∃ p : ℕ, p = L ∨ (p + 1 ≤ L ∧ D (p + 1) ≠ -1) := ⟨L, Or.inl rfl⟩
  obtain ⟨p, hp1, hpmin⟩ : ∃ p : ℕ, (p = L ∨ (p + 1 ≤ L ∧ D (p + 1) ≠ -1)) ∧
      ∀ n, n < p → ¬ (n = L ∨ (n + 1 ≤ L ∧ D (n + 1) ≠ -1)) :=
    ⟨Nat.find hexp, Nat.find_spec hexp, fun n hn => Nat.find_min hexp hn⟩
  have hpL : p ≤ L := by rcases hp1 with h | h <;> omega
  have hp2 : ∀ n, n < p → n + 1 ≤ L ∧ D (n + 1) = -1 := by
    intro n hn
    have := hpmin n hn
    push Not at this
    have hn1 : n + 1 ≤ L := by omega
    refine ⟨hn1, ?_⟩
    have := this.2 hn1
    have hb := hD (n + 1) (by omega) hn1
    omega
  -- `q` is the end of the zero portion
  have hexq : ∃ q : ℕ, q = L ∨ (q + 1 ≤ L ∧ D (q + 1) = 1) := ⟨L, Or.inl rfl⟩
  obtain ⟨q, hq1, hqmin⟩ : ∃ q : ℕ, (q = L ∨ (q + 1 ≤ L ∧ D (q + 1) = 1)) ∧
      ∀ n, n < q → ¬ (n = L ∨ (n + 1 ≤ L ∧ D (n + 1) = 1)) :=
    ⟨Nat.find hexq, Nat.find_spec hexq, fun n hn => Nat.find_min hexq hn⟩
  have hqL : q ≤ L := by rcases hq1 with h | h <;> omega
  have hq2 : ∀ n, n < q → n + 1 ≤ L ∧ D (n + 1) ≠ 1 := by
    intro n hn
    have := hqmin n hn
    push Not at this
    have hn1 : n + 1 ≤ L := by omega
    exact ⟨hn1, this.2 hn1⟩
  -- the portions are ordered
  have hpq : p ≤ q := by
    by_contra hcon
    have hlt : q < p := by omega
    obtain ⟨h1, h2⟩ := hp2 q hlt
    rcases hq1 with h | ⟨-, h⟩
    · omega
    · omega
  -- on `[p + 1, q]` the differences vanish
  have hzero : ∀ n, p < n → n ≤ q → D n = 0 := by
    intro n hn1 hn2
    have hnL : n ≤ L := by omega
    have h1 : D n ≠ 1 := (hq2 (n - 1) (by omega)).2 |> fun h => by
      have : n - 1 + 1 = n := by omega
      rwa [this] at h
    have h2 : D n ≥ 0 := by
      rcases hp1 with h | ⟨h3, h4⟩
      · omega
      · have := hmono (p + 1) n (by omega) (by omega) hnL
        have hb := hD (p + 1) (by omega) h3
        omega
    have hb := hD n (by omega) hnL
    omega
  have hone : ∀ n, q < n → n ≤ L → D n = 1 := by
    intro n hn1 hn2
    rcases hq1 with h | ⟨h3, h4⟩
    · omega
    · have := hmono (q + 1) n (by omega) (by omega) hn2
      have hb := hD n (by omega) hn2
      omega
  have hneg : ∀ n, 1 ≤ n → n ≤ p → D n = -1 := by
    intro n h1 h2
    have := (hp2 (n - 1) (by omega)).2
    rwa [show n - 1 + 1 = n by omega] at this
  -- level `θ = W p`
  refine ⟨W p, ?_⟩
  -- negative portion: `W n = W (n + 2)`
  have hneg2 : ∀ n, n + 2 ≤ p → W n = W (n + 2) := by
    intro n hn
    have e1 := hneg (n + 1) (by omega) (by omega)
    have e2 := hneg (n + 2) (by omega) (by omega)
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have a1 := hev n (by omega) h
      have a2 : W (n + 2) = W (n + 1) + D (n + 2) := hod (n + 1) (by omega) (by omega)
      omega
    · have a1 := hod n (by omega) h
      have a2 : W (n + 2) = W (n + 1) - D (n + 2) := hev (n + 1) (by omega) (by omega)
      omega
  have hnegp : ∀ k n, n + 2 * k = p → W n = W p := by
    intro k
    induction k with
    | zero => intro n hn; rw [Nat.mul_zero, Nat.add_zero] at hn; rw [hn]
    | succ k ih =>
      intro n hn
      have := hneg2 n (by omega)
      rw [this]
      exact ih (n + 2) (by omega)
  -- positive portion: `W n = W (n + 2)` for `n ≥ q`
  have hpos2 : ∀ n, q ≤ n → n + 2 ≤ L → W n = W (n + 2) := by
    intro n hn hnL
    have e1 := hone (n + 1) (by omega) (by omega)
    have e2 := hone (n + 2) (by omega) (by omega)
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have a1 := hev n (by omega) h
      have a2 : W (n + 2) = W (n + 1) + D (n + 2) := hod (n + 1) (by omega) (by omega)
      omega
    · have a1 := hod n (by omega) h
      have a2 : W (n + 2) = W (n + 1) - D (n + 2) := hev (n + 1) (by omega) (by omega)
      omega
  -- constant on `[p, q]`
  have hconst : ∀ n, p ≤ n → n ≤ q → W n = W p := by
    intro n h1 h2
    induction n, h1 using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      have hz := hzero (n + 1) (by omega) h2
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have := hev n (by omega) h
        rw [this, hz, ih (by omega)]; ring
      · have := hod n (by omega) h
        rw [this, hz, ih (by omega)]; ring
  have hWq : W q = W p := hconst q hpq le_rfl
  have hposk : ∀ k n, n = q + 2 * k → n ≤ L → W n = W q := by
    intro k
    induction k with
    | zero => intro n hn _; rw [hn]; simp
    | succ k ih =>
      intro n hn hnL
      have h1 := ih (n - 2) (by omega) (by omega)
      have := hpos2 (n - 2) (by omega) (by omega)
      rw [show n - 2 + 2 = n by omega] at this
      rw [← this, h1]
  intro n hn
  by_cases h1 : n + 1 ≤ p
  · -- negative portion
    rcases Nat.mod_two_eq_zero_or_one (p - n) with h | h
    · left
      exact hnegp ((p - n) / 2) n (by omega)
    · right
      exact hnegp ((p - n - 1) / 2) (n + 1) (by omega)
  · have h2 : p ≤ n := by omega
    by_cases h3 : n + 1 ≤ q
    · left; exact hconst n h2 (by omega)
    · have h4 : q ≤ n := by omega
      rcases Nat.mod_two_eq_zero_or_one (n - q) with h | h
      · left
        rw [hposk ((n - q) / 2) n (by omega) (by omega), hWq]
      · right
        rw [hposk ((n + 1 - q) / 2) (n + 1) (by omega) hn, hWq]

end SkewGluing

namespace SkewGluing
namespace MarkedInner

variable {ω η : MarkedInner} {V : Diagram}

/-- The first-row offset `g_j = ℓ_{j+a} - ℓ_j` of the diagonals `j` and `j + a` of `V`
(indexed from the least content `m`). -/
def gStep (V : Diagram) (a j : ℤ) : ℤ :=
  diagLo V (minContent V + j + a) - diagLo V (minContent V + j)

/-- The last-row offset `k_j = h_{j+a} - h_j`. -/
def kStep (V : Diagram) (a j : ℤ) : ℤ :=
  diagHi V (minContent V + j + a) - diagHi V (minContent V + j)

theorem walkDelta_odd (hV : IsConnectedSkew V) {a j : ℤ} (hj : 0 ≤ j)
    (hja : j + a ≤ (span V : ℤ) - 1) (ha : 0 ≤ a) :
    walkDelta V a (2 * (minContent V + j) + 1) = gStep V a j - kStep V a j := by
  have hsp := aligned_span_eq hV
  unfold walkDelta gStep kStep
  have e : 2 * (minContent V + j) + 1 + 2 * a = 2 * (minContent V + j + a) + 1 := by ring
  rw [e, profIL_odd, profIL_odd, aligned_profM_eq (by omega), aligned_profM_eq (by omega)]
  ring

theorem walkDelta_even (hV : IsConnectedSkew V) {a j : ℤ} (hj : 1 ≤ j)
    (hja : j + a ≤ (span V : ℤ) - 1) (ha : 0 ≤ a) :
    walkDelta V a (2 * (minContent V + j)) = gStep V a j - kStep V a (j - 1) := by
  have hsp := aligned_span_eq hV
  unfold walkDelta gStep kStep
  have e : 2 * (minContent V + j) + 2 * a = 2 * (minContent V + j + a) := by ring
  rw [e, profIL_even, profIL_even, aligned_profS_eq (by omega), aligned_profS_eq (by omega)]
  have e1 : minContent V + j - 1 = minContent V + (j - 1) := by ring
  have e2 : minContent V + j + a - 1 = minContent V + (j - 1) + a := by ring
  rw [e1, e2]
  ring

/-- **The level `θ` of the lower mark** (`lem:gluing-aligned`, case (d)): some `θ` equals
`g_j` or `k_j` for every `j < b`, and `k_{j-1}` or `g_j` for every `1 ≤ j < b`.  It is obtained
from the walk `g_0, k_0, g_1, k_1, …` of `eq:gluing-walk-signs`. -/
theorem exists_theta (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period) :
    ∃ θ : ℤ, (∀ j, 0 ≤ j → j < (span V : ℤ) - a → θ = gStep V a j ∨ θ = kStep V a j) ∧
      (∀ j, 1 ≤ j → j < (span V : ℤ) - a → θ = kStep V a (j - 1) ∨ θ = gStep V a j) := by
  have hap := eta_pos hω hV hη hU ha
  have hle := eta_le_span hω hV hη hU ha
  obtain ⟨hb1, hmono, -, -⟩ := walk_signs hω hd hV hη hU ha
  set b := (span V : ℤ) - a with hb
  by_cases hb0 : b = 0
  · exact ⟨0, fun j h1 h2 => by omega, fun j h1 h2 => by omega⟩
  have hbpos : 1 ≤ b := by omega
  let W : ℕ → ℤ := fun n => if n % 2 = 0 then gStep V a ((n / 2 : ℕ) : ℤ)
    else kStep V a ((n / 2 : ℕ) : ℤ)
  let D : ℕ → ℤ := fun n => walkDelta V a (2 * minContent V + (n : ℤ))
  obtain ⟨θ, hθ⟩ := walk_level (2 * b - 1).toNat W D
    (fun i h1 h2 => hb1 _ (by omega) (by omega))
    (fun i j h1 h2 h3 => hmono _ _ (by omega) (by omega) (by omega))
    (fun n hn hpar => by
      -- even step: `W (n+1) = W n - D (n+1)`
      have hj : ((n / 2 : ℕ) : ℤ) = ((n : ℤ) / 2) := by push_cast; rfl
      have hn' : (n : ℤ) = 2 * ((n / 2 : ℕ) : ℤ) := by omega
      have h1 := walkDelta_odd hV (a := a) (j := ((n / 2 : ℕ) : ℤ)) (by omega) (by omega)
        (by omega)
      have e : 2 * minContent V + ((n + 1 : ℕ) : ℤ) =
          2 * (minContent V + ((n / 2 : ℕ) : ℤ)) + 1 := by push_cast; omega
      have hW1 : W (n + 1) = kStep V a ((n / 2 : ℕ) : ℤ) := by
        simp only [W]
        have : (n + 1) % 2 ≠ 0 := by omega
        simp only [this, ↓reduceIte]
        have h : (((n + 1) / 2 : ℕ) : ℤ) = ((n / 2 : ℕ) : ℤ) := by omega
        rw [h]
      have hW0 : W n = gStep V a ((n / 2 : ℕ) : ℤ) := by
        simp only [W, hpar, ↓reduceIte]
      simp only [D]
      rw [hW1, hW0, e, h1]; ring)
    (fun n hn hpar => by
      have hn' : (n : ℤ) = 2 * ((n / 2 : ℕ) : ℤ) + 1 := by omega
      have h1 := walkDelta_even hV (a := a) (j := ((n / 2 : ℕ) : ℤ) + 1) (by omega) (by omega)
        (by omega)
      have e : 2 * minContent V + ((n + 1 : ℕ) : ℤ) =
          2 * (minContent V + (((n / 2 : ℕ) : ℤ) + 1)) := by push_cast; omega
      have hW1 : W (n + 1) = gStep V a (((n / 2 : ℕ) : ℤ) + 1) := by
        simp only [W]
        have : (n + 1) % 2 = 0 := by omega
        simp only [this, ↓reduceIte]
        have h : (((n + 1) / 2 : ℕ) : ℤ) = ((n / 2 : ℕ) : ℤ) + 1 := by omega
        rw [h]
      have hW0 : W n = kStep V a ((n / 2 : ℕ) : ℤ) := by
        simp only [W]
        have : n % 2 ≠ 0 := by omega
        simp only [this, ↓reduceIte]
      simp only [D]
      rw [hW1, hW0, e, h1]
      have : (((n / 2 : ℕ) : ℤ) + 1 - 1) = ((n / 2 : ℕ) : ℤ) := by ring
      rw [this]; ring)
  refine ⟨θ, ?_, ?_⟩
  · intro j hj0 hj1
    have := hθ (2 * j.toNat) (by omega)
    have e1 : W (2 * j.toNat) = gStep V a j := by
      simp only [W]
      have : (2 * j.toNat) % 2 = 0 := by omega
      simp only [this, ↓reduceIte]
      congr 1; omega
    have e2 : W (2 * j.toNat + 1) = kStep V a j := by
      simp only [W]
      have : (2 * j.toNat + 1) % 2 ≠ 0 := by omega
      simp only [this, ↓reduceIte]
      congr 1; omega
    rw [e1, e2] at this
    rcases this with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · intro j hj0 hj1
    have := hθ (2 * (j - 1).toNat + 1) (by omega)
    have e1 : W (2 * (j - 1).toNat + 1) = kStep V a (j - 1) := by
      simp only [W]
      have : (2 * (j - 1).toNat + 1) % 2 ≠ 0 := by omega
      simp only [this, ↓reduceIte]
      congr 1; omega
    have e2 : W (2 * (j - 1).toNat + 1 + 1) = gStep V a j := by
      simp only [W]
      have : (2 * (j - 1).toNat + 1 + 1) % 2 = 0 := by omega
      simp only [this, ↓reduceIte]
      congr 1; omega
    rw [e1, e2] at this
    rcases this with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm

end MarkedInner
end SkewGluing
