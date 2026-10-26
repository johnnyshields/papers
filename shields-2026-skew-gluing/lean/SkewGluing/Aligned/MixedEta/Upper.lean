import SkewGluing.Aligned.MixedEta.Extract

/-!
# The upper copy of an aligned pair

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`, `eq:gluing-nested-count`), the identity `W_η = W_μ ∘_ω E`.

`Setup.W_eq_compose` shows `U ∩ (U - v_η) = (V ∩ (V - z)) ∘_ω E` for an ordinary `ω` and a
case-(d) mark `η`, through the nested endpoints of `eq:gluing-nested-count`.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

namespace MixedEta

variable {ω η : MarkedInner} {V : Diagram} {a : ℤ}

/-- The cells of `V ∩ (V - z)` for `z = (θ, θ + a)`, read on the diagonals of `V`. -/
theorem mem_inter {V : Diagram} (hV : IsConnectedSkew V) {θ a i j : ℤ} :
    (i, i + j) ∈ V.filter (fun y => y + (θ, θ + a) ∈ V) ↔
      j ∈ contents V ∧ j + a ∈ contents V ∧
        max (diagLo V j) (diagLo V (j + a) - θ) ≤ i ∧
        i ≤ min (diagHi V j) (diagHi V (j + a) - θ) := by
  have hs := isConnectedSkew_iff_diagonal.mp hV
  rw [Finset.mem_filter]
  have e : ((i, i + j) : ℤ × ℤ) + (θ, θ + a) = (i + θ, i + θ + (j + a)) := by
    ext <;> simp; ring
  rw [e, hs.mem_iff, hs.mem_iff]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
    exact ⟨h1, h4, by omega, by omega⟩
  · rintro ⟨h1, h4, h5, h6⟩
    exact ⟨⟨h1, by omega, by omega⟩, h4, by omega, by omega⟩

theorem diag_inter {V : Diagram} (hV : IsConnectedSkew V) {θ a j : ℤ}
    (hj : j ∈ contents (V.filter fun y => y + (θ, θ + a) ∈ V)) :
    diagLo (V.filter fun y => y + (θ, θ + a) ∈ V) j = max (diagLo V j) (diagLo V (j + a) - θ) ∧
    diagHi (V.filter fun y => y + (θ, θ + a) ∈ V) j = min (diagHi V j) (diagHi V (j + a) - θ) := by
  obtain ⟨i, hi⟩ := mem_contents_iff.mp hj
  have hi' := (mem_inter hV (θ := θ) (a := a)).mp hi
  obtain ⟨h1, h2, h3, h4⟩ := hi'
  have hle : max (diagLo V j) (diagLo V (j + a) - θ) ≤ min (diagHi V j) (diagHi V (j + a) - θ) := by
    omega
  constructor
  · apply diagLo_eq_of (l := max (diagLo V j) (diagLo V (j + a) - θ))
    · rw [mem_inter hV]
      exact ⟨h1, h2, le_refl _, hle⟩
    · intro i' hi'
      rw [mem_inter hV] at hi'
      exact hi'.2.2.1
  · apply diagHi_eq_of (l := min (diagHi V j) (diagHi V (j + a) - θ))
    · rw [mem_inter hV]
      exact ⟨h1, h2, hle, le_refl _⟩
    · intro i' hi'
      rw [mem_inter hV] at hi'
      exact hi'.2.2.2

theorem eta_rowShift_eq {θ : ℤ} (hz : ω.lat (θ, θ + a) = η.v) :
    η.v.1 = a * ω.rowShift + ω.ordSign * θ := by
  have := congrArg Prod.fst hz
  rw [lat_fst] at this
  have hc : content ((θ, θ + a) : ℤ × ℤ) = a := by simp [content]
  rw [hc] at this
  unfold rowShift
  simp only at this
  omega

namespace Setup

variable (S : Setup ω η V a)
include S

/-- Differences of the origin rows of `V` at `j` and `j + a`, against the row shift of `η`. -/
theorem gamma_data (hb : 1 ≤ (span V : ℤ) - a) :
    (∀ j, minContent V ≤ j → j ≤ minContent V + ((span V : ℤ) - a) - 1 →
      ω.oRowHi V (j + a) = ω.oRowHi V j + η.v.1) ∧
    ω.oRowLo V (minContent V + a) - ω.oRowLo V (minContent V) - η.v.1 ≤ 0 ∧
    0 ≤ ω.oRowLo V (minContent V + ((span V : ℤ) - a) - 1 + a) -
      ω.oRowLo V (minContent V + ((span V : ℤ) - a) - 1) - η.v.1 ∧
    (∀ j, minContent V ≤ j → j ≤ minContent V + ((span V : ℤ) - a) - 1 →
      -1 ≤ ω.oRowLo V (j + a) - ω.oRowLo V j - η.v.1 ∧
      ω.oRowLo V (j + a) - ω.oRowLo V j - η.v.1 ≤ 1) ∧
    (∀ j, minContent V + 1 ≤ j → j ≤ minContent V + ((span V : ℤ) - a) - 1 →
      (ω.oRowLo V (j + a) - ω.oRowLo V j - η.v.1) -
        (ω.oRowLo V (j - 1 + a) - ω.oRowLo V (j - 1) - η.v.1) ≤ 1 ∧
      -1 ≤ (ω.oRowLo V (j + a) - ω.oRowLo V j - η.v.1) -
        (ω.oRowLo V (j - 1 + a) - ω.oRowLo V (j - 1) - η.v.1)) := by
  have hM := S.M_eq
  have hapos := S.a_pos
  have hna := S.two_a_gt
  have hends := S.ends_single
  have hT := ordT_cases S.hord
  refine ⟨fun j h1 h2 => ?_, ?_, ?_, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩
  · have := (S.private_sides hb h1 h2).1
    omega
  · have h1 := (S.private_sides hb (le_refl _) (by omega)).1
    have h2 := oRow_le (ω := ω) S.hV (j := minContent V + a)
      ⟨by omega, by omega⟩
    have h3 := hends.1
    omega
  · have h1 := (S.private_sides hb (j := minContent V + ((span V : ℤ) - a) - 1)
      (by omega) (le_refl _)).1
    have h2 := oRow_le (ω := ω) S.hV (j := minContent V + ((span V : ℤ) - a) - 1)
      ⟨by omega, by omega⟩
    have h3 := hends.2
    have e : minContent V + ((span V : ℤ) - a) - 1 + a = maxContent V := by omega
    rw [e] at h1 ⊢
    omega
  · have := S.private_sides hb h1 h2
    omega
  · have d1 := oRow_diff (ω := ω) S.hV S.hord (J := j) h1 (by omega)
    have d2 := oRow_diff (ω := ω) S.hV S.hord (J := j + a) (by omega) (by omega)
    have e : j + a - 1 = j - 1 + a := by ring
    rw [e] at d2
    omega


/-- **The nested lower endpoints** (`eq:gluing-nested-count`, lower endpoint).  For a diagram `Z`
whose origin rows on the diagonals `[m, m + b - 1]` are the maxima of those of `V` and of the
translated ones at distance `a`, the first row of `Z ∘_ω E` on every class of `Z` is at most
that of the intersection `U ∩ (U - v_η)`. -/
theorem ordLo_Z_le (hb : 1 ≤ (span V : ℤ) - a) {Z : Diagram}
    (hZmin : minContent Z = minContent V)
    (hZmax : maxContent Z = minContent V + ((span V : ℤ) - a) - 1)
    (hZlo : ∀ j, minContent V ≤ j → j ≤ minContent V + ((span V : ℤ) - a) - 1 →
      ω.oRowLo Z j = max (ω.oRowLo V j) (ω.oRowLo V (j + a) - η.v.1))
    {J ρ : ℤ} (_h0 : 0 ≤ ρ) (_h1 : ρ < ω.period)
    (hv : ValidClass (minContent Z) (maxContent Z) ω.widthZ J ρ) :
    ω.ordLo Z J ρ ≤ max (ω.ordLo V J ρ) (ω.ordLo V (J + a) ρ - η.v.1) := by
  obtain ⟨hgh, hg0, hg1, hgr, hgd⟩ := S.gamma_data hb
  have hM := S.M_eq
  have hapos := S.a_pos
  have hna := S.two_a_gt
  have hwq := S.w_lt_q
  have hw0 := S.w_nonneg
  rw [hZmin, hZmax] at hv
  unfold ValidClass at hv
  rcases hv with ⟨hJ1, hJ2⟩ | ⟨hJ, hρ⟩
  · have hJV : minContent V ≤ J ∧ J ≤ maxContent V := ⟨hJ1, by omega⟩
    have hJaV : minContent V ≤ J + a ∧ J + a ≤ maxContent V := ⟨by omega, by omega⟩
    have hZJ : minContent Z ≤ J ∧ J ≤ maxContent Z := ⟨by omega, by omega⟩
    have hrJ := hZlo J hJ1 hJ2
    by_cases hρw : ρ < ω.widthZ
    · by_cases hJm : J = minContent V
      · subst hJm
        have e1 : ¬ (minContent Z ≤ minContent V - 1 ∧ minContent V - 1 ≤ maxContent Z) := by
          omega
        have e2 : ¬ (minContent V ≤ minContent V - 1 ∧ minContent V - 1 ≤ maxContent V) := by
          omega
        rw [ordLo_first hZJ e1, ordLo_first hJV e2, hrJ]
        have e3 : minContent V ≤ minContent V + a - 1 ∧ minContent V + a - 1 ≤ maxContent V := by
          omega
        rw [ordLo_two hJaV (by omega) hρw]
        omega
      · have hZJ1 : minContent Z ≤ J - 1 ∧ J - 1 ≤ maxContent Z := ⟨by omega, by omega⟩
        have hJV1 : minContent V ≤ J - 1 ∧ J - 1 ≤ maxContent V := ⟨by omega, by omega⟩
        have hJaV1 : minContent V ≤ J + a - 1 ∧ J + a - 1 ≤ maxContent V :=
          ⟨by omega, by omega⟩
        have e : J - 1 + a = J + a - 1 := by ring
        have hz1 := hZlo (J - 1) (by omega) (by omega)
        rw [e] at hz1
        rw [ordLo_two hZJ hZJ1 hρw, ordLo_two hJV hJV1 hρw, ordLo_two hJaV hJaV1 hρw,
          hrJ, hz1]
        have hd := hgd J (by omega) hJ2
        rw [e] at hd
        have hr1 := hgr J hJ1 hJ2
        have hr2 := hgr (J - 1) (by omega) (by omega)
        rw [e] at hr2
        omega
    · have hρ' : ω.widthZ ≤ ρ := by omega
      rw [ordLo_private hZJ hρ', ordLo_private hJV hρ', ordLo_private hJaV hρ', hrJ]
      omega
  · have hJV : minContent V ≤ J ∧ J ≤ maxContent V := ⟨by omega, by omega⟩
    have hJV1 : minContent V ≤ J - 1 ∧ J - 1 ≤ maxContent V := ⟨by omega, by omega⟩
    have hZJ1 : minContent Z ≤ J - 1 ∧ J - 1 ≤ maxContent Z := ⟨by omega, by omega⟩
    have hnot : ¬ (minContent Z ≤ J ∧ J ≤ maxContent Z) := by omega
    have hnotV : ¬ (minContent V ≤ J + a ∧ J + a ≤ maxContent V) := by omega
    rw [ordLo_prev hnot, ordLo_two hJV hJV1 hρ, ordLo_prev hnotV,
      hZlo (J - 1) (by omega) (by omega)]
    have hl := hg1
    have e : J + a - 1 = minContent V + ((span V : ℤ) - a) - 1 + a := by omega
    have e' : J - 1 = minContent V + ((span V : ℤ) - a) - 1 := by omega
    rw [e, e']
    rw [e, e'] at *
    omega

/-- **The nested upper endpoints** (`eq:gluing-nested-count`, upper endpoint). -/
theorem ordHi_Z_ge (hb : 1 ≤ (span V : ℤ) - a) {Z : Diagram}
    (hZmin : minContent Z = minContent V)
    (hZmax : maxContent Z = minContent V + ((span V : ℤ) - a) - 1)
    (hZhi : ∀ j, minContent V ≤ j → j ≤ minContent V + ((span V : ℤ) - a) - 1 →
      ω.oRowHi Z j = ω.oRowHi V j)
    {J ρ : ℤ} (_h0 : 0 ≤ ρ) (_h1 : ρ < ω.period)
    (hv : ValidClass (minContent Z) (maxContent Z) ω.widthZ J ρ) :
    min (ω.ordHi V J ρ) (ω.ordHi V (J + a) ρ - η.v.1) ≤ ω.ordHi Z J ρ := by
  obtain ⟨hgh, hg0, hg1, hgr, hgd⟩ := S.gamma_data hb
  have hM := S.M_eq
  have hapos := S.a_pos
  have hna := S.two_a_gt
  have hwq := S.w_lt_q
  have hw0 := S.w_nonneg
  rw [hZmin, hZmax] at hv
  unfold ValidClass at hv
  rcases hv with ⟨hJ1, hJ2⟩ | ⟨hJ, hρ⟩
  · have hJV : minContent V ≤ J ∧ J ≤ maxContent V := ⟨hJ1, by omega⟩
    have hJaV : minContent V ≤ J + a ∧ J + a ≤ maxContent V := ⟨by omega, by omega⟩
    have hZJ : minContent Z ≤ J ∧ J ≤ maxContent Z := ⟨by omega, by omega⟩
    have hrJ := hZhi J hJ1 hJ2
    by_cases hρw : ρ < ω.widthZ
    · by_cases hJm : J = minContent V
      · subst hJm
        have e1 : ¬ (minContent Z ≤ minContent V - 1 ∧ minContent V - 1 ≤ maxContent Z) := by
          omega
        have e2 : ¬ (minContent V ≤ minContent V - 1 ∧ minContent V - 1 ≤ maxContent V) := by
          omega
        rw [ordHi_first hZJ e1, ordHi_first hJV e2, hrJ]
        omega
      · have hZJ1 : minContent Z ≤ J - 1 ∧ J - 1 ≤ maxContent Z := ⟨by omega, by omega⟩
        have hJV1 : minContent V ≤ J - 1 ∧ J - 1 ≤ maxContent V := ⟨by omega, by omega⟩
        rw [ordHi_two hZJ hZJ1 hρw, ordHi_two hJV hJV1 hρw, hrJ,
          hZhi (J - 1) (by omega) (by omega)]
        omega
    · have hρ' : ω.widthZ ≤ ρ := by omega
      rw [ordHi_private hZJ hρ', ordHi_private hJV hρ', hrJ]
      omega
  · have hJV : minContent V ≤ J ∧ J ≤ maxContent V := ⟨by omega, by omega⟩
    have hJV1 : minContent V ≤ J - 1 ∧ J - 1 ≤ maxContent V := ⟨by omega, by omega⟩
    have hnot : ¬ (minContent Z ≤ J ∧ J ≤ maxContent Z) := by omega
    have hnotV : ¬ (minContent V ≤ J + a ∧ J + a ≤ maxContent V) := by omega
    rw [ordHi_prev hnot, ordHi_two hJV hJV1 hρ, ordHi_prev hnotV,
      hZhi (J - 1) (by omega) (by omega)]
    have e : J + a - 1 = minContent V + ((span V : ℤ) - a) - 1 + a := by omega
    have e' : J - 1 = minContent V + ((span V : ℤ) - a) - 1 := by omega
    have hk := hgh (minContent V + ((span V : ℤ) - a) - 1) (by omega) (le_refl _)
    rw [e, e'] at *
    omega


/-- The origin rows of `Z = V ∩ (V - z)` on the diagonals of `Z`. -/
theorem Z_oRow (hb : 1 ≤ (span V : ℤ) - a) {θ : ℤ} (hz : ω.lat (θ, θ + a) = η.v)
    {Z : Diagram} (hZ : Z = V.filter fun y => y + (θ, θ + a) ∈ V)
    (hZc : contents Z = Finset.Icc (minContent V) (minContent V + ((span V : ℤ) - a) - 1)) :
    (∀ j, minContent V ≤ j → j ≤ minContent V + ((span V : ℤ) - a) - 1 →
      ω.oRowLo Z j = max (ω.oRowLo V j) (ω.oRowLo V (j + a) - η.v.1)) ∧
    (∀ j, minContent V ≤ j → j ≤ minContent V + ((span V : ℤ) - a) - 1 →
      ω.oRowHi Z j = ω.oRowHi V j) := by
  obtain ⟨hgh, -⟩ := S.gamma_data hb
  have hp := eta_rowShift_eq (ω := ω) (η := η) (a := a) hz
  have hsg := ordSign_cases ω
  have hcase : ω.case = .a ∨ ω.case = .b := by
    have := S.hord
    unfold AttachCase.IsMixed at this
    cases hh : ω.case <;> simp_all
  have hmul : ∀ j : ℤ, (j + a) * ω.rowShift = j * ω.rowShift + a * ω.rowShift := fun j => by ring
  have hdi : ∀ j, minContent V ≤ j → j ≤ minContent V + ((span V : ℤ) - a) - 1 →
      diagLo Z j = max (diagLo V j) (diagLo V (j + a) - θ) ∧
      diagHi Z j = min (diagHi V j) (diagHi V (j + a) - θ) := by
    intro j h1 h2
    have hj : j ∈ contents Z := by rw [hZc, Finset.mem_Icc]; exact ⟨h1, h2⟩
    rw [hZ] at hj ⊢
    exact diag_inter S.hV hj
  refine ⟨fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩
  · have hd := hdi j h1 h2
    rcases hcase with hc | hc
    · have hs : ω.ordSign = 1 := by simp [ordSign, hc]
      rw [hs] at hp
      have e1 : ∀ D : Diagram, ∀ j, ω.oRowLo D j = j * ω.rowShift + diagLo D j := by
        intro D j; simp [oRowLo, hc]
      simp only [e1, hd.1, hmul]
      omega
    · have hs : ω.ordSign = -1 := by simp [ordSign, hc]
      rw [hs] at hp
      have e1 : ∀ D : Diagram, ∀ j, ω.oRowLo D j = j * ω.rowShift - diagHi D j := by
        intro D j; simp [oRowLo, hc]
      simp only [e1, hd.2, hmul]
      omega
  · have hd := hdi j h1 h2
    have hF := hgh j h1 h2
    rcases hcase with hc | hc
    · have hs : ω.ordSign = 1 := by simp [ordSign, hc]
      rw [hs] at hp
      have e1 : ∀ D : Diagram, ∀ j, ω.oRowHi D j = j * ω.rowShift + diagHi D j := by
        intro D j; simp [oRowHi, hc]
      simp only [e1, hmul] at hF ⊢
      rw [hd.2]
      omega
    · have hs : ω.ordSign = -1 := by simp [ordSign, hc]
      rw [hs] at hp
      have e1 : ∀ D : Diagram, ∀ j, ω.oRowHi D j = j * ω.rowShift - diagLo D j := by
        intro D j; simp [oRowHi, hc]
      simp only [e1, hmul] at hF ⊢
      rw [hd.1]
      omega


/-- **The lower copy of `η` is `Z ∘_ω E`** (`lem:gluing-aligned`): the intersection
`U ∩ (U - v_η)` is the composition of `Z = V ∩ (V - z)` with `ω`.  **Differs from the paper's
route.**  The paper compares the heights of both sides by the nested counts
`eq:gluing-nested-count`; here only the endpoint inequalities `ordLo_Z_le`, `ordHi_Z_ge` are
needed, the other inclusion being the lattice identity. -/
theorem W_eq_compose (hb : 1 ≤ (span V : ℤ) - a) {θ : ℤ} (hz : ω.lat (θ, θ + a) = η.v)
    {Z : Diagram} (hZ : Z = V.filter fun y => y + (θ, θ + a) ∈ V) (hZc : IsConnectedSkew Z)
    (hZcont : contents Z = Finset.Icc (minContent V) (minContent V + ((span V : ℤ) - a) - 1)) :
    η.W = ω.compose Z := by
  have hq := S.q_pos
  have hwq := S.w_lt_q
  have hw0 := S.w_nonneg
  have hM := S.M_eq
  have hapos := S.a_pos
  have hna := S.two_a_gt
  have hZne := hZc.2.1
  have hVne := S.hV.2.1
  have hZmin : minContent Z = minContent V := by
    apply minContent_eq_of (k := minContent V)
    · rw [hZcont, Finset.mem_Icc]; omega
    · intro k hk
      rw [hZcont, Finset.mem_Icc] at hk
      exact hk.1
  have hZmax : maxContent Z = minContent V + ((span V : ℤ) - a) - 1 := by
    apply maxContent_eq_of (k := minContent V + ((span V : ℤ) - a) - 1)
    · rw [hZcont, Finset.mem_Icc]; omega
    · intro k hk
      rw [hZcont, Finset.mem_Icc] at hk
      exact hk.2
  obtain ⟨hZlo, hZhi⟩ := S.Z_oRow hb hz hZ hZcont
  have hηW : η.W = η.fullIntersection := S.hη.W_eq_fullIntersection S.eta_ne.2
  have hZV : ∀ y ∈ Z, y ∈ V ∧ y + (θ, θ + a) ∈ V := by
    intro y hy
    rw [hZ] at hy
    exact Finset.mem_filter.mp hy
  ext x
  rw [hηW]
  unfold fullIntersection
  rw [Finset.mem_filter, S.hU]
  constructor
  · rintro ⟨hxU, hxU'⟩
    obtain ⟨r, K, rfl⟩ : ∃ r K, x = (r, r + K) := ⟨x.1, x.2 - x.1, by ext <;> simp⟩
    set c0 := minContent ω.E with hc0
    obtain ⟨J, ρ, hρ0, hρq, hK⟩ :
        ∃ J ρ : ℤ, 0 ≤ ρ ∧ ρ < ω.period ∧ K = c0 + (J * ω.period + ρ) := by
      refine ⟨(K - c0) / ω.period, (K - c0) % ω.period, Int.emod_nonneg _ hq.ne',
        Int.emod_lt_of_pos _ hq, ?_⟩
      have := Int.mul_ediv_add_emod (K - c0) ω.period
      have e : (K - c0) / ω.period * ω.period = ω.period * ((K - c0) / ω.period) := by ring
      omega
    subst hK
    have hcl := mem_compose_class S.hω S.hord S.hV (J := J) (ρ := ρ) (r := r) hρ0 hρq
    rw [hcl] at hxU
    have hv : η.v = (η.v.1, η.v.1 + a * ω.period) := by
      have := η.v_eq
      rw [S.eta_period] at this
      exact this
    have e2 : ((r, r + (c0 + (J * ω.period + ρ))) : ℤ × ℤ) + η.v =
        (r + η.v.1, r + η.v.1 + (c0 + ((J + a) * ω.period + ρ))) := by
      rw [hv]
      ext
      · simp
      · simp only [Prod.snd_add]; ring
    rw [e2, mem_compose_class S.hω S.hord S.hV (J := J + a) (ρ := ρ) (r := r + η.v.1) hρ0
      hρq] at hxU'
    obtain ⟨hv1, hl1, hh1⟩ := hxU
    obtain ⟨hv2, hl2, hh2⟩ := hxU'
    rw [mem_compose_class S.hω S.hord hZc hρ0 hρq]
    have hvZ : ValidClass (minContent Z) (maxContent Z) ω.widthZ J ρ := by
      rw [hZmin, hZmax]
      unfold ValidClass at hv1 hv2 ⊢
      omega
    refine ⟨hvZ, ?_, ?_⟩
    · have := S.ordLo_Z_le hb hZmin hZmax hZlo hρ0 hρq hvZ
      omega
    · have := S.ordHi_Z_ge hb hZmin hZmax hZhi hρ0 hρq hvZ
      omega
  · intro hx
    rw [mem_compose_lat S.hord hZne] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    obtain ⟨hy1, hy2⟩ := hZV y hy
    rw [mem_compose_lat S.hord hVne]
    refine ⟨⟨y, hy1, hxy⟩, ?_⟩
    rw [mem_compose_lat S.hord hVne]
    refine ⟨y + (θ, θ + a), hy2, ?_⟩
    rw [lat_add, hz]
    have : x + η.v - (ω.lat y + η.v) = x - ω.lat y := by abel
    rw [this]; exact hxy

end Setup

end MixedEta

end MarkedInner

end SkewGluing
