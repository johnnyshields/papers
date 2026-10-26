import SkewGluing.Aligned.CaseD.Asm2

/-!
# Aligned marks, case (d): the reassociation identity from the nested count

Formalizes `shields-2026-skew-gluing.tex`, «Equal and divisible periods»
(`eq:gluing-reassociation`, `eq:gluing-nested-count`).

`alD_identity_of_NCI` proves `C ∘_η U = (C ∘_μ V) ∘_ω E` from the nested count `alD_NCI`: both
sides are connected skew diagrams (`lem:gluing-local` (3)), with the same contents, the same
southeast rows (`alD_FL_diagHi`, `alD_FR_diagHi`) and the same heights on every class
(`alD_class_height_eq`).

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

theorem alD_eq_of_diag_eq {A B : Diagram} (hA : IsConnectedSkew A) (hB : IsConnectedSkew B)
    (hc : contents A = contents B) (hlo : ∀ k ∈ contents A, diagLo A k = diagLo B k)
    (hhi : ∀ k ∈ contents A, diagHi A k = diagHi B k) : A = B := by
  have sA := isConnectedSkew_iff_diagonal.mp hA
  have sB := isConnectedSkew_iff_diagonal.mp hB
  ext ⟨i, j⟩
  have e : (i, j) = (i, i + (j - i)) := by ext <;> simp
  rw [e, sA.mem_iff, sB.mem_iff, ← hc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by rw [← hlo _ h1]; exact h2, by rw [← hhi _ h1]; exact h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by rw [hlo _ h1]; exact h2, by rw [hhi _ h1]; exact h3⟩

variable {ω η : MarkedInner} {V C : Diagram}

theorem alD_x_bounds {q w b i α : ℤ} (hq0 : 0 < q) (hα0 : 0 ≤ α) (_hα1 : α < q)
    (hx : i * q + α < b * q + w) (_hw0 : 0 ≤ w) (hwq : w < q) : i ≤ b ∧ (i = b → α < w) := by
  constructor
  · by_contra hne
    have h5 : (b + 1) * q ≤ i * q := mul_le_mul_of_nonneg_right (by omega) hq0.le
    have e : (b + 1) * q = b * q + q := by ring
    linarith
  · intro h
    rw [h] at hx
    linarith

theorem alD_validX (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    {θ : ℤ} (hD : alD_Data V a θ) (hC : IsConnectedSkew C) {J i α : ℤ} (hi0 : 0 ≤ i)
    (hi1 : i < a) (hα0 : 0 ≤ α) (hα1 : α < ω.period)
    (hv : ValidClass (minContent C) (maxContent C) η.widthZ J (i * ω.period + α)) :
    ValidClass (minContent ((alD_lowerMark V a θ).compose C))
      (maxContent ((alD_lowerMark V a θ).compose C)) ω.widthZ (minContent V + (J * a + i)) α := by
  have hl := aligned_legalNonempty hω hd
  have hq := hl.width_lt_period
  have hw0 := hl.width_pos
  have hq0 : 0 < ω.period := by omega
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hwη := eta_width_eq hω hV hη hU ha
  have hwη' : η.widthZ = ((span V : ℤ) - a) * ω.period + ω.widthZ := by
    have : η.widthZ = (η.width : ℤ) := rfl
    rw [this, hwη]; rfl
  have hminX := alD_minContent_X hV hD hC
  have hmaxX := alD_maxContent_X hV hD hC
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
  unfold ValidClass at hv ⊢
  rw [hminX, hmaxX]
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have e1 := mul_le_mul_of_nonneg_right h1 hap.le
    have e2 := mul_le_mul_of_nonneg_right h2 hap.le
    constructor <;> omega
  · rw [hwη'] at h2
    have hbd := alD_x_bounds (b := (span V : ℤ) - a) hq0 hα0 hα1 h2 (by omega) hq
    have e : (maxContent C + 1) * a = maxContent C * a + a := by ring
    have e3 := mul_le_mul_of_nonneg_right hmM hap.le
    by_cases hib : i < (span V : ℤ) - a
    · left
      subst h1
      constructor <;> omega
    · right
      have hie : i = (span V : ℤ) - a := by omega
      subst h1
      exact ⟨by omega, hbd.2 hie⟩

theorem alD_identity_of_NCI (hω : ω.IsLegal) (hd : ω.case = .d) (hV : IsConnectedSkew V)
    (hη : η.IsLegal) (hU : η.E = ω.compose V) {a : ℤ} (ha : content η.v = a * ω.period)
    {θ : ℤ} (hD : alD_Data V a θ) (hC : IsConnectedSkew C) (hNCI : alD_NCI V a θ C) :
    η.compose C = ω.compose ((alD_lowerMark V a θ).compose C) := by
  have hl := aligned_legalNonempty hω hd
  have hq := hl.width_lt_period
  have hw0 := hl.width_pos
  have hq0 : 0 < ω.period := by omega
  have hb := hD.hb
  have hba := hD.hba
  have hap := hD.ha
  have hper : η.period = a * ω.period := ha
  have hwη := eta_width_eq hω hV hη hU ha
  have hwη' : η.widthZ = ((span V : ℤ) - a) * ω.period + ω.widthZ := by
    have : η.widthZ = (η.width : ℤ) := rfl
    rw [this, hwη]; rfl
  have hwη'' : (η.width : ℤ) = ((span V : ℤ) - a) * ω.period + ω.widthZ := hwη'
  have hμ := alD_lowerMark_isLegal hV hD
  set X := (alD_lowerMark V a θ).compose C with hXdef
  have hX : IsConnectedSkew X := hμ.isConnectedSkew_compose hC
  have hL : IsConnectedSkew (η.compose C) := hη.isConnectedSkew_compose hC
  have hR : IsConnectedSkew (ω.compose X) := hω.isConnectedSkew_compose hX
  have hmM : minContent C ≤ maxContent C := minContent_le (maxContent_mem hC.2.1)
  have hminX : minContent X = minContent V + minContent C * a := alD_minContent_X hV hD hC
  have hmaxX : maxContent X = minContent V + maxContent C * a + a + ((span V : ℤ) - a) - 1 :=
    alD_maxContent_X hV hD hC
  have hηmin := eta_minContent hω hV hU
  have hLmin : minContent (η.compose C) =
      minContent ω.E + (minContent V + minContent C * a) * ω.period := by
    rw [hη.minContent_compose hC, hηmin, hper]; unfold alignedC0; ring
  have hLmax : maxContent (η.compose C) =
      minContent ω.E + (minContent V + maxContent C * a + a + ((span V : ℤ) - a)) * ω.period
        + ω.widthZ - 1 := by
    rw [hη.maxContent_compose hC, hηmin, hper, hwη'']; unfold alignedC0; ring
  have hRmin : minContent (ω.compose X) =
      minContent ω.E + (minContent V + minContent C * a) * ω.period := by
    rw [hω.minContent_compose hX, hminX]
  have hRmax : maxContent (ω.compose X) =
      minContent ω.E + (minContent V + maxContent C * a + a + ((span V : ℤ) - a)) * ω.period
        + ω.widthZ - 1 := by
    rw [hω.maxContent_compose hX, hmaxX]
    have : (ω.width : ℤ) = ω.widthZ := rfl
    rw [this]; ring
  have sL := isConnectedSkew_iff_diagonal.mp hL
  have sR := isConnectedSkew_iff_diagonal.mp hR
  have key : ∀ k ∈ contents (η.compose C), ∃ J i α : ℤ, 0 ≤ i ∧ i < a ∧ 0 ≤ α ∧
      α < ω.period ∧ ValidClass (minContent C) (maxContent C) η.widthZ J (i * ω.period + α) ∧
      k = minContent ω.E + ((minContent V + (J * a + i)) * ω.period + α) := by
    intro k hk
    rw [sL.mem_contents_iff, hLmin, hLmax] at hk
    obtain ⟨hk1, hk2⟩ := hk
    set r := k - minContent ω.E with hr
    have hr1 := Int.mul_ediv_add_emod r ω.period
    have hr2 := Int.emod_nonneg r hq0.ne'
    have hr3 := Int.emod_lt_of_pos r hq0
    set Jt := r / ω.period with hJt
    set α := r % ω.period with hα
    set A := minContent V + minContent C * a with hA
    set B := minContent V + maxContent C * a + a + ((span V : ℤ) - a) with hB
    have e0 : ω.period * Jt = Jt * ω.period := by ring
    have hJ1 : A ≤ Jt := by
      by_contra hne
      have h5 : (Jt + 1) * ω.period ≤ A * ω.period :=
        mul_le_mul_of_nonneg_right (by omega) hq0.le
      have e1 : (Jt + 1) * ω.period = Jt * ω.period + ω.period := by ring
      linarith
    have hJ2 : Jt ≤ B := by
      by_contra hne
      have h5 : (B + 1) * ω.period ≤ Jt * ω.period :=
        mul_le_mul_of_nonneg_right (by omega) hq0.le
      have e1 : (B + 1) * ω.period = B * ω.period + ω.period := by ring
      linarith
    have hJ3 : Jt = B → α < ω.widthZ := by
      intro he
      rw [he] at hr1 e0
      linarith
    set u := Jt - minContent V with hu
    have hu1 := Int.mul_ediv_add_emod u a
    have hu2 := Int.emod_nonneg u hap.ne'
    have hu3 := Int.emod_lt_of_pos u hap
    set J := u / a with hJ
    set i := u % a with hi
    have e5 : a * J = J * a := by ring
    have hJmin : minContent C ≤ J := by
      by_contra hne
      have h5 : (J + 1) * a ≤ minContent C * a :=
        mul_le_mul_of_nonneg_right (by omega) hap.le
      have e1 : (J + 1) * a = J * a + a := by ring
      omega
    have hJmax : J ≤ maxContent C + 1 := by
      by_contra hne
      have h5 : (maxContent C + 2) * a ≤ J * a :=
        mul_le_mul_of_nonneg_right (by omega) hap.le
      have e1 : (maxContent C + 2) * a = maxContent C * a + 2 * a := by ring
      omega
    refine ⟨J, i, α, hu2, hu3, hr2, hr3, ?_, ?_⟩
    · unfold ValidClass
      by_cases hc2 : J ≤ maxContent C
      · left; exact ⟨hJmin, hc2⟩
      · right
        have hc3 : J = maxContent C + 1 := by omega
        refine ⟨hc3, ?_⟩
        rw [hwη']
        have hib : i ≤ (span V : ℤ) - a := by
          rw [hc3] at hu1 e5
          have : (maxContent C + 1) * a = maxContent C * a + a := by ring
          omega
        by_cases hi2 : i < (span V : ℤ) - a
        · have h5 : (i + 1) * ω.period ≤ ((span V : ℤ) - a) * ω.period :=
            mul_le_mul_of_nonneg_right (by omega) hq0.le
          have h6 : (i + 1) * ω.period = i * ω.period + ω.period := by ring
          omega
        · have hie : i = (span V : ℤ) - a := by omega
          have hJe : Jt = B := by
            rw [hc3] at hu1 e5
            have : (maxContent C + 1) * a = maxContent C * a + a := by ring
            rw [hie] at hu1
            omega
          have := hJ3 hJe
          rw [hie]; omega
    · have e : Jt = minContent V + (J * a + i) := by omega
      rw [← e]; linarith
  refine alD_eq_of_diag_eq hL hR ?_ ?_ ?_
  · rw [sL.contents_eq, sR.contents_eq, hLmin, hLmax, hRmin, hRmax]
  · intro k hk
    obtain ⟨J, i, α, hi0, hi1, hα0, hα1, hv, rfl⟩ := key k hk
    have h1 := alD_class_height_eq hω hd hV hη hU ha hD hC hNCI hi0 hi1 hα0 hα1 hv
    have h2 := alD_FL_diagHi hω hd hV hη hU ha hC hi0 hi1 hα0 hα1 hv
    have h3 : diagHi (ω.compose ((alD_lowerMark V a θ).compose C))
        (minContent ω.E + ((minContent V + (J * a + i)) * ω.period + α)) =
        ω.hi α + (minContent V + (J * a + i)) * ω.rowShift := by
      apply alD_FR_diagHi hω hd hX hα0 hα1
      exact alD_validX hω hd hV hη hU ha hD hC hi0 hi1 hα0 hα1 hv
    unfold height at h1
    rw [hXdef]
    omega
  · intro k hk
    obtain ⟨J, i, α, hi0, hi1, hα0, hα1, hv, rfl⟩ := key k hk
    have h2 := alD_FL_diagHi hω hd hV hη hU ha hC hi0 hi1 hα0 hα1 hv
    have h3 : diagHi (ω.compose ((alD_lowerMark V a θ).compose C))
        (minContent ω.E + ((minContent V + (J * a + i)) * ω.period + α)) =
        ω.hi α + (minContent V + (J * a + i)) * ω.rowShift := by
      apply alD_FR_diagHi hω hd hX hα0 hα1
      exact alD_validX hω hd hV hη hU ha hD hC hi0 hi1 hα0 hα1 hv
    rw [hXdef, h2, h3]

end MarkedInner

end SkewGluing
