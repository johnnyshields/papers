import SkewGluing.OrdinaryFold.Mark
import SkewGluing.Invariance
import SkewGluing.Antitranspose
import SkewGluing.AntitransposeMixed

/-!
# The ordinary cell criterion

Formalizes `shields-2026-skew-gluing.tex`, «Reconstructing a chart from its two words»
(`ge:cell-criterion`): a connected skew diagram `K` of span `g + a`, whose boundary bits satisfy
the displayed recursions of the criterion, carries a full legal ordinary mark of period `g`,
width `a` and contacts `(σ, τ)`, with the stated lower and upper copies.

The diagonals of `K` are indexed from its least content `m`: `λ_c = diagLo K (m + c)`,
`μ_c = diagHi K (m + c)`, `A_c = bitA K (m + c)`, `B_c = bitB K (m + c)` and
`h(c) = height K (m + c)`.
The proof checks the diagonal data `SlotGeom` of `SkewGluing.OrdinaryFold.Mark` on the
content-normalized translate of `K` and translates the mark back.

* `cell_criterion`: the mark of case (a);
* `cell_criterion_anti`: the actual antitransposed mark, of case (b), on `AT(K)`;
* `ordinary_block_formula`: the block formula `ge:eq:ordinary-block` for the height sums of the
  completed native row and column words of an ordinary inner whose classes modulo `g` are full or
  empty off one exceptional class in each word.

Sorry-free.
-/

namespace SkewGluing

open MarkedInner

/-- The first row of the diagonal of content `m + c` of `K`, with `m = minContent K`. -/
def cLo (K : Diagram) (c : ℤ) : ℤ := diagLo K (minContent K + c)

/-- The last row of the diagonal of content `m + c` of `K`, with `m = minContent K`. -/
def cHi (K : Diagram) (c : ℤ) : ℤ := diagHi K (minContent K + c)

theorem bitA_cLo (K : Diagram) (c : ℤ) : bitA K (minContent K + c) = cLo K (c - 1) - cLo K c := by
  unfold bitA cLo
  rw [show minContent K + (c - 1) = minContent K + c - 1 by ring]

theorem bitB_cHi (K : Diagram) (c : ℤ) : bitB K (minContent K + c) = cHi K (c - 1) - cHi K c := by
  unfold bitB cHi
  rw [show minContent K + (c - 1) = minContent K + c - 1 by ring]

theorem height_cLo (K : Diagram) (c : ℤ) : height K (minContent K + c) = cHi K c - cLo K c + 1 :=
  rfl

/-- Translating a diagonal description by `(0, m)` moves the contents by `m`. -/
theorem DiagSet.translate_zero_fst {S : Diagram} {k₀ k₁ : ℤ} {lo hi : ℤ → ℤ} (m : ℤ)
    (h : DiagSet S k₀ k₁ lo hi) :
    DiagSet (translate (0, m) S) (k₀ + m) (k₁ + m) (fun k => lo (k - m)) (fun k => hi (k - m)) := by
  intro i k
  rw [mem_translate]
  have e : (i, i + k) - (0, m) = (i, i + (k - m)) := by
    ext <;> simp
    ring
  rw [e, h]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by omega, by omega, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by omega, by omega, h3, h4⟩

section Normalized

variable {K : Diagram}

theorem maxContent_of_span (hK : IsConnectedSkew K) {n : ℤ} (hn : (span K : ℤ) = n) :
    maxContent K = minContent K + n - 1 := by
  have := span_eq_of_isConnectedSkew hK
  omega

theorem diagSet_normalize (hK : IsConnectedSkew K) {n : ℤ} (hn : (span K : ℤ) = n) :
    DiagSet (translate (0, -minContent K) K) 0 (n - 1) (cLo K) (cHi K) ∧
      DiagShape 0 (n - 1) (cLo K) (cHi K) := by
  have hD := isConnectedSkew_iff_diagonal.mp hK
  have hmax := maxContent_of_span hK hn
  have hc := hD.contents_eq
  have memC : ∀ k, minContent K ≤ k → k ≤ minContent K + n - 1 → k ∈ contents K := by
    intro k h1 h2
    rw [hc, Finset.mem_Icc]
    omega
  have hmin : minContent K ∈ contents K := minContent_mem hD.1
  have hn1 : 1 ≤ n := by
    have := minContent_le (maxContent_mem hD.1)
    omega
  refine ⟨?_, ?_⟩
  · intro i k
    rw [mem_translate]
    have e : (i, i + k) - (0, -minContent K) = (i, i + (minContent K + k)) := by
      ext <;> simp
      ring
    rw [e, hD.mem_iff, hc, Finset.mem_Icc]
    unfold cLo cHi
    omega
  · refine ⟨by omega, fun k h1 h2 => ?_, fun k h1 h2 => ?_, fun k h1 h2 => ?_, ?_, ?_⟩
    · exact diagLo_le_diagHi (memC _ (by omega) (by omega))
    · have := hD.2.2.2.1 (minContent K + k) (memC _ (by omega) (by omega))
        (by have := memC (minContent K + k - 1) (by omega) (by omega); exact this)
      have h3 := this.1
      simp only [Finset.mem_insert, Finset.mem_singleton] at h3
      rw [← bitA_cLo]
      exact h3
    · have := hD.2.2.2.1 (minContent K + k) (memC _ (by omega) (by omega))
        (by have := memC (minContent K + k - 1) (by omega) (by omega); exact this)
      have h3 := this.2
      simp only [Finset.mem_insert, Finset.mem_singleton] at h3
      rw [← bitB_cHi]
      exact h3
    · have := hD.2.2.2.2 (minContent K) hmin
        (Or.inl (by rw [hc, Finset.mem_Icc]; omega))
      unfold cLo cHi
      simpa using this
    · have := hD.2.2.2.2 (minContent K + (n - 1)) (memC _ (by omega) (by omega))
        (Or.inr (by rw [hc, Finset.mem_Icc]; omega))
      unfold cLo cHi
      exact this

end Normalized

section Criterion

variable {K : Diagram} {g a τ σ : ℤ}

/-- The hypotheses of the criterion, on the diagonals of `K` indexed from `minContent K`. -/
structure CellCriterionData (K : Diagram) (g a τ σ : ℤ) : Prop where
  conn : IsConnectedSkew K
  span_eq : (span K : ℤ) = g + a
  a_pos : 1 ≤ a
  a_lt : a < g
  τ_nonneg : 0 ≤ τ
  τ_lt : τ < a
  σ_pos : 1 ≤ σ
  σ_le : σ ≤ a
  bitA_rec : ∀ c, 1 ≤ c → c < a →
    bitA K (minContent K + (g + c)) = bitA K (minContent K + c) - if c = τ then 1 else 0
  bitB_rec : ∀ c, 1 ≤ c → c < a →
    bitB K (minContent K + (g + c)) = bitB K (minContent K + c) + if c = σ then 1 else 0
  height_g : height K (minContent K + g) = 1 + if 0 < τ then 1 else 0
  height_pos : ∀ c, 0 ≤ c → c < a →
    1 + (if σ ≤ c then 1 else 0) ≤ height K (minContent K + c)
  height_a : height K (minContent K + a) = 1
  height_pred : height K (minContent K + (g - 1)) = 1
  bitB_a : σ = a → bitB K (minContent K + a) = 0
  bitA_g : τ = 0 → bitA K (minContent K + g) = 0

/-- The row displacement `ν₁ = λ_g + 1_{τ>0} - λ_0` of the mark. -/
def cellShift (K : Diagram) (g τ : ℤ) : ℤ := cLo K g + (if 0 < τ then 1 else 0) - cLo K 0

theorem CellCriterionData.slotGeom (h : CellCriterionData K g a τ σ) :
    SlotGeom g a τ σ (cellShift K g τ) (cLo K) (cHi K) := by
  have hn : (span K : ℤ) = g + a := h.span_eq
  obtain ⟨-, hsh⟩ := diagSet_normalize h.conn (n := g + a) hn
  have ha := h.a_pos
  have hag := h.a_lt
  have hτ0 := h.τ_nonneg
  have hτa := h.τ_lt
  have hσ1 := h.σ_pos
  have hσa := h.σ_le
  have bA : ∀ c, 1 ≤ c → c < a →
      cLo K (g + c - 1) - cLo K (g + c) = cLo K (c - 1) - cLo K c - if c = τ then 1 else 0 := by
    intro c h1 h2
    have := h.bitA_rec c h1 h2
    rw [bitA_cLo, bitA_cLo] at this
    simpa using this
  have bB : ∀ c, 1 ≤ c → c < a →
      cHi K (g + c - 1) - cHi K (g + c) = cHi K (c - 1) - cHi K c + if c = σ then 1 else 0 := by
    intro c h1 h2
    have := h.bitB_rec c h1 h2
    rw [bitB_cHi, bitB_cHi] at this
    simpa using this
  have e0 : cLo K 0 = cHi K 0 := hsh.endLo
  have hhg : cHi K g - cLo K g + 1 = 1 + if 0 < τ then 1 else 0 := by
    have := h.height_g
    rwa [height_cLo] at this
  have hsingA : cHi K a = cLo K a := by
    have := h.height_a
    rw [height_cLo] at this
    omega
  have hsingG : cHi K (g - 1) = cLo K (g - 1) := by
    have := h.height_pred
    rw [height_cLo] at this
    omega
  -- first rows
  have key_lo : ∀ n : ℕ, (n : ℤ) < a →
      cLo K (g + n) + (if (n : ℤ) < τ then 1 else 0) = cLo K n + cellShift K g τ := by
    intro n
    induction n with
    | zero =>
      intro _
      unfold cellShift
      by_cases hτ : 0 < τ <;> simp [hτ]
    | succ n ih =>
      intro hn1
      have ih' := ih (by push_cast at hn1; omega)
      have := bA ((n : ℤ) + 1) (by omega) (by push_cast at hn1; omega)
      push_cast
      have e1 : g + ((n : ℤ) + 1) - 1 = g + n := by ring
      have e2 : (n : ℤ) + 1 - 1 = n := by ring
      rw [e1, e2] at this
      by_cases h1 : (n : ℤ) + 1 = τ
      · have h2 : (n : ℤ) < τ := by omega
        have h3 : ¬ (n : ℤ) + 1 < τ := by omega
        simp only [h1, h2, ite_true] at this ih' ⊢
        omega
      · have h3 : (n : ℤ) < τ ↔ (n : ℤ) + 1 < τ := by omega
        by_cases h4 : (n : ℤ) < τ
        · have h5 : (n : ℤ) + 1 < τ := h3.mp h4
          simp only [h1, h4, h5, ite_false] at this ih' ⊢
          omega
        · have h5 : ¬ (n : ℤ) + 1 < τ := fun hh => h4 (h3.mpr hh)
          simp only [h1, h4, h5, ite_false] at this ih' ⊢
          omega
  have key_hi : ∀ n : ℕ, (n : ℤ) < a →
      cHi K (g + n) + (if σ ≤ (n : ℤ) then 1 else 0) = cHi K n + cellShift K g τ := by
    intro n
    induction n with
    | zero =>
      intro _
      unfold cellShift
      have : ¬ σ ≤ 0 := by omega
      by_cases hτ : 0 < τ <;> simp [hτ, this] <;> omega
    | succ n ih =>
      intro hn1
      have ih' := ih (by push_cast at hn1; omega)
      have := bB ((n : ℤ) + 1) (by omega) (by push_cast at hn1; omega)
      push_cast
      have e1 : g + ((n : ℤ) + 1) - 1 = g + n := by ring
      have e2 : (n : ℤ) + 1 - 1 = n := by ring
      rw [e1, e2] at this
      by_cases h1 : (n : ℤ) + 1 = σ
      · have h2 : ¬ σ ≤ (n : ℤ) := by omega
        have h3 : σ ≤ (n : ℤ) + 1 := by omega
        simp only [h1, h2, ite_true] at this ih' ⊢
        omega
      · by_cases h4 : σ ≤ (n : ℤ)
        · have h5 : σ ≤ (n : ℤ) + 1 := by omega
          simp only [h1, h4, h5, ite_false] at this ih' ⊢
          omega
        · have h5 : ¬ σ ≤ (n : ℤ) + 1 := by omega
          simp only [h1, h4, h5, ite_false] at this ih' ⊢
          omega
  have klo : ∀ r : ℤ, 0 ≤ r → r < a →
      cLo K (g + r) + (if r < τ then 1 else 0) = cLo K r + cellShift K g τ := by
    intro r h0 h1
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    exact key_lo n h1
  have khi : ∀ r : ℤ, 0 ≤ r → r < a →
      cHi K (g + r) + (if σ ≤ r then 1 else 0) = cHi K r + cellShift K g τ := by
    intro r h0 h1
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    exact key_hi n h1
  have stepLo := hsh.stepLo
  have stepHi := hsh.stepHi
  have ne := hsh.ne
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hsh
  · intro r h0 hr
    have := klo r h0 (by omega)
    simp only [hr, ite_true] at this
    omega
  · intro r hr h1
    have := klo r (by omega) h1
    have : ¬ r < τ := by omega
    simp only [this, ite_false] at *
    omega
  · intro r h0 hr
    have := khi r h0 (by omega)
    have h2 : ¬ σ ≤ r := by omega
    simp only [h2, ite_false] at this
    omega
  · intro r hr h1
    have := khi r (by omega) h1
    simp only [hr, ite_true] at this
    omega
  · omega
  · omega
  · intro r h0 h1
    have := h.height_pos r h0 h1
    rw [height_cLo] at this
    omega
  · intro hσ
    have h1 := h.bitB_rec σ hσ1 hσ
    have h2 := stepHi (g + σ) (by omega) (by omega)
    have h3 := stepHi σ (by omega) (by omega)
    rw [bitB_cHi, bitB_cHi] at h1
    simp only [ite_true] at h1
    omega
  · by_cases hσ : σ < a
    · have h2 := h.height_pos σ (by omega) hσ
      rw [height_cLo] at h2
      have h3 := stepLo σ (by omega) (by omega)
      simp only [le_refl, ite_true] at h2
      omega
    · have hσe : σ = a := by omega
      have h2 := h.bitB_a hσe
      rw [bitB_cHi] at h2
      have h3 := ne (σ - 1) (by omega) (by omega)
      subst hσe
      omega
  · by_cases hτ : 0 < τ
    · have h1 := h.bitA_rec τ hτ h.τ_lt
      rw [bitA_cLo, bitA_cLo] at h1
      simp only [ite_true] at h1
      have h2 := stepLo τ (by omega) (by omega)
      have h3 := ne (g + τ) (by omega) (by omega)
      omega
    · have hτ0' : τ = 0 := by omega
      have h1 := h.bitA_g hτ0'
      have h2 := bitA_cLo K g
      have h3 := ne g (by omega) (by omega)
      subst hτ0'
      simp only [add_zero]
      omega

theorem DiagSet.congr {S : Diagram} {k₀ k₁ k₀' k₁' : ℤ} {lo hi lo' hi' : ℤ → ℤ}
    (h : DiagSet S k₀ k₁ lo hi) (h0 : k₀ = k₀') (h1 : k₁ = k₁') (hl : ∀ k, lo k = lo' k)
    (hh : ∀ k, hi k = hi' k) : DiagSet S k₀' k₁' lo' hi' := by
  subst h0 h1
  intro i k
  rw [h, hl, hh]

/-- **`ge:cell-criterion`.**  A connected skew diagram `K` of span `g + a` satisfying the bit
recursions, the height conditions and the two contact conditions of `CellCriterionData` carries a
full legal ordinary mark of case (a), period `g`, width `a` and contacts `(σ, τ)`, with
displacement `ν = (ν₁, ν₁ + g)`, `ν₁ = λ_g + 1_{τ>0} - λ_0`.  Its lower copy on the content
`m + c` (`0 ≤ c < a`) is `[λ_c, μ_c - 1_{c≥σ}]` and its upper copy on the content `m + g + c` is
`[λ_{g+c} + 1_{c<τ}, μ_{g+c}]`, where `m = minContent K`. -/
theorem cell_criterion (h : CellCriterionData K g a τ σ) :
    ∃ ω : MarkedInner, ω.E = K ∧ ω.IsLegal ∧ ω.W.Nonempty ∧ ω.case = .a ∧ ω.period = g ∧
      (ω.width : ℤ) = a ∧ ω.v = (cellShift K g τ, cellShift K g τ + g) ∧ ω.IsPhases σ τ ∧
      DiagSet ω.W (minContent K) (minContent K + a - 1) (diagLo K)
        (fun k => diagHi K k - if σ ≤ k - minContent K then 1 else 0) ∧
      DiagSet ω.upper (minContent K + g) (minContent K + g + a - 1)
        (fun k => diagLo K k + if k - minContent K - g < τ then 1 else 0) (diagHi K) := by
  obtain ⟨hG, -⟩ := diagSet_normalize h.conn (n := g + a) h.span_eq
  have hs := h.slotGeom
  have hw := h.a_pos
  have hwq := h.a_lt
  set m := minContent K with hm
  set K' := translate (0, -m) K with hK'
  have hG' : DiagSet K' 0 (g + a - 1) (cLo K) (cHi K) := hG
  have hG'' : DiagSet K' 0 (g + a - 1) (cLo K) (cHi K) := hG'
  set ω0 := SlotGeom.mark K' g a σ (cellShift K g τ) (cHi K) with hω0
  have hleg := SlotGeom.mark_isLegal (q := g) (w := a) (τ := τ) (σ := σ) (v₁ := cellShift K g τ)
    (lo := cLo K) (hi := cHi K) (by simpa using hG'') hs
  have hE : (ω0.translate (0, m)).E = K := by
    rw [translate_E]
    change translate (0, m) K' = K
    rw [hK', SkewGluing.translate_translate]
    have : ((0 : ℤ), m) + (0, -m) = 0 := by ext <;> simp
    rw [this, SkewGluing.translate_zero]
  have hper : ω0.period = g := SlotGeom.mark_period
  have hwid : (ω0.width : ℤ) = a := SlotGeom.mark_width hG'' hs
  have e1 : ∀ k, cLo K (k - m) = diagLo K k := fun k => by unfold cLo; rw [← hm, add_sub_cancel]
  have e2 : ∀ k, cHi K (k - m) = diagHi K k := fun k => by unfold cHi; rw [← hm, add_sub_cancel]
  refine ⟨ω0.translate (0, m), hE, isLegal_translate _ hleg, ?_, rfl, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := SlotGeom.mark_nonempty hG'' hs
    exact ⟨x + (0, m), Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  · rw [period_translate]; exact hper
  · rw [width_translate]; exact hwid
  · have hph := SlotGeom.mark_phases hG'' hs
    have hloT : ∀ b, (ω0.translate (0, m)).lo b = cLo K b := fun b => by
      unfold MarkedInner.lo; rw [hE]; rfl
    have hhiT : ∀ b, (ω0.translate (0, m)).hi b = cHi K b := fun b => by
      unfold MarkedInner.hi; rw [hE]; rfl
    have hloO : ∀ b, 0 ≤ b → b ≤ g + a - 1 → ω0.lo b = cLo K b := fun b h1 h2 =>
      SlotGeom.mark_lo hG'' hs h1 h2
    have hhiO : ∀ b, 0 ≤ b → b ≤ g + a - 1 → ω0.hi b = cHi K b := fun b h1 h2 =>
      SlotGeom.mark_hi hG'' hs h1 h2
    have hwz : (ω0.translate (0, m)).widthZ = ω0.widthZ := by
      unfold MarkedInner.widthZ; rw [width_translate]
    have hd : ∀ b, 0 ≤ b → b ≤ a - 1 →
        (ω0.translate (0, m)).dLo b = ω0.dLo b ∧ (ω0.translate (0, m)).dHi b = ω0.dHi b := by
      intro b h1 h2
      have hp : (ω0.translate (0, m)).period = g := by rw [period_translate]; exact hper
      unfold MarkedInner.dLo MarkedInner.dHi
      rw [hp, hper, hloT, hloT, hhiT, hhiT, hloO b h1 (by omega),
        hloO (b + g) (by omega) (by omega), hhiO b h1 (by omega),
        hhiO (b + g) (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    have hwZ : ω0.widthZ = a := hwid
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hph
    refine ⟨p1, ?_, p3, ?_, fun b h1 h2 => ?_, fun b h1 h2 => ?_⟩
    · rw [hwz]; exact p2
    · rw [hwz]; exact p4
    · rw [hwz] at h2
      have := p5 b h1 h2
      unfold MarkedInner.TailLower at this ⊢
      rw [(hd b h1 (by omega)).1, (hd b h1 (by omega)).2]
      exact this
    · rw [hwz] at h2
      have := p6 b h1 h2
      unfold MarkedInner.TailUpper at this ⊢
      rw [(hd b h1 (by omega)).1, (hd b h1 (by omega)).2]
      exact this
  · have := (DiagSet.translate_zero_fst m
      (SlotGeom.diagSet_lowerCopy (σ := σ) hG'' hw hwq))
    refine this.congr (by omega) (by omega) e1 ?_
    intro k
    unfold SlotGeom.hiW
    rw [e2]
  · have := (DiagSet.translate_zero_fst m (SlotGeom.diagSet_upper hG'' hw hwq hs))
    rw [upper_translate]
    refine this.congr (by omega) (by omega) ?_ e2
    intro k
    rw [e1]

/-- **`ge:cell-criterion`, the other ordinary gauge.**  Antitransposing the whole construction
gives the actual transformed mark on `AT(K)`: legal, of case (b), with the same period, width and
contacts. -/
theorem cell_criterion_anti (h : CellCriterionData K g a τ σ) :
    ∃ ω : MarkedInner, ω.E = antitranspose K ∧ ω.IsLegal ∧ ω.W.Nonempty ∧ ω.case = .b ∧
      ω.period = g ∧ (ω.width : ℤ) = a ∧ ω.IsPhases σ τ := by
  obtain ⟨ω, hE, hleg, hW, hc, hper, hwid, -, hph, -, -⟩ := cell_criterion h
  have hn : ω.IsLegalNonempty := ⟨hleg, hW⟩
  refine ⟨ω.anti, by rw [anti_E, hE], isLegal_anti hleg hW, ?_, by rw [anti_case, hc]; rfl, ?_,
    ?_, hn.isPhases_anti hph⟩
  · obtain ⟨x, hx⟩ := hW
    exact ⟨(-x.2, -x.1), Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  · rw [period_anti]; exact hper
  · rw [width_anti]; exact hwid

end Criterion

/-! ### The block formula `ge:eq:ordinary-block`

The completed native row and column words are the indicator words `b`, `c` of the sets `B`, `C`
on `[0, R g)`.  Off the classes `r_s` (row word) and `r_t` (column word) modulo `g`, every class is
full or empty, so the words are `g`-periodic there; `φB`, `φC` are the full-class indicator words
(the exceptional class removed), `x_k = b(k g + r_s)`, `y_k = c(k g + r_t)`, and the height sums
`H(n) = ∑_{i ≤ n} (c(i) - b(i))` satisfy
`H(k g + z) = E(k) + Ψ(z) + 1_{z ≥ r_t} y_k - 1_{z ≥ r_s} x_k` with `Ψ(g - 1) = 0`. -/

/-- The full-class row indicator word: the exceptional class removed. -/
def fullWord (b : ℕ → ℤ) (r : ℕ) (q : ℕ) : ℤ := if q = r then 0 else b q

/-- `Ψ(z) = ∑_{i ≤ z} (φC(i) - φB(i))`. -/
def psiWord (b c : ℕ → ℤ) (rs rt z : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (z + 1), (fullWord c rt i - fullWord b rs i)

/-- `E(k) = ∑_{i < k} (y_i - x_i)`. -/
def exWord (b c : ℕ → ℤ) (g rs rt k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range k, (c (i * g + rt) - b (i * g + rs))

/-- The height sum `H(n) = ∑_{i ≤ n} (c(i) - b(i))`. -/
def hsumWord (b c : ℕ → ℤ) (n : ℕ) : ℤ := ∑ i ∈ Finset.range (n + 1), (c i - b i)

theorem sum_blocks (d : ℕ → ℤ) (g : ℕ) (k : ℕ) :
    ∑ i ∈ Finset.range (k * g), d i =
      ∑ j ∈ Finset.range k, ∑ q ∈ Finset.range g, d (j * g + q) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- **`ge:eq:ordinary-block`.**  Let `b`, `c` be `{0, 1}`-valued on `[0, R g)`, periodic modulo `g`
off the residues `rs` (for `b`) and `rt` (for `c`), with equal totals and nonempty exceptional
classes.  Then `Ψ(g - 1) = 0` and `H(k g + z) = E(k) + Ψ(z) + 1_{z ≥ rt} y_k - 1_{z ≥ rs} x_k`
for `k < R`, `z < g`. -/
theorem ordinary_block_formula {g R : ℕ} (hg : 0 < g) (hR : 0 < R) {b c : ℕ → ℤ} {rs rt : ℕ}
    (hrs : rs < g) (hrt : rt < g)
    (hbit : ∀ i, i < R * g → (b i = 0 ∨ b i = 1) ∧ (c i = 0 ∨ c i = 1))
    (hB : ∀ k q, k < R → q < g → q ≠ rs → b (k * g + q) = b q)
    (hC : ∀ k q, k < R → q < g → q ≠ rt → c (k * g + q) = c q)
    (hcard : ∑ i ∈ Finset.range (R * g), b i = ∑ i ∈ Finset.range (R * g), c i)
    (hx : 1 ≤ ∑ k ∈ Finset.range R, b (k * g + rs))
    (hy : 1 ≤ ∑ k ∈ Finset.range R, c (k * g + rt)) :
    psiWord b c rs rt (g - 1) = 0 ∧
      ∀ k z, k < R → z < g →
        hsumWord b c (k * g + z) = exWord b c g rs rt k + psiWord b c rs rt z +
          (if rt ≤ z then c (k * g + rt) else 0) - (if rs ≤ z then b (k * g + rs) else 0) := by
  have hd : ∀ j q, j < R → q < g →
      c (j * g + q) - b (j * g + q) = (fullWord c rt q - fullWord b rs q) +
        ((if q = rt then c (j * g + rt) else 0) - (if q = rs then b (j * g + rs) else 0)) := by
    intro j q hj hq
    unfold fullWord
    by_cases h1 : q = rt <;> by_cases h2 : q = rs
    · subst h1; subst h2; simp
    · subst h1; simp [h2, hB j q hj hq h2]; ring
    · subst h2; simp [h1, hC j q hj hq h1]; ring
    · simp [h1, h2, hB j q hj hq h2, hC j q hj hq h1]
  have hg1 : g - 1 + 1 = g := Nat.sub_add_cancel hg
  have hblock : ∀ j, j < R → ∑ q ∈ Finset.range g, (c (j * g + q) - b (j * g + q)) =
      psiWord b c rs rt (g - 1) + (c (j * g + rt) - b (j * g + rs)) := by
    intro j hj
    rw [Finset.sum_congr rfl fun q hq => hd j q hj (Finset.mem_range.mp hq)]
    have hs : ∑ x ∈ Finset.range g, ((if x = rt then c (j * g + rt) else 0) -
        (if x = rs then b (j * g + rs) else 0)) = c (j * g + rt) - b (j * g + rs) := by
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp [hrs, hrt]
    rw [Finset.sum_add_distrib, hs]
    unfold psiWord
    rw [hg1]
  have hpsi : psiWord b c rs rt (g - 1) = 0 := by
    have hT : ∑ i ∈ Finset.range (R * g), (c i - b i) = 0 := by
      rw [Finset.sum_sub_distrib]; omega
    rw [sum_blocks (fun i => c i - b i) g R,
      Finset.sum_congr rfl fun j hj => hblock j (Finset.mem_range.mp hj)] at hT
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range] at hT
    have hxle : ∑ k ∈ Finset.range R, b (k * g + rs) ≤ R := by
      have : ∑ k ∈ Finset.range R, b (k * g + rs) ≤ ∑ k ∈ Finset.range R, (1 : ℤ) :=
        Finset.sum_le_sum fun k hk => by
          have := (hbit (k * g + rs) (by
            have := Finset.mem_range.mp hk
            nlinarith)).1
          omega
      simpa using this
    have hyle : ∑ k ∈ Finset.range R, c (k * g + rt) ≤ R := by
      have : ∑ k ∈ Finset.range R, c (k * g + rt) ≤ ∑ k ∈ Finset.range R, (1 : ℤ) :=
        Finset.sum_le_sum fun k hk => by
          have := (hbit (k * g + rt) (by
            have := Finset.mem_range.mp hk
            nlinarith)).2
          omega
      simpa using this
    simp only [nsmul_eq_mul] at hT
    set Ψ := psiWord b c rs rt (g - 1)
    have hRz : (1 : ℤ) ≤ R := by exact_mod_cast hR
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith
    · nlinarith
  refine ⟨hpsi, fun k z hk hz => ?_⟩
  have hT1 : ∑ i ∈ Finset.range (k * g + (z + 1)), (c i - b i) =
      ∑ i ∈ Finset.range (k * g), (c i - b i) +
        ∑ q ∈ Finset.range (z + 1), (c (k * g + q) - b (k * g + q)) :=
    Finset.sum_range_add _ _ _
  have hT2 : ∑ i ∈ Finset.range (k * g), (c i - b i) = exWord b c g rs rt k := by
    rw [sum_blocks (fun i => c i - b i) g k]
    unfold exWord
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hblock j (lt_trans (Finset.mem_range.mp hj) hk), hpsi, zero_add]
  have hT3 : ∑ q ∈ Finset.range (z + 1), (c (k * g + q) - b (k * g + q)) =
      psiWord b c rs rt z + ((if rt ≤ z then c (k * g + rt) else 0) -
        (if rs ≤ z then b (k * g + rs) else 0)) := by
    rw [Finset.sum_congr rfl fun q hq => hd k q hk (by have := Finset.mem_range.mp hq; omega)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hs : ∑ x ∈ Finset.range (z + 1), ((if x = rt then c (k * g + rt) else 0) -
        (if x = rs then b (k * g + rs) else 0)) =
        (if rt ≤ z then c (k * g + rt) else 0) - (if rs ≤ z then b (k * g + rs) else 0) := by
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp only [Finset.mem_range]
      have e1 : rt < z + 1 ↔ rt ≤ z := by omega
      have e2 : rs < z + 1 ↔ rs ≤ z := by omega
      simp only [e1, e2]
    rw [hs]
    unfold psiWord
    rw [Finset.sum_sub_distrib]
  unfold hsumWord
  rw [show k * g + z + 1 = k * g + (z + 1) by ring, hT1, hT2, hT3]
  ring

end SkewGluing
