import SkewGluing.Decoder.Defs
import SkewGluing.Coding
import SkewGluing.OrdinaryFold.Compose
import SkewGluing.AntitransposeMixed

/-!
# The variable slots of a composite read the outer

Formalizes `shields-2026-skew-gluing.tex`, «Reconstructing a chart from its two words»
(`ge:eq:ports`, the variable slots).

For a legal marked inner `ω` of period `f`, width `a` and phases `(s, t)` (the phases of the empty
mark are `(0, 0)`), and a connected outer `A` of span `m`, the composite `A ∘_ω K` has span
`m f + a`, and the two variable slots of every block `j`, `0 ≤ j ≤ m`, read the outer words
`X_A(j)`, `Y_A(j)` through the table: `IsLegal.compose_ports`.  The interior blocks are the
interface formulas of `lem:gluing-coding`; the first and last blocks are its caps together with the
closed caps `X(0) = 0`, `Y(0) = 1`, `X(N) = 1`, `Y(N) = 0`.  Case (b) is read from case (a) by
antitransposition.

Sorry-free.
-/

namespace SkewGluing

namespace MarkedInner

variable {ω : MarkedInner} {A : Diagram}

theorem span_compose_Z (hω : ω.IsLegal) (hA : IsConnectedSkew A) :
    (span (ω.compose A) : ℤ) = (span A : ℤ) * ω.period + ω.widthZ :=
  span_compose hA hω

theorem interior_pos {j m f a r : ℤ} (hf : 0 < f) (_haf : a < f) (hj1 : 1 ≤ j) (hj2 : j < m)
    (hr0 : 0 ≤ r) (hra : r ≤ a) : 1 ≤ j * f + r ∧ j * f + r < m * f + a := by
  constructor <;> nlinarith

theorem span_A_pos (hA : IsConnectedSkew A) : 1 ≤ (span A : ℤ) := span_pos hA

/-- Case (a), nonempty mark. -/
theorem IsLegalNonempty.ports_a (h : ω.IsLegalNonempty) (hA : IsConnectedSkew A)
    (hca : ω.case = .a) {s t : ℤ} (hph : ω.IsPhases s t) :
    ∀ j : ℤ, 0 ≤ j → j ≤ (span A : ℤ) →
      portDecode ω.case s t ω.period (ω.compose A) j = (Xw A j, Yw A j) := by
  intro j hj0 hjm
  have hq := h.width_lt_period
  have hw := h.width_pos
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hca]
  have hz := (ordT_eq_zero_iff hmix).mpr hca
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hN := span_compose_Z h.1 hA
  have hm1 := span_A_pos hA
  have hWlo : ∀ z, 0 ≤ z → z < ω.widthZ → diagLo ω.W (minContent ω.E + z) = ω.lo z := by
    intro z hz0 hz1
    rw [h.diagLo_W hz0 (by omega)]
    have := (ord_offsets h hmix hph hz0 (by omega)).1 hz
    have h3 := this.1
    have h4 := this.2.1
    unfold dLo at h3 h4
    by_cases hc : z < t
    · have := h3 hc; omega
    · have := h4 (by omega); omega
  have hWhi : ∀ z, 0 ≤ z → z < ω.widthZ →
      diagHi ω.W (minContent ω.E + z) = ω.hi z - if s ≤ z then 1 else 0 := by
    intro z hz0 hz1
    rw [h.diagHi_W hz0 (by omega)]
    have := (ord_offsets h hmix hph hz0 (by omega)).1 hz
    have h3 := this.2.2.1
    have h4 := this.2.2.2
    unfold dHi at h3 h4
    by_cases hc : s ≤ z
    · have := h3 hc; simp only [hc, ite_true]; omega
    · have := h4 (by omega); simp only [hc, ite_false]; omega
  obtain ⟨c1, c2, c3, c4⟩ := h.caps_a hA hca hph
  simp only [hca, portDecode, Prod.mk.injEq]
  have hf : 0 < ω.period := by omega
  have hmf : ω.period ≤ (span A : ℤ) * ω.period := by nlinarith
  by_cases j0 : j = 0
  · subst j0
    rw [Xw_zero, Yw_zero]
    simp only [zero_mul, zero_add]
    constructor
    · rw [Xw_of_mem (by omega) (by omega)]; exact c2
    · by_cases ht0 : t = 0
      · subst ht0; exact Yw_zero _
      · rw [Yw_of_mem (by omega) (by omega)]; exact c1 (by omega)
  · by_cases jm : j = (span A : ℤ)
    · subst jm
      rw [Xw_span hm1, Yw_span hm1]
      constructor
      · by_cases hs : s < ω.widthZ
        · rw [Xw_of_mem (by nlinarith) (by nlinarith)]
          have e : (span A : ℤ) * ω.period + s = (span (ω.compose A) : ℤ) - ω.widthZ + s := by omega
          rw [e]; exact c4 hs
        · have e : (span A : ℤ) * ω.period + s = (span (ω.compose A) : ℤ) := by omega
          rw [e]
          exact Xw_span (by nlinarith)
      · rw [Yw_of_mem (by nlinarith) (by nlinarith)]
        have e : (span A : ℤ) * ω.period + t = (span (ω.compose A) : ℤ) - ω.widthZ + t := by omega
        rw [e]; exact c3
    · have hj1 : 1 ≤ j := by omega
      have hj2 : j < (span A : ℤ) := by omega
      rw [Xw_of_mem (P := A) hj1 hj2, Yw_of_mem (P := A) hj1 hj2]
      obtain ⟨p1, p2⟩ := interior_pos (a := ω.widthZ) hf hq hj1 hj2 (r := s) (by omega) (by omega)
      obtain ⟨p3, p4⟩ := interior_pos (a := ω.widthZ) hf hq hj1 hj2 (r := t) (by omega) (by omega)
      rw [Xw_of_mem (by omega) (by omega), Yw_of_mem (by omega) (by omega)]
      have hJ1 : minContent A + 1 ≤ minContent A + j := by omega
      have hmaxA := span_eq_of_isConnectedSkew hA
      have hJ2 : minContent A + j ≤ maxContent A := by omega
      have e1 := h.wordB_slot hA hca hph hWhi hJ1 hJ2
      have e2 := h.wordA_slot hA hca hph hWlo hJ1 hJ2
      have q : minContent A + j - minContent A = j := by ring
      rw [q] at e1 e2
      exact ⟨e1, e2⟩

/-- Case (c), nonempty mark. -/
theorem IsLegalNonempty.ports_c (h : ω.IsLegalNonempty) (hA : IsConnectedSkew A)
    (hcc : ω.case = .c) {s t : ℤ} (hph : ω.IsPhases s t) :
    ∀ j : ℤ, 0 ≤ j → j ≤ (span A : ℤ) →
      portDecode ω.case s t ω.period (ω.compose A) j = (Xw A j, Yw A j) := by
  intro j hj0 hjm
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hN := span_compose_Z h.1 hA
  have hm1 := span_A_pos hA
  obtain ⟨c1, c2, c3, c4, -, -⟩ := h.caps_c hA hcc hph
  simp only [hcc, portDecode, Prod.mk.injEq]
  have hf : 0 < ω.period := by omega
  have hmf : ω.period ≤ (span A : ℤ) * ω.period := by nlinarith
  by_cases j0 : j = 0
  · subst j0
    rw [Xw_zero, Yw_zero]
    simp only [zero_mul, zero_add]
    constructor
    · rw [Xw_of_mem (by omega) (by omega)]; exact c2
    · by_cases ht0 : t = 0
      · subst ht0; rw [Xw_zero]; norm_num
      · rw [Xw_of_mem (by omega) (by omega), c1 (by omega)]; norm_num
  · by_cases jm : j = (span A : ℤ)
    · subst jm
      rw [Xw_span hm1, Yw_span hm1]
      have e2 : (span A : ℤ) * ω.period + t = (span (ω.compose A) : ℤ) - ω.widthZ + t := by omega
      constructor
      · by_cases hs : s < ω.widthZ
        · rw [Xw_of_mem (by nlinarith) (by nlinarith)]
          have e : (span A : ℤ) * ω.period + s = (span (ω.compose A) : ℤ) - ω.widthZ + s := by omega
          rw [e]; exact c4 hs
        · have e : (span A : ℤ) * ω.period + s = (span (ω.compose A) : ℤ) := by omega
          rw [e]
          exact Xw_span (by nlinarith)
      · rw [Xw_of_mem (by nlinarith) (by nlinarith), e2, c3]; norm_num
    · have hj1 : 1 ≤ j := by omega
      have hj2 : j < (span A : ℤ) := by omega
      rw [Xw_of_mem (P := A) hj1 hj2, Yw_of_mem (P := A) hj1 hj2]
      obtain ⟨p1, p2⟩ := interior_pos (a := ω.widthZ) hf hq hj1 hj2 (r := s) (by omega) (by omega)
      obtain ⟨p3, p4⟩ := interior_pos (a := ω.widthZ) hf hq hj1 hj2 (r := t) (by omega) (by omega)
      rw [Xw_of_mem (by omega) (by omega), Xw_of_mem (by omega) (by omega)]
      obtain ⟨e1, e2⟩ := h.interface_c hA hcc hph hj1 hj2
      rw [e1, e2]
      constructor <;> ring

/-- Case (d), nonempty mark. -/
theorem IsLegalNonempty.ports_d (h : ω.IsLegalNonempty) (hA : IsConnectedSkew A)
    (hcd : ω.case = .d) {s t : ℤ} (hph : ω.IsPhases s t) :
    ∀ j : ℤ, 0 ≤ j → j ≤ (span A : ℤ) →
      portDecode ω.case s t ω.period (ω.compose A) j = (Xw A j, Yw A j) := by
  intro j hj0 hjm
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hN := span_compose_Z h.1 hA
  have hm1 := span_A_pos hA
  obtain ⟨c1, c2, c3, c4, -, -⟩ := h.caps_d hA hcd hph
  simp only [hcd, portDecode, Prod.mk.injEq]
  have hf : 0 < ω.period := by omega
  have hmf : ω.period ≤ (span A : ℤ) * ω.period := by nlinarith
  by_cases j0 : j = 0
  · subst j0
    rw [Xw_zero, Yw_zero]
    simp only [zero_mul, zero_add]
    constructor
    · rw [Yw_of_mem (by omega) (by omega), c2]; norm_num
    · by_cases ht0 : t = 0
      · subst ht0; exact Yw_zero _
      · rw [Yw_of_mem (by omega) (by omega)]; exact c1 (by omega)
  · by_cases jm : j = (span A : ℤ)
    · subst jm
      rw [Xw_span hm1, Yw_span hm1]
      constructor
      · by_cases hs : s < ω.widthZ
        · rw [Yw_of_mem (by nlinarith) (by nlinarith)]
          have e : (span A : ℤ) * ω.period + s = (span (ω.compose A) : ℤ) - ω.widthZ + s := by omega
          rw [e, c4 hs]; norm_num
        · have e : (span A : ℤ) * ω.period + s = (span (ω.compose A) : ℤ) := by omega
          rw [e, Yw_span (by nlinarith)]; norm_num
      · rw [Yw_of_mem (by nlinarith) (by nlinarith)]
        have e : (span A : ℤ) * ω.period + t = (span (ω.compose A) : ℤ) - ω.widthZ + t := by omega
        rw [e]; exact c3
    · have hj1 : 1 ≤ j := by omega
      have hj2 : j < (span A : ℤ) := by omega
      rw [Xw_of_mem (P := A) hj1 hj2, Yw_of_mem (P := A) hj1 hj2]
      obtain ⟨p1, p2⟩ := interior_pos (a := ω.widthZ) hf hq hj1 hj2 (r := s) (by omega) (by omega)
      obtain ⟨p3, p4⟩ := interior_pos (a := ω.widthZ) hf hq hj1 hj2 (r := t) (by omega) (by omega)
      rw [Yw_of_mem (by omega) (by omega), Yw_of_mem (by omega) (by omega)]
      obtain ⟨e1, e2⟩ := h.interface_d hA hcd hph hj1 hj2
      rw [e1, e2]
      constructor <;> ring

/-- Case (b), nonempty mark, from case (a) by antitransposition. -/
theorem IsLegalNonempty.ports_b (h : ω.IsLegalNonempty) (hA : IsConnectedSkew A)
    (hcb : ω.case = .b) {s t : ℤ} (hph : ω.IsPhases s t) :
    ∀ j : ℤ, 0 ≤ j → j ≤ (span A : ℤ) →
      portDecode ω.case s t ω.period (ω.compose A) j = (Xw A j, Yw A j) := by
  intro j hj0 hjm
  have hmix : ¬ ω.case.IsMixed := by simp [AttachCase.IsMixed, hcb]
  have hl' := h.anti
  have hca : ω.anti.case = .a := by rw [anti_case, hcb]; rfl
  have key := hl'.ports_a hA hca (h.isPhases_anti hph) j hj0 hjm
  have hAT := antitranspose_compose hmix hA.2.1
  have hC : IsConnectedSkew (ω.anti.compose A) := hl'.1.isConnectedSkew_compose hA
  have hC' : IsConnectedSkew (ω.compose A) := by
    have := isConnectedSkew_antitranspose hC
    rwa [← hAT, antitranspose_antitranspose] at this
  have hN := span_compose_Z h.1 hA
  have hN' := span_compose_Z hl'.1 hA
  have hq := h.width_lt_period
  have hw := h.width_pos
  obtain ⟨hs1, hs2, ht1, ht2, -, -⟩ := id hph
  have hX : ∀ k, 0 ≤ k → k ≤ (span (ω.compose A) : ℤ) →
      1 - Yw (ω.compose A) k = Xw (ω.anti.compose A) k := by
    intro k k0 k1
    rw [← hAT]
    have := Xw_antitranspose hC' k0 k1
    omega
  have hY : ∀ k, 0 ≤ k → k ≤ (span (ω.compose A) : ℤ) →
      1 - Xw (ω.compose A) k = Yw (ω.anti.compose A) k := by
    intro k k0 k1
    rw [← hAT]
    have := Yw_antitranspose hC' k0 k1
    omega
  have hm1 := span_A_pos hA
  have hf : 0 < ω.period := by omega
  have hmf : ω.period ≤ (span A : ℤ) * ω.period := by nlinarith
  have b1 : 0 ≤ j * ω.period + s ∧ j * ω.period + s ≤ (span (ω.compose A) : ℤ) := by
    constructor <;> nlinarith
  have b2 : 0 ≤ j * ω.period + t ∧ j * ω.period + t ≤ (span (ω.compose A) : ℤ) := by
    constructor <;> nlinarith
  simp only [hca, portDecode, Prod.mk.injEq] at key
  simp only [hcb, portDecode, Prod.mk.injEq]
  have p : (ω.anti).period = ω.period := period_anti ω
  rw [p] at key
  rw [hX _ b1.1 b1.2, hY _ b2.1 b2.2]
  exact key

/-- Empty mark. -/
theorem IsLegalEmpty.ports (h : ω.IsLegalEmpty) (hA : IsConnectedSkew A) :
    ∀ j : ℤ, 0 ≤ j → j ≤ (span A : ℤ) →
      portDecode ω.case 0 0 ω.period (ω.compose A) j = (Xw A j, Yw A j) := by
  intro j hj0 hjm
  have hq := h.period_pos
  have hw := h.width_zero
  have hN := span_compose_Z h.1 hA
  have hm1 := span_A_pos hA
  simp only [h.case_a, portDecode, Prod.mk.injEq, add_zero]
  by_cases j0 : j = 0
  · subst j0
    simp only [zero_mul, Xw_zero, Yw_zero]
    exact ⟨trivial, trivial⟩
  · by_cases jm : j = (span A : ℤ)
    · subst jm
      rw [Xw_span hm1, Yw_span hm1]
      have e : (span A : ℤ) * ω.period = (span (ω.compose A) : ℤ) := by omega
      rw [e]
      exact ⟨Xw_span (by nlinarith), Yw_span (by nlinarith)⟩
    · have hj1 : 1 ≤ j := by omega
      have hj2 : j < (span A : ℤ) := by omega
      rw [Xw_of_mem (P := A) hj1 hj2, Yw_of_mem (P := A) hj1 hj2]
      have p1 : 1 ≤ j * ω.period ∧ j * ω.period < (span (ω.compose A) : ℤ) := by
        constructor <;> nlinarith
      rw [Xw_of_mem p1.1 p1.2, Yw_of_mem p1.1 p1.2]
      obtain ⟨e1, e2⟩ := h.joining hA hj1 hj2
      exact ⟨e2, e1⟩

/-- **`ge:eq:ports`.**  The two variable slots of every block `j`, `0 ≤ j ≤ m`, of the composite of
a connected outer `A` of span `m` with a legal marked inner read the outer words `X_A(j)`,
`Y_A(j)`. -/
theorem IsLegal.compose_ports (hω : ω.IsLegal) {s t : ℤ} (hph : ω.HasPhases s t)
    (hA : IsConnectedSkew A) :
    ∀ j : ℤ, 0 ≤ j → j ≤ (span A : ℤ) →
      portDecode ω.case s t ω.period (ω.compose A) j = (Xw A j, Yw A j) := by
  rcases hph with ⟨hW, rfl, rfl⟩ | ⟨hW, hp⟩
  · exact IsLegalEmpty.ports ⟨hω, hW⟩ hA
  · have h : ω.IsLegalNonempty := ⟨hω, hW⟩
    cases hc : ω.case
    · exact hc ▸ h.ports_a hA hc hp
    · exact hc ▸ h.ports_b hA hc hp
    · exact hc ▸ h.ports_c hA hc hp
    · exact hc ▸ h.ports_d hA hc hp

end MarkedInner

end SkewGluing
