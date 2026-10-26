/- TODO-COPIED: adapted from
`skew-factor-gluing/lean/SkewGluing/Aligned/CaseD/Legal0.lean`. -/
import GluingCore.Aligned.CaseD.Compl

/-!
# Aligned marks, case (d): the lower mark is a nonempty mark with the right ends

Formalizes `shields-2026-skew-factor-gluing.tex`, «Equal and divisible periods»
(`lem:gluing-aligned`).

For `alD_Data V a θ`, the candidate mark `alD_mark V a θ cs` has copies `Z`, `Z + z` inside `V`,
`sw V ∈ Z`, `ne V ∈ Z + z`, its width is `b = N_V - a`, its period is `a`, and it satisfies
conditions I, II and IV of legality (IV is the content-distance argument: two cells of the middle
on one diagonal lie on a diagonal in `[b + 1, a - 2]`, while marked contents are `≡ [0, b - 1]`
modulo `a`).

Sorry-free.
-/

namespace GluingCore

section Legal0

variable {V : Diagram} {a θ : ℤ} {cs : AttachCase}

theorem alD_Z_nonempty (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    (alD_Z V a θ).Nonempty := (alD_Z_connected hV hD).2.1

theorem alD_Z_content (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {x : ℤ × ℤ}
    (hx : x ∈ alD_Z V a θ) :
    minContent V ≤ content x ∧ content x ≤ minContent V + ((span V : ℤ) - a - 1) := by
  obtain ⟨r, c⟩ := x
  have h2 : (r, c) = (r, r + (minContent V + (c - r - minContent V))) := by
    ext <;> simp
  rw [h2, alD_mem_Z hV hD.ha.le] at hx
  simp only [content]
  omega

theorem alD_minContent_Z (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    minContent (alD_Z V a θ) = minContent V := by
  have hZ := alD_Z_connected hV hD
  have hb := hD.hb
  have z := alD_zrows hV hD (j := 0) le_rfl hb
  have hmem : (alD_zl V a θ 0, alD_zl V a θ 0 + (minContent V + 0)) ∈ alD_Z V a θ := by
    rw [alD_mem_Z hV hD.ha.le]
    have := hD.ha
    omega
  apply minContent_eq_of (k := minContent V)
  · have := content_mem_contents hmem
    simpa [content] using this
  · intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact (alD_Z_content hV hD hx).1

theorem alD_maxContent_Z (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    maxContent (alD_Z V a θ) = minContent V + ((span V : ℤ) - a - 1) := by
  have hb := hD.hb
  have ha := hD.ha
  have z := alD_zrows hV hD (j := (span V : ℤ) - a - 1) (by omega) (by omega)
  have hmem : (alD_zl V a θ ((span V : ℤ) - a - 1),
      alD_zl V a θ ((span V : ℤ) - a - 1) + (minContent V + ((span V : ℤ) - a - 1))) ∈
      alD_Z V a θ := by
    rw [alD_mem_Z hV ha.le]
    omega
  apply maxContent_eq_of (k := minContent V + ((span V : ℤ) - a - 1))
  · have := content_mem_contents hmem
    simpa [content] using this
  · intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact (alD_Z_content hV hD hx).2

theorem alD_width (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    ((alD_mark V a θ cs).width : ℤ) = (span V : ℤ) - a := by
  have hZ := alD_Z_connected hV hD
  have h := span_eq_of_isConnectedSkew hZ
  have e1 := alD_minContent_Z hV hD
  have e2 := alD_maxContent_Z hV hD
  unfold MarkedInner.width
  change (span (alD_Z V a θ) : ℤ) = _
  omega

theorem alD_period (cs : AttachCase) : (alD_mark V a θ cs).period = a := by
  unfold MarkedInner.period
  change content (alD_z a θ) = a
  simp [content, alD_z]

theorem alD_sw_mem (hV : IsConnectedSkew V) (hD : alD_Data V a θ) : sw V ∈ alD_Z V a θ := by
  have hb := hD.hb
  have ha := hD.ha
  have z := alD_zrows hV hD (j := 0) le_rfl hb
  have e0 := alD_e_first hV hD
  have h0 := alD_end0 hV
  have hsw : sw V = (alD_L V 0, alD_L V 0 + (minContent V + 0)) := by
    unfold sw alD_L
    ext <;> simp
  rw [hsw, alD_mem_Z hV ha.le]
  have := z.2.2.2.2.2.1 e0
  omega

theorem alD_mem_upper_of (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {j : ℤ}
    (hj0 : 0 ≤ j) (hj1 : j < (span V : ℤ) - a) (hge : 0 ≤ alD_e V a j) {r : ℤ}
    (hr : alD_L V (j + a) ≤ r ∧ r ≤ alD_H V (j + a)) :
    (r, r + (minContent V + (j + a))) ∈ (alD_mark V a θ cs).upper := by
  have ha := hD.ha
  rw [alD_mem_upper hV ha.le]
  have z := alD_zrows hV hD hj0 hj1
  have e : j + a - a = j := by ring
  rw [e]
  have := z.2.2.2.2.2.2 hge
  refine ⟨by omega, by omega, ?_, ?_⟩ <;> omega

theorem alD_ne_mem (hV : IsConnectedSkew V) (hD : alD_Data V a θ) :
    ne V ∈ (alD_mark V a θ cs).upper := by
  have hb := hD.hb
  have ha := hD.ha
  have hsp := span_eq_of_isConnectedSkew hV
  have e0 := alD_e_last hV hD
  have h0 := alD_endN hV
  have hne : ne V = (alD_L V ((span V : ℤ) - 1),
      alD_L V ((span V : ℤ) - 1) + (minContent V + ((span V : ℤ) - a - 1 + a))) := by
    unfold ne alD_L
    have : minContent V + ((span V : ℤ) - a - 1 + a) = maxContent V := by omega
    rw [this]
    have e : (span V : ℤ) - 1 = maxContent V - minContent V := by omega
    rw [e]
    ext <;> simp
  rw [hne]
  apply alD_mem_upper_of hV hD (by omega) (by omega) e0
  have e : (span V : ℤ) - a - 1 + a = (span V : ℤ) - 1 := by ring
  rw [e]
  omega

theorem alD_upper_sub (hV : IsConnectedSkew V) (hD : alD_Data V a θ) {x : ℤ × ℤ}
    (hx : x ∈ (alD_mark V a θ cs).upper) : x ∈ V := by
  obtain ⟨r, c⟩ := x
  have h2 : (r, c) = (r, r + (minContent V + (c - r - minContent V))) := by
    ext <;> simp
  rw [h2, alD_mem_upper hV hD.ha.le] at hx
  rw [h2, alD_mem_V hV]
  have hb := hD.hb
  have ha := hD.ha
  have z := alD_zrows hV hD (j := c - r - minContent V - a) (by omega) (by omega)
  have e : c - r - minContent V - a + a = c - r - minContent V := by ring
  rw [e] at z
  omega

end Legal0

end GluingCore
