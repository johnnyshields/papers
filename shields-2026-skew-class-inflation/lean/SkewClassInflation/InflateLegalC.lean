/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.InflateLegalD

/-!
# Inflation of a legal case-(c) mark

Supports `lem:inflate-chart` in `shields-2026-skew-class-inflation.tex`, case (c),
\(0<w<q-1\).  The rotation of the inflated mark is a translate of the inflation of the
rotated mark, so case (c) follows from case (d).  Sorry-free.
-/

namespace SkewClassInflation

open SkewGluing MarkedInner

variable {ω : MarkedInner}

theorem isPhases_rotate (h : ω.IsLegalNonempty) {s t : ℤ} (hp : ω.IsPhases s t) :
    ω.rotate.IsPhases (ω.widthZ - t) (ω.widthZ - s) := by
  obtain ⟨hs1, hs2, ht1, ht2, hS, hT⟩ := hp
  have hw := h.width_pos
  rw [IsPhases, widthZ_rotate]
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩
  · intro a h0 h1
    have e := h.dLo_rotate (ω.widthZ - 1 - a)
    have e2 := h.dHi_rotate (ω.widthZ - 1 - a)
    rw [show ω.widthZ - 1 - (ω.widthZ - 1 - a) = a by ring] at e e2
    have := hT (ω.widthZ - 1 - a) (by omega) (by omega)
    unfold TailLower at ⊢
    unfold TailUpper at this
    rw [e, e2]
    omega
  · intro a h0 h1
    have e := h.dLo_rotate (ω.widthZ - 1 - a)
    have e2 := h.dHi_rotate (ω.widthZ - 1 - a)
    rw [show ω.widthZ - 1 - (ω.widthZ - 1 - a) = a by ring] at e e2
    have := hS (ω.widthZ - 1 - a) (by omega) (by omega)
    unfold TailLower at this
    unfold TailUpper at ⊢
    rw [e, e2]
    omega

theorem rotate_inflateCells (D : Diagram) :
    rotate (inflateCells D) = translate (0, -1) (inflateCells (rotate D)) := by
  ext ⟨a, b⟩
  simp only [inflateCells, mem_rotate, mem_translate, Finset.mem_union, Prod.neg_mk,
    Prod.mk_sub_mk, sub_zero, sub_neg_eq_add]
  have e2 : (-a, -(b + 1)) = (-a, -b - 1) := by ext <;> simp <;> ring
  have e3 : (-a, -(b + 1 - 1)) = (-a, -b) := by ext <;> simp
  rw [e2, e3]
  tauto

theorem rotate_inflateMarked (ω : MarkedInner) :
    ω.rotate.rotate = ω := rotate_rotate ω

theorem rotate_inflateMarked_eq (ω : MarkedInner) :
    (inflateMarked ω).rotate = (inflateMarked ω.rotate).translate (0, -1) := by
  refine MarkedInner.mk.injEq .. |>.mpr ⟨?_, ?_, rfl, rfl⟩
  · exact rotate_inflateCells ω.E
  · change SkewGluing.rotate (inflateMarked ω).upper = _
    rw [upper_inflateMarked, rotate_inflateCells]
    rfl

/-- **Inflation of a legal case-(c) mark.**  If the two private pinches hold and
\(w+1<q\), the inflated mark is a legal case-(c) mark of the same period and of width
\(w+1\), with the middle phases \((\sigma+1,\tau+1)\). -/
theorem inflate_isLegal_c (h : ω.IsLegalNonempty) (hc : ω.case = .c) {s t : ℤ}
    (hp : ω.IsPhases s t) (hw1 : ω.widthZ + 1 < ω.period)
    (h1 : ω.lo (ω.widthZ + 1) = ω.lo ω.widthZ)
    (h2 : ω.hi (ω.period - 2) = ω.hi (ω.period - 1)) :
    (inflateMarked ω).IsLegal ∧ (inflateMarked ω).IsPhases (s + 1) (t + 1) ∧
      (inflateMarked ω).widthZ = ω.widthZ + 1 ∧ (inflateMarked ω).period = ω.period ∧
      (inflateMarked ω).case = .c := by
  have hr := h.rotate
  have hcd : ω.rotate.case = .d := by
    show ω.case.rotate = .d
    rw [hc]; rfl
  have hpr := isPhases_rotate h hp
  have hw1' : ω.rotate.widthZ + 1 < ω.rotate.period := by
    rw [widthZ_rotate, period_rotate]; exact hw1
  have h1' : ω.rotate.lo (ω.rotate.widthZ + 1) = ω.rotate.lo ω.rotate.widthZ := by
    rw [widthZ_rotate, h.lo_rotate, h.lo_rotate,
      show ω.period + ω.widthZ - 1 - (ω.widthZ + 1) = ω.period - 2 by ring,
      show ω.period + ω.widthZ - 1 - ω.widthZ = ω.period - 1 by ring, h2]
  have h2' : ω.rotate.hi (ω.rotate.period - 2) = ω.rotate.hi (ω.rotate.period - 1) := by
    rw [period_rotate, h.hi_rotate, h.hi_rotate,
      show ω.period + ω.widthZ - 1 - (ω.period - 2) = ω.widthZ + 1 by ring,
      show ω.period + ω.widthZ - 1 - (ω.period - 1) = ω.widthZ by ring, h1]
  obtain ⟨leg, ph, wd, -, -⟩ := inflate_isLegal_d hr hcd hpr hw1' h1' h2'
  rw [widthZ_rotate] at wd
  have hne' : (inflateMarked ω.rotate).IsLegalNonempty :=
    ⟨leg, inflateMarked_W_nonempty hr.2⟩
  have heq := rotate_inflateMarked_eq ω
  have legr : (inflateMarked ω).rotate.IsLegal := by
    rw [heq]; exact isLegal_translate _ leg
  have hleg : (inflateMarked ω).IsLegal := isLegal_rotate_iff.mp legr
  have hne : (inflateMarked ω).IsLegalNonempty := ⟨hleg, inflateMarked_W_nonempty h.2⟩
  have phr : (inflateMarked ω).rotate.IsPhases (ω.widthZ - t) (ω.widthZ - s) := by
    rw [heq, isPhases_translate_iff hne']
    exact ph
  have wd' : (inflateMarked ω).widthZ = ω.widthZ + 1 := by
    have a2 : ((inflateMarked ω.rotate).translate (0, -1)).widthZ =
        (inflateMarked ω.rotate).widthZ := by
      unfold MarkedInner.widthZ; rw [width_translate]
    rw [← widthZ_rotate (inflateMarked ω), heq, a2, wd]
  refine ⟨hleg, ?_, wd', rfl, hc⟩
  have := isPhases_rotate hne.rotate (s := ω.widthZ - t) (t := ω.widthZ - s) phr
  rw [MarkedInner.rotate_rotate, widthZ_rotate, wd'] at this
  have e1 : ω.widthZ + 1 - (ω.widthZ - s) = s + 1 := by ring
  have e2 : ω.widthZ + 1 - (ω.widthZ - t) = t + 1 := by ring
  rw [e1, e2] at this
  exact this

end SkewClassInflation
