/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.NonVRemovals

/-!
# Legality of the infinite ordinary-mark family

Formalizes `shields-2026-skew-corner-descent.tex`, «Cofactor transport under composition»
(`sec:transport`, `eq:non-v-family`). The attachments, maximality, and empty hatted
middle are proved from the literal cells for every `k ≥ 3`. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing

/-- Both actual extreme cells lie in their stated marked copies. -/
theorem nonVMark_extremes (k : ℕ) (hk : 3 ≤ k) :
    sw (nonVMark k).E = (0, 0) ∧ ne (nonVMark k).E = (-2, (k : ℤ) - 1) := by
  change sw (nonVDiagram k) = _ ∧ ne (nonVDiagram k) = _
  constructor
  · symm
    apply MarkedInner.eq_sw_of_content (nonVDiagram_isConnectedSkew k hk)
    · simp [mem_nonVDiagram]
    · rw [nonVDiagram_minContent k hk]; rfl
  · symm
    apply MarkedInner.eq_ne_of_content (nonVDiagram_isConnectedSkew k hk)
    · rw [mem_nonVDiagram]
      have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
      omega
    · rw [nonVDiagram_maxContent k hk]
      dsimp [content]
      ring

/-- Both stated attachments are genuinely horizontal at the actual middle endpoints. -/
theorem nonVMark_attachments (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).LowerH ∧ (nonVMark k).UpperH := by
  constructor
  · refine ⟨(0, 1), ?_, ?_, ?_⟩
    · rw [mem_nonVMark_middle k hk]; omega
    · rw [nonVMark_middle_minContent k hk]; rfl
    · simp [nonVMark]
  · refine ⟨(-2, (k : ℤ) - 2), ?_, ?_, ?_⟩
    · rw [mem_nonVMark_middle k hk]; omega
    · rw [nonVMark_middle_maxContent k hk]
      dsimp [content]
      ring
    · rw [nonVMark_upper]
      simp
      omega

/-- The original lower and upper copies supply a genuine nonempty marked inner. -/
theorem nonVMark_isNonemptyMark (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).IsNonemptyMark := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ({((-1 : ℤ), (0 : ℤ)), (0, 0)} : Diagram).Nonempty
    decide
  · change IsConnectedSkew {((-1 : ℤ), (0 : ℤ)), (0, 0)}
    decide
  · intro p hp
    obtain ⟨a, b⟩ := p
    change (a, b) ∈ {(-1, 0), (0, 0)} at hp
    change (a, b) ∈ nonVDiagram k
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hp
    rw [mem_nonVDiagram]
    have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
    omega
  · rw [nonVMark_upper]
    intro p hp
    obtain ⟨a, b⟩ := p
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hp
    change (a, b) ∈ nonVDiagram k
    rw [mem_nonVDiagram]
    have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
    omega
  · rw [(nonVMark_extremes k hk).1]
    simp [nonVMark]
  · rw [(nonVMark_extremes k hk).2, nonVMark_upper]
    simp
  · unfold MarkedInner.AttachmentMatches
    refine ⟨fun _ => nonVMark_attachments k hk, ?_, ?_, ?_⟩
    all_goals intro h; cases h

/-- Adding any cell on the lower copy's two diagonals violates skewness already at that end. -/
theorem nonVMark_isMaximal (k : ℕ) (hk : 3 ≤ k) : (nonVMark k).IsMaximal := by
  intro W' hW hlt hsk hc
  exfalso
  have hWE : W' ⊆ nonVDiagram k := Finset.mem_powerset.mp hW
  obtain ⟨⟨a, b⟩, hz, hnz⟩ := Finset.exists_of_ssubset hlt
  have hzE := hWE hz
  rw [mem_nonVDiagram] at hzE
  have hcz : b - a = 0 ∨ b - a = 1 := by
    have ht := content_mem_contents hz
    rw [hc] at ht
    simpa [nonVMark, contents, content, eq_comm, or_comm] using ht
  change (a, b) ∉ {(-1, 0), (0, 0)} at hnz
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or] at hnz
  have hkZ : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hab : a = 0 ∧ b = 1 := by omega
  have h01 : (0, 1) ∈ W' := by simpa only [hab.1, hab.2] using hz
  have h10 : (-1, 0) ∈ W' := hlt.le (by simp [nonVMark])
  have h11 : (-1, 1) ∈ W' :=
    hsk.mem h10 h01 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have ht := content_mem_contents h11
  rw [hc] at ht
  norm_num [nonVMark, contents, content] at ht

/-- The actual middle has no southeast-neighbor pair. -/
theorem nonVMark_middle_noInterior (k : ℕ) (hk : 3 ≤ k) {x : ℤ × ℤ}
    (hx : x ∈ (nonVMark k).middle) : x + eCell ∉ (nonVMark k).middle := by
  obtain ⟨a, b⟩ := x
  intro hxe
  rw [mem_nonVMark_middle k hk] at hx
  change (a + 1, b + 1) ∈ (nonVMark k).middle at hxe
  rw [mem_nonVMark_middle k hk] at hxe
  omega

/-- Empty hatted middles make condition IV hold at every strip translate. -/
theorem nonVMark_noHatAdjacency (k : ℕ) (hk : 3 ≤ k) :
    (nonVMark k).NoHatAdjacency := by
  intro a _ x hx _ _
  exfalso
  have hx0 := mem_translate.mp hx.1
  have hx1 := mem_translate.mp hx.2
  have he : x + eCell - a • (nonVMark k).v = (x - a • (nonVMark k).v) + eCell := by
    abel
  rw [he] at hx1
  exact nonVMark_middle_noInterior k hk hx0 hx1

/-- The infinite family satisfies all four legal-mark conditions without Hypothesis V. -/
theorem nonVMark_isLegal (k : ℕ) (hk : 3 ≤ k) : (nonVMark k).IsLegal :=
  ⟨⟨nonVDiagram_isConnectedSkew k hk, Or.inr (nonVMark_isNonemptyMark k hk)⟩,
    nonVMark_isMaximal k hk, nonVMark_isNarrow k hk,
    nonVMark_removalsConnected k hk, nonVMark_noHatAdjacency k hk⟩

end SkewCornerDescent
