/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SuperthresholdClass

/-!
# Complete class transport below the boundary

Formalizes the class-transport clause of `lem:subthreshold-transport`
and `thm:sharp-inflation` in `shields-2026-skew-class-inflation.tex`.
The full beta grids bound every negative entry, not just a selected
subdiagonal.  The arbitrary-mate inverse supplies the same bound for
every member of the original class.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- Rotation transposes and reverses the full matrix of signed beta differences. -/
theorem noOpening_rotate {n : ℕ} (P : Profile n) (t : ℕ) (hP : NoOpening t P) :
    NoOpening t P.rotate := by
  intro i j hij
  have he : P.rotate.xi i - P.rotate.zeta j = P.xi j.rev - P.zeta i.rev := by
    rw [Gluing.Profile.xi_rotate, Gluing.Profile.zeta_rotate]
    ring
  rw [he] at hij ⊢
  exact hP _ _ hij

namespace ThinParameters

variable (B : ThinParameters)

/-- All four residue pairs in the complete beta grids have the same negative-depth floor. -/
theorem grid_negative_depth (u v : ℕ) (r s : ℤ)
    (hr : r = 0 ∨ r = B.b) (hs : s = 0 ∨ s = (B.b : ℤ) - B.c)
    (hn : r + u * B.boundary.q - (s + v * B.boundary.q) < 0) :
    r + u * B.boundary.q - (s + v * B.boundary.q) ≤ -(B.boundary.p : ℤ) := by
  have hca := B.c_lt_a
  have hab := B.a_lt_b
  have hc := B.c_pos
  have hq := B.boundary_q_eq
  have hp : (B.boundary.p : ℤ) = (B.a : ℤ) - B.c := by
    dsimp [boundary, BoundaryParameters.ofThin]
    omega
  have hqpos : 0 ≤ (B.boundary.q : ℤ) := by omega
  have hrlo : 0 ≤ r := by rcases hr with rfl | rfl <;> omega
  have hrhi : r ≤ B.b := by rcases hr with rfl | rfl <;> omega
  have hslo : 0 ≤ s := by rcases hs with rfl | rfl <;> omega
  have hshi : s ≤ (B.b : ℤ) - B.c := by rcases hs with rfl | rfl <;> omega
  rcases lt_trichotomy u v with huv | huv | huv
  · have hm := mul_le_mul_of_nonneg_right
      (show (u : ℤ) + 1 ≤ v by omega) hqpos
    nlinarith
  · subst v
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;> omega
  · have hm := mul_le_mul_of_nonneg_right
      (show (v : ℤ) + 1 ≤ u by omega) hqpos
    nlinarith

/-- The actual complete beta lists give a uniform bound on every negative matrix index. -/
theorem diagram_negative_depth {M : ℕ} (α : Composition M) (hM : 0 < M) :
    ∀ i j, (B.diagram α hM).2.xi i - (B.diagram α hM).2.zeta j < 0 →
      (B.diagram α hM).2.xi i - (B.diagram α hM).2.zeta j ≤ -(B.boundary.p : ℤ) := by
  intro i j hij
  have hi : (B.diagram α hM).2.xi i ∈ (B.diagram α hM).2.toBetaDiagram.rowSet :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hj : (B.diagram α hM).2.zeta j ∈ (B.diagram α hM).2.toBetaDiagram.colSet :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  rw [B.diagram_rowSet] at hi
  rw [B.diagram_colSet] at hj
  have hrow : ∃ u : ℕ, ∃ r : ℤ, (r = 0 ∨ r = B.b) ∧
      (B.diagram α hM).2.xi i = r + u * B.boundary.q := by
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hi
      exact ⟨u, B.b, Or.inr rfl, hu.symm⟩
    · obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hi
      exact ⟨u, 0, Or.inl rfl, by simpa only [zero_add] using hu.symm⟩
  have hcol : ∃ v : ℕ, ∃ s : ℤ, (s = 0 ∨ s = (B.b : ℤ) - B.c) ∧
      (B.diagram α hM).2.zeta j = s + v * B.boundary.q := by
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hj
      exact ⟨v, (B.b : ℤ) - B.c, Or.inr rfl, hv.symm⟩
    · obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hj
      exact ⟨v, 0, Or.inl rfl, by simpa only [zero_add] using hv.symm⟩
  obtain ⟨u, r, hr, hx⟩ := hrow
  obtain ⟨v, s, hs, hy⟩ := hcol
  rw [hx, hy] at hij ⊢
  exact B.grid_negative_depth u v r s hr hs hij

/-- No actual negative entry opens before the exact boundary parameter. -/
theorem diagram_noOpening {M : ℕ} (α : Composition M) (hM : 0 < M)
    (t : ℕ) (ht : t < B.boundary.p) : NoOpening t (B.diagram α hM).2 :=
  noOpening_of_depth _ ht (B.diagram_negative_depth α hM)

/-- Below the boundary, every original connected mate survives and no new mate escapes lowering. -/
theorem subthreshold_full_class {M : ℕ} (α : Composition M) (hM : 0 < M)
    (t : ℕ) (ht : t < B.boundary.p) :
    (ConnectedProfile.inflate t (B.diagram α hM)).schurClass =
      ConnectedProfile.inflate t '' (B.diagram α hM).schurClass := by
  apply ConnectedProfile.class_transport_of_noOpening
  rintro ⟨k, Q⟩ hQ
  have he : Q.toBetaDiagram.schur = (B.diagram α hM).2.toBetaDiagram.schur := by
    change profileSchur Q = profileSchur (B.diagram α hM).2 at hQ
    simpa only [profileSchur_eq_inherited, Gluing.Profile.toBetaDiagram_schur] using hQ
  obtain ⟨β, hβ | hβ⟩ := B.arbitrary_mate_geometry α hM Q he
  · have hh := congrArg
      (fun D : ConnectedProfile => NoOpening t D.2) hβ
    exact hh.mpr (B.diagram_noOpening β hM t ht)
  · have hh := congrArg
      (fun D : ConnectedProfile => NoOpening t D.2) hβ
    exact hh.mpr (noOpening_rotate _ t (B.diagram_noOpening β hM t ht))

end ThinParameters
end SkewClassInflation
