/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewGluing.DisconnectedTableau

/-!
# Skew functions of finite separated unions

Formalizes the finite component-product step in `shields-2026-skew-corner-descent.tex`,
«Marked inners and finite end caps» (`lem:row-amalgamation`).  Separation is checked on
actual cells, and skewness of a subunion is derived from the full skew diagram.

Sorry-free.
-/

namespace SkewGluing

/-- An edge path starting inside a diagram ends inside it. -/
theorem DiagReach.mem_right {D : Diagram} {x y : ℤ × ℤ} (hr : DiagReach D x y)
    (hx : x ∈ D) : y ∈ D := by
  induction hr with
  | refl => exact hx
  | tail _ hstep _ => exact hstep.2.1

/-- A nonadjacent subunion of a skew diagram is itself skew. -/
theorem IsSkew.union_left_of_noAdj {A B : Diagram} (hu : IsSkew (A ∪ B))
    (hadj : ∀ a ∈ A, ∀ b ∈ B, ¬ CellAdj a b) : IsSkew A := by
  intro x hx y hy h1 h2 i hi j hj
  have hxU := Finset.mem_union_left B hx
  have hyU := Finset.mem_union_left B hy
  have hzU := hu x hxU y hyU h1 h2 i hi j hj
  have hr := hu.reach_of_le hxU hzU (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1
  exact (diagReach_union_left hadj hx hr).mem_right hx

/-- Skew functions multiply over any finite cell-disjoint, pairwise nonadjacent skew union. -/
theorem cellSchur_biUnion {ι : Type*} (s : Finset ι) (D : ι → Diagram)
    (hskew : ∀ i, IsSkew (D i)) (hu : IsSkew (s.biUnion D))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (D i) (D j))
    (hadj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ D i, ∀ y ∈ D j, ¬ CellAdj x y) :
    cellSchur (s.biUnion D) hu = ∏ i ∈ s, cellSchur (D i) (hskew i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cellSchur, edgeComponents]
  | @insert i s hi ih =>
    have had : ∀ x ∈ D i, ∀ y ∈ s.biUnion D, ¬ CellAdj x y := by
      intro x hx y hy
      obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.mp hy
      exact hadj i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (by intro hh; subst hh; exact hi hj) x hx y hyj
    have hd : Disjoint (D i) (s.biUnion D) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.mp hy
      have hij : i ≠ j := by intro hh; subst hh; exact hi hj
      exact Finset.disjoint_left.mp
        (hdisj i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) hij) hx hyj
    have hu' : IsSkew (D i ∪ s.biUnion D) := by
      simpa only [Finset.biUnion_insert] using hu
    have hs : IsSkew (s.biUnion D) :=
      (show IsSkew (s.biUnion D ∪ D i) by rwa [Finset.union_comm]).union_left_of_noAdj
        (fun x hx y hy ha => had y hy x hx ha.symm')
    have hds : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Disjoint (D a) (D b) :=
      fun a ha b hb => hdisj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb)
    have has : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
        ∀ x ∈ D a, ∀ y ∈ D b, ¬ CellAdj x y :=
      fun a ha b hb => hadj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb)
    have heq := cellSchur_union (hskew i) hs hu' hd had
    simpa only [Finset.biUnion_insert, Finset.prod_insert hi] using
      heq.trans (congrArg (fun p => cellSchur (D i) (hskew i) * p) (ih hs hds has))

end SkewGluing
