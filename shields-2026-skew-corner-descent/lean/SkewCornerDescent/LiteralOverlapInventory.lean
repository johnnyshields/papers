/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.InteriorWindowPeriod
import SkewCornerDescent.OverlapSchurProduct
import SkewGluing.InteriorBounds
import SkewGluing.PolynomialSupport

/-!
# Complete literal overlap corner inventories

Formalizes `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`). Equal complete end windows preserve every southeast
pair in the actual two-copy overlap union. No independently matched component inventory is
substituted for the cells.
-/

namespace SkewCornerDescent

open SkewGluing

/-- Complete matching content windows prevent a southeast pair from crossing between copies. -/
theorem literalOverlap_interior (D : Diagram) (q w : ℤ) (v : ℤ × ℤ)
    (hv : content v = q - w)
    (hbound : ∀ x ∈ D, 0 ≤ content x ∧ content x < q)
    (hwindow : D.filter (fun x => q - w ≤ content x ∧ content x < q) =
      translate v (D.filter fun x => 0 ≤ content x ∧ content x < w)) :
    diagramInterior (D ∪ translate v D) =
      diagramInterior D ∪ translate v (diagramInterior D) := by
  have hc (x : ℤ × ℤ) : content (x + eCell) = content x := by
    simp only [content, eCell, Prod.fst_add, Prod.snd_add]
    omega
  have ht (x : ℤ × ℤ) : content (x - v) = content x - (q - w) := by
    simp only [content, Prod.fst_sub, Prod.snd_sub] at hv ⊢
    omega
  have high_copy {x : ℤ × ℤ} (hx : x ∈ D)
      (hh : q - w ≤ content x ∧ content x < q) : x ∈ translate v D := by
    have hx' : x ∈ translate v (D.filter fun x => 0 ≤ content x ∧ content x < w) := by
      rw [← hwindow]
      exact Finset.mem_filter.mpr ⟨hx, hh⟩
    exact mem_translate.mpr (Finset.mem_filter.mp (mem_translate.mp hx')).1
  ext x
  rw [← interior_translate D v]
  simp only [diagramInterior, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hxe⟩
    rcases hx with hx | hx <;> rcases hxe with hxe | hxe
    · exact Or.inl ⟨hx, hxe⟩
    · have hb := hbound _ (mem_translate.mp hxe)
      rw [ht, hc] at hb
      have hx' := high_copy hx (by have hb' := hbound x hx; omega)
      exact Or.inr ⟨hx', hxe⟩
    · have hb := hbound _ (mem_translate.mp hx)
      rw [ht] at hb
      have hxe' := high_copy hxe (by
        have hb' := hbound _ hxe
        have hcx := hc x
        omega)
      exact Or.inr ⟨hx, hxe'⟩
    · exact Or.inr ⟨hx, hxe⟩
  · rintro (⟨hx, hxe⟩ | ⟨hx, hxe⟩)
    · exact ⟨Or.inl hx, Or.inl hxe⟩
    · exact ⟨Or.inr hx, Or.inr hxe⟩

/-- The shared actual interior is exactly the translated complete first-window interior. -/
theorem literalOverlap_interior_intersection (D : Diagram) (q w : ℤ) (v : ℤ × ℤ)
    (hv : content v = q - w)
    (hbound : ∀ x ∈ D, 0 ≤ content x ∧ content x < q)
    (hwindow : D.filter (fun x => q - w ≤ content x ∧ content x < q) =
      translate v (D.filter fun x => 0 ≤ content x ∧ content x < w)) :
    diagramInterior D ∩ translate v (diagramInterior D) =
      translate v (diagramInterior (D.filter fun x => 0 ≤ content x ∧ content x < w)) := by
  have hw := congrArg diagramInterior hwindow
  rw [interior_content_filter D (fun k => q - w ≤ k ∧ k < q), interior_translate] at hw
  rw [← hw]
  ext x
  simp only [Finset.mem_inter, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hxv⟩
    have hb := hbound x (Finset.mem_filter.mp hx).1
    have hbv := hbound (x - v) (Finset.mem_filter.mp (mem_translate.mp hxv)).1
    have ht : content (x - v) = content x - (q - w) := by
      simp only [content, Prod.fst_sub, Prod.snd_sub] at hv ⊢
      omega
    rw [ht] at hbv
    exact ⟨hx, by omega⟩
  · rintro ⟨hx, hh⟩
    have ht : x ∈ translate v
        (diagramInterior (D.filter fun x => 0 ≤ content x ∧ content x < w)) := by
      rw [← hw]
      exact Finset.mem_filter.mpr ⟨hx, hh⟩
    have hz := mem_translate.mp ht
    rw [interior_content_filter D (fun k => 0 ≤ k ∧ k < w)] at hz
    exact ⟨hx, mem_translate.mpr (Finset.mem_filter.mp hz).1⟩

/-- The exclusive original interior lies strictly below the translated interior, with a
missing content diagonal between them. The separation is derived from the complete window. -/
theorem literalOverlap_interior_separated (D : Diagram) (hD : IsConnectedSkew D)
    (q w : ℤ) (v : ℤ × ℤ) (hmin : minContent D = 0) (hv : content v = q - w)
    (hbound : ∀ x ∈ D, 0 ≤ content x ∧ content x < q)
    (hwindow : D.filter (fun x => q - w ≤ content x ∧ content x < q) =
      translate v (D.filter fun x => 0 ≤ content x ∧ content x < w)) :
    ∀ x ∈ diagramInterior D \ translate v (diagramInterior D),
      ∀ y ∈ translate v (diagramInterior D), ¬ CellAdj x y := by
  intro x hx y hy ha
  have hxD := (Finset.mem_sdiff.mp hx).1
  have hxnot := (Finset.mem_sdiff.mp hx).2
  have hxB := hbound x (Finset.mem_filter.mp hxD).1
  have hlow : content x < q - w := by
    by_contra hn
    have hxH : x ∈ (diagramInterior D).filter
        (fun x => q - w ≤ content x ∧ content x < q) :=
      Finset.mem_filter.mpr ⟨hxD, by omega⟩
    have hw := congrArg diagramInterior hwindow
    rw [interior_content_filter D (fun k => q - w ≤ k ∧ k < q), interior_translate] at hw
    rw [hw] at hxH
    have hz := mem_translate.mp hxH
    rw [interior_content_filter D (fun k => 0 ≤ k ∧ k < w)] at hz
    exact hxnot (mem_translate.mpr (Finset.mem_filter.mp hz).1)
  have hyB := interior_content_strict hD (mem_translate.mp hy)
  rw [hmin] at hyB
  have ht : content (y - v) = content y - (q - w) := by
    simp only [content, Prod.fst_sub, Prod.snd_sub] at hv ⊢
    omega
  rw [ht] at hyB
  have ha' := content_adj ha
  omega

/-- The actual two-copy overlap corner product equals the original square. The complete literal
window supplies the shared components; their function and multiplicity are not extra inputs. -/
theorem literalOverlap_corner_product (D W : Diagram) (hD : IsConnectedSkew D)
    (hW : IsSkew W) (q w : ℤ) (v : ℤ × ℤ)
    (hmin : minContent D = 0) (hv : content v = q - w)
    (hbound : ∀ x ∈ D, 0 ≤ content x ∧ content x < q)
    (hwindow : D.filter (fun x => q - w ≤ content x ∧ content x < q) =
      translate v (D.filter fun x => 0 ≤ content x ∧ content x < w))
    (hWcells : W = D.filter fun x => 0 ≤ content x ∧ content x < w)
    (hU : IsSkew (D ∪ translate v D)) :
    cellSchur (diagramInterior (D ∪ translate v D)) hU.interior *
        cellSchur (diagramInterior W) hW.interior =
      cellSchur (diagramInterior D) hD.1.interior ^ 2 := by
  have he := literalOverlap_interior D q w v hv hbound hwindow
  have hs : IsSkew (diagramInterior D ∪ translate v (diagramInterior D)) := by
    rw [← he]
    exact hU.interior
  obtain ⟨hI, hp⟩ := cellSchur_complete_overlap (diagramInterior D)
    (translate v (diagramInterior D)) hD.1.interior
    (isSkew_translate v hD.1.interior) hs
    (literalOverlap_interior_separated D hD q w v hmin hv hbound hwindow)
  have hi : diagramInterior D ∩ translate v (diagramInterior D) =
      translate v (diagramInterior W) := by
    rw [literalOverlap_interior_intersection D q w v hv hbound hwindow, ← hWcells]
  have hIv := cellSchur_congr hi hI (isSkew_translate v hW.interior)
  rw [SkewGluing.cellSchur_translate (diagramInterior W) hW.interior v] at hIv
  have hUv := cellSchur_congr he hU.interior hs
  rw [hIv, ← hUv, SkewGluing.cellSchur_translate (diagramInterior D) hD.1.interior v] at hp
  simpa only [pow_two] using hp

/-- The prescribed original corner powers determine the actual overlap inventory exactly. -/
theorem literalOverlap_corner_power (D W : Diagram) (hD : IsConnectedSkew D)
    (hW : IsSkew W) (q w : ℤ) (v : ℤ × ℤ)
    (hmin : minContent D = 0) (hv : content v = q - w)
    (hbound : ∀ x ∈ D, 0 ≤ content x ∧ content x < q)
    (hwindow : D.filter (fun x => q - w ≤ content x ∧ content x < q) =
      translate v (D.filter fun x => 0 ≤ content x ∧ content x < w))
    (hWcells : W = D.filter fun x => 0 ≤ content x ∧ content x < w)
    (hU : IsSkew (D ∪ translate v D)) (Λ : Lambda) (b a : ℕ) (ha : a ≤ b)
    (hKD : cellSchur (diagramInterior D) hD.1.interior = Λ ^ b)
    (hKW : cellSchur (diagramInterior W) hW.interior = Λ ^ a) :
    cellSchur (diagramInterior (D ∪ translate v D)) hU.interior = Λ ^ (2 * b - a) := by
  apply mul_right_cancel₀ (cellSchur_ne_zero (diagramInterior W) hW.interior)
  have hp := literalOverlap_corner_product D W hD hW q w v hmin hv hbound hwindow hWcells hU
  rw [hp, hKD, hKW, ← pow_mul, ← pow_add,
    Nat.sub_add_cancel (show a ≤ 2 * b by omega), Nat.mul_comm b 2]

end SkewCornerDescent
