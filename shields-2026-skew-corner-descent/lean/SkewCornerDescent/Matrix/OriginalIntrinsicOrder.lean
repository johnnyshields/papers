/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalOrdinarySupportInterface
import SkewCornerDescent.Matrix.OriginalOneActiveNormalInterface
import SkewCornerDescent.Matrix.OriginalPurePrimitiveFirst
import SkewCornerDescent.Matrix.OriginalPrimitiveShort
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Original determinant normal order or whole literal repetition

Formalizes `shields-2026-skew-corner-descent.tex` (`thm:intrinsic-order`).
The original support and pin suppliers compose with the complete normal
interface. A positive detected coefficient bounds the extended order of
the unchanged original defect series in the exact coordinate t = psi.
The other branch reconstructs the whole actual parent, including both caps,
as a proper literal empty row or column composition. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
noncomputable local instance intrinsicOrderRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

set_option maxHeartbeats 1200000 in
-- The two complete dependent ordinary interfaces and the original defect are retained.
/-- On the actual ordinary full-window domain, the original normal order is
at most the selected multiplicity times the outer-count difference, or the
whole parent has the stated proper literal empty root. -/
theorem originalIntrinsic_order_or_literal_root {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (H : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hH : originalHorizontalClosure P = translate w H.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hprevq : diagLo P.cells (q - 1) = diagHi P.cells (q - 1))
    (hprevLq : diagLo P.cells (P.xi 0 - q - 1) = diagHi P.cells (P.xi 0 - q - 1))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hr : 0 < r)
    (hcop : Nat.Coprime b a) (hprime : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det = Λ^b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ) (fun j => W.zeta j.castSucc)).det = Λ^a)
    (δ : ℤ) (hspan : P.xi 0 = (b : ℤ) * δ)
    (hqspan : q = ((b-a : ℕ) : ℤ) * δ)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₁)
    (lo prevlo hi prevhi : ℤ × ℤ)
    (hlo : lo ∈ P.cells) (hprevlo : prevlo ∈ P.cells)
    (hhi : hi ∈ P.cells) (hprevhi : prevhi ∈ P.cells)
    (hclo : content lo = P.xi 0 - q) (hcprevlo : content prevlo = P.xi 0 - q - 1)
    (hchi : content hi = q) (hcprevhi : content prevhi = q - 1)
    (hdir : lo.2 = prevlo.2 ↔ hi.2 = prevhi.2) :
    PowerSeries.order (c.originalDeterminantDefect P A H a b p₀ p₁) ≤ (r*(b-a) : ℕ) ∨
      ∃ E : Diagram, IsConnectedSkew E ∧ span E = δ.toNat ∧
        (emptyMarkH E).IsLegal ∧ 2 ≤ E.card ∧
        (∃ x ∈ E, ∃ y ∈ E, x.1 ≠ y.1 ∧ x.2 ≠ y.2) ∧
        2 ≤ (horizontalRow b).card ∧ 2 ≤ (verticalColumn b).card ∧
        (P.cells = (emptyMarkH E).compose (horizontalRow b) ∨
          P.cells = (emptyMarkH E).compose (verticalColumn b)) := by
  have hcountP : originalSelectedCount (hD := hD) P = b*r := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hprime]
  let : NeZero (originalSelectedCount (hD := hD) P) := ⟨by
    rw [hcountP]
    exact ne_of_gt (Nat.mul_pos (show 0 < b by omega) hr)⟩
  rcases c.originalOrdinary_support_interface P W A H q v u z w hq hv hwindow hW hA hH
      hcutq hcutLq hprevq hprevLq hmax Λ b a r ha hab hr hcop hprime hKU hKW
      δ hspan hqspan p₀ p₁ hpq hdep lo prevlo hi prevhi hlo hprevlo hhi hprevhi
      hclo hcprevlo hchi hcprevhi hdir with hdet | hdata
  · obtain ⟨j, _, hj, hcoef⟩ := hdet
    apply Or.inl
    apply (PowerSeries.order_le j hcoef).trans
    exact_mod_cast (hj.trans (Nat.sub_le (r*(b-a)) 1))
  · obtain ⟨active, _, hother, hgap, hresponse, on, O, zO, hO, hcenter⟩ := hdata
    rcases c.originalOneActive_normal_interface P W A H O q v u z w zO hq hv hwindow hW hA
        hH hO hcutq hcutLq hmax Λ b a r ha hab hr hprime hKU hKW p₀ p₁ hpq hdep
        active hother hcenter hresponse hgap hcop.symm (by omega) δ hspan with hdet | hroot
    · obtain ⟨j, _, hj, _, hcoef⟩ := hdet
      apply Or.inl
      apply (PowerSeries.order_le j hcoef).trans
      exact_mod_cast (hj.trans_eq (Nat.mul_comm (b-a) r))
    · exact Or.inr hroot

set_option maxHeartbeats 1200000 in
-- The constant and nonconstant branches share the complete original defect and literal-root type.
/-- The pure primitive intrinsic alternative improves the normal-order bound
by one. The constant branch uses the genuine first-normal theorem; the other
branch produces two active classes from the actual nonconstant word. -/
theorem originalPure_intrinsic_order_or_literal_root {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (H : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hH : originalHorizontalClosure P = translate w H.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hprevq : diagLo P.cells (q - 1) = diagHi P.cells (q - 1))
    (hprevLq : diagLo P.cells (P.xi 0 - q - 1) = diagHi P.cells (P.xi 0 - q - 1))
    (b a : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hcop : Nat.Coprime b a)
    (hKP : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ) (fun j => W.zeta j.castSucc)).det =
      cellSchur D hD.1 ^ a)
    (δ : ℤ) (hspan : P.xi 0 = (b : ℤ) * δ)
    (hqspan : q = ((b-a : ℕ) : ℤ) * δ)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₁)
    (lo prevlo hi prevhi : ℤ × ℤ)
    (hlo : lo ∈ P.cells) (hprevlo : prevlo ∈ P.cells)
    (hhi : hi ∈ P.cells) (hprevhi : prevhi ∈ P.cells)
    (hclo : content lo = P.xi 0 - q) (hcprevlo : content prevlo = P.xi 0 - q - 1)
    (hchi : content hi = q) (hcprevhi : content prevhi = q - 1)
    (hdir : lo.2 = prevlo.2 ↔ hi.2 = prevhi.2) :
    PowerSeries.order (c.originalDeterminantDefect P A H a b p₀ p₁) ≤ (b-a-1 : ℕ) ∨
      ∃ E : Diagram, IsConnectedSkew E ∧ span E = δ.toNat ∧
        (emptyMarkH E).IsLegal ∧ 2 ≤ E.card ∧
        (∃ x ∈ E, ∃ y ∈ E, x.1 ≠ y.1 ∧ x.2 ≠ y.2) ∧
        2 ≤ (horizontalRow b).card ∧ 2 ≤ (verticalColumn b).card ∧
        (P.cells = (emptyMarkH E).compose (horizontalRow b) ∨
          P.cells = (emptyMarkH E).compose (verticalColumn b)) := by
  classical
  by_cases hconstant : ∀ i j, c.originalInternalResidue P i = c.originalInternalResidue P j
  · rcases c.originalPurePrimitive_first_or_literal_root P W A H q v u z w hq hv hwindow hW
        hA hH hcutq hcutLq hprevq hprevLq b a ha hab hcop hKP hKW p₀ p₁ hpq hdep
        hconstant lo prevlo hi prevhi hlo hprevlo hhi hprevhi hclo hcprevlo hchi hcprevhi
        hdir δ hspan with hcoef | hroot
    · apply Or.inl
      apply (PowerSeries.order_le 1 hcoef).trans
      exact_mod_cast (show 1 ≤ b-a-1 by omega)
    · exact Or.inr hroot
  · push Not at hconstant
    have hr : primeOrder (cellSchur D hD.1) (cellSchur D hD.1) = 1 :=
      primeOrder_self (irreducible_cellSchur hD).prime
    have hmax := c.originalPure_component_span P b hKP
    have hspan' : P.xi 0 - P.zeta (Fin.last n) = (b : ℤ)*δ := by
      rw [P.zeta_last, sub_zero]
      exact hspan
    obtain ⟨j, _, hj, hcoef⟩ := c.originalPrimitive_short P W A H q v u z w hq hv hwindow hW
      hA hH hcutq hcutLq hmax (cellSchur D hD.1) b a ha hab hcop hr hKP hKW
      δ hspan' hqspan p₀ p₁ hpq hdep hconstant
    exact Or.inl ((PowerSeries.order_le j hcoef).trans (by exact_mod_cast hj))

/-- Two actual active classes improve the original normal-order bound by
one, without needing an ordinary cut-direction or gap-period assumption. -/
theorem originalManyActive_intrinsic_order {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (H : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hH : originalHorizontalClosure P = translate w H.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hr : 0 < r)
    (hcop : Nat.Coprime b a) (hprime : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det = Λ^b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ) (fun j => W.zeta j.castSucc)).det = Λ^a)
    (δ : ℤ) (hspan : P.xi 0 = (b : ℤ) * δ)
    (hqspan : q = ((b-a : ℕ) : ℤ) * δ)
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap H.schur / c.residueMap P.schur ^ 2) p₁)
    (htwo : ∃ X Y : c.OriginalResponseClass P, X ≠ Y ∧
      c.originalResponseClassExponent P W a b X ≠ 0 ∧
      c.originalResponseClassExponent P W a b Y ≠ 0) :
    PowerSeries.order (c.originalDeterminantDefect P A H a b p₀ p₁) ≤ (r*(b-a)-1 : ℕ) := by
  have hspan' : P.xi 0 - P.zeta (Fin.last n) = (b : ℤ)*δ := by
    rw [P.zeta_last, sub_zero]
    exact hspan
  obtain ⟨j, _, hj, hcoef⟩ := c.originalManyActive_general P W A H q v u z w hq hv hwindow hW
    hA hH hcutq hcutLq hmax Λ b a r ha hab hr hcop hprime hKU hKW δ hspan' hqspan p₀ p₁
    hpq hdep htwo
  exact (PowerSeries.order_le j hcoef).trans (by exact_mod_cast hj)

end SkewCornerDescent.Matrix.SelectedCoordinate
