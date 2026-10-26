/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalActualInventories
import SkewCornerDescent.Matrix.OriginalActualCoefficient

/-!
# Many-active detection in the original normal series

Formalizes the periodic-gap branch of `shields-2026-skew-corner-descent.tex`
(`cor:many-active`). Actual dual inventories are composed with the original
coefficient producer. Length one is excluded by the literal class-count identity,
and all units of the normal prefactor are produced on the same selected chart.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

/-- Equality of period and closure lengths reindexes the same literal source
word, without making any claim about distinct response values. -/
theorem finiteWord_windowDefect_congr {F ι : Type*} [Field F] [Fintype ι]
    {B n m C E : ℕ} [NeZero n] [NeZero m] [NeZero C] [NeZero E]
    (l : Fin (B - 1) → F) (S : ι → F) (e : ι → ℤ) (b j : ℕ)
    (hn : n = m) (hC : C = E) (hp : n ≤ B - 1) (hq : m ≤ B - 1) :
    windowDefect (finiteWordCycle (n := n) l hp) S e b C j =
      windowDefect (finiteWordCycle (n := m) l hq) S e b E j := by
  subst m
  subst E
  rfl

end SkewCornerDescent.CyclicWindows

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows
open scoped BigOperators

noncomputable local instance manyActiveRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Periodic actual gaps and two unbalanced actual classes supply a nonzero
original coefficient at a positive order no greater than `r*(b-a)-1`.
The detecting length is either the complete period or an eligible short remainder. -/
theorem originalManyActive_periodic {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (Q : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hQ : originalHorizontalClosure P = translate w Q.cells)
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (Λ : Lambda) (b a r : ℕ) (ha : 0 < a) (hab : a + 2 ≤ b) (hrpos : 0 < r)
    (hr : primeOrder (cellSchur D hD.1) Λ = r)
    (hKU : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin s => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a)
    [NeZero (originalSelectedCount (hD := hD) P)]
    [NeZero (originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W)]
    [NeZero (r * (b - a))] [NeZero (r * b)]
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁)
    (htwo : ∃ X Y : c.OriginalResponseClass P, X ≠ Y ∧
      c.originalResponseClassExponent P W a b X ≠ 0 ∧
      c.originalResponseClassExponent P W a b Y ≠ 0) :
    ∃ j : ℕ, 2 ≤ j ∧ j ≤ r * (b - a) ∧ r ∣ j ∧
      PowerSeries.coeff (j - 1) (c.originalDeterminantDefect P A Q a b p₀ p₁) ≠ 0 := by
  classical
  have hcountP : originalSelectedCount (hD := hD) P = r * b := by
    rw [originalSelectedCount_eq_primeOrder, hKU,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hcountW : originalSelectedCount (hD := hD) W = r * a := by
    rw [originalSelectedCount_eq_primeOrder, hKW,
      primeOrder_pow (irreducible_cellSchur hD).prime, hr, Nat.mul_comm]
  have hC : 0 < originalSelectedCount (hD := hD) W := by
    rw [hcountW]; exact Nat.mul_pos hrpos ha
  obtain ⟨k, s, hk, hs, hsd, hbshape, hperiod, _, heligible⟩ :=
    c.originalWindow_inventory_dual_nonvanishing P W A Q q v u z w hv hwindow hW hA hQ
      hcutq hcutLq hmax Λ b a r ha hab hrpos hr hKU hKW p₀ p₁ hpq hdep htwo
  let cycle := finiteWordCycle (n := r * (b - a)) (c.originalInternalResidue P) hperiod
  have hdetect : ∃ j : ℕ, 2 ≤ j ∧ j ≤ r * (b - a) ∧ r ∣ j ∧
      windowDefect cycle Subtype.val (c.originalResponseClassExponent P W a b)
        b (r * b) j ≠ 0 := by
    rcases heligible with hn | ⟨hsize, hshort⟩
    · have hnsize : 2 ≤ r * (b - a) :=
        (by simpa only [one_mul] using
          Nat.mul_le_mul (show 1 ≤ r by omega) (show 2 ≤ b - a by omega))
      exact ⟨r * (b - a), hnsize, le_rfl, dvd_mul_right r _, hn⟩
    · exact ⟨r * s, hsize, Nat.mul_le_mul_left r hsd, dvd_mul_right r _, hshort⟩
  obtain ⟨j, hj, hjn, hjr, hdetector⟩ := hdetect
  have hjB : j ≤ originalSelectedCount (hD := hD) P := by
    rw [hcountP]
    exact hjn.trans (Nat.mul_le_mul_left r (Nat.sub_le b a))
  obtain ⟨K, hK, _, hcoeff, _⟩ := c.originalActual_coefficient P W A Q q v u z w
    hq hv hwindow hW hA hQ hcutq hcutLq hC hmax Λ b a r (by omega) hrpos hr hKU hKW
    hp j hj hjB hjr p₀ p₁ hpq hdep
  have hdiff : originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) W =
      r * (b - a) := by rw [hcountP, hcountW, Nat.mul_sub_left_distrib]
  rw [finiteWord_windowDefect_congr (c.originalInternalResidue P) Subtype.val
    (c.originalResponseClassExponent P W a b) b j hdiff hcountP _ hperiod] at hcoeff
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hρ0, _, _⟩ :=
    c.originalWindow_rational_class_sums P W A Q q v u z w hv hwindow hW hA hQ hcutq
      hcutLq hC hmax Λ b a (by omega) hKU hKW p₀ p₁ hpq hdep
  have hderiv : residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff (j - 1) (c.originalDeterminantDefect P A Q a b p₀ p₁)) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero hρ0 (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (inv_ne_zero c.normalCoefficient_ne_zero))) hdetector)
  refine ⟨j, hj, hjn, hjr, ?_⟩
  intro hz
  exact hderiv (by rw [hz, map_zero])

end SkewCornerDescent.Matrix.SelectedCoordinate
