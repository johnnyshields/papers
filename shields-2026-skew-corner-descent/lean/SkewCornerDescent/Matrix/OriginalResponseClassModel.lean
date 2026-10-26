/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResponseClassActiveLabels
import SkewCornerDescent.Matrix.OriginalClassAffineScale

/-!
# A complete actual model for the constant-label dual detector

Supports `shields-2026-skew-corner-descent.tex` (`lem:exposure`, `lem:dual-identities`).
The matched literal chart produces the finite class word, reduced counts, original
monic representatives, active tops and rational labels, and two actual common
chambers. Their shared polynomial base, cap, and scale stay regular at the same
assignments. No abstract response-model premise is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows PhaseInventory

noncomputable local instance responseClassModelRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every analytic model input of the original constant-label detector is produced
from the actual matched chart and one faithful family of original representatives. -/
theorem originalWindow_responseClass_model {n m s t : ℕ}
    (P : Profile n) (W : Profile s) (A : Profile m) (Q : Profile t)
    (q : ℤ) (v u z w : ℤ × ℤ) (hv : content v = q)
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
    [NeZero (r * (b - a))]
    (p₀ p₁ : Polynomial ℚ) (hpq : IsCoprime p₀ p₁)
    (hdep : c.residueMap P.schur ^ a / c.residueMap W.schur ^ b =
      Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₀ /
        Polynomial.aeval (c.residueMap Q.schur / c.residueMap P.schur ^ 2) p₁) :
    let d := b - a
    ∃ hB : 0 < originalSelectedCount (hD := hD) P, ∃ K : ℕ+, c.top < K ∧
    ∃ k s : ℕ, 0 < k ∧ 0 < s ∧ s ≤ d ∧ b = k * d + s ∧
    ∃ hperiod : r * d ≤ originalSelectedCount (hD := hD) P - 1,
    ∃ p q : c.OriginalResponseClass P → OtherPolynomial c.top,
    ∃ label : c.OriginalResponseClass P → ℚ,
    ∃ base cap scaleDen : OtherPolynomial c.top,
    ∃ xnegative xpositive : ℕ → ℝ,
      let top := c.originalResponseClassTop P hB
      let word := c.originalResponseClassWord P (r * d) hperiod
      (∀ X j, j ∈ (realResiduePolynomial c.top (p X)).vars → j < (top X : ℕ)) ∧
      (∀ X j, j ∈ (realResiduePolynomial c.top (q X)).vars → j < (c.top : ℕ)) ∧
      (∀ X, q X ≠ 0) ∧
      (∀ X, X.val = residueGenerator c.top
          ⟨top X, ne_of_gt (c.originalResponseClassTop_gt P hB X)⟩ +
        algebraMap (OtherPolynomial c.top) (OtherField c.top) (p X) /
          algebraMap (OtherPolynomial c.top) (OtherField c.top) (q X)) ∧
      (∀ X, classDefect word 1 d s (r * s - 1) 0 X ≠ 0 → top X = K) ∧
      (∀ X Y, classDefect word 1 d s (r * s - 1) 0 X ≠ 0 →
        classDefect word 1 d s (r * s - 1) 0 Y ≠ 0 → label X = label Y → X = Y) ∧
      (∀ X, classDefect word 1 d s (r * s - 1) 0 X ≠ 0 →
        let ι := algebraMap (OtherPolynomial c.top) (OtherField c.top)
        residueGenerator c.top ⟨top X, ne_of_gt (c.originalResponseClassTop_gt P hB X)⟩ +
            ι (p X) / ι (q X) =
          residueGenerator c.top ⟨top X, ne_of_gt (c.originalResponseClassTop_gt P hB X)⟩ +
            ι base / ι scaleDen - (label X : OtherField c.top) * (ι cap / ι scaleDen)) ∧
      xnegative ∈ simultaneousActualChamber c.top K top p q false ∧
      xpositive ∈ simultaneousActualChamber c.top K top p q true ∧
      MvPolynomial.eval xnegative (realResiduePolynomial c.top scaleDen) ≠ 0 ∧
      MvPolynomial.eval xpositive (realResiduePolynomial c.top scaleDen) ≠ 0 ∧
      0 < MvPolynomial.eval xnegative (realResiduePolynomial c.top cap) /
        MvPolynomial.eval xnegative (realResiduePolynomial c.top scaleDen) ∧
      0 < MvPolynomial.eval xpositive (realResiduePolynomial c.top cap) /
        MvPolynomial.eval xpositive (realResiduePolynomial c.top scaleDen) := by
  classical
  let d := b - a
  obtain ⟨hB, K, hKeq, hNK, k, s, hk, hs, hsd, hbshape, hperiod, oldlabel,
      hactive, _, hexists, _⟩ := c.originalWindow_responseClass_active_labels P W A Q
    q v u z w hv hwindow hW hA hQ hcutq hcutLq hmax Λ b a r ha hab hrpos hr hKU hKW
    p₀ p₁ hpq hdep
  obtain ⟨a0, ha0⟩ := hexists
  have hanchor : ∃ X : c.OriginalResponseClass P, c.originalResponseClassTop P hB X = K :=
    ⟨a0, (hactive a0 ha0).1⟩
  obtain ⟨p, q, hp, hq, hrep, hchamber⟩ :=
    c.originalResponseClasses_two_chambers P Q w hQ hB hmax K hKeq hanchor
  obtain ⟨xnegative, hxnegative⟩ := (hchamber false).2.1
  obtain ⟨xpositive, hxpositive⟩ := (hchamber true).2.1
  have hn := (hchamber false).2.2 xnegative hxnegative
  have hp' := (hchamber true).2.2 xpositive hxpositive
  have hq0 : ∀ X, q X ≠ 0 := by
    intro X hz
    have h := hn.1 X
    rw [hz, map_zero, map_zero] at h
    exact h rfl
  let active := fun X : c.OriginalResponseClass P =>
    classDefect (c.originalResponseClassWord P (r * d) hperiod) 1 d s (r * s - 1) 0 X ≠ 0
  have htop : ∀ X, active X → c.originalResponseClassTop P hB X =
      c.originalResponseClassTop P hB a0 := by
    intro X hX
    exact (hactive X hX).1.trans (hactive a0 ha0).1.symm
  obtain ⟨base, cap, scaleDen, haffine, hinj, hscale⟩ :=
    c.originalResponseClasses_affine_scale P hB p q hq0 hrep active a0 ha0 oldlabel
      _ htop (fun X hX => (hactive X hX).2)
  have hnegative := hscale xnegative hn.1 hn.2
  have hpositive := hscale xpositive hp'.1 hp'.2
  dsimp only
  refine ⟨hB, K, hNK, k, s, hk, hs, hsd, hbshape, hperiod, p, q,
    (fun X => oldlabel X - oldlabel a0), base, cap, scaleDen, xnegative, xpositive,
    hp, hq, hq0, hrep, ?_, hinj, haffine, hxnegative, hxpositive,
    hnegative.1, hpositive.1, hnegative.2, hpositive.2⟩
  intro X hX
  exact (hactive X hX).1

end SkewCornerDescent.Matrix.SelectedCoordinate
