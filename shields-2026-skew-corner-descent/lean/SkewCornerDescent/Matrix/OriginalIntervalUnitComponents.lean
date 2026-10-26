/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalUnitComponentOrder
import SkewCornerDescent.Matrix.OriginalIntervalBlockSubsetInverse
import SkewCornerDescent.Matrix.OriginalUnitComponentInverse

/-!
# Actual full unit components inside a retained response interval

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Only original blocks inside the actual endpoint cuts form the known prefix and
suffix. Their complete inverses, full component indices and strict beta separation
are produced without importing unrelated exterior source blocks. Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every remaining actual index in the response interval strictly before the current block. -/
abbrev OriginalIntervalUnitPrefix {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P) :=
  {j : OriginalResponseInterval (hD := hD) P b d // j.1.1.1 < u}

/-- Every remaining actual index in the response interval strictly after the current block. -/
abbrev OriginalIntervalUnitSuffix {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P) :=
  {j : OriginalResponseInterval (hD := hD) P b d // u < j.1.1.1}

/-- The whole nonselected component is contained in the actual interval whenever its
original block label is between the two actual endpoint cuts. -/
def originalIntervalUnitIndex {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hu : originalResponseLowerCut P b < (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P d)
    (i : Fin (interiorBlockLength P u.val + 1)) : OriginalResponseInterval (hD := hD) P b d :=
  ⟨⟨⟨u, originalUnitIndex P u hs i⟩, hu.2⟩, hu.1⟩

/-- The complete actual interval prefix has its own genuine inverse. -/
@[instance_reducible]
def originalIntervalUnitPrefixInverse {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P) :
    Invertible (vertexBetaMatrix c.residueMap
      (fun j : OriginalIntervalUnitPrefix (hD := hD) P b d u => originalResponseRows P j.1.1.1)
      (fun j : OriginalIntervalUnitPrefix (hD := hD) P b d u =>
        originalResponseCols P j.1.1.1)) := by
  classical
  let := c.originalResponseResidueIntervalInverse P b d
  exact c.originalIntervalKeptBlockInverse P b d (fun z => z < u)

/-- The complete actual interval suffix likewise receives its own genuine inverse. -/
@[instance_reducible]
def originalIntervalUnitSuffixInverse {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P) :
    Invertible (vertexBetaMatrix c.residueMap
      (fun j : OriginalIntervalUnitSuffix (hD := hD) P b d u => originalResponseRows P j.1.1.1)
      (fun j : OriginalIntervalUnitSuffix (hD := hD) P b d u =>
        originalResponseCols P j.1.1.1)) := by
  classical
  let := c.originalResponseResidueIntervalInverse P b d
  exact c.originalIntervalKeptBlockInverse P b d (fun z => u < z)

/-- The current normalized complete unit component lies strictly below every actual
interval-prefix column. No separate beta separation premise is supplied. -/
theorem original_interval_unit_prefix_separation {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ)
    (i : Fin (interiorBlockLength P u.val + 1))
    (j : OriginalIntervalUnitPrefix (hD := hD) P b d u) :
    (interiorBlockProfile P u.val hne).xi i + originalComponentTau P u <
      originalResponseCols P j.1.1.1 := by
  exact original_unit_prefix_separation P u hs hne i ⟨j.1.1.1, j.property⟩

/-- Every actual interval-suffix row lies strictly below each current component column. -/
theorem original_interval_unit_suffix_separation {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ)
    (i : Fin (interiorBlockLength P u.val + 1))
    (j : OriginalIntervalUnitSuffix (hD := hD) P b d u) :
    originalResponseRows P j.1.1.1 <
      (interiorBlockProfile P u.val hne).zeta i + originalComponentTau P u := by
  exact original_unit_suffix_separation P u hs hne i ⟨j.1.1.1, j.property⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
