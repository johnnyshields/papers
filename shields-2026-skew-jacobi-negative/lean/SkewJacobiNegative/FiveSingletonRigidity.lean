/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.FiveEndpointLeader
import SkewJacobiNegative.FourRowClasses

/-!
# Singleton parents of a rigid five-negative core

The actual source conclusion of `lem:singleton-five-rigid`.  The fixed
leader is produced from the five-negative board; endpoint isolation is
then derived inside singleton lifting.  No endpoint-extension rigidity
premise is imposed.
-/
namespace SkewJacobiNegative.BetaDiagram

/-- Every positive singleton context over a regular five-negative core is rigid. -/
theorem singleton_five_rotationRigid (Q : BetaDiagram 5)
    (hQ : Q.Connected) (hZQ : Q.ZeroFree) (hCount : negativeCount Q = 5)
    (hRQ : Q.RotationRigid) (s u v g : ℤ)
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hg : 0 < g) :
    (Q.singletonContext s u v g hs hu hv hg).RotationRigid :=
  Q.singletonContext_rotationRigid hQ hZQ hRQ
    (Q.endpointLeader_five_negative hQ hZQ hCount) s u v g hs hu hv hg

/-- First-cut source geometry produces every parameter of the singleton context. -/
theorem singleton_five_first_cut_rigidity (D : BetaDiagram 7)
    (hD : D.Connected) (hZ : D.ZeroFree)
    (hCut : D.row 2 < D.col 0)
    (hQ : (D.cornerDiagram (D.positiveCorner_of_connected_zeroFree hD hZ)).tail.Connected)
    (hCount : negativeCount
      (D.cornerDiagram (D.positiveCorner_of_connected_zeroFree hD hZ)).tail = 5)
    (hRQ : (D.cornerDiagram (D.positiveCorner_of_connected_zeroFree hD hZ)).tail.RotationRigid) :
    D.RotationRigid := by
  let hP := D.positiveCorner_of_connected_zeroFree hD hZ
  let Q : BetaDiagram 5 := (D.cornerDiagram hP).tail
  have hZQ : Q.ZeroFree := by
    intro i j
    exact hZ i.succ.succ j.succ.castSucc
  obtain ⟨s,u,v,g,hs,hu,hv,hg,hmotion⟩ := D.singleton_parent_of_first_cut hP hCut
  exact D.rotationRigid_of_translation _ hmotion
    (Q.singleton_five_rotationRigid hQ hZQ hCount hRQ s u v g hs hu hv hg)

end SkewJacobiNegative.BetaDiagram
