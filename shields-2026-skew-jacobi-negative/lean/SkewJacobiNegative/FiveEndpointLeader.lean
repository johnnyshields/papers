/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.FiveMarkers
import SkewJacobiNegative.EndpointLeaders

/-!
# Fixed endpoint leaders for five negative indices

The fixed-coefficient assertion `lem:five-negative-leading` and its
alternant identity `eq:five-negative-alternants` in
`shields-2026-skew-jacobi-negative.tex`.  The balanced middle placement
uses its actual lower moving level, not the ordinary boundary level.
-/

namespace SkewJacobiNegative

open MvPolynomial
open scoped BigOperators

namespace BetaDiagram

variable {n : ℕ}

theorem endpointDifference_of_translation (D E : BetaDiagram (n+1))
    (h : D.TranslationEquivalent E) (t : ℤ) (ht : 0<t) :
    D.endpointDifference t ht=E.endpointDifference t ht := by
  unfold endpointDifference
  rw [extendTop_schur_eq_of_translation D E h,extendBottom_schur_eq_of_translation D E h]

theorem EndpointLeader.of_translation (D E : BetaDiagram (n+1))
    (h : D.TranslationEquivalent E) (hE : E.EndpointLeader) : D.EndpointLeader := by
  have hL : D.largestLabel=E.largestLabel := by
    obtain ⟨c,hr,hc⟩ := h
    unfold largestLabel
    rw [hr,hc]
    ring
  obtain ⟨k,hk,hlt,c,hc,hs⟩ := hE
  refine ⟨k,hk,by simpa only [hL] using hlt,c,hc,?_⟩
  intro t ht
  obtain ⟨r,he,hcl,hrl⟩ := hs t ht
  exact ⟨r,(D.endpointDifference_of_translation E h t ht).trans he,hcl,hrl⟩

theorem EndpointLeader.of_rotate (D : BetaDiagram (n+1))
    (h : D.rotate.EndpointLeader) : D.EndpointLeader := by
  obtain ⟨k,hk,hlt,c,hc,hs⟩ := h
  refine ⟨k,hk,by simpa only [D.rotate_largestLabel] using hlt,-c,neg_ne_zero.mpr hc,?_⟩
  intro t ht
  obtain ⟨r,he,hcl,hrl⟩ := hs t ht
  rw [D.endpointDifference_rotate t ht] at he
  refine ⟨-r,?_,hcl.neg,hrl.neg⟩
  linear_combination -he

theorem zeroFree_of_translation (D E : BetaDiagram n)
    (h : D.TranslationEquivalent E) (hD : D.ZeroFree) : E.ZeroFree := by
  obtain ⟨c,hr,hc⟩ := h
  intro i j he
  apply hD i j
  rw [hr,hc,he]

theorem symmetric_of_translation (D E : BetaDiagram n)
    (h : D.TranslationEquivalent E) (hE : E.Symmetric) : D.Symmetric := by
  obtain ⟨c,hr,hc⟩ := h
  obtain ⟨k,hEr,hEc⟩ := hE
  refine ⟨k+2*c,?_,?_⟩
  · intro i
    rw [hr,hc,hEr]
    ring
  · intro i
    rw [hc,hr,hEc]
    ring

theorem symmetric_of_rotate_symmetric (D : BetaDiagram n) (h : D.rotate.Symmetric) :
    D.Symmetric := by
  obtain ⟨k,hr,hc⟩ := h
  refine ⟨-k,?_,?_⟩
  · intro i
    have hh := hc i.rev
    simp only [rotate,Fin.rev_rev] at hh
    omega
  · intro i
    have hh := hr i.rev
    simp only [rotate,Fin.rev_rev] at hh
    omega

theorem zeroFree_rotate (D : BetaDiagram n) (h : D.ZeroFree) : D.rotate.ZeroFree := by
  intro i j he
  apply h j.rev i.rev
  change -D.col i.rev=-D.row j.rev at he
  omega

/-- The ordinary untied level already provides its complete fixed leader. -/
theorem endpointLeader_untied (D : BetaDiagram (n+3)) (hC : D.Connected)
    (hZ : D.ZeroFree) (hne : D.topMargin≠D.bottomMargin) : D.EndpointLeader :=
  D.endpointLeader_of_endpointCoefficient_ne_zero
    (D.endpointCoefficient_ne_zero_untied
      (D.positiveCorner_of_connected_zeroFree hC hZ) hne)

end BetaDiagram

namespace FiveEndpoint

/-- The original positive parameters of the balanced middle placement. -/
structure CriticalData where
  b : ℤ
  q : ℤ
  c : ℤ
  d : ℤ
  u : ℤ
  w : ℤ
  sigma : ℤ
  b_pos : 0<b
  q_pos : 0<q
  c_pos : 0<c
  d_pos : 0<d
  u_pos : 0<u
  w_pos : 0<w
  sigma_pos : 0<sigma
  sigma_lt_c : sigma<c
  sigma_lt_d : sigma<d

namespace CriticalData

def x (A : CriticalData) : ℤ := A.b+A.c+A.u
def z (A : CriticalData) : ℤ := A.b+A.d+A.w
def y (A : CriticalData) : ℤ := A.c+A.d-A.sigma
def X (A : CriticalData) : ℤ := A.x+A.y-A.c
def Y (A : CriticalData) : ℤ := A.y+A.z-A.d
def S (A : CriticalData) : ℤ := A.x+A.z+2*A.q-A.sigma
def k (A : CriticalData) : ℤ := max A.X A.Y+A.q

theorem k_pos (A : CriticalData) : 0<A.k := by
  rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
  dsimp [k,X,Y,x,y,z]
  omega

theorem k_lt_S (A : CriticalData) : A.k<A.S := by
  rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
  dsimp [k,S,X,Y,x,y,z]
  omega

noncomputable def K (A : CriticalData) (j : ℤ) : CompleteRing :=
  complete (A.b+A.q)*complete j-complete A.b*complete (j+A.q)

noncomputable def alt (A : CriticalData) (r s t : ℤ) : CompleteRing :=
  -(!![complete A.b,complete (A.b+A.q),complete (A.b+A.q+t);
    complete r,complete (r+A.q),complete (r+A.q+t);
    complete s,complete (s+A.q),complete (s+A.q+t)]).det

noncomputable def delta (A : CriticalData) (t : ℤ) : CompleteRing :=
  complete A.b*(complete A.y*A.alt A.x A.z t-
    complete A.c*A.alt A.X A.z t-complete A.d*A.alt A.x A.Y t+
    complete A.sigma*A.alt A.X A.Y t)

noncomputable def coeffB (A : CriticalData) : CompleteRing :=
  complete A.b*(complete A.y*(complete (A.x+A.q)*complete A.z-
    complete A.x*complete (A.z+A.q))-
    complete A.c*(complete (A.X+A.q)*complete A.z-complete A.X*complete (A.z+A.q))-
    complete A.d*(complete (A.x+A.q)*complete A.Y-complete A.x*complete (A.Y+A.q))+
    complete A.sigma*(complete (A.X+A.q)*complete A.Y-complete A.X*complete (A.Y+A.q)))

noncomputable def coeffx (A : CriticalData) : CompleteRing :=
  complete A.b*(-complete A.y*A.K A.z+complete A.d*A.K A.Y)
noncomputable def coeffz (A : CriticalData) : CompleteRing :=
  complete A.b*(complete A.y*A.K A.x-complete A.c*A.K A.X)
noncomputable def coeffX (A : CriticalData) : CompleteRing :=
  complete A.b*(complete A.c*A.K A.z-complete A.sigma*A.K A.Y)
noncomputable def coeffY (A : CriticalData) : CompleteRing :=
  complete A.b*(-complete A.d*A.K A.x+complete A.sigma*A.K A.X)

noncomputable def coefficient (A : CriticalData) : CompleteRing :=
  if A.X<A.Y then A.coeffY else if A.Y<A.X then A.coeffX else A.coeffX+A.coeffY

noncomputable def remainder (A : CriticalData) (t : ℤ) : CompleteRing :=
  complete (A.b+A.q+t)*A.coeffB+complete (A.x+A.q+t)*A.coeffx+
    complete (A.z+A.q+t)*A.coeffz+
    (if A.X<A.Y then complete (A.X+A.q+t)*A.coeffX else 0)+
    (if A.Y<A.X then complete (A.Y+A.q+t)*A.coeffY else 0)

theorem alt_expand (A : CriticalData) (r s t : ℤ) :
    A.alt r s t=complete (s+A.q+t)*A.K r-complete (r+A.q+t)*A.K s+
      complete (A.b+A.q+t)*(complete (r+A.q)*complete s-complete r*complete (s+A.q)) := by
  simp [alt,Matrix.det_fin_three,K]
  ring

theorem delta_expand (A : CriticalData) (t : ℤ) :
    A.delta t=complete (A.b+A.q+t)*A.coeffB+complete (A.x+A.q+t)*A.coeffx+
      complete (A.z+A.q+t)*A.coeffz+complete (A.X+A.q+t)*A.coeffX+
      complete (A.Y+A.q+t)*A.coeffY := by
  simp only [delta,alt_expand,coeffB,coeffx,coeffz,coeffX,coeffY,K]
  ring

theorem delta_split (A : CriticalData) (t : ℤ) :
    A.delta t=complete (A.k+t)*A.coefficient+A.remainder t := by
  rw [delta_expand]
  rcases lt_trichotomy A.X A.Y with h | h | h
  · simp only [coefficient,remainder,k,max_eq_right h.le,if_pos h,
      if_neg (not_lt.mpr h.le)]
    ring
  · simp only [coefficient,remainder,k,h,max_self,lt_self_iff_false,if_false]
    ring
  · simp only [coefficient,remainder,k,max_eq_left h.le,if_neg (not_lt.mpr h.le),if_pos h]
    ring

private theorem fixed_generator_labels (A : CriticalData) (t : ℤ) (ht : 0<t) :
    LabelsBelow (complete A.b) (A.k+t) ∧ LabelsBelow (complete A.c) (A.k+t) ∧
    LabelsBelow (complete A.d) (A.k+t) ∧ LabelsBelow (complete A.sigma) (A.k+t) ∧
    LabelsBelow (complete A.y) (A.k+t) ∧ LabelsBelow (complete A.x) (A.k+t) ∧
    LabelsBelow (complete A.z) (A.k+t) ∧ LabelsBelow (complete A.X) (A.k+t) ∧
    LabelsBelow (complete A.Y) (A.k+t) ∧ LabelsBelow (complete (A.b+A.q)) (A.k+t) ∧
    LabelsBelow (complete (A.x+A.q)) (A.k+t) ∧ LabelsBelow (complete (A.z+A.q)) (A.k+t) ∧
    LabelsBelow (complete (A.X+A.q)) (A.k+t) ∧ LabelsBelow (complete (A.Y+A.q)) (A.k+t) := by
  rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
  refine ⟨LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_,
    LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_,
    LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_,
    LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_,
    LabelsBelow.complete ?_,LabelsBelow.complete ?_⟩
  all_goals dsimp only [k,X,Y,x,y,z]; omega

private theorem fixed_coefficient_labels (A : CriticalData) (t : ℤ) (ht : 0<t) :
    LabelsBelow A.coeffB (A.k+t) ∧ LabelsBelow A.coeffx (A.k+t) ∧
    LabelsBelow A.coeffz (A.k+t) ∧ LabelsBelow A.coeffX (A.k+t) ∧
    LabelsBelow A.coeffY (A.k+t) := by
  rcases A.fixed_generator_labels t ht with
    ⟨hb,hc,hd,hs,hy,hx,hz,hX,hY,hbq,hxq,hzq,hXq,hYq⟩
  have hKx : LabelsBelow (A.K A.x) (A.k+t) :=
    (hbq.mul hx).sub (hb.mul hxq)
  have hKz : LabelsBelow (A.K A.z) (A.k+t) :=
    (hbq.mul hz).sub (hb.mul hzq)
  have hKX : LabelsBelow (A.K A.X) (A.k+t) :=
    (hbq.mul hX).sub (hb.mul hXq)
  have hKY : LabelsBelow (A.K A.Y) (A.k+t) :=
    (hbq.mul hY).sub (hb.mul hYq)
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact hb.mul ((((hy.mul ((hxq.mul hz).sub (hx.mul hzq))).sub
      (hc.mul ((hXq.mul hz).sub (hX.mul hzq)))).sub
      (hd.mul ((hxq.mul hY).sub (hx.mul hYq)))).add
      (hs.mul ((hXq.mul hY).sub (hX.mul hYq))))
  · exact hb.mul ((hy.neg.mul hKz).add (hd.mul hKY))
  · exact hb.mul ((hy.mul hKx).sub (hc.mul hKX))
  · exact hb.mul ((hc.mul hKz).sub (hs.mul hKY))
  · exact hb.mul ((hd.neg.mul hKx).add (hs.mul hKX))

theorem coefficient_labels (A : CriticalData) (t : ℤ) (ht : 0<t) :
    LabelsBelow A.coefficient (A.k+t) := by
  have h := A.fixed_coefficient_labels t ht
  unfold coefficient
  split_ifs
  · exact h.2.2.2.2
  · exact h.2.2.2.1
  · exact h.2.2.2.1.add h.2.2.2.2

theorem remainder_labels (A : CriticalData) (t : ℤ) (ht : 0<t) :
    LabelsBelow (A.remainder t) (A.k+t) := by
  have h := A.fixed_coefficient_labels t ht
  have hB : A.b+A.q+t<A.k+t := by
    rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
    dsimp [k,X,Y,x,y,z]
    omega
  have hx : A.x+A.q+t<A.k+t := by
    rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
    dsimp [k,X,Y,x,y,z]
    omega
  have hz : A.z+A.q+t<A.k+t := by
    rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
    dsimp [k,X,Y,x,y,z]
    omega
  unfold remainder
  apply LabelsBelow.add
  · apply LabelsBelow.add
    · exact (((LabelsBelow.complete hB).mul h.1).add
        ((LabelsBelow.complete hx).mul h.2.1)).add ((LabelsBelow.complete hz).mul h.2.2.1)
    · split_ifs with hXY
      · exact (LabelsBelow.complete (by unfold k; omega)).mul h.2.2.2.1
      · exact LabelsBelow.zero _
  · split_ifs with hYX
    · exact (LabelsBelow.complete (by unfold k; omega)).mul h.2.2.2.2
    · exact LabelsBelow.zero _

private theorem linear_marker_ne_zero (j : ℤ) (hj : 0<j) (c r : CompleteRing)
    (hc : c≠0) (hcl : LabelsBelow c j) (hrl : LabelsBelow r j) :
    complete j*c+r≠0 := by
  let v : ℕ+ := ⟨j.toNat,by omega⟩
  have hv : (v.val : ℤ)=j := by dsimp [v]; omega
  have he : complete j=(MvPolynomial.X v : CompleteRing) := complete_of_pos hj
  have hdc : pderiv v c=0 := pderiv_eq_zero_of_notMem_vars (hcl.not_mem v hv)
  have hdr : pderiv v r=0 := pderiv_eq_zero_of_notMem_vars (hrl.not_mem v hv)
  intro hz
  have hd := congrArg (pderiv v) hz
  rw [he,map_add,pderiv_mul,pderiv_X_self,hdc,hdr,map_zero] at hd
  exact hc (by simpa using hd)

private theorem below_Yq (A : CriticalData) :
    LabelsBelow (complete A.b) (A.Y+A.q) ∧ LabelsBelow (complete A.c) (A.Y+A.q) ∧
    LabelsBelow (complete A.sigma) (A.Y+A.q) ∧ LabelsBelow (complete (A.b+A.q)) (A.Y+A.q) ∧
    LabelsBelow (complete A.z) (A.Y+A.q) ∧ LabelsBelow (complete (A.z+A.q)) (A.Y+A.q) ∧
    LabelsBelow (complete A.Y) (A.Y+A.q) := by
  rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
  refine ⟨LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_,
    LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_⟩
  all_goals dsimp only [Y,x,y,z]; omega

private theorem below_Xq (A : CriticalData) :
    LabelsBelow (complete A.b) (A.X+A.q) ∧ LabelsBelow (complete A.d) (A.X+A.q) ∧
    LabelsBelow (complete A.sigma) (A.X+A.q) ∧ LabelsBelow (complete (A.b+A.q)) (A.X+A.q) ∧
    LabelsBelow (complete A.x) (A.X+A.q) ∧ LabelsBelow (complete (A.x+A.q)) (A.X+A.q) ∧
    LabelsBelow (complete A.X) (A.X+A.q) := by
  rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
  refine ⟨LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_,
    LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_⟩
  all_goals dsimp only [X,x,y,z]; omega

private theorem below_zq (A : CriticalData) (h : A.x<A.z) :
    LabelsBelow (complete A.b) (A.z+A.q) ∧ LabelsBelow (complete A.c) (A.z+A.q) ∧
    LabelsBelow (complete A.d) (A.z+A.q) ∧ LabelsBelow (complete (A.b+A.q)) (A.z+A.q) ∧
    LabelsBelow (complete A.z) (A.z+A.q) ∧ LabelsBelow (complete A.x) (A.z+A.q) ∧
    LabelsBelow (complete (A.x+A.q)) (A.z+A.q) := by
  rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
  refine ⟨LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_,
    LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_⟩
  all_goals dsimp only [x,z] at *; omega

private theorem below_xq (A : CriticalData) (h : A.z<A.x) :
    LabelsBelow (complete A.b) (A.x+A.q) ∧ LabelsBelow (complete A.c) (A.x+A.q) ∧
    LabelsBelow (complete A.d) (A.x+A.q) ∧ LabelsBelow (complete (A.b+A.q)) (A.x+A.q) ∧
    LabelsBelow (complete A.x) (A.x+A.q) ∧ LabelsBelow (complete A.z) (A.x+A.q) ∧
    LabelsBelow (complete (A.z+A.q)) (A.x+A.q) := by
  rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
  refine ⟨LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_,
    LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_,LabelsBelow.complete ?_⟩
  all_goals dsimp only [x,z] at *; omega

theorem coeffX_ne_zero (A : CriticalData) : A.coeffX≠0 := by
  rcases A.below_Yq with ⟨hbL,hcL,hsL,hbqL,hzL,hzqL,hYL⟩
  have hKz : LabelsBelow (A.K A.z) (A.Y+A.q) :=
    (hbqL.mul hzL).sub (hbL.mul hzqL)
  let c := complete A.b*complete A.b*complete A.sigma
  let r := complete A.b*(complete A.c*A.K A.z-
    complete A.sigma*complete (A.b+A.q)*complete A.Y)
  have he : A.coeffX=complete (A.Y+A.q)*c+r := by
    dsimp only [coeffX,c,r,K]
    ring
  rw [he]
  apply linear_marker_ne_zero
  · rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
    dsimp [Y,x,y,z]
    omega
  · exact mul_ne_zero (mul_ne_zero
      ((complete_ne_zero_iff _).mpr A.b_pos.le)
      ((complete_ne_zero_iff _).mpr A.b_pos.le))
      ((complete_ne_zero_iff _).mpr A.sigma_pos.le)
  · exact (hbL.mul hbL).mul hsL
  · exact hbL.mul ((hcL.mul hKz).sub ((hsL.mul hbqL).mul hYL))

theorem coeffY_ne_zero (A : CriticalData) : A.coeffY≠0 := by
  rcases A.below_Xq with ⟨hbL,hdL,hsL,hbqL,hxL,hxqL,hXL⟩
  have hKx : LabelsBelow (A.K A.x) (A.X+A.q) :=
    (hbqL.mul hxL).sub (hbL.mul hxqL)
  let c := -(complete A.b*complete A.b*complete A.sigma)
  let r := complete A.b*(-complete A.d*A.K A.x+
    complete A.sigma*complete (A.b+A.q)*complete A.X)
  have he : A.coeffY=complete (A.X+A.q)*c+r := by
    dsimp only [coeffY,c,r,K]
    ring
  rw [he]
  apply linear_marker_ne_zero
  · rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
    dsimp [X,x,y,z]
    omega
  · exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero
      ((complete_ne_zero_iff _).mpr A.b_pos.le)
      ((complete_ne_zero_iff _).mpr A.b_pos.le))
      ((complete_ne_zero_iff _).mpr A.sigma_pos.le))
  · exact ((hbL.mul hbL).mul hsL).neg
  · exact hbL.mul ((hdL.neg.mul hKx).add ((hsL.mul hbqL).mul hXL))

theorem tied_coefficient_eq (A : CriticalData) (h : A.X=A.Y) :
    A.coeffX+A.coeffY=complete A.b*(complete A.c*A.K A.z-complete A.d*A.K A.x) := by
  unfold coeffX coeffY
  rw [h]
  ring

theorem tied_coefficient_ne_zero (A : CriticalData) (h : A.X=A.Y) (hne : A.x≠A.z) :
    A.coeffX+A.coeffY≠0 := by
  rw [A.tied_coefficient_eq h]
  rcases lt_or_gt_of_ne hne with hx | hx
  · rcases A.below_zq hx with ⟨hbL,hcL,hdL,hbqL,hzL,hxL,hxqL⟩
    have hKx : LabelsBelow (A.K A.x) (A.z+A.q) :=
      (hbqL.mul hxL).sub (hbL.mul hxqL)
    let c := -(complete A.b*complete A.b*complete A.c)
    let r := complete A.b*(complete A.c*complete (A.b+A.q)*complete A.z-
      complete A.d*A.K A.x)
    have he : complete A.b*(complete A.c*A.K A.z-complete A.d*A.K A.x)=
        complete (A.z+A.q)*c+r := by dsimp only [c,r,K]; ring
    rw [he]
    apply linear_marker_ne_zero
    · rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
      dsimp [z] at *
      omega
    · exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero
        ((complete_ne_zero_iff _).mpr A.b_pos.le)
        ((complete_ne_zero_iff _).mpr A.b_pos.le))
        ((complete_ne_zero_iff _).mpr A.c_pos.le))
    · exact ((hbL.mul hbL).mul hcL).neg
    · exact hbL.mul (((hcL.mul hbqL).mul hzL).sub (hdL.mul hKx))
  · rcases A.below_xq hx with ⟨hbL,hcL,hdL,hbqL,hxL,hzL,hzqL⟩
    have hKz : LabelsBelow (A.K A.z) (A.x+A.q) :=
      (hbqL.mul hzL).sub (hbL.mul hzqL)
    let c := complete A.b*complete A.b*complete A.d
    let r := complete A.b*(complete A.c*A.K A.z-
      complete A.d*complete (A.b+A.q)*complete A.x)
    have he : complete A.b*(complete A.c*A.K A.z-complete A.d*A.K A.x)=
        complete (A.x+A.q)*c+r := by dsimp only [c,r,K]; ring
    rw [he]
    apply linear_marker_ne_zero
    · rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
      dsimp [x] at *
      omega
    · exact mul_ne_zero (mul_ne_zero
        ((complete_ne_zero_iff _).mpr A.b_pos.le)
        ((complete_ne_zero_iff _).mpr A.b_pos.le))
        ((complete_ne_zero_iff _).mpr A.d_pos.le)
    · exact (hbL.mul hbL).mul hdL
    · exact hbL.mul ((hcL.mul hKz).sub ((hdL.mul hbqL).mul hxL))

theorem coefficient_ne_zero (A : CriticalData) (hsep : A.X=A.Y → A.x≠A.z) :
    A.coefficient≠0 := by
  rcases lt_trichotomy A.X A.Y with h | h | h
  · simpa only [coefficient,if_pos h] using A.coeffY_ne_zero
  · simpa only [coefficient,h,lt_self_iff_false,if_false] using A.tied_coefficient_ne_zero h (hsep h)
  · simpa only [coefficient,if_neg (not_lt.mpr h.le),if_pos h] using A.coeffX_ne_zero

theorem delta_leader (A : CriticalData) (hsep : A.X=A.Y → A.x≠A.z) :
    ∃ c : CompleteRing, c≠0 ∧ ∀ (t : ℤ), 0<t →
      ∃ r : CompleteRing, A.delta t=complete (A.k+t)*c+r ∧
        LabelsBelow c (A.k+t) ∧ LabelsBelow r (A.k+t) :=
  ⟨A.coefficient,A.coefficient_ne_zero hsep,fun t ht =>
    ⟨A.remainder t,A.delta_split t,A.coefficient_labels t ht,A.remainder_labels t ht⟩⟩

end CriticalData

open FiveNegative

theorem middle_zeroFree_parameters (t : Parameters) (h : ValidM t)
    (hZ : (M t h).ZeroFree) : 0<t.a ∧ 0<t.p ∧ 0<t.tau := by
  have ha := hZ 1 0
  have hp := hZ 4 3
  have ht := hZ 3 1
  have ea := M_index t h 1 0
  have ep := M_index t h 4 3
  have et := M_index t h 3 1
  have hL : t.L+t.tau=t.u+t.v := by
    rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
    dsimp [Parameters.L]
    omega
  simp [profileIndex,Fin.sum_univ_succ] at ea ep et
  omega

theorem end_zeroFree_parameters (t : Parameters) (h : ValidE t)
    (hZ : (E t h).ZeroFree) : 0<t.a ∧ 0<t.p ∧ 0<t.tau := by
  have ha := hZ 3 2
  have hp := hZ 4 3
  have ht := hZ 2 0
  have ea := E_index t h 3 2
  have ep := E_index t h 4 3
  have et := E_index t h 2 0
  have hL : t.L+t.tau=t.u+t.v := by
    rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
    dsimp [Parameters.L]
    omega
  simp [profileIndex,Fin.sum_univ_succ] at ea ep et
  omega

theorem middle_margins (t : Parameters) (h : ValidM t) :
    (M t h).topMargin=(t.x : ℤ)-t.a ∧
    (M t h).bottomMargin=(t.b : ℤ)-t.p := by
  have e00 := M_index t h 0 0
  have e10 := M_index t h 1 0
  have e43 := M_index t h 4 3
  have e44 := M_index t h 4 4
  simp [profileIndex,Fin.sum_univ_succ] at e00 e10 e43 e44
  change (M t h).row 0-(M t h).row 1=(t.x : ℤ)-t.a ∧
    (M t h).col 3-(M t h).col 4=(t.b : ℤ)-t.p
  omega

theorem end_margins (t : Parameters) (h : ValidE t) :
    (E t h).topMargin=(t.x : ℤ)-t.u ∧
    (E t h).bottomMargin=(t.b : ℤ)-t.p := by
  have e00 := E_index t h 0 0
  have e10 := E_index t h 1 0
  have e43 := E_index t h 4 3
  have e44 := E_index t h 4 4
  simp [profileIndex,Fin.sum_univ_succ] at e00 e10 e43 e44
  change (E t h).row 0-(E t h).row 1=(t.x : ℤ)-t.u ∧
    (E t h).col 3-(E t h).col 4=(t.b : ℤ)-t.p
  omega

def ofMiddle (t : Parameters) (h : ValidM t) (hZ : (M t h).ZeroFree) : CriticalData where
  b := t.a
  q := (t.b : ℤ)-t.p
  c := t.u
  d := t.v
  u := (t.y : ℤ)-t.a-t.u
  w := (t.c : ℤ)-t.p-t.v
  sigma := t.tau
  b_pos := by have hh := middle_zeroFree_parameters t h hZ; omega
  q_pos := by rcases h with ⟨hu,hv,hb,hx,hy,hc⟩; omega
  c_pos := by rcases h with ⟨hu,hv,hb,hx,hy,hc⟩; omega
  d_pos := by rcases h with ⟨hu,hv,hb,hx,hy,hc⟩; omega
  u_pos := by rcases h with ⟨hu,hv,hb,hx,hy,hc⟩; omega
  w_pos := by rcases h with ⟨hu,hv,hb,hx,hy,hc⟩; omega
  sigma_pos := by have hh := middle_zeroFree_parameters t h hZ; omega
  sigma_lt_c := by rcases h with ⟨hu,hv,hb,hx,hy,hc⟩; omega
  sigma_lt_d := by rcases h with ⟨hu,hv,hb,hx,hy,hc⟩; omega

namespace CriticalData

def parameters (A : CriticalData) : Parameters where
  x := (A.b+A.q).toNat
  y := A.x.toNat
  c := A.z.toNat
  b := (A.b+A.q).toNat
  a := A.b.toNat
  u := A.c.toNat
  v := A.d.toNat
  p := A.b.toNat
  tau := A.sigma.toNat

theorem parameters_valid (A : CriticalData) : ValidM A.parameters := by
  rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
  dsimp [parameters,ValidM,x,z]
  omega

def diagram (A : CriticalData) : BetaDiagram 5 := M A.parameters A.parameters_valid

def W (A : CriticalData) : ℤ := A.x+A.z-A.sigma

/-- Both endpoint shifts, with the common corner counted only once in each difference. -/
noncomputable def shiftedMatrix (A : CriticalData) (s t : ℤ) :
    Matrix (Fin 5) (Fin 5) CompleteRing :=
  !![complete (A.b+A.q+s),complete (A.x+A.q+s),complete (A.X+A.q+s),
      complete (A.W+A.q+s),complete (A.S+s+t);
    complete A.b,complete A.x,complete A.X,complete A.W,complete (A.W+A.q+t);
    0,complete A.c,complete A.y,complete A.Y,complete (A.Y+A.q+t);
    0,complete A.sigma,complete A.d,complete A.z,complete (A.z+A.q+t);
    0,0,0,complete A.b,complete (A.b+A.q+t)]

end CriticalData

theorem profile_palindrome_symmetric {n : ℕ} (P : Gluing.Profile n)
    (hr : ∀ i,P.r i=P.r i.rev) (hg : ∀ j,P.g j=P.g j.rev) :
    P.toBetaDiagram.Symmetric := by
  have he : P.rotate=P := by
    apply Gluing.Profile.ext
    · funext i
      exact (hr i).symm
    · funext j
      exact (hg j).symm
  refine ⟨P.xi 0,?_,?_⟩
  · intro i
    change P.xi i=P.xi 0-P.zeta i.rev
    have hh := P.xi_rotate i
    rwa [he] at hh
  · intro i
    change P.zeta i=P.xi 0-P.xi i.rev
    have hh := P.zeta_rotate i
    rwa [he] at hh

theorem middle_symmetric_of_palindrome (t : Parameters) (h : ValidM t)
    (hxb : t.x=t.b) (hyc : t.y=t.c) (hap : t.a=t.p) (huv : t.u=t.v) :
    (M t h).Symmetric := by
  apply profile_palindrome_symmetric (mProfile t h)
  · intro i
    fin_cases i <;> simp [mProfile,Fin.rev,hxb,hyc]
  · intro j
    fin_cases j <;> simp [mProfile,Fin.rev,hap,huv]

theorem critical_parameters_recover (t : Parameters) (h : ValidM t)
    (hZ : (M t h).ZeroFree) (htie : (M t h).topMargin=(M t h).bottomMargin)
    (hap : t.a=t.p) : (ofMiddle t h hZ).parameters=t := by
  have hm := middle_margins t h
  have hxb : t.x=t.b := by omega
  rcases h with ⟨hu,hv,hb,hx,hy,hc⟩
  cases t
  dsimp [ofMiddle,CriticalData.parameters,CriticalData.x,CriticalData.z] at *
  congr <;> omega

theorem critical_nonsymmetry (t : Parameters) (h : ValidM t)
    (hZ : (M t h).ZeroFree) (htie : (M t h).topMargin=(M t h).bottomMargin)
    (hap : t.a=t.p) (hS : ¬(M t h).Symmetric) :
    (ofMiddle t h hZ).X=(ofMiddle t h hZ).Y →
      (ofMiddle t h hZ).x≠(ofMiddle t h hZ).z := by
  intro hXY hxz
  have hm := middle_margins t h
  have hxb : t.x=t.b := by omega
  have hyc : t.y=t.c := by
    dsimp [ofMiddle,CriticalData.x,CriticalData.z] at hxz
    omega
  have huv : t.u=t.v := by
    dsimp [ofMiddle,CriticalData.X,CriticalData.Y,CriticalData.x,CriticalData.y,CriticalData.z] at hXY
    omega
  exact hS (middle_symmetric_of_palindrome t h hxb hyc hap huv)

theorem dehom_X_complete (j : ℕ) : Gluing.dehom (X j)=complete (j : ℤ) := by
  have he : Gluing.hTilde (j : ℤ)=(X j : Gluing.HomLambda) := by
    rw [Gluing.hTilde,if_neg (show ¬(j : ℤ)<0 by omega),Int.toNat_natCast]
  rw [←he,Gluing.dehom_hTilde,complete_eq_hh]

theorem dehom_cofactor (D : BetaDiagram 5) (i j : Fin 5) :
    Gluing.dehom (homCofactor D i j)=D.cofactor i j := by
  have hm (a b : Fin 5) : Gluing.dehom (D.homMatrix a b)=D.matrix a b := by
    change Gluing.dehom (Gluing.hTilde (D.row a-D.col b))=complete (D.row a-D.col b)
    rw [Gluing.dehom_hTilde,complete_eq_hh]
  have hsub : Gluing.dehom.mapMatrix (D.homMatrix.submatrix i.succAbove j.succAbove)=
      D.matrix.submatrix i.succAbove j.succAbove := by
    apply Matrix.ext
    intro a b
    exact hm (i.succAbove a) (j.succAbove b)
  unfold homCofactor BetaDiagram.cofactor
  rw [map_mul,map_pow,map_neg,map_one,AlgHom.map_det,hsub]

theorem affine_B_ne_zero (u v tau : ℕ) (hu : tau<u) (hv : tau<v) :
    Gluing.dehom (B u v tau)≠0 := by
  rw [B_eq_F,←quadratic_homSchur u v tau hu hv,BetaDiagram.dehom_homSchur]
  exact ((quadraticDiagram u v tau hu hv).schur_irreducible
    (quadratic_connected u v tau hu hv)).ne_zero

theorem affine_F_erased_ne_zero (s z tau : ℕ) (hs : tau<s) (hz : tau<z) (v : ℕ+) :
    eraseGenerator v (Gluing.dehom (F s z tau))≠0 := by
  rw [←quadratic_homSchur s z tau hs hz,BetaDiagram.dehom_homSchur]
  exact (quadraticDiagram s z tau hs hz).connected_erased_ne_zero
    (quadratic_connected s z tau hs hz) v

theorem tied_coefficient_sites (D : BetaDiagram 5) (h : D.topMargin=D.bottomMargin) :
    D.endpointCoefficient=D.cofactor 0 3-D.cofactor 1 4 := by
  have h14 : D.row 0-D.col 3=D.endpointKappa := by
    change D.row 0-D.row 1=D.col 3-D.col 4 at h
    change D.row 0-D.col 3=max (D.row 1-D.col 4) (D.row 0-D.col 3)
    omega
  have h25 : D.row 1-D.col 4=D.endpointKappa := by
    change D.row 0-D.row 1=D.col 3-D.col 4 at h
    change D.row 1-D.col 4=max (D.row 1-D.col 4) (D.row 0-D.col 3)
    omega
  rw [D.endpointCoefficient_eq_sites]
  change (if D.row 0-D.col 3=D.endpointKappa then D.cofactor 0 3 else 0)-
    (if D.row 1-D.col 4=D.endpointKappa then D.cofactor 1 4 else 0)=_
  rw [if_pos h14,if_pos h25]

theorem middle_tied_coefficient (t : Parameters) (h : ValidM t)
    (htie : (M t h).topMargin=(M t h).bottomMargin) :
    (M t h).endpointCoefficient=
      (complete (t.x : ℤ)*complete (t.p : ℤ)-complete (t.a : ℤ)*complete (t.b : ℤ))*
        Gluing.dehom (B t.u t.v t.tau) := by
  rw [tied_coefficient_sites _ htie]
  have h14 := congrArg Gluing.dehom (M_C14 t h)
  have h25 := congrArg Gluing.dehom (M_C25 t h)
  rw [dehom_cofactor] at h14 h25
  rw [h14,h25]
  simp only [C14,C25M,map_neg,map_mul,dehom_X_complete]
  ring

theorem end_tied_coefficient (t : Parameters) (h : ValidE t)
    (htie : (E t h).topMargin=(E t h).bottomMargin) :
    (E t h).endpointCoefficient=complete (t.a : ℤ)*
      (complete (t.p : ℤ)*Gluing.dehom (F t.v t.x t.tau)-
        complete (t.b : ℤ)*Gluing.dehom (B t.u t.v t.tau)) := by
  rw [tied_coefficient_sites _ htie]
  have h14 := congrArg Gluing.dehom (E_C14 t h)
  have h25 := congrArg Gluing.dehom (E_C25 t h)
  rw [dehom_cofactor] at h14 h25
  rw [h14,h25]
  simp only [C14,C25E,map_neg,map_mul,dehom_X_complete]
  ring

theorem middle_tied_coefficient_ne_zero (t : Parameters) (h : ValidM t)
    (hZ : (M t h).ZeroFree) (htie : (M t h).topMargin=(M t h).bottomMargin)
    (hne : t.a≠t.p) : (M t h).endpointCoefficient≠0 := by
  rw [middle_tied_coefficient t h htie]
  apply mul_ne_zero
  · have hpos := middle_zeroFree_parameters t h hZ
    have hm := middle_margins t h
    let q := (M t h).topMargin
    have hq : 0<q := (M t h).topMargin_pos
    have hx : (t.x : ℤ)=q+t.a := by dsimp [q]; omega
    have hb : (t.b : ℤ)=(t.p : ℤ)+q := by dsimp [q]; omega
    rw [hx,hb]
    intro hz
    have hbin : complete (t.p : ℤ)*complete (q+(t.a : ℤ))-
        complete ((t.p : ℤ)+q)*complete (t.a : ℤ)=0 := by
      linear_combination hz
    have he := (BetaDiagram.endpoint_binomial_eq_zero_iff q (t.a : ℤ) (t.p : ℤ)
      hq (by omega) (by omega)).mp hbin
    apply hne
    omega
  · exact affine_B_ne_zero _ _ _ h.1 h.2.1

theorem middle_ordinary_leader (t : Parameters) (h : ValidM t)
    (hZ : (M t h).ZeroFree) (hne : t.a≠t.p) : (M t h).EndpointLeader := by
  by_cases htie : (M t h).topMargin=(M t h).bottomMargin
  · exact (M t h).endpointLeader_of_endpointCoefficient_ne_zero
      (middle_tied_coefficient_ne_zero t h hZ htie hne)
  · exact (M t h).endpointLeader_untied (M_connected t h) hZ htie

theorem end_tied_coefficient_ne_zero (t : Parameters) (h : ValidE t)
    (htie : (E t h).topMargin=(E t h).bottomMargin) :
    (E t h).endpointCoefficient≠0 := by
  rw [end_tied_coefficient t h htie]
  apply mul_ne_zero ((complete_ne_zero_iff _).mpr (by omega))
  intro hz
  have hb := h.2.2.1
  let v : ℕ+ := ⟨t.b,by omega⟩
  have hpb : (t.p : ℤ)≠(v.val : ℤ) := by dsimp [v]; omega
  have hbb : (t.b : ℤ)=(v.val : ℤ) := rfl
  have hh := congrArg (eraseGenerator v) hz
  simp only [map_sub,map_mul,eraseGenerator_complete,if_pos hbb,if_neg hpb,
    zero_mul,sub_zero,map_zero] at hh
  have hF := affine_F_erased_ne_zero t.v t.x t.tau h.2.1
    (by have hu := h.1; have hx := h.2.2.2.1; omega) v
  exact (mul_ne_zero ((complete_ne_zero_iff _).mpr (by omega)) hF) hh

theorem end_leader (t : Parameters) (h : ValidE t) (hZ : (E t h).ZeroFree) :
    (E t h).EndpointLeader := by
  by_cases htie : (E t h).topMargin=(E t h).bottomMargin
  · exact (E t h).endpointLeader_of_endpointCoefficient_ne_zero
      (end_tied_coefficient_ne_zero t h htie)
  · exact (E t h).endpointLeader_untied (E_connected t h) hZ htie

namespace CriticalData

def indexMatrix (A : CriticalData) : Matrix (Fin 5) (Fin 5) ℤ :=
  !![A.b+A.q,A.x+A.q,A.X+A.q,A.W+A.q,A.S;
    A.b,A.x,A.X,A.W,A.W+A.q;
    -A.u,A.c,A.y,A.Y,A.Y+A.q;
    A.b+A.sigma-A.x,A.sigma,A.d,A.z,A.z+A.q;
    2*A.b+A.sigma-A.x-A.z,A.b+A.sigma-A.z,-A.w,A.b,A.b+A.q]

theorem diagram_index (A : CriticalData) (i j : Fin 5) :
    A.diagram.row i-A.diagram.col j=A.indexMatrix i j := by
  unfold diagram
  rw [M_index]
  rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
  fin_cases i <;> fin_cases j <;>
    simp [parameters,profileIndex,Fin.sum_univ_succ,indexMatrix,W,S,X,Y,x,y,z,Parameters.L] <;>
    omega

theorem diagram_largestLabel (A : CriticalData) : A.diagram.largestLabel=A.S := by
  have hh := A.diagram_index 0 4
  simpa [BetaDiagram.largestLabel,indexMatrix] using hh

private theorem top_index_complete (A : CriticalData) (t : ℤ) (i j : Fin 5) :
    complete (A.indexMatrix i j+(if i=0 then t else 0))=A.shiftedMatrix t 0 i j := by
  rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
  fin_cases i <;> fin_cases j <;> simp [indexMatrix,shiftedMatrix] <;>
    first
    | rfl
    | apply complete_of_neg
      first | omega | (simp only [X,Y,W,S,x,y,z] at * <;> omega)

private theorem bottom_index_complete (A : CriticalData) (t : ℤ) (i j : Fin 5) :
    complete (A.indexMatrix i j+(if j=4 then t else 0))=A.shiftedMatrix 0 t i j := by
  rcases A with ⟨b,q,c,d,u,w,s,hb,hq,hc,hd,hu,hw,hs,hsc,hsd⟩
  fin_cases i <;> fin_cases j <;> simp [indexMatrix,shiftedMatrix] <;>
    first
    | rfl
    | apply complete_of_neg
      first | omega | (simp only [X,Y,W,S,x,y,z] at * <;> omega)

theorem extendTop_matrix (A : CriticalData) (t : ℤ) (ht : 0<t) :
    (A.diagram.extendTop t ht).matrix=A.shiftedMatrix t 0 := by
  apply Matrix.ext
  intro i j
  change complete ((if i=0 then A.diagram.row i+t else A.diagram.row i)-A.diagram.col j)=_
  have hi : (if i=0 then A.diagram.row i+t else A.diagram.row i)-A.diagram.col j=
      A.diagram.row i-A.diagram.col j+(if i=0 then t else 0) := by
    split_ifs <;> ring
  rw [hi,A.diagram_index]
  exact A.top_index_complete t i j

theorem extendBottom_matrix (A : CriticalData) (t : ℤ) (ht : 0<t) :
    (A.diagram.extendBottom t ht).matrix=A.shiftedMatrix 0 t := by
  apply Matrix.ext
  intro i j
  change complete (A.diagram.row i-(if j=4 then A.diagram.col j-t else A.diagram.col j))=_
  have hj : A.diagram.row i-(if j=4 then A.diagram.col j-t else A.diagram.col j)=
      A.diagram.row i-A.diagram.col j+(if j=4 then t else 0) := by
    split_ifs <;> ring
  rw [hj,A.diagram_index]
  exact A.bottom_index_complete t i j

private theorem det_five_last_two {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R)
    (h0 : A 4 0=0) (h1 : A 4 1=0) (h2 : A 4 2=0) :
    A.det= -A 4 3*(A.submatrix (4 : Fin 5).succAbove (3 : Fin 5).succAbove).det+
      A 4 4*(A.submatrix (4 : Fin 5).succAbove (4 : Fin 5).succAbove).det := by
  rw [Matrix.det_succ_row A (4 : Fin 5),Fin.sum_univ_five,h0,h1,h2]
  norm_num <;> ring

private theorem det_four_first_two {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R)
    (h2 : A 2 0=0) (h3 : A 3 0=0) :
    A.det=A 0 0*(A.submatrix (0 : Fin 4).succAbove (0 : Fin 4).succAbove).det-
      A 1 0*(A.submatrix (1 : Fin 4).succAbove (0 : Fin 4).succAbove).det := by
  rw [Matrix.det_succ_column A (0 : Fin 4),Fin.sum_univ_four,h2,h3]
  norm_num <;> ring

private theorem castSucc_one {n : ℕ} :
    (1 : Fin (n+2)).castSucc=(1 : Fin (n+3)) := rfl

private theorem castSucc_two {n : ℕ} :
    (2 : Fin (n+3)).castSucc=(2 : Fin (n+4)) := rfl

private theorem castSucc_three {n : ℕ} :
    (3 : Fin (n+4)).castSucc=(3 : Fin (n+5)) := rfl

private theorem succ_two {n : ℕ} :
    (2 : Fin (n+3)).succ=(3 : Fin (n+4)) := rfl

private theorem succ_three {n : ℕ} :
    (3 : Fin (n+4)).succ=(4 : Fin (n+5)) := rfl

private theorem endpoint_matrix_identity {R : Type*} [CommRing R]
    (b bq bqt x xq xqt z zq zqt X Xq Xqt Y Yq Yqt y c d sigma W Wq Wqt S : R) :
    (!![bqt,xqt,Xqt,Wqt,S; b,x,X,W,Wq; 0,c,y,Y,Yq; 0,sigma,d,z,zq; 0,0,0,b,bq]).det-
      (!![bq,xq,Xq,Wq,S; b,x,X,W,Wqt; 0,c,y,Y,Yqt; 0,sigma,d,z,zqt; 0,0,0,b,bqt]).det=
    b*(y*(-(!![b,bq,bqt; x,xq,xqt; z,zq,zqt]).det)-
      c*(-(!![b,bq,bqt; X,Xq,Xqt; z,zq,zqt]).det)-
      d*(-(!![b,bq,bqt; x,xq,xqt; Y,Yq,Yqt]).det)+
      sigma*(-(!![b,bq,bqt; X,Xq,Xqt; Y,Yq,Yqt]).det)) := by
  let T : Matrix (Fin 5) (Fin 5) R :=
    !![bqt,xqt,Xqt,Wqt,S; b,x,X,W,Wq; 0,c,y,Y,Yq; 0,sigma,d,z,zq; 0,0,0,b,bq]
  let U : Matrix (Fin 5) (Fin 5) R :=
    !![bq,xq,Xq,Wq,S; b,x,X,W,Wqt; 0,c,y,Y,Yqt; 0,sigma,d,z,zqt; 0,0,0,b,bqt]
  change T.det-U.det=_
  rw [det_five_last_two T rfl rfl rfl,det_five_last_two U rfl rfl rfl,
    det_four_first_two
      (T.submatrix (4 : Fin 5).succAbove (3 : Fin 5).succAbove) rfl rfl,
    det_four_first_two
      (T.submatrix (4 : Fin 5).succAbove (4 : Fin 5).succAbove) rfl rfl,
    det_four_first_two
      (U.submatrix (4 : Fin 5).succAbove (3 : Fin 5).succAbove) rfl rfl,
    det_four_first_two
      (U.submatrix (4 : Fin 5).succAbove (4 : Fin 5).succAbove) rfl rfl]
  simp only [Matrix.det_fin_three]
  dsimp only [T,U,Matrix.submatrix]
  norm_num only [Matrix.of_apply,Equiv.refl_apply,Equiv.refl,Matrix.cons_val,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.cons_val_fin_one,
    Matrix.head_cons,Matrix.tail_cons,Fin.succAbove,Fin.lt_def,Fin.val_castSucc,Fin.val_succ,
    Fin.coe_ofNat_eq_mod,Fin.val_natCast,Fin.val_zero,ite_true,ite_false,
    Fin.castSucc_zero,castSucc_one,castSucc_two,castSucc_three,
    Fin.succ_zero_eq_one,Fin.succ_one_eq_two,succ_two,succ_three]
  ring

/-- Complementary expansion of the actual five-row endpoint matrices. -/
theorem shifted_determinant_difference (A : CriticalData) (t : ℤ) :
    (A.shiftedMatrix t 0).det-(A.shiftedMatrix 0 t).det=A.delta t := by
  simpa only [shiftedMatrix,delta,alt,add_zero,zero_add] using
    (endpoint_matrix_identity
      (complete A.b) (complete (A.b+A.q)) (complete (A.b+A.q+t))
      (complete A.x) (complete (A.x+A.q)) (complete (A.x+A.q+t))
      (complete A.z) (complete (A.z+A.q)) (complete (A.z+A.q+t))
      (complete A.X) (complete (A.X+A.q)) (complete (A.X+A.q+t))
      (complete A.Y) (complete (A.Y+A.q)) (complete (A.Y+A.q+t))
      (complete A.y) (complete A.c) (complete A.d) (complete A.sigma)
      (complete A.W) (complete (A.W+A.q)) (complete (A.W+A.q+t)) (complete (A.S+t)))

theorem endpointDifference_eq_delta (A : CriticalData) (t : ℤ) (ht : 0<t) :
    A.diagram.endpointDifference t ht=A.delta t := by
  unfold BetaDiagram.endpointDifference BetaDiagram.schur
  rw [A.extendTop_matrix t ht,A.extendBottom_matrix t ht]
  exact A.shifted_determinant_difference t

theorem diagram_leader (A : CriticalData) (hsep : A.X=A.Y → A.x≠A.z) :
    A.diagram.EndpointLeader := by
  obtain ⟨c,hc,hs⟩ := A.delta_leader hsep
  refine ⟨A.k,A.k_pos,by rw [A.diagram_largestLabel]; exact A.k_lt_S,c,hc,?_⟩
  intro t ht
  obtain ⟨r,he,hcl,hrl⟩ := hs t ht
  exact ⟨r,(A.endpointDifference_eq_delta t ht).trans he,hcl,hrl⟩

end CriticalData

private theorem middle_eq_of_parameters (t s : Parameters) (ht : ValidM t) (hs : ValidM s)
    (h : t=s) : M t ht=M s hs := by
  subst s
  rfl

theorem middle_balanced_leader (t : Parameters) (h : ValidM t)
    (hZ : (M t h).ZeroFree) (htie : (M t h).topMargin=(M t h).bottomMargin)
    (hap : t.a=t.p) (hS : ¬(M t h).Symmetric) : (M t h).EndpointLeader := by
  let A := ofMiddle t h hZ
  have hpar : A.parameters=t := critical_parameters_recover t h hZ htie hap
  have he : A.diagram=M t h :=
    middle_eq_of_parameters _ _ A.parameters_valid h hpar
  have hsep : A.X=A.Y → A.x≠A.z := critical_nonsymmetry t h hZ htie hap hS
  rw [←he]
  exact A.diagram_leader hsep

theorem middle_leader (t : Parameters) (h : ValidM t) (hZ : (M t h).ZeroFree)
    (hS : ¬(M t h).Symmetric) : (M t h).EndpointLeader := by
  by_cases htie : (M t h).topMargin=(M t h).bottomMargin
  · by_cases hap : t.a=t.p
    · exact middle_balanced_leader t h hZ htie hap hS
    · exact middle_ordinary_leader t h hZ hap
  · exact (M t h).endpointLeader_untied (M_connected t h) hZ htie

end FiveEndpoint

namespace BetaDiagram

/-- `lem:five-negative-leading`: the offset may be below the ordinary boundary level. -/
theorem endpointLeader_five_negative (Q : BetaDiagram 5) (hConnected : Q.Connected)
    (hZeroFree : Q.ZeroFree) (hCount5 : negativeCount Q=5) (hNonsymmetric : ¬Q.Symmetric) :
    Q.EndpointLeader := by
  rcases FiveNegative.normal_form_exhaustion Q hConnected hCount5 with hM | hE | hER
  · obtain ⟨t,h,htr⟩ := hM
    have hZ := zeroFree_of_translation Q (FiveNegative.M t h) htr hZeroFree
    have hS : ¬(FiveNegative.M t h).Symmetric := by
      intro hs
      exact hNonsymmetric (symmetric_of_translation Q _ htr hs)
    exact EndpointLeader.of_translation Q _ htr (FiveEndpoint.middle_leader t h hZ hS)
  · obtain ⟨t,h,htr⟩ := hE
    have hZ := zeroFree_of_translation Q (FiveNegative.E t h) htr hZeroFree
    exact EndpointLeader.of_translation Q _ htr (FiveEndpoint.end_leader t h hZ)
  · obtain ⟨t,h,htr⟩ := hER
    have hZR := zeroFree_rotate Q hZeroFree
    have hZ := zeroFree_of_translation Q.rotate (FiveNegative.E t h) htr hZR
    apply EndpointLeader.of_rotate Q
    exact EndpointLeader.of_translation Q.rotate _ htr (FiveEndpoint.end_leader t h hZ)

end BetaDiagram

end SkewJacobiNegative
