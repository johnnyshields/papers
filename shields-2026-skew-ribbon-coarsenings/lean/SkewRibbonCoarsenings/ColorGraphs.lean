/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.SkewTernary

/-!
# Color graphs of an inseparable sum of two disjoint-support skew-ternary matrices

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:balance`, subsection
`subsec:support` (`eq:matrix-triangle`, `lem:color`).

`MatrixTriangle U V` is `eq:matrix-triangle`; `IsColorPair U V` bundles the standing assumptions
(`U`, `V` skew-ternary with disjoint supports satisfying `eq:matrix-triangle`).  The color graphs
of `A = U + V` are the support graphs of `U` and `V`.  `SuppDisconnected R W` says the support
graph of `R` on the vertex set `W` is disconnected (a nontrivial partition of `W` with no support
edge across it).  `color_disconnected` is `lem:color`, proved for every principal submatrix `W` by
induction on `|W|`, with the cases of at most four vertices settled by a finite case check
(`four_core`) and the larger cases by `exists_inseparable_erase` (`lem:deletion`).

Sorry-free.
-/

namespace SkewRibbonCoarsenings

variable {X : Type*}

/-- The triangle sum of `eq:matrix-triangle` at the triple `(i, j, k)`:
`∑_{cyc(i,j,k)} (U_ij V_jk + V_ij U_jk)`. -/
def triSum (U V : X → X → ℤ) (i j k : X) : ℤ :=
  (U i j * V j k + V i j * U j k) + (U j k * V k i + V j k * U k i) +
    (U k i * V i j + V k i * U i j)

/-- `eq:matrix-triangle`: the triangle sum vanishes at every triple. -/
def MatrixTriangle (U V : X → X → ℤ) : Prop := ∀ i j k, triSum U V i j k = 0

/-- The standing assumptions of `subsec:support` for the color graphs: `U, V` are skew-ternary
matrices with disjoint supports satisfying `eq:matrix-triangle`. -/
structure IsColorPair (U V : X → X → ℤ) : Prop where
  hU : IsSkewTernary U
  hV : IsSkewTernary V
  disj : ∀ x y, U x y * V x y = 0
  tri : MatrixTriangle U V

/-- The support graph of `R` restricted to `W` is disconnected: a nontrivial partition of `W`
(by the predicate `P`) across which `R` vanishes. -/
def SuppDisconnected (R : X → X → ℤ) (W : Finset X) : Prop :=
  ∃ P : X → Prop, IsCutOf (fun p q => R p q = 0) W P

theorem triSum_comm (U V : X → X → ℤ) (i j k : X) : triSum V U i j k = triSum U V i j k := by
  unfold triSum
  ring

theorem IsColorPair.symm {U V : X → X → ℤ} (h : IsColorPair U V) : IsColorPair V U where
  hU := h.hV
  hV := h.hU
  disj x y := by rw [mul_comm]; exact h.disj x y
  tri i j k := by rw [triSum_comm]; exact h.tri i j k

theorem IsColorPair.vanish_of_ne {U V : X → X → ℤ} (h : IsColorPair U V) {x y : X}
    (hx : U x y ≠ 0) : V x y = 0 := by
  rcases mul_eq_zero.1 (h.disj x y) with h1 | h1
  · exact absurd h1 hx
  · exact h1

/-- The sum of a color pair is a skew-ternary matrix. -/
theorem IsColorPair.isSkewTernary {U V : X → X → ℤ} (h : IsColorPair U V) :
    IsSkewTernary (fun x y => U x y + V x y) where
  skew x y := by
    have := h.hU.skew x y
    have := h.hV.skew x y
    omega
  ternary x y := by
    have h1 := h.hU.ternary x y
    have h2 := h.hV.ternary x y
    have h3 := h.disj x y
    rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
      simp [h1, h2] at h3 ⊢

/-! ### The four-vertex case check -/

/-- The five possible pairs `(U_ij, V_ij)` of entries of a color pair. -/
def L5 : List (ℤ × ℤ) := [(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)]

theorem IsColorPair.mem_L5 {U V : X → X → ℤ} (h : IsColorPair U V) (x y : X) :
    (U x y, V x y) ∈ L5 := by
  have h1 := h.hU.ternary x y
  have h2 := h.hV.ternary x y
  have h3 := h.disj x y
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    simp [h1, h2, L5] at h3 ⊢

/-- The triangle sum on the triple `1, 2, 3` written with the entries `12, 23, 13`. -/
def tri3 (u12 v12 u23 v23 u13 v13 : ℤ) : ℤ :=
  u12 * v23 + v12 * u23 - u23 * v13 - v23 * u13 - u13 * v12 - v13 * u12

/-- The seven constant-cut shapes of a four-vertex matrix, written with the six entries
`A 12, A 13, A 14, A 23, A 24, A 34` (upper triangle). -/
def ConstCut7 (e12 e13 e14 e23 e24 e34 : ℤ) : Prop :=
  (e12 = e13 ∧ e13 = e14) ∨ (-e12 = e23 ∧ e23 = e24) ∨ (-e13 = -e23 ∧ -e23 = e34) ∨
  (-e14 = -e24 ∧ -e24 = -e34) ∨ (e13 = e14 ∧ e14 = e23 ∧ e23 = e24) ∨
  (e12 = e14 ∧ e14 = -e23 ∧ -e23 = e34) ∨ (e12 = e13 ∧ e13 = -e24 ∧ -e24 = -e34)

/-- The seven zero-cut shapes of a four-vertex matrix with upper triangle `e12, …, e34`. -/
def ZeroCut7 (e12 e13 e14 e23 e24 e34 : ℤ) : Prop :=
  (e12 = 0 ∧ e13 = 0 ∧ e14 = 0) ∨ (e12 = 0 ∧ e23 = 0 ∧ e24 = 0) ∨ (e13 = 0 ∧ e23 = 0 ∧ e34 = 0) ∨
  (e14 = 0 ∧ e24 = 0 ∧ e34 = 0) ∨ (e13 = 0 ∧ e14 = 0 ∧ e23 = 0 ∧ e24 = 0) ∨
  (e12 = 0 ∧ e14 = 0 ∧ e23 = 0 ∧ e34 = 0) ∨ (e12 = 0 ∧ e13 = 0 ∧ e24 = 0 ∧ e34 = 0)

instance (a b c d e f : ℤ) : Decidable (ConstCut7 a b c d e f) := by
  unfold ConstCut7; infer_instance

instance (a b c d e f : ℤ) : Decidable (ZeroCut7 a b c d e f) := by
  unfold ZeroCut7; infer_instance

/-- The finite check behind the four-vertex case of `lem:color`: on four vertices, two
disjoint-support skew-ternary matrices satisfying `eq:matrix-triangle` whose sum has no constant
cut cannot both have all seven zero-cut shapes excluded. -/
theorem four_core : ∀ p12 ∈ L5, ∀ p13 ∈ L5, ∀ p14 ∈ L5, ∀ p23 ∈ L5, ∀ p24 ∈ L5, ∀ p34 ∈ L5,
    tri3 p12.1 p12.2 p23.1 p23.2 p13.1 p13.2 = 0 →
    tri3 p12.1 p12.2 p24.1 p24.2 p14.1 p14.2 = 0 →
    tri3 p13.1 p13.2 p34.1 p34.2 p14.1 p14.2 = 0 →
    tri3 p23.1 p23.2 p34.1 p34.2 p24.1 p24.2 = 0 →
    ¬ConstCut7 (p12.1 + p12.2) (p13.1 + p13.2) (p14.1 + p14.2) (p23.1 + p23.2) (p24.1 + p24.2)
      (p34.1 + p34.2) →
    ZeroCut7 p12.1 p13.1 p14.1 p23.1 p24.1 p34.1 ∨
      ZeroCut7 p12.2 p13.2 p14.2 p23.2 p24.2 p34.2 := by
  decide +kernel

theorem IsColorPair.tri3_eq {U V : X → X → ℤ} (h : IsColorPair U V) (a b c : X) :
    tri3 (U a b) (V a b) (U b c) (V b c) (U a c) (V a c) = 0 := by
  have := h.tri a b c
  simp only [triSum, h.hU.skew a c, h.hV.skew a c] at this
  unfold tri3
  linear_combination this

set_option linter.unusedSimpArgs false in
theorem constCut7_of_props (e12 e13 e14 e23 e24 e34 k : ℤ) (pa pb pc pd : Prop)
    (hP : pa ∨ pb ∨ pc ∨ pd) (hQ : ¬pa ∨ ¬pb ∨ ¬pc ∨ ¬pd)
    (hab : pa → ¬pb → e12 = k) (hba : pb → ¬pa → -e12 = k)
    (hac : pa → ¬pc → e13 = k) (hca : pc → ¬pa → -e13 = k)
    (had : pa → ¬pd → e14 = k) (hda : pd → ¬pa → -e14 = k)
    (hbc : pb → ¬pc → e23 = k) (hcb : pc → ¬pb → -e23 = k)
    (hbd : pb → ¬pd → e24 = k) (hdb : pd → ¬pb → -e24 = k)
    (hcd : pc → ¬pd → e34 = k) (hdc : pd → ¬pc → -e34 = k) :
    ConstCut7 e12 e13 e14 e23 e24 e34 := by
  unfold ConstCut7
  by_cases ha : pa <;> by_cases hb : pb <;> by_cases hc : pc <;> by_cases hd : pd
  all_goals
    simp only [ha, hb, hc, hd, false_implies, not_true, not_false_eq_true, or_true, or_false,
      false_or, imp_false, imp_true_iff, forall_const, true_and, and_true, false_and, and_false,
      not_false_iff] at *
  all_goals
    first
    | exact Or.inl ⟨by omega, by omega⟩
    | exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
    | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)))))

section Cuts

variable [DecidableEq X]

theorem isCutOf_two (S : X → X → Prop) {a b : X} (hab : a ≠ b) (h : S a b) :
    IsCutOf S {a, b} (· = a) := by
  refine ⟨⟨a, by simp, rfl⟩, ⟨b, by simp, fun e => hab e.symm⟩, ?_⟩
  intro p hp q hq hP hQ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  subst hP
  rcases hq with rfl | rfl
  · exact absurd rfl hQ
  · exact h

theorem isCutOf_three (S : X → X → Prop) {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (S a b → S a c → IsCutOf S {a, b, c} (· = a)) ∧
    (S b a → S b c → IsCutOf S {a, b, c} (· = b)) ∧
    (S c a → S c b → IsCutOf S {a, b, c} (· = c)) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h1 h2
  · refine ⟨⟨a, by simp, rfl⟩, ⟨b, by simp, fun e => hab e.symm⟩, ?_⟩
    intro p hp q hq hP hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    subst hP
    rcases hq with rfl | rfl | rfl <;> simp_all
  · refine ⟨⟨b, by simp, rfl⟩, ⟨a, by simp, hab⟩, ?_⟩
    intro p hp q hq hP hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    subst hP
    rcases hq with rfl | rfl | rfl <;> simp_all
  · refine ⟨⟨c, by simp, rfl⟩, ⟨a, by simp, hac⟩, ?_⟩
    intro p hp q hq hP hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    subst hP
    rcases hq with rfl | rfl | rfl <;> simp_all

theorem isCutOf_four (S : X → X → Prop) {a b c d : X} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (S a b → S a c → S a d → IsCutOf S {a, b, c, d} (· = a)) ∧
    (S b a → S b c → S b d → IsCutOf S {a, b, c, d} (· = b)) ∧
    (S c a → S c b → S c d → IsCutOf S {a, b, c, d} (· = c)) ∧
    (S d a → S d b → S d c → IsCutOf S {a, b, c, d} (· = d)) ∧
    (S a c → S a d → S b c → S b d → IsCutOf S {a, b, c, d} (fun x => x = a ∨ x = b)) ∧
    (S a b → S a d → S c b → S c d → IsCutOf S {a, b, c, d} (fun x => x = a ∨ x = c)) ∧
    (S a b → S a c → S d b → S d c → IsCutOf S {a, b, c, d} (fun x => x = a ∨ x = d)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h2 h3
    refine ⟨⟨a, by simp, rfl⟩, ⟨b, by simp, fun e => hab e.symm⟩, ?_⟩
    intro p hp q hq hP hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    subst hP
    rcases hq with rfl | rfl | rfl | rfl <;> simp_all
  · intro h1 h2 h3
    refine ⟨⟨b, by simp, rfl⟩, ⟨a, by simp, hab⟩, ?_⟩
    intro p hp q hq hP hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    subst hP
    rcases hq with rfl | rfl | rfl | rfl <;> simp_all
  · intro h1 h2 h3
    refine ⟨⟨c, by simp, rfl⟩, ⟨a, by simp, hac⟩, ?_⟩
    intro p hp q hq hP hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    subst hP
    rcases hq with rfl | rfl | rfl | rfl <;> simp_all
  · intro h1 h2 h3
    refine ⟨⟨d, by simp, rfl⟩, ⟨a, by simp, had⟩, ?_⟩
    intro p hp q hq hP hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    subst hP
    rcases hq with rfl | rfl | rfl | rfl <;> simp_all
  · intro h1 h2 h3 h4
    refine ⟨⟨a, by simp, Or.inl rfl⟩, ⟨c, by simp, ?_⟩, ?_⟩
    · rintro (h | h)
      · exact hac h.symm
      · exact hbc h.symm
    intro p hp q hq hP hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hP with rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;> simp_all
  · intro h1 h2 h3 h4
    refine ⟨⟨a, by simp, Or.inl rfl⟩, ⟨b, by simp, ?_⟩, ?_⟩
    · rintro (h | h)
      · exact hab h.symm
      · exact hbc h
    intro p hp q hq hP hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hP with rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;> simp_all
  · intro h1 h2 h3 h4
    refine ⟨⟨a, by simp, Or.inl rfl⟩, ⟨b, by simp, ?_⟩, ?_⟩
    · rintro (h | h)
      · exact hab h.symm
      · exact hbd h
    intro p hp q hq hP hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hP with rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;> simp_all

/-- A constant cut of a four-vertex matrix has one of the seven shapes of `ConstCut7`. -/
theorem constCut7_of_isConstCut {A : X → X → ℤ} (hA : ∀ x y, A y x = -A x y) {a b c d : X}
    {P : X → Prop} (h : IsConstCut A {a, b, c, d} P) :
    ConstCut7 (A a b) (A a c) (A a d) (A b c) (A b d) (A c d) := by
  obtain ⟨k, ⟨p, hp, hPp⟩, ⟨q, hq, hPq⟩, h⟩ := h
  have ha : a ∈ ({a, b, c, d} : Finset X) := by simp
  have hb : b ∈ ({a, b, c, d} : Finset X) := by simp
  have hc : c ∈ ({a, b, c, d} : Finset X) := by simp
  have hd : d ∈ ({a, b, c, d} : Finset X) := by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  have hP : P a ∨ P b ∨ P c ∨ P d := by rcases hp with rfl | rfl | rfl | rfl <;> simp [hPp]
  have hQ : ¬P a ∨ ¬P b ∨ ¬P c ∨ ¬P d := by rcases hq with rfl | rfl | rfl | rfl <;> simp [hPq]
  have s1 := hA a b
  have s2 := hA a c
  have s3 := hA a d
  have s4 := hA b c
  have s5 := hA b d
  have s6 := hA c d
  refine constCut7_of_props _ _ _ _ _ _ k (P a) (P b) (P c) (P d) hP hQ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_
  · exact fun h1 h2 => h a ha b hb h1 h2
  · exact fun h1 h2 => by have := h b hb a ha h1 h2; omega
  · exact fun h1 h2 => h a ha c hc h1 h2
  · exact fun h1 h2 => by have := h c hc a ha h1 h2; omega
  · exact fun h1 h2 => h a ha d hd h1 h2
  · exact fun h1 h2 => by have := h d hd a ha h1 h2; omega
  · exact fun h1 h2 => h b hb c hc h1 h2
  · exact fun h1 h2 => by have := h c hc b hb h1 h2; omega
  · exact fun h1 h2 => h b hb d hd h1 h2
  · exact fun h1 h2 => by have := h d hd b hb h1 h2; omega
  · exact fun h1 h2 => h c hc d hd h1 h2
  · exact fun h1 h2 => by have := h d hd c hc h1 h2; omega

/-- Conversely, each shape of `ConstCut7` is a constant cut. -/
theorem isConstCut_of_constCut7 {A : X → X → ℤ} (hA : ∀ x y, A y x = -A x y) {a b c d : X}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h : ConstCut7 (A a b) (A a c) (A a d) (A b c) (A b d) (A c d)) :
    ∃ P, IsConstCut A {a, b, c, d} P := by
  have s1 := hA a b
  have s2 := hA a c
  have s3 := hA a d
  have s4 := hA b c
  have s5 := hA b d
  have s6 := hA c d
  unfold ConstCut7 at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩
  · exact ⟨_, A a b, (isCutOf_four (fun p q => A p q = A a b) hab hac had hbc hbd hcd).1
      (by omega) (by omega) (by omega)⟩
  · exact ⟨_, A b c, (isCutOf_four (fun p q => A p q = A b c) hab hac had hbc hbd hcd).2.1
      (by omega) (by omega) (by omega)⟩
  · exact ⟨_, A c d, (isCutOf_four (fun p q => A p q = A c d) hab hac had hbc hbd hcd).2.2.1
      (by omega) (by omega) (by omega)⟩
  · exact ⟨_, -A c d, (isCutOf_four (fun p q => A p q = -A c d) hab hac had hbc hbd hcd).2.2.2.1
      (by omega) (by omega) (by omega)⟩
  · exact ⟨_, A a c, (isCutOf_four (fun p q => A p q = A a c) hab hac had hbc hbd hcd).2.2.2.2.1
      (by omega) (by omega) (by omega) (by omega)⟩
  · exact ⟨_, A a b,
      (isCutOf_four (fun p q => A p q = A a b) hab hac had hbc hbd hcd).2.2.2.2.2.1
      (by omega) (by omega) (by omega) (by omega)⟩
  · exact ⟨_, A a b,
      (isCutOf_four (fun p q => A p q = A a b) hab hac had hbc hbd hcd).2.2.2.2.2.2
      (by omega) (by omega) (by omega) (by omega)⟩

/-- Each shape of `ZeroCut7` gives a disconnection of the support graph on four vertices. -/
theorem suppDisconnected_of_zeroCut7 {R : X → X → ℤ} (hR : ∀ x y, R y x = -R x y) {a b c d : X}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h : ZeroCut7 (R a b) (R a c) (R a d) (R b c) (R b d) (R c d)) :
    ∃ P : X → Prop, IsCutOf (fun p q => R p q = 0) {a, b, c, d} P := by
  have s1 := hR a b
  have s2 := hR a c
  have s3 := hR a d
  have s4 := hR b c
  have s5 := hR b d
  have s6 := hR c d
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ :=
    isCutOf_four (fun p q => R p q = 0) hab hac had hbc hbd hcd
  unfold ZeroCut7 at h
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ |
    ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact ⟨_, k1 (by omega) (by omega) (by omega)⟩
  · exact ⟨_, k2 (by omega) (by omega) (by omega)⟩
  · exact ⟨_, k3 (by omega) (by omega) (by omega)⟩
  · exact ⟨_, k4 (by omega) (by omega) (by omega)⟩
  · exact ⟨_, k5 (by omega) (by omega) (by omega) (by omega)⟩
  · exact ⟨_, k6 (by omega) (by omega) (by omega) (by omega)⟩
  · exact ⟨_, k7 (by omega) (by omega) (by omega) (by omega)⟩

end Cuts

section Components

variable [DecidableEq X]

/-- `K` is closed for `R` in `W`: `K ⊆ W` and `R` vanishes from `K` to `W ∖ K`
(a union of connected components of the support graph of `R` on `W`, when `R` is skew). -/
def IsClosedIn (R : X → X → ℤ) (W K : Finset X) : Prop :=
  K ⊆ W ∧ ∀ a ∈ K, ∀ b ∈ W, b ∉ K → R a b = 0

omit [DecidableEq X] in
theorem suppDisconnected_iff (R : X → X → ℤ) (W : Finset X) :
    SuppDisconnected R W ↔ ∃ K, IsClosedIn R W K ∧ K.Nonempty ∧ K ≠ W := by
  constructor
  · rintro ⟨P, ⟨p, hp, hPp⟩, ⟨q, hq, hPq⟩, h⟩
    classical
    refine ⟨W.filter P, ⟨Finset.filter_subset _ _, ?_⟩, ⟨p, by simp [hp, hPp]⟩, ?_⟩
    · intro a ha b hb hbK
      simp only [Finset.mem_filter, not_and] at ha hbK
      exact h a ha.1 b hb ha.2 (hbK hb)
    · intro heq
      have : q ∈ W.filter P := by rw [heq]; exact hq
      exact hPq (Finset.mem_filter.1 this).2
  · rintro ⟨K, ⟨hKW, hcl⟩, ⟨p, hp⟩, hne⟩
    obtain ⟨q, hqW, hqK⟩ : ∃ q ∈ W, q ∉ K := by
      by_contra hno
      push Not at hno
      exact hne (Finset.Subset.antisymm hKW hno)
    exact ⟨fun x => x ∈ K, ⟨p, hKW hp, hp⟩, ⟨q, hqW, hqK⟩,
      fun a ha b hb haK hbK => hcl a haK b hb hbK⟩

theorem IsClosedIn.inter {R : X → X → ℤ} {W K K' : Finset X} (h : IsClosedIn R W K)
    (h' : IsClosedIn R W K') : IsClosedIn R W (K ∩ K') := by
  refine ⟨fun x hx => h.1 (Finset.mem_inter.1 hx).1, fun a ha b hb hbK => ?_⟩
  rw [Finset.mem_inter] at ha hbK
  by_cases hbK1 : b ∈ K
  · exact h'.2 a ha.2 b hb (fun hh => hbK ⟨hbK1, hh⟩)
  · exact h.2 a ha.1 b hb hbK1

theorem IsClosedIn.sdiff {R : X → X → ℤ} (hR : ∀ x y, R y x = -R x y) {W K : Finset X}
    (h : IsClosedIn R W K) : IsClosedIn R W (W \ K) := by
  refine ⟨Finset.sdiff_subset, fun a ha b hb hbK => ?_⟩
  rw [Finset.mem_sdiff] at ha hbK
  have hbK' : b ∈ K := by
    by_contra hh
    exact hbK ⟨hb, hh⟩
  have := h.2 b hbK' a ha.1 ha.2
  have := hR b a
  omega

omit [DecidableEq X] in
/-- Every vertex of `W` lies in an atom: a closed set containing it with no proper nonempty
closed subset (its connected component). -/
theorem exists_atom {R : X → X → ℤ} (hR : ∀ x y, R y x = -R x y) {W : Finset X} {x : X}
    (hx : x ∈ W) :
    ∃ K, IsClosedIn R W K ∧ x ∈ K ∧
      ∀ K', IsClosedIn R W K' → K' ⊆ K → K'.Nonempty → K' = K := by
  classical
  let S : Finset (Finset X) := W.powerset.filter fun K => IsClosedIn R W K ∧ x ∈ K
  have hS : S.Nonempty := ⟨W, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.Subset.refl _),
    ⟨Finset.Subset.refl _, fun a _ b hb hbK => absurd hb hbK⟩, hx⟩⟩
  obtain ⟨K, hKS, hKmin⟩ := Finset.exists_min_image S Finset.card hS
  simp only [S, Finset.mem_filter, Finset.mem_powerset] at hKS
  obtain ⟨-, hKcl, hxK⟩ := hKS
  refine ⟨K, hKcl, hxK, fun K' hK' hsub hne => ?_⟩
  by_cases hxK' : x ∈ K'
  · have hmem : K' ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hK'.1, hK', hxK'⟩
    exact Finset.eq_of_subset_of_card_le hsub (hKmin K' hmem)
  · have hcl := hKcl.inter (hK'.sdiff hR)
    have hmem : K ∩ (W \ K') ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hcl.1, hcl, Finset.mem_inter.2 ⟨hxK, Finset.mem_sdiff.2 ⟨hx, hxK'⟩⟩⟩
    obtain ⟨p, hp⟩ := hne
    have hlt : (K ∩ (W \ K')).card < K.card := by
      apply Finset.card_lt_card
      refine ⟨Finset.inter_subset_left, fun hh => ?_⟩
      have := hh (hsub hp)
      rw [Finset.mem_inter, Finset.mem_sdiff] at this
      exact this.2.2 hp
    exact absurd (hKmin _ hmem) (not_le.2 hlt)

omit [DecidableEq X] in
/-- The pair lemma behind the clan property of color components: if `U a b ≠ 0` and `z` has no
`U`-entry to `a` or `b`, then `eq:matrix-triangle` at `(z, a, b)` gives `A z a = A z b`. -/
theorem IsColorPair.pair_eq {U V : X → X → ℤ} (h : IsColorPair U V) {z a b : X}
    (hab : U a b ≠ 0) (hza : U z a = 0) (hzb : U z b = 0) :
    U z a + V z a = U z b + V z b := by
  have hVab : V a b = 0 := h.vanish_of_ne hab
  have hUbz : U b z = 0 := by
    have := h.hU.skew z b
    omega
  have hVbz := h.hV.skew z b
  have e := h.tri z a b
  simp only [triSum, hza, hVab, hUbz] at e
  have key : U a b * (V z a - V z b) = 0 := by
    rw [hVbz] at e
    linear_combination e
  rcases mul_eq_zero.1 key with h1 | h1
  · exact absurd h1 hab
  · omega

omit [DecidableEq X] in
/-- Every atom of the support graph of `U` on `W` is a clan of `A = U + V` on `W`: the clan
property of color components, in `lem:color`. -/
theorem atom_isClan {U V A : X → X → ℤ} (h : IsColorPair U V)
    (hA : ∀ x y, A x y = U x y + V x y) {W K : Finset X} (hK : IsClosedIn U W K)
    (hatom : ∀ K', IsClosedIn U W K' → K' ⊆ K → K'.Nonempty → K' = K) :
    IsClan A W K := by
  classical
  refine ⟨hK.1, fun z hz hzK x hx y hy => ?_⟩
  let S : Finset X := K.filter fun t => A z t = A z x
  have hxS : x ∈ S := Finset.mem_filter.2 ⟨hx, rfl⟩
  have hUz : ∀ a ∈ K, U z a = 0 := by
    intro a ha
    have := hK.2 a ha z hz hzK
    have := h.hU.skew a z
    omega
  have hSc : IsClosedIn U W S := by
    refine ⟨fun t ht => hK.1 (Finset.mem_filter.1 ht).1, fun a ha b hb hbS => ?_⟩
    have haK := (Finset.mem_filter.1 ha).1
    have haS := (Finset.mem_filter.1 ha).2
    by_cases hbK : b ∈ K
    · by_contra hne
      have := h.pair_eq hne (hUz a haK) (hUz b hbK)
      have e1 := hA z a
      have e2 := hA z b
      exact hbS (Finset.mem_filter.2 ⟨hbK, by omega⟩)
    · exact hK.2 a haK b hb hbK
  have hSK : S ⊆ K := Finset.filter_subset _ _
  have := hatom S hSc hSK ⟨x, hxS⟩
  have hyS : y ∈ S := by rw [this]; exact hy
  exact (Finset.mem_filter.1 hyS).2.symm

/-- The color step of `lem:color`: if `A[W ∖ z]` is inseparable with the red color of `A = U + V`
disconnected on `W ∖ z`, then one of the two colors is disconnected on `W`. -/
theorem color_step {U V A : X → X → ℤ} (h : IsColorPair U V)
    (hA : ∀ x y, A x y = U x y + V x y) {W : Finset X} {z : X} (hz : z ∈ W)
    (hins : IsInseparable A (W.erase z)) (hd : SuppDisconnected U (W.erase z)) :
    SuppDisconnected U W ∨ SuppDisconnected V W := by
  by_contra hcon
  obtain ⟨hU, hV⟩ := not_or.1 hcon
  have hUs := h.hU.skew
  have hVs := h.hV.skew
  have hAs : ∀ x y, A y x = -A x y := fun x y => by
    rw [hA, hA]
    have := hUs x y
    have := hVs x y
    omega
  -- a blue neighbor of `z`
  have hW'ne : (W.erase z).Nonempty := Finset.card_pos.1 (by have := hins.1; omega)
  obtain ⟨x, hxW', hVzx⟩ : ∃ x ∈ W.erase z, V z x ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hV
    refine ⟨fun t => t = z, ⟨z, hz, rfl⟩, ?_, ?_⟩
    · obtain ⟨q, hq⟩ := hW'ne
      exact ⟨q, Finset.mem_of_mem_erase hq, Finset.ne_of_mem_erase hq⟩
    · intro p _ q hq hpz hqz
      subst hpz
      exact hno q (Finset.mem_erase.2 ⟨hqz, hq⟩)
  have hUzx : U z x = 0 := h.symm.vanish_of_ne hVzx
  have hx' := Finset.mem_of_mem_erase hxW'
  -- the red component of `x` in `W ∖ z`
  obtain ⟨Cx, hCxcl, hxCx, hCxatom⟩ := exists_atom hUs hxW'
  have hCxne : Cx.Nonempty := ⟨x, hxCx⟩
  obtain ⟨K0, hK0cl, hK0ne, hK0W⟩ := (suppDisconnected_iff _ _).1 hd
  have hCxW : Cx ≠ W.erase z := by
    intro heq
    apply hK0W
    have := hCxatom K0 hK0cl (by rw [heq]; exact hK0cl.1) hK0ne
    rw [this, heq]
  obtain ⟨w0, hw0W, hw0C⟩ : ∃ w0 ∈ W.erase z, w0 ∉ Cx := by
    by_contra hno
    push Not at hno
    exact hCxW (Finset.Subset.antisymm hCxcl.1 hno)
  have hCxclan := atom_isClan h hA hCxcl hCxatom
  refine hins.2 ⟨fun t => t ∈ Cx, A x z, ⟨x, hxW', hxCx⟩, ⟨w0, hw0W, hw0C⟩, ?_⟩
  intro c hc w hw hcC hwC
  -- the red component of `w`
  obtain ⟨Cw, hCwcl, hwCw, hCwatom⟩ := exists_atom hUs hw
  have hCwclan := atom_isClan h hA hCwcl hCwatom
  -- `z` has a red neighbor in `Cw`
  obtain ⟨y, hyCw, hUzy⟩ : ∃ y ∈ Cw, U z y ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hU
    rw [suppDisconnected_iff]
    refine ⟨Cw, ⟨fun t ht => Finset.mem_of_mem_erase (hCwcl.1 ht), fun a ha b hb hbC => ?_⟩,
      ⟨w, hwCw⟩, fun heq => ?_⟩
    · by_cases hbz : b = z
      · subst hbz
        have := hno a ha
        have := hUs a b
        omega
      · exact hCwcl.2 a ha b (Finset.mem_erase.2 ⟨hbz, hb⟩) hbC
    · have hzC : z ∈ Cw := by rw [heq]; exact hz
      exact Finset.notMem_erase z W (hCwcl.1 hzC)
  have hyW' := hCwcl.1 hyCw
  -- `x ∉ Cw`
  have hxCw : x ∉ Cw := by
    intro hxCw
    have hcl := hCxcl.inter hCwcl
    have hsub : Cx ∩ Cw ⊆ Cw := Finset.inter_subset_right
    have heq := hCwatom _ hcl hsub ⟨x, Finset.mem_inter.2 ⟨hxCx, hxCw⟩⟩
    have : w ∈ Cx ∩ Cw := by rw [heq]; exact hwCw
    exact hwC (Finset.mem_inter.1 this).1
  have hUxy : U x y = 0 := by
    have := hCwcl.2 y hyCw x hxW' hxCw
    have := hUs y x
    omega
  have hVzy : V z y = 0 := h.vanish_of_ne hUzy
  -- the triangle at `(z, x, y)`
  have hAxy : A x y = A x z := by
    have e := h.tri z x y
    have hVyz : V y z = 0 := by
      have := hVs z y
      omega
    have hUyz : U y z ≠ 0 := by
      have := hUs z y
      omega
    simp only [triSum, hUzx, hUxy, hVyz] at e
    have key : U y z * (V x y + V z x) = 0 := by linear_combination e
    rcases mul_eq_zero.1 key with h1 | h1
    · exact absurd h1 hUyz
    · have := hVs z x
      have := hUs z x
      rw [hA, hA]
      omega
  have e1 := hCxclan.2 w hw hwC c hcC x hxCx
  have e2 := hCwclan.2 x hxW' hxCw w hwCw y hyCw
  have := hAs c w
  have := hAs x w
  have := hAs w c
  have := hAs w x
  omega

end Components

section Main

variable [DecidableEq X]

theorem three_core : ∀ p12 ∈ L5, ∀ p13 ∈ L5, ∀ p23 ∈ L5,
    (p12.1 ≠ 0 ∨ p13.1 ≠ 0) → (p12.1 ≠ 0 ∨ p23.1 ≠ 0) → (p13.1 ≠ 0 ∨ p23.1 ≠ 0) →
    (p12.2 ≠ 0 ∨ p13.2 ≠ 0) → (p12.2 ≠ 0 ∨ p23.2 ≠ 0) → (p13.2 ≠ 0 ∨ p23.2 ≠ 0) → False := by
  decide +kernel

omit [DecidableEq X] in
/-- `lem:color` for a principal submatrix: if `A = U + V` is inseparable on `W`, at least one of
the two color graphs (the support graphs of `U` and of `V`) is disconnected on `W`.  This is
proved by strong induction on `|W|`; the cases `|W| ≤ 4` are the finite checks `three_core`
and `four_core`, and `|W| ≥ 5` uses `exists_inseparable_erase` (`lem:deletion`) and `color_step`.

**Differs from the paper's route.**  The paper settles four vertices by hand through the
path-and-star analysis; here the finite case check `four_core` (all triples of the five possible
color pairs on six entries) is verified by kernel evaluation. -/
theorem color_disconnected_aux {U V A : X → X → ℤ} (h : IsColorPair U V)
    (hA : ∀ x y, A x y = U x y + V x y) :
    ∀ n : ℕ, ∀ W : Finset X, W.card = n → IsInseparable A W →
      SuppDisconnected U W ∨ SuppDisconnected V W := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hWn hins
    have hUs := h.hU.skew
    have hVs := h.hV.skew
    have hAst : IsSkewTernary A :=
      { skew := fun x y => by
          rw [hA, hA]
          have := hUs x y
          have := hVs x y
          omega
        ternary := fun x y => by
          rw [hA]
          exact h.isSkewTernary.ternary x y }
    have hAs := hAst.skew
    have h2 := hins.1
    by_cases hn2 : n = 2
    · exfalso
      subst hn2
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hWn
      exact hins.2 ⟨_, A a b, isCutOf_two (fun p q => A p q = A a b) hab rfl⟩
    by_cases hn3 : n = 3
    · subst hn3
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hWn
      by_contra hcon
      obtain ⟨hU, hV⟩ := not_or.1 hcon
      have kU := isCutOf_three (fun p q => U p q = 0) hab hac hbc
      have kV := isCutOf_three (fun p q => V p q = 0) hab hac hbc
      have u1 := hUs a b
      have u2 := hUs a c
      have u3 := hUs b c
      have v1 := hVs a b
      have v2 := hVs a c
      have v3 := hVs b c
      refine three_core _ (h.mem_L5 a b) _ (h.mem_L5 a c) _ (h.mem_L5 b c) ?_ ?_ ?_ ?_ ?_ ?_
      · by_contra hh
        push Not at hh
        exact hU ⟨_, kU.1 hh.1 hh.2⟩
      · by_contra hh
        push Not at hh
        exact hU ⟨_, kU.2.1 (by simp only at hh ⊢; omega) hh.2⟩
      · by_contra hh
        push Not at hh
        exact hU ⟨_, kU.2.2 (by simp only at hh ⊢; omega) (by simp only at hh ⊢; omega)⟩
      · by_contra hh
        push Not at hh
        exact hV ⟨_, kV.1 hh.1 hh.2⟩
      · by_contra hh
        push Not at hh
        exact hV ⟨_, kV.2.1 (by simp only at hh ⊢; omega) hh.2⟩
      · by_contra hh
        push Not at hh
        exact hV ⟨_, kV.2.2 (by simp only at hh ⊢; omega) (by simp only at hh ⊢; omega)⟩
    by_cases hn4 : n = 4
    · subst hn4
      obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.1 hWn
      have h7 : ¬ConstCut7 (U a b + V a b) (U a c + V a c) (U a d + V a d) (U b c + V b c)
          (U b d + V b d) (U c d + V c d) := by
        intro hc
        apply hins.2
        refine isConstCut_of_constCut7 hAs hab hac had hbc hbd hcd ?_
        simpa only [hA] using hc
      have := four_core _ (h.mem_L5 a b) _ (h.mem_L5 a c) _ (h.mem_L5 a d) _ (h.mem_L5 b c) _
        (h.mem_L5 b d) _ (h.mem_L5 c d) (h.tri3_eq a b c) (h.tri3_eq a b d) (h.tri3_eq a c d)
        (h.tri3_eq b c d) h7
      rcases this with hz | hz
      · exact Or.inl (suppDisconnected_of_zeroCut7 hUs hab hac had hbc hbd hcd hz)
      · exact Or.inr (suppDisconnected_of_zeroCut7 hVs hab hac had hbc hbd hcd hz)
    · -- at least five vertices
      have h5 : 5 ≤ n := by omega
      obtain ⟨z, hz, hz'⟩ := exists_inseparable_erase hAst (hWn ▸ h5) hins
      have hcard : (W.erase z).card = n - 1 := by rw [Finset.card_erase_of_mem hz, hWn]
      rcases ih (n - 1) (by omega) (W.erase z) hcard hz' with hd | hd
      · exact color_step h hA hz hz' hd
      · have hA' : ∀ x y, A x y = V x y + U x y := fun x y => by rw [hA]; ring
        exact (color_step h.symm hA' hz hz' hd).symm

omit [DecidableEq X] in
/-- `lem:color`: if `A = U + V` is inseparable, at least one of its two color graphs is
disconnected.  Stated for the principal submatrix on a finite vertex set `W` (at least two
vertices); `SuppDisconnected R W` says the support graph of `R` on `W` is disconnected. -/
theorem color_disconnected {U V A : X → X → ℤ} (h : IsColorPair U V)
    (hA : ∀ x y, A x y = U x y + V x y) {W : Finset X} (hins : IsInseparable A W) :
    SuppDisconnected U W ∨ SuppDisconnected V W :=
  color_disconnected_aux h hA _ W rfl hins

omit [DecidableEq X] in
/-- `lem:color` on a finite vertex type: if `A = U + V` is inseparable (on all of `X`), at least
one of its two color graphs is disconnected. -/
theorem color_disconnected_univ [Fintype X] {U V : X → X → ℤ} (h : IsColorPair U V)
    (hins : IsInseparable (fun x y => U x y + V x y) Finset.univ) :
    SuppDisconnected U Finset.univ ∨ SuppDisconnected V Finset.univ :=
  color_disconnected h (fun _ _ => rfl) hins

end Main

end SkewRibbonCoarsenings
