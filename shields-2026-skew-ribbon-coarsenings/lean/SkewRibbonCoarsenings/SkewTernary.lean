/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# Skew-ternary matrices: constant cuts, clans, small cores, and deletion

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:balance`, subsection
`subsec:support` (`lem:small-core`, `lem:deletion`).

A skew-ternary matrix on a type `X` is a function `A : X → X → ℤ` with `A y x = -A x y` and
entries in `{-1, 0, 1}`.  Principal submatrices are indexed by a `Finset X`.  A constant cut of the
principal submatrix on `W` is a nontrivial partition `W = P ⊔ Q` (given by a predicate `P`) on
which all entries `A p q` with `p ∈ P`, `q ∈ Q` agree; `IsInseparable A W` says there are at
least two vertices and no constant cut.  A clan of `A` on `W` is a subset every outside vertex of
which sees all of it in one entry.

* `graph_fact` is the graph fact inside the proof of `lem:small-core`: a graph on at least two
  vertices with no induced four-vertex path has a disconnected graph or a disconnected
  complement.
* `small_core` is `lem:small-core`; `contract_inseparable_iff` and `exists_inseparable_erase` are
  the two assertions of `lem:deletion`.

Sorry-free.
-/

namespace SkewRibbonCoarsenings

variable {X : Type*}

/-- A skew-ternary matrix on `X`: skew-symmetric with entries in `{-1, 0, 1}`. -/
structure IsSkewTernary (A : X → X → ℤ) : Prop where
  skew : ∀ x y, A y x = -A x y
  ternary : ∀ x y, A x y = -1 ∨ A x y = 0 ∨ A x y = 1

/-- `P` splits the vertex set `W` nontrivially (both sides meet `W`) and the relation `S` holds
across every pair `(p, q)` with `p` on the `P` side and `q` on the other side. -/
def IsCutOf (S : X → X → Prop) (W : Finset X) (P : X → Prop) : Prop :=
  (∃ p ∈ W, P p) ∧ (∃ q ∈ W, ¬P q) ∧ ∀ p ∈ W, ∀ q ∈ W, P p → ¬P q → S p q

/-- A constant cut of the principal submatrix of `A` on `W`: a nontrivial partition `W = P ⊔ Q`
all of whose cross entries `A p q` (`p ∈ P`, `q ∈ Q`) are equal to a common value. -/
def IsConstCut (A : X → X → ℤ) (W : Finset X) (P : X → Prop) : Prop :=
  ∃ c : ℤ, IsCutOf (fun p q => A p q = c) W P

/-- The principal submatrix of `A` on `W` is inseparable: it has at least two vertices and no
constant cut. -/
def IsInseparable (A : X → X → ℤ) (W : Finset X) : Prop :=
  2 ≤ W.card ∧ ¬∃ P : X → Prop, IsConstCut A W P

/-- `C` is a clan of `A` on `W`: `C ⊆ W` and every vertex of `W` outside `C` has the same entry
to every vertex of `C`. -/
def IsClan (A : X → X → ℤ) (W C : Finset X) : Prop :=
  C ⊆ W ∧ ∀ z ∈ W, z ∉ C → ∀ x ∈ C, ∀ y ∈ C, A z x = A z y

/-- No induced four-vertex path `a - b - c - d` of the symmetric relation `R` inside `W`. -/
def P4Free (R : X → X → Prop) (W : Finset X) : Prop :=
  ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ∀ d ∈ W, ¬(R a b ∧ R b c ∧ R c d ∧ ¬R a c ∧ ¬R a d ∧ ¬R b d)

theorem IsSkewTernary.diag {A : X → X → ℤ} (hA : IsSkewTernary A) (x : X) : A x x = 0 := by
  have := hA.skew x x
  omega

theorem IsCutOf.mono {S T : X → X → Prop} (h : ∀ x y, S x y → T x y) {W : Finset X}
    {P : X → Prop} (hP : IsCutOf S W P) : IsCutOf T W P :=
  ⟨hP.1, hP.2.1, fun p hp q hq a b => h _ _ (hP.2.2 p hp q hq a b)⟩

theorem IsCutOf.compl {S : X → X → Prop} (hS : ∀ x y, S x y → S y x) {W : Finset X}
    {P : X → Prop} (h : IsCutOf S W P) : IsCutOf S W (fun x => ¬P x) := by
  obtain ⟨⟨p, hp, hPp⟩, ⟨q, hq, hPq⟩, h⟩ := h
  refine ⟨⟨q, hq, hPq⟩, ⟨p, hp, not_not.2 hPp⟩, ?_⟩
  intro a ha b hb hPa hPb
  exact hS _ _ (h b hb a ha (not_not.1 hPb) hPa)

theorem IsCutOf.mono_set {S : X → X → Prop} {W W' : Finset X} (hW : W' ⊆ W) {P : X → Prop}
    (hP : IsCutOf S W P) (h1 : ∃ p ∈ W', P p) (h2 : ∃ q ∈ W', ¬P q) : IsCutOf S W' P :=
  ⟨h1, h2, fun p hp q hq a b => hP.2.2 p (hW hp) q (hW hq) a b⟩

theorem IsConstCut.compl {A : X → X → ℤ} (hA : ∀ x y, A y x = -A x y) {W : Finset X}
    {P : X → Prop} (h : IsConstCut A W P) : IsConstCut A W (fun x => ¬P x) := by
  obtain ⟨c, ⟨p, hp, hPp⟩, ⟨q, hq, hPq⟩, h⟩ := h
  refine ⟨-c, ⟨q, hq, hPq⟩, ⟨p, hp, not_not.2 hPp⟩, ?_⟩
  intro a ha b hb hPa hPb
  have := h b hb a ha (not_not.1 hPb) hPa
  have := hA a b
  omega

/-- Two vertices not separated by a cut whose cross entries all equal `k` lie on one side if
neither of their mutual entries equals `k`. -/
theorem cut_same {A : X → X → ℤ} {W : Finset X} {P : X → Prop} {k : ℤ}
    (h : IsCutOf (fun p q => A p q = k) W P) {x y : X} (hx : x ∈ W) (hy : y ∈ W)
    (hxy : A x y ≠ k) (hyx : A y x ≠ k) : P x ↔ P y := by
  constructor
  · intro hPx
    by_contra hPy
    exact hxy (h.2.2 x hx y hy hPx hPy)
  · intro hPy
    by_contra hPx
    exact hyx (h.2.2 y hy x hx hPy hPx)

/-- `P4Free` is invariant under passing to the complement of a symmetric relation. -/
theorem P4Free.compl {R : X → X → Prop} (hsym : ∀ x y, R x y → R y x) {W : Finset X}
    (h : P4Free R W) : P4Free (fun x y => ¬R x y) W := by
  intro a ha b hb c hc d hd hh
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hh
  refine h c hc a ha d hd b hb ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hsym _ _ (not_not.1 h4)
  · exact not_not.1 h5
  · exact hsym _ _ (not_not.1 h6)
  · exact fun e => h3 e
  · exact fun e => h2 (hsym _ _ e)
  · exact fun e => h1 e

theorem P4Free.mono {R : X → X → Prop} {W W' : Finset X} (hW : W' ⊆ W) (h : P4Free R W) :
    P4Free R W' := fun a ha b hb c hc d hd => h a (hW ha) b (hW hb) c (hW hc) d (hW hd)

section Graph

variable [DecidableEq X]

/-- A three-vertex principal submatrix is separable exactly when one vertex has equal entries
to the other two. -/
theorem constCut_three_iff {A : X → X → ℤ} (hA : ∀ x y, A y x = -A x y) {a b c : X}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∃ P, IsConstCut A {a, b, c} P) ↔ (A a b = A a c ∨ A b a = A b c ∨ A c a = A c b) := by
  constructor
  · rintro ⟨P, k, ⟨p, hp, hPp⟩, ⟨q, hq, hPq⟩, h⟩
    have ha : a ∈ ({a, b, c} : Finset X) := by simp
    have hb : b ∈ ({a, b, c} : Finset X) := by simp
    have hc : c ∈ ({a, b, c} : Finset X) := by simp
    have eab := h a ha b hb
    have eac := h a ha c hc
    have eba := h b hb a ha
    have ebc := h b hb c hc
    have eca := h c hc a ha
    have ecb := h c hc b hb
    have s1 := hA a b
    have s2 := hA a c
    have s3 := hA b c
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    have hP : P a ∨ P b ∨ P c := by rcases hp with rfl | rfl | rfl <;> simp [hPp]
    have hQ : ¬P a ∨ ¬P b ∨ ¬P c := by rcases hq with rfl | rfl | rfl <;> simp [hPq]
    by_cases hPa : P a <;> by_cases hPb : P b <;> by_cases hPc : P c <;>
      simp [hPa, hPb, hPc] at eab eac eba ebc eca ecb hP hQ <;> omega
  · rintro (h | h | h)
    · refine ⟨fun x => x = a, A a b, ⟨a, by simp, rfl⟩, ⟨b, by simp, fun e => hab e.symm⟩, ?_⟩
      intro p hp q hq hpa hqa
      subst hpa
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact absurd rfl hqa
      · rfl
      · exact h.symm
    · refine ⟨fun x => x = b, A b a, ⟨b, by simp, rfl⟩, ⟨a, by simp, hab⟩, ?_⟩
      intro p hp q hq hpa hqa
      subst hpa
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · rfl
      · exact absurd rfl hqa
      · exact h.symm
    · refine ⟨fun x => x = c, A c a, ⟨c, by simp, rfl⟩, ⟨a, by simp, hac⟩, ?_⟩
      intro p hp q hq hpa hqa
      subst hpa
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · rfl
      · exact h.symm
      · exact absurd rfl hqa

/-- The four-vertex principal submatrix carried by an induced path `a - b - c - d` of nonzero
entries (with `A a c = A a d = A b d = 0`) is inseparable: the path and its complement are both
connected. -/
theorem not_constCut_path {A : X → X → ℤ} (hA : ∀ x y, A y x = -A x y) {a b c d : X}
    (hac : A a c = 0) (had : A a d = 0) (hbd : A b d = 0)
    (hab : A a b ≠ 0) (hbc : A b c ≠ 0) (hcd : A c d ≠ 0) {P : X → Prop} :
    ¬IsConstCut A {a, b, c, d} P := by
  rintro ⟨k, h⟩
  have ha : a ∈ ({a, b, c, d} : Finset X) := by simp
  have hb : b ∈ ({a, b, c, d} : Finset X) := by simp
  have hc : c ∈ ({a, b, c, d} : Finset X) := by simp
  have hd : d ∈ ({a, b, c, d} : Finset X) := by simp
  have s1 := hA a b
  have s2 := hA b c
  have s3 := hA c d
  have s4 := hA a c
  have s5 := hA a d
  have s6 := hA b d
  obtain ⟨p, hp, hPp⟩ := h.1
  obtain ⟨q, hq, hPq⟩ := h.2.1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  have hP : P a ∨ P b ∨ P c ∨ P d := by rcases hp with rfl | rfl | rfl | rfl <;> simp [hPp]
  have hQ : ¬P a ∨ ¬P b ∨ ¬P c ∨ ¬P d := by rcases hq with rfl | rfl | rfl | rfl <;> simp [hPq]
  by_cases hk : k = 0
  · have e1 := cut_same h ha hb (by omega) (by omega)
    have e2 := cut_same h hb hc (by omega) (by omega)
    have e3 := cut_same h hc hd (by omega) (by omega)
    by_cases hPa : P a
    · have hPb := e1.1 hPa
      have hPc := e2.1 hPb
      have hPd := e3.1 hPc
      simp [hPa, hPb, hPc, hPd] at hQ
    · have hPb : ¬P b := fun x => hPa (e1.2 x)
      have hPc : ¬P c := fun x => hPb (e2.2 x)
      have hPd : ¬P d := fun x => hPc (e3.2 x)
      simp [hPa, hPb, hPc, hPd] at hP
  · have e1 := cut_same h ha hc (by omega) (by omega)
    have e2 := cut_same h ha hd (by omega) (by omega)
    have e3 := cut_same h hb hd (by omega) (by omega)
    by_cases hPa : P a
    · have hPc := e1.1 hPa
      have hPd := e2.1 hPa
      have hPb := e3.2 hPd
      simp [hPa, hPb, hPc, hPd] at hQ
    · have hPc : ¬P c := fun x => hPa (e1.2 x)
      have hPd : ¬P d := fun x => hPa (e2.2 x)
      have hPb : ¬P b := fun x => hPd (e3.1 x)
      simp [hPa, hPb, hPc, hPd] at hP

/-- `lem:small-core`, inductive step of `graph_fact`: if `W` has no cut across which `R` fails
everywhere (the graph is connected) but `W.erase z` does, then `z` is adjacent to every other
vertex.

**Differs from the paper's route.**  The paper takes a component of `W.erase z` containing a
neighbor and a nonneighbor of `z`; here a cardinality-minimal closed set `K` of `W.erase z` is
chosen, which yields the same induced four-vertex path. -/
theorem graph_fact_step {R : X → X → Prop} (hsym : ∀ x y, R x y → R y x) {W : Finset X}
    (hP4 : P4Free R W) {z : X} (hz : z ∈ W)
    (hE : ∃ P, IsCutOf (fun p q => ¬R p q) (W.erase z) P)
    (hnoE : ¬∃ P, IsCutOf (fun p q => ¬R p q) W P) :
    IsCutOf R W (fun x => x = z) := by
  classical
  obtain ⟨P0, hP0⟩ := hE
  have hsym' : ∀ x y, ¬R x y → ¬R y x := fun x y h h' => h (hsym _ _ h')
  refine ⟨⟨z, hz, rfl⟩, ?_, ?_⟩
  · obtain ⟨q, hq, -⟩ := hP0.1
    exact ⟨q, Finset.mem_of_mem_erase hq, Finset.ne_of_mem_erase hq⟩
  intro p hp q hq hpz hqz
  subst hpz
  by_contra hRzq
  have hqW' : q ∈ W.erase p := Finset.mem_erase.2 ⟨hqz, hq⟩
  -- candidates: closed subsets of `W.erase z` containing `q`
  let Cand : Finset (Finset X) := (W.erase p).powerset.filter fun K =>
    q ∈ K ∧ (∃ s ∈ W.erase p, s ∉ K) ∧ ∀ a ∈ K, ∀ b ∈ W.erase p, b ∉ K → ¬R a b
  have hCand : Cand.Nonempty := by
    by_cases hqP : P0 q
    · refine ⟨(W.erase p).filter P0, ?_⟩
      simp only [Cand, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.filter_subset _ _, ⟨hqW', hqP⟩, ?_, ?_⟩
      · obtain ⟨s, hs, hPs⟩ := hP0.2.1
        exact ⟨s, hs, by simp [hPs]⟩
      · intro a ha b hb hbK
        have : ¬P0 b := fun h => hbK ⟨hb, h⟩
        exact hP0.2.2 a ha.1 b hb ha.2 this
    · refine ⟨(W.erase p).filter fun x => ¬P0 x, ?_⟩
      simp only [Cand, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.filter_subset _ _, ⟨hqW', hqP⟩, ?_, ?_⟩
      · obtain ⟨s, hs, hPs⟩ := hP0.1
        exact ⟨s, hs, by simp [hPs]⟩
      · intro a ha b hb hbK
        have : P0 b := by
          by_contra h
          exact hbK ⟨hb, h⟩
        exact hsym' _ _ (hP0.2.2 b hb a ha.1 this ha.2)
  obtain ⟨K, hKC, hKmin⟩ := Finset.exists_min_image Cand Finset.card hCand
  simp only [Cand, Finset.mem_filter, Finset.mem_powerset] at hKC
  obtain ⟨hKW, hqK, ⟨s0, hs0W, hs0K⟩, hKcl⟩ := hKC
  have hKW' : ∀ x ∈ K, x ∈ W ∧ x ≠ p := fun x hx => by
    have := hKW hx
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  -- `p` has a neighbor in `K`
  have hN : ∃ n ∈ K, R p n := by
    by_contra hno
    push Not at hno
    apply hnoE
    refine ⟨fun x => x ∈ K, ⟨q, hq, hqK⟩, ⟨p, hz, fun h => (hKW' p h).2 rfl⟩, ?_⟩
    intro a ha b hb haK hbK
    by_cases hbp : b = p
    · subst hbp
      exact hsym' _ _ (hno a haK)
    · exact hKcl a haK b (Finset.mem_erase.2 ⟨hbp, hb⟩) hbK
  obtain ⟨n, hnK, hRpn⟩ := hN
  -- `p` has a neighbor outside `K`
  have hM : ∃ s ∈ W.erase p, s ∉ K ∧ R p s := by
    by_contra hno
    push Not at hno
    apply hnoE
    refine ⟨fun x => x ∈ W.erase p ∧ x ∉ K,
      ⟨s0, Finset.mem_of_mem_erase hs0W, hs0W, hs0K⟩, ⟨p, hz, ?_⟩, ?_⟩
    · intro h
      exact (Finset.ne_of_mem_erase h.1) rfl
    · intro a ha b hb haK hbK
      by_cases hbp : b = p
      · subst hbp
        exact hsym' _ _ (fun h => hno a haK.1 haK.2 h)
      · have hbK' : b ∈ K := by
          by_contra hbK''
          exact hbK ⟨Finset.mem_erase.2 ⟨hbp, hb⟩, hbK''⟩
        exact hsym' _ _ (hKcl b hbK' a haK.1 haK.2)
  obtain ⟨s, hsW, hsK, hRps⟩ := hM
  -- there is an edge between the neighbors and the nonneighbors of `p` inside `K`
  have hEdge : ∃ m ∈ K, ¬R p m ∧ ∃ n' ∈ K, R p n' ∧ R n' m := by
    by_contra hno
    push Not at hno
    have hmem : K.filter (fun m => ¬R p m) ∈ Cand := by
      simp only [Cand, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨(Finset.filter_subset _ _).trans hKW, ⟨hqK, hRzq⟩, ⟨s, hsW, ?_⟩, ?_⟩
      · simp [hsK]
      · intro a ha b hb hbK
        by_cases hbK' : b ∈ K
        · have hRpb : R p b := by
            by_contra h
            exact hbK ⟨hbK', h⟩
          by_contra hRab
          exact hno a ha.1 ha.2 b hbK' hRpb (hsym _ _ hRab)
        · exact hKcl a ha.1 b hb hbK'
    have hlt : (K.filter fun m => ¬R p m).card < K.card := by
      apply Finset.card_lt_card
      refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
      have := h hnK
      simp only [Finset.mem_filter] at this
      exact this.2 hRpn
    exact absurd (hKmin _ hmem) (not_le.2 hlt)
  obtain ⟨m, hmK, hRpm, n', hn'K, hRpn', hRn'm⟩ := hEdge
  -- the induced path `m - n' - p - s`
  have hmW := (hKW' m hmK).1
  have hn'W := (hKW' n' hn'K).1
  have hsW' := Finset.mem_of_mem_erase hsW
  refine hP4 m hmW n' hn'W p hz s hsW' ⟨hsym _ _ hRn'm, hsym _ _ hRpn', hRps, ?_, ?_, ?_⟩
  · exact fun h => hRpm (hsym _ _ h)
  · exact hKcl m hmK s hsW hsK
  · exact hKcl n' hn'K s hsW hsK

omit [DecidableEq X] in
/-- `lem:small-core`, graph fact: a symmetric relation on at least two
vertices with no induced four-vertex path is disconnected or has disconnected complement.  Here
"disconnected" is a nontrivial partition with no edge (`graph_fact`, left) or with every cross pair
an edge (right). -/
theorem graph_fact {R : X → X → Prop} (hsym : ∀ x y, R x y → R y x) :
    ∀ n : ℕ, ∀ W : Finset X, W.card = n → 2 ≤ n → P4Free R W →
      (∃ P, IsCutOf (fun p q => ¬R p q) W P) ∨ ∃ P, IsCutOf R W P := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hWn hn hP4
    by_cases hF : ∃ P, IsCutOf R W P
    · exact Or.inr hF
    by_cases hE : ∃ P, IsCutOf (fun p q => ¬R p q) W P
    · exact Or.inl hE
    exfalso
    by_cases h2 : n = 2
    · subst h2
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hWn
      by_cases hR : R x y
      · apply hF
        refine ⟨fun t => t = x, ⟨x, by simp, rfl⟩, ⟨y, by simp, fun h => hxy h.symm⟩, ?_⟩
        intro p hp q hq hpx hqx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
        subst hpx
        rcases hq with rfl | rfl
        · exact absurd rfl hqx
        · exact hR
      · apply hE
        refine ⟨fun t => t = x, ⟨x, by simp, rfl⟩, ⟨y, by simp, fun h => hxy h.symm⟩, ?_⟩
        intro p hp q hq hpx hqx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
        subst hpx
        rcases hq with rfl | rfl
        · exact absurd rfl hqx
        · exact hR
    · have hWne : W.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨z, hz⟩ := hWne
      have hcard : (W.erase z).card = n - 1 := by rw [Finset.card_erase_of_mem hz, hWn]
      have hsym' : ∀ x y, ¬R x y → ¬R y x := fun x y h h' => h (hsym _ _ h')
      rcases ih (n - 1) (by omega) (W.erase z) hcard (by omega)
          (hP4.mono (Finset.erase_subset _ _)) with hE' | hF'
      · exact hF ⟨_, graph_fact_step hsym hP4 hz hE' hE⟩
      · have h1 := graph_fact_step (R := fun x y => ¬R x y) hsym' (hP4.compl hsym) hz
          (hF'.imp fun P hP => hP.mono fun x y h => not_not.2 h)
          (fun ⟨P, hP⟩ => hF ⟨P, hP.mono fun x y h => not_not.1 h⟩)
        exact hE ⟨_, h1⟩

end Graph

section SmallCore

open scoped Classical in
/-- The series-split step of `lem:small-core`: if the relation `A x y = 1` is transitive on `W`
and `W` has a nontrivial partition all of whose cross pairs are comparable (`A p q ≠ 0`), then
the matrix has a constant cut. -/
theorem series_split {A : X → X → ℤ} (hA : IsSkewTernary A) {W : Finset X}
    (htrans : ∀ x ∈ W, ∀ y ∈ W, ∀ z ∈ W, A x y = 1 → A y z = 1 → A x z = 1) :
    ∀ n : ℕ, ∀ P : X → Prop, IsCutOf (fun p q => A p q ≠ 0) W P → (W.filter P).card = n →
      ∃ Q : X → Prop, IsConstCut A W Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hP hn
    obtain ⟨⟨p0, hp0W, hPp0⟩, ⟨q0, hq0W, hPq0⟩, hcross⟩ := hP
    have tern := hA.ternary
    have skew := hA.skew
    by_cases hmix : ∃ q ∈ W, ¬P q ∧ ∃ p1 ∈ W, P p1 ∧ ∃ p2 ∈ W, P p2 ∧ A p1 q = 1 ∧ A p2 q = -1
    · obtain ⟨q, hqW, hPq, p1, hp1W, hPp1, p2, hp2W, hPp2, h1, h2⟩ := hmix
      refine ih ((W.filter fun x => P x ∧ A x q = 1).card) ?_ (fun x => P x ∧ A x q = 1) ?_
        (by convert rfl)
      · rw [← hn]
        apply Finset.card_lt_card
        refine ⟨fun x hx => ?_, fun hsub => ?_⟩
        · simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, hx.2.1⟩
        · have := hsub (Finset.mem_filter.2 ⟨hp2W, hPp2⟩)
          simp only [Finset.mem_filter] at this
          omega
      · refine ⟨⟨p1, hp1W, hPp1, h1⟩, ⟨p2, hp2W, ?_⟩, ?_⟩
        · intro h
          have := h.2
          omega
        · intro p hp y hy hpP hyP
          have hpq : A p q = 1 := hpP.2
          by_cases hPy : P y
          · have hyq : A y q ≠ 0 := hcross y hy q hqW hPy hPq
            have hyq' : A y q ≠ 1 := fun h => hyP ⟨hPy, h⟩
            have := skew y q
            have := htrans p hp q hqW y hy hpq (by have := tern y q; omega)
            omega
          · exact hcross p hp y hy hpP.1 hPy
    · push Not at hmix
      -- uniform: every outside vertex sees `P` in one direction
      have key : ∀ x ∈ W, ¬P x → (∀ p ∈ W, P p → A p x = 1) ∨ (∀ p ∈ W, P p → A p x = -1) := by
        intro x hx hPx
        by_cases h1 : ∀ p ∈ W, P p → A p x = 1
        · exact Or.inl h1
        · right
          push Not at h1
          obtain ⟨p, hpW, hPp, hne⟩ := h1
          have hp : A p x = -1 := by
            have := hcross p hpW x hx hPp hPx
            have := tern p x
            omega
          intro p' hp'W hPp'
          have := hcross p' hp'W x hx hPp' hPx
          have := tern p' x
          by_contra hne'
          have h1' : A p' x = 1 := by omega
          exact hmix x hx hPx p' hp'W hPp' p hpW hPp h1' hp
      by_cases hQ : ∃ q0 ∈ W, ¬P q0 ∧ ∀ p ∈ W, P p → A p q0 = 1
      · obtain ⟨q1, hq1W, hPq1, hq1⟩ := hQ
        refine ⟨fun x => ¬(¬P x ∧ ∀ p ∈ W, P p → A p x = 1), 1, ⟨p0, hp0W, ?_⟩, ⟨q1, hq1W, ?_⟩, ?_⟩
        · exact fun h => h.1 hPp0
        · exact not_not.2 ⟨hPq1, hq1⟩
        · intro x hx q hq hxQ hqQ
          have hqQ' := not_not.1 hqQ
          by_cases hPx : P x
          · exact hqQ'.2 x hx hPx
          · have hxneg : ∀ p ∈ W, P p → A p x = -1 := by
              rcases key x hx hPx with h | h
              · exact absurd ⟨hPx, h⟩ hxQ
              · exact h
            have hxp0 : A x p0 = 1 := by
              have := skew x p0
              rw [hxneg p0 hp0W hPp0] at this
              omega
            exact htrans x hx p0 hp0W q hq hxp0 (hqQ'.2 p0 hp0W hPp0)
      · push Not at hQ
        refine ⟨P, -1, ⟨p0, hp0W, hPp0⟩, ⟨q0, hq0W, hPq0⟩, ?_⟩
        intro p hp q hq hPp hPq
        rcases key q hq hPq with h | h
        · exact absurd h (by
            obtain ⟨p', hp'W, hPp', hne⟩ := hQ q hq hPq
            exact fun hh => hne (hh p' hp'W hPp'))
        · exact h p hp hPp

/-- `lem:small-core`, contrapositive form: if every three- and four-vertex principal submatrix
of `A` on `W` is separable (and `|W| ≥ 2`), then `A` is separable on `W`.

**Differs from the paper's route.**  The paper orders the complement components of the
comparability graph and takes an extreme component; here `series_split` removes a vertex set
from a completely comparable partition by induction on its size until a constant cut appears. -/
theorem exists_constCut_of_small_sep {A : X → X → ℤ} (hA : IsSkewTernary A) {W : Finset X}
    (h2 : 2 ≤ W.card)
    (hsep : ∀ W' ⊆ W, (W'.card = 3 ∨ W'.card = 4) → ∃ P, IsConstCut A W' P) :
    ∃ P, IsConstCut A W P := by
  classical
  have skew := hA.skew
  -- transitivity of `A x y = 1`
  have htrans : ∀ x ∈ W, ∀ y ∈ W, ∀ z ∈ W, A x y = 1 → A y z = 1 → A x z = 1 := by
    intro x hx y hy z hz hxy hyz
    have hxy' : x ≠ y := by
      rintro rfl
      have := hA.diag x
      omega
    have hyz' : y ≠ z := by
      rintro rfl
      have := hA.diag y
      omega
    have hxz' : x ≠ z := by
      rintro rfl
      have := skew x y
      omega
    have hsub : ({x, y, z} : Finset X) ⊆ W := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> assumption
    have hc3 : ({x, y, z} : Finset X).card = 3 :=
      Finset.card_eq_three.2 ⟨x, y, z, hxy', hxz', hyz', rfl⟩
    obtain ⟨P, hP⟩ := hsep _ hsub (Or.inl hc3)
    have := (constCut_three_iff skew hxy' hxz' hyz').1 ⟨P, hP⟩
    have := skew x z
    have := skew x y
    have := skew y z
    omega
  -- no induced four-vertex path in the comparability graph
  have hP4 : P4Free (fun x y => A x y ≠ 0) W := by
    intro a ha b hb c hc d hd hh
    obtain ⟨h1, h2', h3, h4, h5, h6⟩ := hh
    have hac : A a c = 0 := not_not.1 h4
    have had : A a d = 0 := not_not.1 h5
    have hbd : A b d = 0 := not_not.1 h6
    have e1 := skew a b
    have e2 := skew b c
    have e3 := skew c d
    have e4 := skew a c
    have e5 := skew a d
    have e6 := skew b d
    have d1 := hA.diag a
    have d2 := hA.diag b
    have d3 := hA.diag c
    have d4 := hA.diag d
    have hab' : a ≠ b := by rintro rfl; exact h1 d1
    have hbc' : b ≠ c := by rintro rfl; exact h2' d2
    have hcd' : c ≠ d := by rintro rfl; exact h3 d3
    have hac' : a ≠ c := by rintro rfl; exact h5 h3
    have had' : a ≠ d := by rintro rfl; exact h3 (by omega)
    have hbd' : b ≠ d := by rintro rfl; exact h5 h1
    have hsub : ({a, b, c, d} : Finset X) ⊆ W := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> assumption
    have hc4 : ({a, b, c, d} : Finset X).card = 4 :=
      Finset.card_eq_four.2 ⟨a, b, c, d, hab', hac', had', hbc', hbd', hcd', rfl⟩
    obtain ⟨P, hP⟩ := hsep _ hsub (Or.inr hc4)
    exact not_constCut_path skew hac had hbd h1 h2' h3 hP
  have hsym : ∀ x y, (fun x y => A x y ≠ 0) x y → (fun x y => A x y ≠ 0) y x := by
    intro x y h
    have := skew x y
    change A x y ≠ 0 at h
    change A y x ≠ 0
    omega
  rcases graph_fact hsym W.card W rfl h2 hP4 with ⟨P, hP⟩ | ⟨P, hP⟩
  · exact ⟨P, 0, hP.mono fun x y h => not_not.1 h⟩
  · exact series_split hA htrans _ P hP rfl

/-- `lem:small-core`: every inseparable skew-ternary matrix has an inseparable principal
submatrix on three or four vertices.  Stated for the principal submatrix on a finite set `W`
of vertices; see `small_core_univ` for the whole matrix on a `Fintype`. -/
theorem small_core {A : X → X → ℤ} (hA : IsSkewTernary A) {W : Finset X}
    (h : IsInseparable A W) :
    ∃ W' ⊆ W, (W'.card = 3 ∨ W'.card = 4) ∧ IsInseparable A W' := by
  by_contra hne
  push Not at hne
  apply h.2
  refine exists_constCut_of_small_sep hA h.1 fun W' hW' hc => ?_
  by_contra hcut
  exact hne W' hW' hc ⟨by omega, hcut⟩

/-- `lem:small-core` for a matrix on a finite type. -/
theorem small_core_univ [Fintype X] {A : X → X → ℤ} (hA : IsSkewTernary A)
    (h : IsInseparable A Finset.univ) :
    ∃ W' : Finset X, (W'.card = 3 ∨ W'.card = 4) ∧ IsInseparable A W' := by
  obtain ⟨W', -, h1, h2⟩ := small_core hA h
  exact ⟨W', h1, h2⟩

end SmallCore

section Deletion

variable [DecidableEq X]

/-- The contraction of the clan `C` of `W` to the representative `r ∈ C`: the vertex set
`(W ∖ C) ∪ {r}`, with the entries of `A`. -/
def contract (W C : Finset X) (r : X) : Finset X := W \ C.erase r

theorem mem_contract {W C : Finset X} {r x : X} (hr : r ∈ C) :
    x ∈ contract W C r ↔ x ∈ W ∧ (x ∉ C ∨ x = r) := by
  simp only [contract, Finset.mem_sdiff, Finset.mem_erase]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_cases hxC : x ∈ C
    · right
      by_contra hxr
      exact h2 ⟨hxr, hxC⟩
    · exact Or.inl hxC
  · rintro ⟨h1, h2 | rfl⟩
    · exact ⟨h1, fun h => h2 h.2⟩
    · exact ⟨h1, fun h => h.1 rfl⟩

/-- Contracting a proper nonempty clan to a representative: a constant cut of the contraction
expands to one of the original. -/
theorem contract_expand {A : X → X → ℤ} (hA : ∀ x y, A y x = -A x y) {W C : Finset X} {r : X}
    (hC : IsClan A W C) (_hCW : C ⊂ W) (hr : r ∈ C) {P : X → Prop}
    (hP : IsConstCut A (contract W C r) P) : ∃ Q : X → Prop, IsConstCut A W Q := by
  obtain ⟨c, ⟨p0, hp0, hPp0⟩, ⟨q0, hq0, hPq0⟩, hcross⟩ := hP
  have hrW : r ∈ W := hC.1 hr
  have hrM : r ∈ contract W C r := (mem_contract hr).2 ⟨hrW, Or.inr rfl⟩
  have hMW : ∀ x ∈ contract W C r, x ∈ W := fun x hx => ((mem_contract hr).1 hx).1
  refine ⟨fun x => (x ∈ C ∧ P r) ∨ (x ∉ C ∧ P x), c, ?_, ?_, ?_⟩
  · refine ⟨p0, hMW p0 hp0, ?_⟩
    rcases ((mem_contract hr).1 hp0).2 with h | rfl
    · exact Or.inr ⟨h, hPp0⟩
    · exact Or.inl ⟨hr, hPp0⟩
  · refine ⟨q0, hMW q0 hq0, ?_⟩
    rcases ((mem_contract hr).1 hq0).2 with h | rfl
    · rintro (⟨h', _⟩ | ⟨_, h'⟩)
      · exact h h'
      · exact hPq0 h'
    · rintro (⟨_, h'⟩ | ⟨h', _⟩)
      · exact hPq0 h'
      · exact h' hr
  · intro p hp q hq hPp hPq
    have hxM : ∀ x ∈ W, x ∉ C → x ∈ contract W C r := fun x hx hxC =>
      (mem_contract hr).2 ⟨hx, Or.inl hxC⟩
    rcases hPp with ⟨hpC, hPr⟩ | ⟨hpC, hPp'⟩
    · have hqC : q ∉ C := fun hqC => hPq (Or.inl ⟨hqC, hPr⟩)
      have hPq' : ¬P q := fun h => hPq (Or.inr ⟨hqC, h⟩)
      have e1 := hC.2 q hq hqC r hr p hpC
      have e2 := hcross r hrM q (hxM q hq hqC) hPr hPq'
      have := hA p q
      have := hA r q
      have := hA q p
      have := hA q r
      omega
    · by_cases hqC : q ∈ C
      · have hPr' : ¬P r := fun h => hPq (Or.inl ⟨hqC, h⟩)
        have e1 := hC.2 p hp hpC q hqC r hr
        have e2 := hcross p (hxM p hp hpC) r hrM hPp' hPr'
        omega
      · have hPq' : ¬P q := fun h => hPq (Or.inr ⟨hqC, h⟩)
        exact hcross p (hxM p hp hpC) q (hxM q hq hqC) hPp' hPq'

/-- Contracting a proper nonempty clan to a representative: a constant cut of the original
restricts to one of the contraction. -/
theorem contract_restrict {A : X → X → ℤ} (hA : ∀ x y, A y x = -A x y) {W C : Finset X} {r : X}
    (hC : IsClan A W C) (hCW : C ⊂ W) (hr : r ∈ C) {P : X → Prop}
    (hP : IsConstCut A W P) : ∃ Q : X → Prop, IsConstCut A (contract W C r) Q := by
  have hrW : r ∈ W := hC.1 hr
  have hrM : r ∈ contract W C r := (mem_contract hr).2 ⟨hrW, Or.inr rfl⟩
  have hMW : ∀ x ∈ contract W C r, x ∈ W := fun x hx => ((mem_contract hr).1 hx).1
  have hsub : contract W C r ⊆ W := hMW
  -- the case where the cut puts the whole contraction on the `¬P` side
  have hside : ∀ (P : X → Prop), IsConstCut A W P →
      (∀ x ∈ contract W C r, ¬P x) → ∃ Q : X → Prop, IsConstCut A (contract W C r) Q := by
    intro P hPc hnone
    obtain ⟨c, ⟨p0, hp0W, hPp0⟩, -, hcross⟩ := hPc
    have hp0C : p0 ∈ C := by
      by_contra h
      exact hnone p0 ((mem_contract hr).2 ⟨hp0W, Or.inl h⟩) hPp0
    have hPr : ¬P r := hnone r hrM
    obtain ⟨z0, hz0W, hz0C⟩ := Finset.exists_of_ssubset hCW
    refine ⟨fun x => x = r, c, ⟨r, hrM, rfl⟩, ⟨z0, (mem_contract hr).2 ⟨hz0W, Or.inl hz0C⟩, ?_⟩, ?_⟩
    · rintro rfl
      exact hz0C hr
    · intro p hp q hq hpr hqr
      subst hpr
      have hqW := hMW q hq
      have hqC : q ∉ C := by
        rcases ((mem_contract hr).1 hq).2 with h | h
        · exact h
        · exact absurd h hqr
      have hPq : ¬P q := hnone q hq
      have e1 := hC.2 q hqW hqC p0 hp0C p hr
      have e2 := hcross p0 hp0W q hqW hPp0 hPq
      have := hA p0 q
      have := hA p q
      have := hA q p0
      have := hA q p
      omega
  obtain ⟨c, hPc⟩ := hP
  by_cases h1 : ∃ p ∈ contract W C r, P p
  · by_cases h2 : ∃ q ∈ contract W C r, ¬P q
    · exact ⟨P, c, hPc.mono_set hsub h1 h2⟩
    · push Not at h2
      exact hside (fun x => ¬P x) (IsConstCut.compl hA ⟨c, hPc⟩)
        (fun x hx => not_not.2 (h2 x hx))
  · push Not at h1
    exact hside P ⟨c, hPc⟩ h1

/-- `lem:deletion` (first assertion): contracting a proper nonempty clan to one representative
preserves inseparability in both directions. -/
theorem contract_inseparable_iff {A : X → X → ℤ} (hA : ∀ x y, A y x = -A x y) {W C : Finset X}
    {r : X} (hC : IsClan A W C) (hCW : C ⊂ W) (hr : r ∈ C) :
    IsInseparable A W ↔ IsInseparable A (contract W C r) := by
  have hrW : r ∈ W := hC.1 hr
  have hrM : r ∈ contract W C r := (mem_contract hr).2 ⟨hrW, Or.inr rfl⟩
  obtain ⟨z0, hz0W, hz0C⟩ := Finset.exists_of_ssubset hCW
  have hz0M : z0 ∈ contract W C r := (mem_contract hr).2 ⟨hz0W, Or.inl hz0C⟩
  have hc2 : 2 ≤ (contract W C r).card := by
    have hne : r ≠ z0 := fun h => hz0C (h ▸ hr)
    rw [Nat.succ_le_iff, Finset.one_lt_card]
    exact ⟨r, hrM, z0, hz0M, hne⟩
  have hsub : contract W C r ⊆ W := fun x hx => ((mem_contract hr).1 hx).1
  constructor
  · rintro ⟨-, hW⟩
    exact ⟨hc2, fun ⟨P, hP⟩ => hW ⟨_, (contract_expand hA hC hCW hr hP).choose_spec⟩⟩
  · rintro ⟨-, hM⟩
    exact ⟨hc2.trans (Finset.card_le_card hsub),
      fun ⟨P, hP⟩ => hM (contract_restrict hA hC hCW hr hP)⟩

/-- `lem:deletion` (second assertion): every inseparable skew-ternary matrix on at least five
vertices has an inseparable one-vertex deletion.  The proof follows the paper: a maximal proper
inseparable principal submatrix `V` containing a core of `small_core` is either the deletion or a
clan, and in the latter case a nonrepresentative vertex of the clan is deleted, the contraction
being unchanged (`contract_inseparable_iff`). -/
theorem exists_inseparable_erase {A : X → X → ℤ} (hA : IsSkewTernary A) {W : Finset X}
    (h5 : 5 ≤ W.card) (h : IsInseparable A W) : ∃ z ∈ W, IsInseparable A (W.erase z) := by
  classical
  have skew := hA.skew
  obtain ⟨W0, hW0W, hcard0, hW0⟩ := small_core hA h
  have hW0ne : W0 ≠ W := by
    rintro rfl
    omega
  let Cands : Finset (Finset X) :=
    W.powerset.filter fun V => W0 ⊆ V ∧ V ≠ W ∧ IsInseparable A V
  have hCands : Cands.Nonempty :=
    ⟨W0, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hW0W, Finset.Subset.refl _, hW0ne, hW0⟩⟩
  obtain ⟨V, hVC, hVmax⟩ := Finset.exists_max_image Cands Finset.card hCands
  simp only [Cands, Finset.mem_filter, Finset.mem_powerset] at hVC
  obtain ⟨hVW, hW0V, hVne, hVins⟩ := hVC
  have hVss : V ⊂ W := lt_of_le_of_ne hVW hVne
  by_cases hVc : V.card + 1 = W.card
  · obtain ⟨z, hzW, hzV⟩ := Finset.exists_of_ssubset hVss
    refine ⟨z, hzW, ?_⟩
    have hsub : V ⊆ W.erase z := fun x hx => Finset.mem_erase.2 ⟨fun h => hzV (h ▸ hx), hVW hx⟩
    have hcardE : (W.erase z).card = V.card := by
      rw [Finset.card_erase_of_mem hzW]
      omega
    have : V = W.erase z := Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [← this]
    exact hVins
  · -- `V` is a clan of `W`
    have hV3 : 3 ≤ V.card := by
      have := Finset.card_le_card hW0V
      omega
    have hz : ∀ z ∈ W, z ∉ V → ∃ c : ℤ, ∀ x ∈ V, A z x = c := by
      intro z hzW hzV
      have hins_sub : insert z V ⊆ W := Finset.insert_subset hzW hVW
      have hins_card : (insert z V).card = V.card + 1 := Finset.card_insert_of_notMem hzV
      have hins_ne : insert z V ≠ W := by
        intro h
        apply hVc
        rw [← h, hins_card]
      have hnot : ¬IsInseparable A (insert z V) := by
        intro hins
        have hmem : insert z V ∈ Cands := by
          simp only [Cands, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨hins_sub, hW0V.trans (Finset.subset_insert _ _), hins_ne, hins⟩
        have := hVmax _ hmem
        omega
      have hcut : ∃ P : X → Prop, IsConstCut A (insert z V) P := by
        by_contra hc
        exact hnot ⟨by omega, hc⟩
      obtain ⟨P, c, ⟨p0, hp0, hPp0⟩, ⟨q0, hq0, hPq0⟩, hcross⟩ := hcut
      have hVsub : V ⊆ insert z V := Finset.subset_insert _ _
      by_cases hmixP : (∃ p ∈ V, P p) ∧ (∃ q ∈ V, ¬P q)
      · exact absurd ⟨P, c, (IsCutOf.mono_set hVsub ⟨⟨p0, hp0, hPp0⟩, ⟨q0, hq0, hPq0⟩, hcross⟩
          hmixP.1 hmixP.2)⟩ hVins.2
      · rw [not_and_or] at hmixP
        rcases hmixP with hno | hno
        · push Not at hno
          -- all of `V` is outside `P`; `z` is the `P` side
          have hPz : P z := by
            rcases Finset.mem_insert.1 hp0 with rfl | hpV
            · exact hPp0
            · exact absurd hPp0 (hno p0 hpV)
          exact ⟨c, fun x hx => hcross z (Finset.mem_insert_self _ _) x (hVsub hx) hPz (hno x hx)⟩
        · push Not at hno
          have hnPz : ¬P z := by
            rcases Finset.mem_insert.1 hq0 with rfl | hqV
            · exact hPq0
            · exact absurd (hno q0 hqV) hPq0
          refine ⟨-c, fun x hx => ?_⟩
          have := hcross x (hVsub hx) z (Finset.mem_insert_self _ _) (hno x hx) hnPz
          have := skew z x
          omega
    have hclan : IsClan A W V := ⟨hVW, fun z hzW hzV x hx y hy => by
      obtain ⟨c, hc⟩ := hz z hzW hzV
      rw [hc x hx, hc y hy]⟩
    obtain ⟨r, hrV⟩ : V.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨x, hxV'⟩ : (V.erase r).Nonempty := Finset.card_pos.1 (by
      rw [Finset.card_erase_of_mem hrV]
      omega)
    have hxV : x ∈ V := Finset.mem_of_mem_erase hxV'
    have hxr : x ≠ r := Finset.ne_of_mem_erase hxV'
    have hxW : x ∈ W := hVW hxV
    refine ⟨x, hxW, ?_⟩
    obtain ⟨z0, hz0W, hz0V⟩ := Finset.exists_of_ssubset hVss
    have hclan' : IsClan A (W.erase x) (V.erase x) := by
      refine ⟨Finset.erase_subset_erase _ hVW, fun z hz hzC y hy y' hy' => ?_⟩
      have hzx : z ≠ x := Finset.ne_of_mem_erase hz
      have hzV : z ∉ V := fun h => hzC (Finset.mem_erase.2 ⟨hzx, h⟩)
      exact hclan.2 z (Finset.mem_of_mem_erase hz) hzV y (Finset.mem_of_mem_erase hy) y'
        (Finset.mem_of_mem_erase hy')
    have hss' : V.erase x ⊂ W.erase x := by
      refine ⟨Finset.erase_subset_erase _ hVW, fun hsub => ?_⟩
      have := hsub (Finset.mem_erase.2 ⟨fun h => hz0V (by rw [h]; exact hxV), hz0W⟩)
      exact hz0V (Finset.mem_of_mem_erase this)
    have hrx : r ∈ V.erase x := Finset.mem_erase.2 ⟨hxr.symm, hrV⟩
    have heq : contract (W.erase x) (V.erase x) r = contract W V r := by
      ext y
      simp only [contract, Finset.mem_sdiff, Finset.mem_erase]
      grind
    have hins1 := (contract_inseparable_iff skew hclan hVss hrV).1 h
    rw [← heq] at hins1
    exact (contract_inseparable_iff skew hclan' hss' hrx).2 hins1

end Deletion

end SkewRibbonCoarsenings
