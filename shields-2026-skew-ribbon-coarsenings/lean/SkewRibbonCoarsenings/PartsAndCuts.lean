/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewRibbonCoarsenings.Seam

/-!
# Compositions as lists of parts, and their cut sets

Formalizes `shields-2026-skew-ribbon-coarsenings.tex`, section `sec:algebra`
(the operations of the subsections on cuts and on composition as substitution).

A composition is a list of positive parts.  Weight is `List.sum`, length is `List.length`,
reversal is `List.reverse`, concatenation is `++`, near-concatenation `α ⊙ β` is `nearConcat`
(the two meeting parts merge), the near-power `ε^{⊙ m}` is `nearPow`, and the composition product
`α ∘ ε = ε^{⊙α₁} · ⋯ · ε^{⊙α_k}` is `compose`.  `partsCuts` is the cut set `S(β)`.  The
bridges to the cut-set operations of `Defs` (`concatCuts`, `nearCuts`, `nearPowerCuts`,
`revCuts`) are proved, together with the fact that a composition is determined by its weight
and its cut set (`partsCuts_injective`, `exists_parts_of_isCutSet`).  Sorry-free.
-/

namespace SkewRibbonCoarsenings

open Finset

/-- A list is a list of positive parts. -/
def IsParts (l : List ℕ) : Prop := ∀ a ∈ l, 0 < a

/-- The cut set `S(β) = {β₁, β₁ + β₂, …, β₁ + ⋯ + β_{k-1}}` of a list of parts. -/
def partsCuts : List ℕ → Finset ℕ
  | [] => ∅
  | [_] => ∅
  | a :: b :: l => insert a ((partsCuts (b :: l)).image (a + ·))

/-- Near-concatenation `α ⊙ β`: the last part of `α` and the first part of `β` merge. -/
def nearConcat : List ℕ → List ℕ → List ℕ
  | [], l' => l'
  | [a], [] => [a]
  | [a], b :: l₁ => (a + b) :: l₁
  | a :: c :: r, l' => a :: nearConcat (c :: r) l'

/-- The near-power `ε^{⊙ m}`. -/
def nearPow (ε : List ℕ) : ℕ → List ℕ
  | 0 => []
  | m + 1 => nearConcat (nearPow ε m) ε

/-- The composition product `α ∘ ε = ε^{⊙α₁} · ⋯ · ε^{⊙α_k}`. -/
def compose (α ε : List ℕ) : List ℕ := (α.map (nearPow ε)).flatten

/-- The product `α₁ ∘ α₂ ∘ ⋯ ∘ α_r` of a list of compositions, right-nested; the empty product is
the identity composition `(1)`. -/
def compProd : List (List ℕ) → List ℕ
  | [] => [1]
  | α :: αs => compose α (compProd αs)

/-- The coarsening polynomial of a list of parts. -/
noncomputable def Gparts (l : List ℕ) : Lam := G l.sum (partsCuts l)

/-! ### Elementary facts about the operations -/

@[simp] lemma partsCuts_nil : partsCuts [] = ∅ := rfl

@[simp] lemma partsCuts_singleton (a : ℕ) : partsCuts [a] = ∅ := rfl

lemma partsCuts_cons (a : ℕ) {l : List ℕ} (hl : l ≠ []) :
    partsCuts (a :: l) = insert a ((partsCuts l).image (a + ·)) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b l => rfl

@[simp] lemma nearConcat_nil_left (l : List ℕ) : nearConcat [] l = l := rfl

lemma nearConcat_cons (a : ℕ) {l : List ℕ} (hl : l ≠ []) (l' : List ℕ) :
    nearConcat (a :: l) l' = a :: nearConcat l l' := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b l => rfl

@[simp] lemma nearConcat_nil_right (l : List ℕ) : nearConcat l [] = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l => rw [nearConcat_cons _ (List.cons_ne_nil _ _), ih]

lemma nearConcat_ne_nil {l l' : List ℕ} (h : l ≠ [] ∨ l' ≠ []) : nearConcat l l' ≠ [] := by
  cases l with
  | nil => simpa using h
  | cons a l =>
    cases l with
    | nil => cases l' <;> simp [nearConcat]
    | cons b l => simp [nearConcat]

lemma sum_nearConcat (l l' : List ℕ) : (nearConcat l l').sum = l.sum + l'.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => cases l' <;> simp [nearConcat]; omega
    | cons b l => rw [nearConcat_cons _ (List.cons_ne_nil _ _), List.sum_cons, ih]; simp; omega

lemma isParts_nearConcat {l l' : List ℕ} (h : IsParts l) (h' : IsParts l') :
    IsParts (nearConcat l l') := by
  induction l with
  | nil => simpa using h'
  | cons a l ih =>
    cases l with
    | nil =>
      cases l' with
      | nil => simpa [nearConcat] using h
      | cons b l₁ =>
        intro x hx
        simp only [nearConcat, List.mem_cons] at hx
        rcases hx with rfl | hx
        · have := h a (by simp); have := h' b (by simp); omega
        · exact h' x (List.mem_cons_of_mem _ hx)
    | cons b l =>
      rw [nearConcat_cons _ (List.cons_ne_nil _ _)]
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h x (by simp)
      · exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx

@[simp] lemma nearPow_zero (ε : List ℕ) : nearPow ε 0 = [] := rfl

lemma nearPow_succ (ε : List ℕ) (m : ℕ) : nearPow ε (m + 1) = nearConcat (nearPow ε m) ε := rfl

@[simp] lemma nearPow_one (ε : List ℕ) : nearPow ε 1 = ε := by simp [nearPow_succ]

lemma sum_nearPow (ε : List ℕ) (m : ℕ) : (nearPow ε m).sum = m * ε.sum := by
  induction m with
  | zero => simp
  | succ m ih => rw [nearPow_succ, sum_nearConcat, ih]; ring

lemma isParts_nearPow {ε : List ℕ} (h : IsParts ε) (m : ℕ) : IsParts (nearPow ε m) := by
  induction m with
  | zero => intro x hx; simp at hx
  | succ m ih => exact isParts_nearConcat ih h

lemma nearPow_ne_nil {ε : List ℕ} (hε : ε ≠ []) {m : ℕ} (hm : m ≠ 0) : nearPow ε m ≠ [] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [nearPow_succ]
  exact nearConcat_ne_nil (Or.inr hε)

@[simp] lemma compose_nil (ε : List ℕ) : compose [] ε = [] := rfl

lemma compose_cons (a : ℕ) (α ε : List ℕ) : compose (a :: α) ε = nearPow ε a ++ compose α ε := by
  simp [compose]

lemma sum_compose (α ε : List ℕ) : (compose α ε).sum = α.sum * ε.sum := by
  induction α with
  | nil => simp
  | cons a α ih => rw [compose_cons, List.sum_append, sum_nearPow, ih, List.sum_cons]; ring

lemma isParts_compose {α ε : List ℕ} (hε : IsParts ε) : IsParts (compose α ε) := by
  induction α with
  | nil => intro x hx; simp [compose] at hx
  | cons a α ih =>
    rw [compose_cons]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact isParts_nearPow hε a x hx
    · exact ih x hx

lemma compose_ne_nil {α ε : List ℕ} (hα : α ≠ []) (hε' : ε ≠ [])
    (hαp : IsParts α) : compose α ε ≠ [] := by
  cases α with
  | nil => exact absurd rfl hα
  | cons a α =>
    rw [compose_cons]
    have ha := hαp a (by simp)
    have := nearPow_ne_nil hε' (by omega : a ≠ 0)
    intro h
    exact this (List.append_eq_nil_iff.mp h).1

/-! ### Bridges to the cut-set operations of `Defs` -/

/-- The cut set of a concatenation of nonempty compositions is `concatCuts`. -/
theorem partsCuts_append {l l' : List ℕ} (hl : l ≠ []) (hl' : l' ≠ []) :
    partsCuts (l ++ l') = concatCuts l.sum (partsCuts l) (partsCuts l') := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    rw [List.cons_append]
    rw [partsCuts_cons a (by simp [hl'])]
    by_cases h : l = []
    · subst h
      simp [concatCuts]
    · rw [ih h, partsCuts_cons a h, List.sum_cons]
      ext x
      simp only [concatCuts, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
        Finset.mem_singleton]
      grind

/-- The cut set of a near-concatenation is `nearCuts`. -/
theorem partsCuts_nearConcat (l l' : List ℕ) :
    partsCuts (nearConcat l l') = nearCuts l.sum (partsCuts l) (partsCuts l') := by
  induction l with
  | nil => simp [nearCuts]
  | cons a l ih =>
    by_cases h : l = []
    · subst h
      cases l' with
      | nil => simp [nearCuts]
      | cons b l₁ =>
        by_cases h₁ : l₁ = []
        · subst h₁; simp [nearConcat, nearCuts]
        · simp only [nearConcat, List.sum_cons, List.sum_nil, nearCuts, partsCuts_singleton,
            Finset.empty_union]
          rw [partsCuts_cons _ h₁, partsCuts_cons _ h₁, Finset.image_insert, Finset.image_image]
          simp [add_assoc]
    · rw [nearConcat_cons _ h, partsCuts_cons _ (nearConcat_ne_nil (Or.inl h)), ih,
        partsCuts_cons _ h, List.sum_cons]
      ext x
      simp only [nearCuts, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      grind

/-- The cut set of a composition lies in `{1, …, n-1}`. -/
theorem partsCuts_isCutSet {l : List ℕ} (hl : IsParts l) : IsCutSet l.sum (partsCuts l) := by
  induction l with
  | nil => simp [IsCutSet]
  | cons a l ih =>
    have ha : 0 < a := hl a (by simp)
    have hl' : IsParts l := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    by_cases h : l = []
    · subst h; simp [IsCutSet]
    · rw [partsCuts_cons a h, List.sum_cons]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_image] at hx
      have hlpos : 0 < l.sum := by
        cases l with
        | nil => exact absurd rfl h
        | cons b l =>
          have := hl' b (by simp)
          simp only [List.sum_cons]; omega
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · exact Finset.mem_Ioo.mpr ⟨ha, by omega⟩
      · have := Finset.mem_Ioo.mp (ih hl' hy)
        exact Finset.mem_Ioo.mpr ⟨by omega, by omega⟩

/-- The cut set of a reversal is `revCuts`. -/
theorem partsCuts_reverse {l : List ℕ} (hl : IsParts l) :
    partsCuts l.reverse = revCuts l.sum (partsCuts l) := by
  induction l with
  | nil => simp [revCuts]
  | cons a l ih =>
    have ha : 0 < a := hl a (by simp)
    have hl' : IsParts l := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    by_cases h : l = []
    · subst h; simp [revCuts]
    · have hc := partsCuts_isCutSet hl'
      rw [List.reverse_cons, partsCuts_append (by simpa using h) (by simp), ih hl',
        List.sum_reverse, partsCuts_cons _ h, List.sum_cons]
      ext x
      simp only [concatCuts, revCuts, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
        Finset.mem_singleton, partsCuts_singleton, Finset.image_empty, Finset.notMem_empty,
        or_false]
      have hb : ∀ y ∈ partsCuts l, y < l.sum := fun y hy => (Finset.mem_Ioo.mp (hc hy)).2
      grind

/-- The cut set of a near-power is `nearPowerCuts`. -/
theorem partsCuts_nearPow (ε : List ℕ) (m : ℕ) :
    partsCuts (nearPow ε m) = nearPowerCuts ε.sum (partsCuts ε) m := by
  induction m with
  | zero => simp [nearPowerCuts]
  | succ m ih =>
    rw [nearPow_succ, partsCuts_nearConcat, ih, sum_nearPow]
    simp only [nearCuts, nearPowerCuts, Finset.range_add_one, Finset.biUnion_insert]
    rw [Finset.union_comm]

lemma mem_compCuts {m : ℕ} {A : Finset ℕ} {p : ℕ} {E : Finset ℕ} {x : ℕ} :
    x ∈ compCuts m A p E ↔ (∃ y ∈ A, p * y = x) ∨ ∃ j < m, ∃ e ∈ E, j * p + e = x := by
  simp [compCuts]

/-- The cut set of a composition product is `compCuts` (`eq:composition-cuts`, list form). -/
theorem partsCuts_compose {α ε : List ℕ} (hα : IsParts α) (hε : ε ≠ []) :
    partsCuts (compose α ε) = compCuts α.sum (partsCuts α) ε.sum (partsCuts ε) := by
  induction α with
  | nil => simp [compose, compCuts]
  | cons a α ih =>
    have ha : 0 < a := hα a (by simp)
    have hα' : IsParts α := fun x hx => hα x (List.mem_cons_of_mem _ hx)
    by_cases h : α = []
    · subst h
      simp [compose_cons, partsCuts_nearPow, compCuts, nearPowerCuts]
    · rw [compose_cons, partsCuts_append (nearPow_ne_nil hε (by omega))
        (compose_ne_nil h hε hα'), partsCuts_nearPow, ih hα', partsCuts_cons a h, List.sum_cons,
        sum_nearPow]
      ext x
      simp only [concatCuts, nearPowerCuts, mem_compCuts, Finset.mem_union, Finset.mem_image,
        Finset.mem_insert, Finset.mem_biUnion, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro (((⟨j, hj, e, he, rfl⟩) | rfl) | ⟨z, (⟨y, hy, rfl⟩ | ⟨j, hj, e, he, rfl⟩), rfl⟩)
        · exact Or.inr ⟨j, by omega, e, he, rfl⟩
        · exact Or.inl ⟨a, Or.inl rfl, by ring⟩
        · exact Or.inl ⟨a + y, Or.inr ⟨y, hy, rfl⟩, by ring⟩
        · exact Or.inr ⟨a + j, by omega, e, he, by ring⟩
      · rintro (⟨y, (rfl | ⟨z, hz, rfl⟩), rfl⟩ | ⟨j, hj, e, he, rfl⟩)
        · exact Or.inl (Or.inr (by ring))
        · exact Or.inr ⟨ε.sum * z, Or.inl ⟨z, hz, rfl⟩, by ring⟩
        · by_cases hja : j < a
          · exact Or.inl (Or.inl ⟨j, hja, e, he, rfl⟩)
          · refine Or.inr ⟨(j - a) * ε.sum + e, Or.inr ⟨j - a, by omega, e, he, rfl⟩, ?_⟩
            have : a * ε.sum + (j - a) * ε.sum = j * ε.sum := by
              rw [← Nat.add_mul]; congr 1; omega
            omega

/-! ### A composition is determined by its weight and its cut set -/

lemma sum_pos_of_ne_nil {l : List ℕ} (hl : IsParts l) (h : l ≠ []) : 0 < l.sum := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l =>
    have := hl a (by simp)
    simp only [List.sum_cons]; omega

lemma eq_nil_of_sum_eq_zero {l : List ℕ} (hl : IsParts l) (h : l.sum = 0) : l = [] := by
  by_contra hne
  have := sum_pos_of_ne_nil hl hne
  omega

lemma isParts_tail {a : ℕ} {l : List ℕ} (h : IsParts (a :: l)) : IsParts l :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

lemma head_pos {a : ℕ} {l : List ℕ} (h : IsParts (a :: l)) : 0 < a := h a (by simp)

lemma mem_partsCuts_pos {l : List ℕ} (hl : IsParts l) {x : ℕ} (hx : x ∈ partsCuts l) : 0 < x :=
  (Finset.mem_Ioo.mp (partsCuts_isCutSet hl hx)).1

/-- Two lists of positive parts with the same weight and the same cut set are equal. -/
theorem partsCuts_injective {l l' : List ℕ} (hl : IsParts l) (hl' : IsParts l')
    (hsum : l.sum = l'.sum) (hcuts : partsCuts l = partsCuts l') : l = l' := by
  induction l generalizing l' with
  | nil => exact (eq_nil_of_sum_eq_zero hl' (by simpa using hsum.symm)).symm
  | cons a l ih =>
    cases l' with
    | nil => simpa using (eq_nil_of_sum_eq_zero hl (by simpa using hsum))
    | cons a' l' =>
      have hl1 := isParts_tail hl
      have hl1' := isParts_tail hl'
      by_cases h : l = []
      · subst h
        by_cases h' : l' = []
        · subst h'; simpa using hsum
        · rw [partsCuts_singleton, partsCuts_cons _ h'] at hcuts
          exact absurd (hcuts ▸ Finset.mem_insert_self a' _) (Finset.notMem_empty _)
      · by_cases h' : l' = []
        · subst h'
          rw [partsCuts_singleton, partsCuts_cons _ h] at hcuts
          exact absurd (hcuts ▸ Finset.mem_insert_self a _) (Finset.notMem_empty _)
        · rw [partsCuts_cons _ h, partsCuts_cons _ h'] at hcuts
          have hmin : ∀ (b : ℕ) (k : List ℕ), IsParts k →
              ∀ x ∈ (partsCuts k).image (b + ·), b < x := by
            intro b k hk x hx
            obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
            have := mem_partsCuts_pos hk hy
            omega
          have haa : a = a' := by
            have h1 : a' ∈ insert a (image (a + ·) (partsCuts l)) :=
              hcuts ▸ Finset.mem_insert_self _ _
            have h2 : a ∈ insert a' (image (a' + ·) (partsCuts l')) :=
              hcuts.symm ▸ Finset.mem_insert_self _ _
            rcases Finset.mem_insert.mp h1 with h1 | h1
            · exact h1.symm
            · rcases Finset.mem_insert.mp h2 with h2 | h2
              · exact h2
              · have := hmin a l hl1 a' h1
                have := hmin a' l' hl1' a h2
                omega
          subst haa
          have hnot : ∀ (k : List ℕ), IsParts k → a ∉ (partsCuts k).image (a + ·) := by
            intro k hk hx
            have := hmin a k hk a hx
            omega
          have himg : (partsCuts l).image (a + ·) = (partsCuts l').image (a + ·) := by
            have := congrArg (fun X => X.erase a) hcuts
            simpa [Finset.erase_insert (hnot l hl1), Finset.erase_insert (hnot l' hl1')] using this
          have hc : partsCuts l = partsCuts l' :=
            Finset.image_injective (fun x y hxy => by simpa using hxy) himg
          have hs : l.sum = l'.sum := by simpa using hsum
          rw [ih hl1 hl1' hs hc]

/-- Every admissible cut set of weight `n` is the cut set of a list of positive parts. -/
theorem exists_parts_of_isCutSet : ∀ (n : ℕ) (S : Finset ℕ), IsCutSet n S →
    ∃ l : List ℕ, IsParts l ∧ l.sum = n ∧ partsCuts l = S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS
    by_cases hn : n = 0
    · subst hn
      have : S = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        have := Finset.mem_Ioo.mp (hS hx)
        omega
      exact ⟨[], fun a ha => by simp at ha, rfl, by simp [this]⟩
    · by_cases hSe : S = ∅
      · exact ⟨[n], fun a ha => by simp at ha; omega, by simp, by simp [hSe]⟩
      · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSe
        set a := S.min' hne with ha
        have haS : a ∈ S := Finset.min'_mem S hne
        have ha0 := Finset.mem_Ioo.mp (hS haS)
        set S' := (S.erase a).image (· - a) with hS'
        have hS'c : IsCutSet (n - a) S' := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          have hyS := Finset.mem_of_mem_erase hy
          have hya : y ≠ a := Finset.ne_of_mem_erase hy
          have h1 := Finset.min'_le S y hyS
          have h2 := Finset.mem_Ioo.mp (hS hyS)
          exact Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
        obtain ⟨l, hlp, hls, hlc⟩ := ih (n - a) (by omega) S' hS'c
        have hlne : l ≠ [] := by
          rintro rfl
          simp at hls
          omega
        refine ⟨a :: l, ?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha0.1
          · exact hlp x hx
        · simp only [List.sum_cons, hls]; omega
        · rw [partsCuts_cons a hlne, hlc]
          ext x
          simp only [hS', Finset.mem_insert, Finset.mem_image, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨z, ⟨y, ⟨hya, hyS⟩, rfl⟩, rfl⟩)
            · exact haS
            · have := Finset.min'_le S y hyS
              convert hyS using 1
              omega
          · intro hx
            by_cases hxa : x = a
            · exact Or.inl hxa
            · refine Or.inr ⟨x - a, ⟨x, ⟨hxa, hx⟩, rfl⟩, ?_⟩
              have := Finset.min'_le S x hx
              omega

end SkewRibbonCoarsenings
