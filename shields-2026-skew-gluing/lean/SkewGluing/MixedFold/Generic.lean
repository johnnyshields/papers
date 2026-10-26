import SkewGluing.MixedFold.Extra
import SkewGluing.MixedFold.Classes

/-!
# Two case-(d) charts of one parent: generic bits

Formalizes `shields-2026-skew-gluing.tex`, «Pairs involving mixed charts»
(`prop:gluing-mixed-fold`, the first paragraph of its proof, with `lem:gluing-collision` and
`lem:gluing-periods` (ii)).

`MixFoldPair A B N p Q …` collects what two case-(d) charts of nondividing periods `p`, `Q` of one
parent say about its bit words: both boundary codings, the extra private heights, the shape of
the words, and a positive remainder `N mod gcd p Q`.  With `g = gcd p Q`:

* `MixFoldPair.noncollide_of_lt`: the two phases of each chart are distinct modulo `g`
  (`lem:gluing-collision`), so every gcd class carries at most one hole from each period;
* `MixFoldPair.generic_eq`: two positions of one class that are not simultaneous holes carry the
  same bit of `A` (`lem:gluing-periods` (ii)), the generic bit `A⁰` of the class.

Sorry-free.
-/

namespace SkewGluing

open PeriodWords

/-- The setting of `prop:gluing-mixed-fold`: two case-(d) charts, of periods `p`, `Q`, widths
`w₁`, `w₂`, phases `(s₁, t₁)`, `(s₂, t₂)`, of one parent with bit words `A`, `B` of span `N`, with
nondividing periods and positive remainder modulo `g = gcd p Q`. -/
structure MixFoldPair (A B : ℤ → ℤ) (N p Q w₁ w₂ : ℕ) (s₁ t₁ s₂ t₂ : ℤ) : Prop where
  c₁ : MixFoldCoding A B N p w₁ .d s₁ t₁
  c₂ : MixFoldCoding A B N Q w₂ .d s₂ t₂
  x₁ : MixFoldExtra A B N p w₁ s₁ t₁
  x₂ : MixFoldExtra A B N Q w₂ s₂ t₂
  ok : MixFoldWordsOK A B N
  w₁_pos : 0 < w₁
  w₂_pos : 0 < w₂
  nd₁ : ¬ p ∣ Q
  nd₂ : ¬ Q ∣ p
  rem : 0 < N % Nat.gcd p Q

/-- A simultaneous hole of the two period constraints on `A`: a position exceptional for both. -/
def mixFoldSim (p Q : ℕ) (s₁ t₁ s₂ t₂ : ℤ) (x : ℤ) : Prop :=
  x % (p : ℤ) ∈ ({t₁, s₁} : Finset ℤ) ∧ x % (Q : ℤ) ∈ ({t₂, s₂} : Finset ℤ)

namespace MixFoldPair

variable {A B : ℤ → ℤ} {N p Q w₁ w₂ : ℕ} {s₁ t₁ s₂ t₂ : ℤ}

theorem symm (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) :
    MixFoldPair A B N Q p w₂ w₁ s₂ t₂ s₁ t₁ := by
  refine ⟨P.c₂, P.c₁, P.x₂, P.x₁, P.ok, P.w₂_pos, P.w₁_pos, P.nd₂, P.nd₁, ?_⟩
  rw [Nat.gcd_comm]; exact P.rem

theorem p_pos (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) : 0 < p := P.c₁.q_pos
theorem Q_pos (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) : 0 < Q := P.c₂.q_pos

theorem g_pos (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) : 0 < Nat.gcd p Q :=
  Nat.gcd_pos_of_pos_left _ P.p_pos

theorem perB (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) :
    PeriodExcept (N - 1) (Nat.gcd p Q) ∅ B :=
  mixFold_B_periodic P.c₁ P.w₁_pos P.c₂ (fun h => by cases h) P.nd₁ P.nd₂

theorem perA₁ (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) :
    PeriodExcept (N - 1) p {t₁, s₁} A := by
  have := P.c₁.perA
  simpa [codingHolesA, P.w₁_pos.ne', holesA] using this

theorem perA₂ (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) :
    PeriodExcept (N - 1) Q {t₂, s₂} A := by
  have := P.c₂.perA
  simpa [codingHolesA, P.w₂_pos.ne', holesA] using this

theorem card_class_le_one {g : ℕ} {a b : ℤ} (h : a % (g : ℤ) ≠ b % (g : ℤ)) (x : ℤ) :
    (mixFoldClass g ({a, b} : Finset ℤ) x).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro y hy z hz
  simp only [mixFoldClass, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hy hz
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hz1, hz2⟩ := hz
  rcases hy1 with rfl | rfl <;> rcases hz1 with rfl | rfl
  · rfl
  · exact absurd (hy2.trans hz2.symm) h
  · exact absurd (hz2.trans hy2.symm) h
  · rfl

theorem class_empty {g : ℕ} {a b : ℤ} (x : ℤ) (ha : a % (g : ℤ) ≠ x % (g : ℤ))
    (hb : b % (g : ℤ) ≠ x % (g : ℤ)) : mixFoldClass g ({a, b} : Finset ℤ) x = ∅ := by
  ext y
  simp only [mixFoldClass, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty, iff_false, not_and]
  rintro (rfl | rfl)
  · exact ha
  · exact hb

/-- **Non-collision, smaller chart.**  If the period of the first chart is the smaller, its two
phases are distinct modulo `g` and so are those of the second chart. -/
theorem noncollide_of_lt (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) (hlt : p < Q) :
    t₁ % (Nat.gcd p Q : ℤ) ≠ s₁ % (Nat.gcd p Q : ℤ) ∧
      t₂ % (Nat.gcd p Q : ℤ) ≠ s₂ % (Nat.gcd p Q : ℤ) := by
  have hg := P.g_pos
  have hgp : Nat.gcd p Q ∣ p := Nat.gcd_dvd_left p Q
  have hgQ : Nat.gcd p Q ∣ Q := Nat.gcd_dvd_right p Q
  have hN1 := P.c₁.two_q_add_w_le
  have hN2 := P.c₂.two_q_add_w_le
  obtain ⟨hs1, hs2, ht1, ht2, -⟩ := P.c₁.phases P.w₁_pos
  obtain ⟨hs1', hs2', ht1', ht2', -⟩ := P.c₂.phases P.w₂_pos
  have hwp := P.c₁.w_lt
  have hwQ := P.c₂.w_lt
  have hone : ∀ x : ℤ, x ∈ Finset.Icc (1 : ℤ) ((N - 1 : ℕ) : ℤ) ↔ 1 ≤ x ∧ x ≤ (N : ℤ) - 1 := by
    intro x; rw [Finset.mem_Icc]; omega
  have hcard : ({t₂, s₂} : Finset ℤ).card ≤ 2 := Finset.card_le_two
  have first : t₁ % (Nat.gcd p Q : ℤ) ≠ s₁ % (Nat.gcd p Q : ℤ) := by
    intro hcol
    refine mixFold_collision_words P.c₁ P.w₁_pos P.ok hg hgp P.rem P.perB
      (R := t₁ % (Nat.gcd p Q : ℤ)) ?_ hcol.symm rfl
    intro x hx hxR
    rw [Finset.mem_Icc] at hx
    have hxR' : x % (Nat.gcd p Q : ℤ) ≠ t₁ % (Nat.gcd p Q : ℤ) := by simpa using hxR
    refine mixFold_class_eq_T_two (u := w₂) (S := {t₁, s₁}) (T := {t₂, s₂}) P.p_pos hlt hwQ
      (fun a ha => ?_) hcard (by omega) P.perA₁ P.perA₂ ((hone x).mpr (by omega))
      ((hone (x + Nat.gcd p Q)).mpr (by omega)) (by simp)
      (class_empty x (fun h => hxR' h.symm) (fun h => hxR' (by rw [hcol]; exact h.symm)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    omega
  refine ⟨first, fun hcol => ?_⟩
  refine mixFold_collision_words P.c₂ P.w₂_pos P.ok hg hgQ P.rem P.perB
    (R := t₂ % (Nat.gcd p Q : ℤ)) ?_ hcol.symm rfl
  intro x hx hxR
  rw [Finset.mem_Icc] at hx
  have hxR' : x % (Nat.gcd p Q : ℤ) ≠ t₂ % (Nat.gcd p Q : ℤ) := by simpa using hxR
  refine mixFold_class_eq_S (S := {t₁, s₁}) (T := {t₂, s₂}) P.p_pos P.Q_pos P.nd₁ P.nd₂
    (by rw [max_eq_right hlt.le]; omega) P.perA₁ P.perA₂ ((hone x).mpr (by omega))
    ((hone (x + Nat.gcd p Q)).mpr (by omega)) (by simp) (card_class_le_one first x)
    (class_empty x (fun h => hxR' h.symm) (fun h => hxR' (by rw [hcol]; exact h.symm)))

/-- Non-collision, for either order of the periods. -/
theorem noncollide (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) :
    t₁ % (Nat.gcd p Q : ℤ) ≠ s₁ % (Nat.gcd p Q : ℤ) ∧
      t₂ % (Nat.gcd p Q : ℤ) ≠ s₂ % (Nat.gcd p Q : ℤ) := by
  rcases lt_trichotomy p Q with hlt | heq | hgt
  · exact P.noncollide_of_lt hlt
  · exact absurd (heq ▸ dvd_refl p) P.nd₁
  · have := P.symm.noncollide_of_lt hgt
    rw [Nat.gcd_comm] at this
    exact ⟨this.2, this.1⟩

/-- **Generic bits.**  Two positions of `1, …, N - 1` in one class modulo `g`, neither a
simultaneous hole, carry the same bit of `A`. -/
theorem generic_eq (P : MixFoldPair A B N p Q w₁ w₂ s₁ t₁ s₂ t₂) {x y : ℤ}
    (hx : 1 ≤ x ∧ x ≤ (N : ℤ) - 1) (hy : 1 ≤ y ∧ y ≤ (N : ℤ) - 1)
    (hxy : ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - x) (hx' : ¬ mixFoldSim p Q s₁ t₁ s₂ t₂ x)
    (hy' : ¬ mixFoldSim p Q s₁ t₁ s₂ t₂ y) : A x = A y := by
  obtain ⟨nc₁, nc₂⟩ := P.noncollide
  obtain ⟨r, hr, hNr⟩ := P.c₁.span_eq
  obtain ⟨m, hm, hNm⟩ := P.c₂.span_eq
  obtain ⟨hs1, hs2, ht1, ht2, -⟩ := P.c₁.phases P.w₁_pos
  obtain ⟨hs1', hs2', ht1', ht2', -⟩ := P.c₂.phases P.w₂_pos
  have hone : ∀ x : ℤ, (1 ≤ x ∧ x ≤ (N : ℤ) - 1) → x ∈ Finset.Icc (1 : ℤ) ((N - 1 : ℕ) : ℤ) := by
    intro x hx
    have := P.c₁.two_q_add_w_le
    rw [Finset.mem_Icc]; omega
  refine mixFold_class_eq_two_holes (S := {t₁, s₁}) (T := {t₂, s₂}) P.p_pos P.Q_pos hr hm
    P.c₁.w_lt P.c₂.w_lt hNr hNm P.nd₁ P.nd₂ (fun a ha => ?_) (fun a ha => ?_) (by simp) (by simp)
    P.perA₁ P.perA₂ (hone x hx) (hone y hy) hxy (card_class_le_one nc₁ x)
    (card_class_le_one nc₂ x) hx' hy'
  · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    omega

end MixFoldPair

end SkewGluing
