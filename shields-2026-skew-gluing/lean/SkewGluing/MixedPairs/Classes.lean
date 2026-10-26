import SkewGluing.MixedPairs.Words

/-!
# Period words restricted to one gcd class

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small overlaps»
(`lem:gluing-periods`) as it is applied in «Pairs involving mixed charts».

`lem:gluing-periods` is stated for words with one exceptional residue per period.  A case-(d) chart
has two exceptional residues `t, s` for the word `A`; when they lie in different classes modulo
`g = gcd p Q`, each gcd class sees at most one of them.  `mixFold_eq_of_joined_class` turns the
period graph of the exceptional residues of one class into equalities of any word with the full
constraints, and `mixFold_class_one_hole` applies `lem:gluing-periods` (i) on a class.

Sorry-free.
-/

namespace SkewGluing

open PeriodWords

/-- A word with a full period `g` is constant on the positions of `1, …, L` in one class modulo
`g`. -/
theorem mixFold_eq_of_period_empty {f : ℤ → ℤ} {L g : ℕ} (hg : 0 < g)
    (hf : PeriodExcept L g ∅ f) {x y : ℤ} (hx : x ∈ Finset.Icc (1 : ℤ) L)
    (hy : y ∈ Finset.Icc (1 : ℤ) L) (hxy : (g : ℤ) ∣ y - x) : f x = f y := by
  have key : ∀ (k : ℕ) (x : ℤ), x ∈ Finset.Icc (1 : ℤ) L → x + k * g ∈ Finset.Icc (1 : ℤ) L →
      f x = f (x + k * g) := by
    intro k
    induction k with
    | zero => intro x _ _; simp
    | succ k ih =>
      intro x hx hxk
      simp only [Finset.mem_Icc] at hx hxk
      have h1 := ih x (by simp only [Finset.mem_Icc]; push_cast at hxk ⊢; constructor <;> nlinarith)
        (by simp only [Finset.mem_Icc]; push_cast at hxk ⊢; constructor <;> nlinarith)
      have h2 : f (x + k * g) = f (x + k * g + g) := hf (x + k * g) (by
        simp only [Finset.mem_Icc]; push_cast at hxk ⊢; constructor <;> nlinarith) (by simp)
      have e : x + ((k + 1 : ℕ) : ℤ) * g = x + k * g + g := by push_cast; ring
      rw [e, ← h2]; exact h1
  obtain ⟨c, hc⟩ := hxy
  rcases le_total 0 c with hc0 | hc0
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hc0
    have e : x + (k : ℤ) * g = y := by linarith
    have := key k x hx (by rw [e]; exact hy)
    rw [e] at this; exact this
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -c by omega)
    have e : y + (k : ℤ) * g = x := by rw [show (k : ℤ) = -c by omega]; linarith
    have := key k y hy (by rw [e]; exact hx)
    rw [e] at this
    exact this.symm

/-- Fewer exceptional residues give more edges: the period graph is monotone. -/
theorem mixFold_periodJoined_mono {L p Q : ℕ} {S S' T T' : Finset ℤ} (hS : S' ⊆ S) (hT : T' ⊆ T)
    {x y : ℤ} (h : PeriodJoined L p S Q T x y) : PeriodJoined L p S' Q T' x y := by
  induction h with
  | rel x y h =>
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Relation.EqvGen.rel _ _ (Or.inl ⟨h1, fun hh => h2 (hS hh), h3⟩)
    · exact Relation.EqvGen.rel _ _ (Or.inr ⟨h1, fun hh => h2 (hT hh), h3⟩)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- A word with period `p` except at `S` and `Q` except at `T`, where `g` divides both periods, is
constant on the positions of one class modulo `g` joined in the period graph of the exceptional
residues of that class alone. -/
theorem mixFold_eq_of_joined_class {f : ℤ → ℤ} {L p Q g : ℕ} {S T : Finset ℤ} (hgp : (g : ℤ) ∣ p)
    (hgQ : (g : ℤ) ∣ Q) (hfp : PeriodExcept L p S f) (hfQ : PeriodExcept L Q T f) (ρ : ℤ)
    {x y : ℤ} (hx : x % (g : ℤ) = ρ)
    (h : PeriodJoined L p (S.filter fun a => a % (g : ℤ) = ρ) Q
      (T.filter fun a => a % (g : ℤ) = ρ) x y) : f x = f y := by
  have key : ∀ a b : ℤ, Relation.EqvGen (fun x y =>
      periodEdge L p (S.filter fun a => a % (g : ℤ) = ρ) x y ∨
      periodEdge L Q (T.filter fun a => a % (g : ℤ) = ρ) x y) a b →
      (a % (g : ℤ) = ρ ↔ b % (g : ℤ) = ρ) ∧ (a % (g : ℤ) = ρ → f a = f b) := by
    intro a b hab
    induction hab with
    | rel a b hr =>
      rcases hr with ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩
      · have hmod : (a + p) % (g : ℤ) = a % (g : ℤ) := by
          obtain ⟨c, hc⟩ := hgp
          rw [hc, Int.add_emod, Int.mul_emod_right, add_zero, Int.emod_emod_of_dvd _ dvd_rfl]
        refine ⟨by rw [hmod], fun hρ => ?_⟩
        apply hfp a h1
        intro hS
        apply h2
        rw [Finset.mem_filter]
        exact ⟨hS, by rw [Int.emod_emod_of_dvd _ hgp]; exact hρ⟩
      · have hmod : (a + Q) % (g : ℤ) = a % (g : ℤ) := by
          obtain ⟨c, hc⟩ := hgQ
          rw [hc, Int.add_emod, Int.mul_emod_right, add_zero, Int.emod_emod_of_dvd _ dvd_rfl]
        refine ⟨by rw [hmod], fun hρ => ?_⟩
        apply hfQ a h1
        intro hT
        apply h2
        rw [Finset.mem_filter]
        exact ⟨hT, by rw [Int.emod_emod_of_dvd _ hgQ]; exact hρ⟩
    | refl a => exact ⟨Iff.rfl, fun _ => rfl⟩
    | symm a b _ ih => exact ⟨ih.1.symm, fun hb => (ih.2 (ih.1.mpr hb)).symm⟩
    | trans a b c _ _ ih1 ih2 =>
      exact ⟨ih1.1.trans ih2.1, fun ha => (ih1.2 ha).trans (ih2.2 (ih1.1.mp ha))⟩
  exact (key x y h).2 hx

/-- **`lem:gluing-periods` (i) on one gcd class.**  A word with a full period `Q` and a smaller
period `p` (`p ∤ Q`) whose exceptional residues `S` contain at most one residue of the class of `x`
modulo `g = gcd p Q` is constant on that class, on `1, …, L` with `L ≥ 2 Q`. -/
theorem mixFold_class_one_hole {f : ℤ → ℤ} {L p Q : ℕ} {S : Finset ℤ} (hp : 0 < p) (hpQ : p < Q)
    (hnd : ¬ p ∣ Q) (hL : 2 * Q ≤ L) (hfQ : PeriodExcept L Q ∅ f) (hfp : PeriodExcept L p S f)
    {x y : ℤ} (hx : x ∈ Finset.Icc (1 : ℤ) L) (hy : y ∈ Finset.Icc (1 : ℤ) L)
    (hxy : ((Nat.gcd p Q : ℕ) : ℤ) ∣ y - x)
    (hS : (S.filter fun a => a % ((Nat.gcd p Q : ℕ) : ℤ) = x % ((Nat.gcd p Q : ℕ) : ℤ)).card ≤ 1) :
    f x = f y := by
  obtain ⟨h, hh⟩ := Finset.card_le_one_iff_subset_singleton.mp hS
  have hgp : ((Nat.gcd p Q : ℕ) : ℤ) ∣ p := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left p Q)
  have hgQ : ((Nat.gcd p Q : ℕ) : ℤ) ∣ Q := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right p Q)
  have hj := periods_one_hole_of_gt hp hpQ hnd h hL hx hy (by rwa [Nat.gcd_comm])
  rw [periodJoined_comm] at hj
  have hj' := mixFold_periodJoined_mono (S := {h}) (S' := S.filter fun a =>
    a % ((Nat.gcd p Q : ℕ) : ℤ) = x % ((Nat.gcd p Q : ℕ) : ℤ)) (T := ∅) (T' := ∅) hh
    (Finset.Subset.refl _) hj
  exact mixFold_eq_of_joined_class hgp hgQ hfp hfQ (x % ((Nat.gcd p Q : ℕ) : ℤ)) rfl hj'

end SkewGluing
