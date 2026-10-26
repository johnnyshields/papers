import Mathlib.RingTheory.Coprime.Lemmas
import SkewGluing.PeriodWords.Defs

/-!
# Connectivity of two-period systems through the cycles of the smaller period

Formalizes `shields-2026-skew-gluing.tex`, «Period words, line inners, and small
overlaps» (`lem:gluing-periods`).

The proof of `lem:gluing-periods` contracts the classes of the smaller period `s`; translation by
the larger period `ℓ` then acts on the contracted residues by cycles, one for each class modulo
`gcd s ℓ`.  This module proves, for an arbitrary equivalence relation `J` containing the edges
(so for the period graph itself and for the kernel of a word), that if the edge out of every
contracted vertex is present except for at most one, then all positions of one gcd class are
related, apart from positions with no edge to any other class.

Sorry-free.
-/

namespace SkewGluing
namespace PeriodWords

section Chain

variable {X : Type*} {J : X → X → Prop}

/-- Walking along consecutive edges of a sequence relates the first node to every later one. -/
theorem chain_rel (hJ : Equivalence J) (f : ℤ → X) (c : ℤ) (N : ℕ)
    (h : ∀ j : ℕ, 1 ≤ j → j < N → J (f (c + j)) (f (c + j + 1))) :
    ∀ j : ℕ, 1 ≤ j → j ≤ N → J (f (c + 1)) (f (c + j)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; simpa using hJ.refl _
  | succ j hj ih =>
    intro hjN
    have h1 := ih (by omega)
    have h2 := h j hj (by omega)
    have e : c + ((j + 1 : ℕ) : ℤ) = c + j + 1 := by push_cast; ring
    rw [e]
    exact hJ.trans h1 h2

end Chain

/-- Congruent integers have equal residues. -/
theorem emod_eq_of_dvd_sub {n a b : ℤ} (h : n ∣ a - b) : a % n = b % n :=
  Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd h)

theorem dvd_sub_of_emod_eq {n a b : ℤ} (h : a % n = b % n) : n ∣ a - b :=
  Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.1 h)

section Closure

variable {J : ℤ → ℤ → Prop}

/-- Positions of one residue class of a period with no exceptional residue there are related. -/
theorem related_of_dvd (hJ : Equivalence J) {L s : ℕ} {S : Finset ℤ} (hs : 0 < s)
    (he : ∀ x y, periodEdge L s S x y → J x y) {x y : ℤ} (hx : x ∈ Finset.Icc (1 : ℤ) L)
    (hy : y ∈ Finset.Icc (1 : ℤ) L) (hxy : (s : ℤ) ∣ y - x) (hS : x % (s : ℤ) ∉ S) :
    J x y := by
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  have fwd : ∀ t : ℕ, ∀ x : ℤ, 1 ≤ x → x + t * s ≤ L → x % (s : ℤ) ∉ S →
      J x (x + t * s) := by
    intro t
    induction t with
    | zero => intro x _ _ _; simpa using hJ.refl x
    | succ t ih =>
      intro x hx1 hxL hS
      push_cast at hxL
      have h1 := ih x hx1 (by nlinarith) hS
      have h2 : J (x + t * s) (x + ((t + 1 : ℕ) : ℤ) * s) := by
        apply he
        refine ⟨?_, ?_, ?_⟩
        · simp only [Finset.mem_Icc]
          constructor <;> nlinarith
        · rwa [Int.add_mul_emod_self_right]
        · push_cast; ring
      exact hJ.trans h1 h2
  obtain ⟨t, ht⟩ := hxy
  have hy' : y = x + t * s := by linarith [mul_comm (s : ℤ) t]
  simp only [Finset.mem_Icc] at hx hy
  rcases le_total 0 t with h0 | h0
  · obtain ⟨t', rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [hy']
    exact fwd t' x hx.1 (by rw [← hy']; exact hy.2) hS
  · obtain ⟨t', ht'⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 h0)
    have hx' : x = y + t' * s := by
      have : t = -(t' : ℤ) := by omega
      rw [this] at hy'
      linarith
    have hSy : y % (s : ℤ) ∉ S := by
      rw [hy', Int.add_mul_emod_self_right]; exact hS
    have := fwd t' y hy.1 (by rw [← hx']; exact hx.2) hSy
    rw [← hx'] at this
    exact hJ.symm this

end Closure

section Cycle

/-- The class of the position `y` modulo `s` has an edge of the larger period `ℓ` leaving it:
some position `z` of the class has its `ℓ`-edge `z ~ z + ℓ` present within `1, …, L`. -/
def Avail (L s ℓ : ℕ) (T : Finset ℤ) (y : ℤ) : Prop :=
  ∃ z ∈ Finset.Icc (1 : ℤ) ((L : ℤ) - ℓ), z % (ℓ : ℤ) ∉ T ∧ (s : ℤ) ∣ z - y

/-- The contracted vertex of `y` has no outgoing edge: its class modulo `s` is exceptional for
the period `s` (so its positions are not identified), or no `ℓ`-edge leaves the class. -/
def Missing (L s ℓ : ℕ) (Ss T : Finset ℤ) (y : ℤ) : Prop :=
  y % (s : ℤ) ∈ Ss ∨ ¬ Avail L s ℓ T y

/-- The `n`-th contracted residue, as a representative in `1, …, s`, met when starting at `y₀` and
translating `n` times by `ℓ` modulo `s`. -/
def cycRep (s ℓ : ℕ) (y₀ n : ℤ) : ℤ := (y₀ - 1 + n * ℓ) % (s : ℤ) + 1

theorem cycRep_mem {s : ℕ} (hs : 0 < s) (ℓ : ℕ) (y₀ n : ℤ) :
    cycRep s ℓ y₀ n ∈ Finset.Icc (1 : ℤ) s := by
  unfold cycRep
  simp only [Finset.mem_Icc]
  have h0 := Int.emod_nonneg (y₀ - 1 + n * ℓ) (by omega : (s : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos (y₀ - 1 + n * ℓ) (by omega : (0 : ℤ) < s)
  omega

theorem cycRep_succ (s ℓ : ℕ) (y₀ n : ℤ) :
    (s : ℤ) ∣ cycRep s ℓ y₀ (n + 1) - (cycRep s ℓ y₀ n + ℓ) := by
  refine ⟨(y₀ - 1 + n * ℓ) / s - (y₀ - 1 + (n + 1) * ℓ) / s, ?_⟩
  unfold cycRep
  rw [Int.emod_def, Int.emod_def]
  ring

theorem cycRep_eq_of_dvd {s ℓ : ℕ} {y₀ n n' : ℤ}
    (h : (s : ℤ) ∣ (n - n') * ℓ) : cycRep s ℓ y₀ n = cycRep s ℓ y₀ n' := by
  unfold cycRep
  congr 1
  apply emod_eq_of_dvd_sub
  have : y₀ - 1 + n * ℓ - (y₀ - 1 + n' * ℓ) = (n - n') * ℓ := by ring
  rw [this]
  exact h

theorem cycRep_edge {J : ℤ → ℤ → Prop} (hJ : Equivalence J) {L s ℓ : ℕ} {Ss T : Finset ℤ}
    (hs : 0 < s) (hsL : s ≤ L) (heS : ∀ x y, periodEdge L s Ss x y → J x y)
    (heT : ∀ x y, periodEdge L ℓ T x y → J x y) {y₀ n : ℤ}
    (hn : ¬ Missing L s ℓ Ss T (cycRep s ℓ y₀ n))
    (hn1 : cycRep s ℓ y₀ (n + 1) % (s : ℤ) ∉ Ss) :
    J (cycRep s ℓ y₀ n) (cycRep s ℓ y₀ (n + 1)) := by
  unfold Missing at hn
  push Not at hn
  obtain ⟨hrS, hav⟩ := hn
  obtain ⟨z, hz, hzT, hzd⟩ := hav
  have hzL : z ∈ Finset.Icc (1 : ℤ) L := by
    simp only [Finset.mem_Icc] at hz ⊢
    omega
  have hmem : ∀ m, cycRep s ℓ y₀ m ∈ Finset.Icc (1 : ℤ) L := by
    intro m
    have := cycRep_mem hs ℓ y₀ m
    simp only [Finset.mem_Icc] at this ⊢
    omega
  have h1 : J (cycRep s ℓ y₀ n) z :=
    related_of_dvd hJ hs heS (hmem n) hzL hzd hrS
  have h2 : J z (z + ℓ) := heT z _ ⟨hz, hzT, rfl⟩
  have hzl : z + ℓ ∈ Finset.Icc (1 : ℤ) L := by
    simp only [Finset.mem_Icc] at hz ⊢
    omega
  have hd : (s : ℤ) ∣ cycRep s ℓ y₀ (n + 1) - (z + ℓ) := by
    have h3 := cycRep_succ s ℓ y₀ n
    have : cycRep s ℓ y₀ (n + 1) - (z + ℓ) =
        (cycRep s ℓ y₀ (n + 1) - (cycRep s ℓ y₀ n + ℓ)) + (cycRep s ℓ y₀ n - z) := by ring
    rw [this]
    exact dvd_add h3 ((dvd_sub_comm).1 hzd)
  have hS : (z + ℓ) % (s : ℤ) ∉ Ss := by
    rw [emod_eq_of_dvd_sub ((dvd_sub_comm).1 hd)]
    exact hn1
  have h3 : J (z + ℓ) (cycRep s ℓ y₀ (n + 1)) :=
    related_of_dvd hJ hs heS hzl (hmem _) hd hS
  exact hJ.trans h1 (hJ.trans h2 h3)

/-- Every contracted vertex on a gcd cycle whose class is not exceptional is related to every
other, provided at most one vertex of `1, …, s` lacks an outgoing edge.  Here `s = g k` and
`ℓ = g l` with `k ≥ 2` and `k, l` coprime, so that the cycle has `k` vertices. -/
theorem cycle_rel {J : ℤ → ℤ → Prop} (hJ : Equivalence J) {L s ℓ g k l : ℕ} {Ss T : Finset ℤ}
    (hs : s = g * k) (hl : ℓ = g * l) (hg : 0 < g) (hk : 2 ≤ k) (hcop : Nat.Coprime k l)
    (hsL : s ≤ L) (heS : ∀ x y, periodEdge L s Ss x y → J x y)
    (heT : ∀ x y, periodEdge L ℓ T x y → J x y)
    (hmiss : ∀ y ∈ Finset.Icc (1 : ℤ) s, ∀ y' ∈ Finset.Icc (1 : ℤ) s,
      Missing L s ℓ Ss T y → Missing L s ℓ Ss T y' → y = y') (y₀ : ℤ) :
    ∀ n m : ℤ, cycRep s ℓ y₀ n % (s : ℤ) ∉ Ss → cycRep s ℓ y₀ m % (s : ℤ) ∉ Ss →
      J (cycRep s ℓ y₀ n) (cycRep s ℓ y₀ m) := by
  have hk0 : 0 < k := by omega
  have hs0 : 0 < s := by rw [hs]; positivity
  have hsZ : (s : ℤ) = g * k := by exact_mod_cast hs
  have hlZ : (ℓ : ℤ) = g * l := by exact_mod_cast hl
  have hgZ : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have mem := cycRep_mem hs0 ℓ y₀
  have hper : ∀ n t : ℤ, cycRep s ℓ y₀ (n + k * t) = cycRep s ℓ y₀ n := by
    intro n t
    unfold cycRep
    have : y₀ - 1 + (n + k * t) * ℓ = (y₀ - 1 + n * ℓ) + s * (l * t) := by
      rw [hsZ, hlZ]; ring
    rw [this, Int.add_mul_emod_self_left]
  have hinj : ∀ n n' : ℤ, cycRep s ℓ y₀ n = cycRep s ℓ y₀ n' → (k : ℤ) ∣ n - n' := by
    intro n n' h
    unfold cycRep at h
    have h1 := dvd_sub_of_emod_eq (by omega : (y₀ - 1 + n * ℓ) % (s : ℤ) =
      (y₀ - 1 + n' * ℓ) % (s : ℤ))
    have h2 : (g : ℤ) * k ∣ g * ((n - n') * l) := by
      have : y₀ - 1 + n * ℓ - (y₀ - 1 + n' * ℓ) = g * ((n - n') * l) := by rw [hlZ]; ring
      rw [this, hsZ] at h1
      exact h1
    have h3 := (mul_dvd_mul_iff_left hgZ).1 h2
    exact (Nat.isCoprime_iff_coprime.2 hcop).dvd_of_dvd_mul_right h3
  obtain ⟨c, hc⟩ : ∃ c : ℤ, ∀ n : ℤ, Missing L s ℓ Ss T (cycRep s ℓ y₀ n) → (k : ℤ) ∣ n - c := by
    by_cases hex : ∃ n, Missing L s ℓ Ss T (cycRep s ℓ y₀ n)
    · obtain ⟨c, hcm⟩ := hex
      exact ⟨c, fun n hn => hinj n c (hmiss _ (mem n) _ (mem c) hn hcm)⟩
    · push Not at hex
      exact ⟨0, fun n hn => absurd hn (hex n)⟩
  have hA : ∀ j : ℕ, 1 ≤ j → j < k → ¬ Missing L s ℓ Ss T (cycRep s ℓ y₀ (c + j)) := by
    intro j hj1 hjk hm
    have h2 : (k : ℤ) ∣ (j : ℤ) := by simpa using hc _ hm
    have := Int.le_of_dvd (by omega) h2
    omega
  have hAS : ∀ j : ℕ, 1 ≤ j → j < k → cycRep s ℓ y₀ (c + j) % (s : ℤ) ∉ Ss := by
    intro j hj1 hjk h
    exact hA j hj1 hjk (Or.inl h)
  have hB : ∀ n : ℤ, cycRep s ℓ y₀ n % (s : ℤ) ∉ Ss →
      J (cycRep s ℓ y₀ n) (cycRep s ℓ y₀ (c + 1)) := by
    intro n hn
    have hkz : (0 : ℤ) < k := by exact_mod_cast hk0
    have h0 := Int.emod_nonneg (n - c - 1) hkz.ne'
    have h1 := Int.emod_lt_of_pos (n - c - 1) hkz
    have h2 := Int.emod_add_mul_ediv (n - c - 1) k
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ (n - c - 1) % (k : ℤ) + 1)
    obtain ⟨q, hq⟩ : ∃ q : ℤ, n = c + j + k * q := ⟨(n - c - 1) / k, by omega⟩
    have hj1 : 1 ≤ j := by omega
    have hjk : j ≤ k := by omega
    have hrn : cycRep s ℓ y₀ n = cycRep s ℓ y₀ (c + j) := by
      rw [hq]; exact hper _ _
    have key := chain_rel hJ (fun m => cycRep s ℓ y₀ m) c j (by
      intro i hi hij
      have hn1 : cycRep s ℓ y₀ (c + i + 1) % (s : ℤ) ∉ Ss := by
        by_cases hik : i + 1 < k
        · have := hAS (i + 1) (by omega) hik
          simpa [add_assoc] using this
        · have hjk' : j = i + 1 := by omega
          have e : c + (i : ℤ) + 1 = c + j := by rw [hjk']; push_cast; ring
          rw [e, ← hrn]; exact hn
      exact cycRep_edge hJ hs0 hsL heS heT (hA i hi (by omega)) hn1) j hj1 le_rfl
    rw [hrn]
    exact hJ.symm key
  intro n m hn hm
  exact hJ.trans (hB n hn) (hJ.symm (hB m hm))

end Cycle

end PeriodWords
end SkewGluing
