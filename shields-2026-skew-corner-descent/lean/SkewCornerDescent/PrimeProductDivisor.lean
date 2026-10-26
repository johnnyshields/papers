/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Algebra.BigOperators.Associated

/-!
# Extracting a response factor from a nonunit polynomial divisor

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:residue-classifier`). A nonunit divisor of a finite prime
response product is divisible by one of its responses. This does not assume that the
divisor itself is irreducible.

Sorry-free.
-/

namespace SkewCornerDescent

/-- A nonunit divisor of a prime product contains a complete prime from that product. -/
theorem primeProduct_divisor_contains_factor {R ι : Type*} [CommMonoidWithZero R]
    [UniqueFactorizationMonoid R] (s : Finset ι) (a : ι → R)
    (ha : ∀ i ∈ s, Prime (a i)) {q : R} (hq0 : q ≠ 0) (hqu : ¬IsUnit q)
    (hd : q ∣ ∏ i ∈ s, a i) : ∃ i ∈ s, a i ∣ q := by
  obtain ⟨r, hr, hrq⟩ := WfDvdMonoid.exists_irreducible_factor hqu hq0
  have hprime : Prime r := irreducible_iff_prime.mp hr
  obtain ⟨i, hi, hri⟩ := (hprime.dvd_finsetProd_iff a).mp (hrq.trans hd)
  refine ⟨i, hi, ?_⟩
  exact (hprime.associated_of_dvd (ha i hi) hri).symm.dvd.trans hrq

end SkewCornerDescent
