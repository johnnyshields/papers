/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Common
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.TFAE
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Zify

/-!
# The Mathlib tactics used throughout the development
TODO-COPIED from `skew-factor-gluing/lean/SkewGluing/Tactics.lean`.

Formalizes `shields-2026-skew-factor-gluing.tex`; this module carries no mathematical content.

Importing it makes the Mathlib tactics that the proofs of the whole development rely on
(`ring`, `linarith`, `nlinarith`, `positivity`, `norm_num`, `abel`, `fin_cases`, `interval_cases`,
`linear_combination`, `tauto`, `set`, `push_cast`, …) available in every module below it.
The modules of the development that import no other module of it import this one.

Sorry-free.
-/
