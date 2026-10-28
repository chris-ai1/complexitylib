/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-! Plain certificates for concrete disjunctions, inequalities, searches, bounded powers and
range products, without a tidy round trip. -/

open Turing.MultiTapeTM

/-- A unary number is zero or above a fixed threshold. -/
example : ComputableInPolyTime (fun n : ℕ => decide (n = 0 ∨ 5 < n)) encUnary encBool := by
  fun_prop

/-- A unary number differs from a fixed value. -/
example : ComputableInPolyTime (fun n : ℕ => n != 3) encUnary encBool := by
  fun_prop

/-- The first entry of a list of unary numbers above the list's length. -/
example : ComputableInPolyTime (fun l : List ℕ => l.find? fun n => decide (l.length < n))
    (encList encUnary) (encOption encUnary) := by
  fun_prop

/-- The least power of two that is at least `n`, in unary. -/
example : ComputableInPolyTime (fun n : ℕ => 2 ^ Nat.clog 2 n) encUnary encUnary := by
  fun_prop

/-- `(-2) ^ n` as a binary integer, as a product over a unary range. -/
example : ComputableInPolyTime (fun n : ℕ => ∏ _i ∈ Finset.range n, (-2 : ℤ))
    encUnary encIntBin :=
  .intBin_prod_range (f := fun _ => -2) (.const _) .id'
