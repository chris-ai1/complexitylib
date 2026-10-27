/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPPpath
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime

/-! # BPPpath: the inclusion chain and a constant-count example -/

@[expose] public section

namespace Cslib.Complexity.Tests.BPPpath

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- The chain `BPP ⊆ SBP ⊆ BPPpath ⊆ PP`. -/
example : BPP enc ⊆ SBP enc ∧ SBP enc ⊆ BPPpath enc ∧ BPPpath enc ⊆ PP enc :=
  ⟨BPP_subset_SBP, SBP_subset_BPPpath, BPPpath_subset_PP⟩

/-- The empty language: one rejecting path and no accepting path on every input. -/
example : (∅ : Set α) ∈ BPPpath enc :=
  ⟨0, SharpP.zero_mem, 1, SharpP.one_mem, fun _ => by simp⟩

end Cslib.Complexity.Tests.BPPpath
