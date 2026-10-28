/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Computability.Complexity.Classes.LogSpace.Randomized
import Complexity.Computability.Complexity.Classes.LogSpace.USTCON

/-!
# Tests for randomized logarithmic space
-/

namespace ComplexityTests.RandomizedLogSpace

open Cslib.Complexity

-- Undirected connectivity, in `L` by Reingold, is in `RL` and in `BPL`.
example : USTCON ∈ RL encUSTCON := L_subset_RL USTCON_mem_L

example : USTCON ∈ BPL encUSTCON := L_subset_BPL USTCON_mem_L

-- Going through `RL` recovers `USTCON ∈ NL`.
example : USTCON ∈ NL encUSTCON := RL_subset_NL (L_subset_RL USTCON_mem_L)

-- The derived clock: an `RL` machine for `USTCON` halts within polynomially many steps.
example : ∃ (k : ℕ) (State : Type) (_ : Finite State)
    (M : Turing.MultiTapePTM k Bool State) (d : ℕ), ∀ G,
      M.toNTM.RunsInTime (encUSTCON G) (2 * (2 * ((encUSTCON G).length + 1)) ^ d) := by
  obtain ⟨k, State, hfin, M, _, d, h⟩ := exists_polyClock_of_mem_RL (L_subset_RL USTCON_mem_L)
  exact ⟨k, State, hfin, M, d, fun G => (h G).2.1⟩

end ComplexityTests.RandomizedLogSpace
