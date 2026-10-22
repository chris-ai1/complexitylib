/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.ACC0.Basic
public import Complexity.Computability.Circuit.Boolean.ACC0.Simulation
public import Complexity.Computability.Circuit.Boolean.ACC0.SymPlus
public import Complexity.Computability.Circuit.Boolean.ACC0.Williams

/-!
# ACC⁰ and Williams's satisfiability-to-lower-bounds method

**ACC⁰** (`Cslib.Circuits.Boolean.ACC0`) is the union of the modular constant-depth circuit classes
`AC0Mod q` over all fixed moduli `q ≥ 2` [Barrington1989], [Vollmer, Chapter 4][Vollmer1999],
[Arora and Barak, Section 14.2][AroraBarak09]: the languages over `Bool` decided at every input
length by polynomial-size, constant-depth nonuniform circuits over negations, unbounded fan-in
conjunctions and disjunctions, and unbounded fan-in `MOD_q` gates (`modGate q`). Since `modGate 0`
is disjunction and `modGate 1` is the constant `false`, the union over all `q : ℕ` gives the same
class (`ACC0_eq_iUnion_AC0Mod`).

This top-level module re-exports the four components of the `ACC⁰` development:

* `Complexity.Computability.Circuit.Boolean.ACC0.Basic`: degenerate moduli `q = 0, 1`, divisibility
  monotonicity `AC0Mod_subset_AC0Mod_of_dvd`, `ACC0`, Boolean closure (`ACC0.compl`, `ACC0.inf`,
  `ACC0.sup`), and strict separations `AC0 ⊂ AC0Mod 2 ⊂ ACC0` and `AC0Mod p ⊂ ACC0`.
* `Complexity.Computability.Circuit.Boolean.ACC0.Simulation`: logarithmic-depth simulation of
  `MOD_q` gates and class inclusions `ACC0 ⊆ TC0`, `ACMod q i ⊆ AC (i + 1)`, and
  `ACC0 ⊆ AC 1 ⊆ NC 2 ⊆ PPoly`.
* `Complexity.Computability.Circuit.Boolean.ACC0.SymPlus`: depth-two `Sym⁺` (`Sym ∘ AND`) circuits,
  split-variable coefficient tables, and fast multipoint evaluation via `Cslib.BitString.fastZeta`.
* `Complexity.Computability.Circuit.Boolean.ACC0.Williams`: `SIZEMod`, unconditional lower bounds in
  `P`, `Σ₂`, and `NEXP`, the Karp–Lipton collapse `PH_eq_SigmaP_two_of_NEXP_subset_ACC0`, and
  Williams's `NEXP ⊄ ACC⁰` theorem (`exists_mem_NEXP_notMem_ACC0`, `not_NEXP_subset_ACC0`).

## Main definitions

* `Cslib.Circuits.Boolean.ACC0`: the class ACC⁰ = `⋃ q ≥ 2, AC0Mod q`.
* `Cslib.Circuits.Boolean.SIZEMod`: languages decided by `MOD_q` circuits of size at most `s n`.
* `Cslib.Circuits.Boolean.SymPlusCircuit`: depth-two `Sym ∘ AND` circuits.
* `Cslib.BitString.zetaTransform`, `Cslib.BitString.fastZeta`: the Boolean-lattice Zeta transform
  and its divide-and-conquer evaluation.
* `Cslib.Circuits.Boolean.SymPlusCircuit.coeffTable`,
  `Cslib.Circuits.Boolean.SymPlusCircuit.fastSymPlusEval`: split-variable coefficient table and
  fast multipoint evaluation of a `Sym⁺` circuit.
* `Cslib.Circuits.Boolean.SymPlusCompilation`: compilation of constant-depth `MOD_q` circuits into
  `Sym⁺` circuits [Yao1990], [BeigelTarui1994].

## Main results

* `Cslib.Circuits.Boolean.AC0Mod_zero`, `Cslib.Circuits.Boolean.AC0Mod_one`:
  `AC⁰[0] = AC⁰[1] = AC⁰`.
* `Cslib.Circuits.Boolean.AC0Mod_subset_AC0Mod_of_dvd`: `AC⁰[q] ⊆ AC⁰[q']` when `q ∣ q'` and
  `0 < q'`.
* `Cslib.Circuits.Boolean.ACC0_eq_iUnion_AC0Mod`: `ACC⁰ = ⋃ q, AC⁰[q]`.
* `Cslib.Circuits.Boolean.ACC0.compl`, `Cslib.Circuits.Boolean.ACC0.inf`,
  `Cslib.Circuits.Boolean.ACC0.sup`: Boolean closure of `ACC⁰`.
* `Cslib.Circuits.Boolean.ACC0_subset_TC0`, `Cslib.Circuits.Boolean.ACC0_subset_AC_one`,
  `Cslib.Circuits.Boolean.ACC0_subset_NC_two`, `Cslib.Circuits.Boolean.ACC0_subset_PPoly`.
* `Cslib.Circuits.Boolean.AC0_ssubset_ACC0`, `Cslib.Circuits.Boolean.AC0Mod_ssubset_ACC0`:
  strictness of `AC⁰ ⊂ ACC⁰` and `AC⁰[p] ⊂ ACC⁰` for odd prime `p`.
* `Cslib.Circuits.Boolean.SymPlusCircuit.zetaTransform_coeffTable_eq_activeCount`,
  `Cslib.BitString.fastZeta_eq_zetaTransform`,
  `Cslib.Circuits.Boolean.SymPlusCircuit.fastSymPlusEval_eq_eval`: correctness of Williams's fast
  `Sym⁺` evaluation.
* `Cslib.Circuits.Boolean.exists_mem_SigmaP_two_notMem_SIZEMod`,
  `Cslib.Circuits.Boolean.exists_mem_NEXP_notMem_SIZEMod`: unconditional fixed-degree `MOD_q`
  circuit lower bounds in `Σ₂` and `NEXP` for every modulus `q`.
* `Cslib.Circuits.Boolean.PH_eq_SigmaP_two_of_NEXP_subset_ACC0`: `NEXP ⊆ ACC⁰` collapses `PH` to
  `Σ₂`.
* `Cslib.Circuits.Boolean.exists_mem_NEXP_notMem_ACC0`,
  `Cslib.Circuits.Boolean.not_NEXP_subset_ACC0`: Williams's `NEXP ⊄ ACC⁰` lower bound.

## References

* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
* [A. C.-C. Yao, *On ACC and threshold circuits*][Yao1990]
* [R. Beigel, J. Tarui, *On ACC*][BeigelTarui1994]
* [D. A. M. Barrington, *Bounded-width polynomial-size branching programs recognize exactly those
  languages in NC¹*][Barrington1989]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section
