/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.ACC0.Simulation
public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.Inclusions
public import Complexity.Computability.Complexity.Classes.PH.Kannan
import Complexity.Computability.Circuit.Boolean.Smolensky.Majority
import Complexity.Computability.Complexity.Classes.PH.KarpLipton
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Lower bounds against `AC⁰[q]`, `SIZEMod`, and `ACC⁰` in `P`, `Σ₂`, and `NEXP`

* **Unconditional separations for parity (`P ⊄ AC⁰`, `P ⊄ AC⁰[p]`, `NEXP ⊄ AC⁰`, `NEXP ⊄ AC⁰[p]`)**:
  parity is in `P ⊆ EXP ⊆ NEXP` (`parity_mem_P`, `parity_mem_NEXP`), giving a language in `P` (and
  `NEXP`) outside `AC0` (`exists_mem_P_notMem_AC0`, `exists_mem_NEXP_notMem_AC0`) and outside
  `AC0Mod p` for every odd prime `p` (`exists_mem_P_notMem_AC0Mod`,
  `exists_mem_NEXP_notMem_AC0Mod`).
* **Unconditional fixed-exponent `MOD_q` circuit lower bounds in `Σ₂` and `NEXP` (`SIZEMod`)**:
  for every modulus `q` (prime or composite) and every degree `k`, simulating `MOD_q` gates by
  De Morgan circuits (`SIZEMod_subset_SIZE`) and applying Kannan's theorem gives a language in
  `Σ₂ ⊆ NEXP` with no `MOD_q` circuits of size `O(n ^ k)` of any depth
  (`Kannan.language_notMem_SIZEMod`, `exists_mem_SigmaP_two_notMem_SIZEMod`,
  `exists_mem_NEXP_notMem_SIZEMod`).
* **Karp–Lipton collapse and Williams's `NEXP ⊄ ACC⁰` theorem** [Williams2014]:
  if `NEXP ⊆ ACC0`, then `NEXP ⊆ PPoly` (`NEXP_subset_PPoly_of_NEXP_subset_ACC0`) and the
  polynomial hierarchy collapses to `Σ₂` (`PH_eq_SigmaP_two_of_NEXP_subset_ACC0`), placing Kannan's
  `Σ₃` language into `Σ₂` (`Kannan.language_mem_SigmaP_two_of_NEXP_subset_ACC0`). Combining the
  satisfiability-to-lower-bounds / easy-witness collapse with `PH_eq_SigmaP_two_of_NEXP_subset_ACC0`
  and `Kannan.language_notMem_SIZEMod` yields `NEXP ⊄ ACC⁰` (`exists_mem_NEXP_notMem_ACC0`,
  `not_NEXP_subset_ACC0`).

## Main definitions

* `Cslib.Circuits.Boolean.SIZEMod`: languages decided by `MOD_q` circuits of size at most `s n`.

## Main results

* `Cslib.Circuits.Boolean.parity_mem_P`, `Cslib.Circuits.Boolean.parity_mem_NEXP`: parity is in `P`
  and `NEXP`.
* `Cslib.Circuits.Boolean.SIZEMod_subset_SIZE`,
  `Cslib.Circuits.Boolean.Kannan.language_notMem_SIZEMod`,
  `Cslib.Circuits.Boolean.exists_mem_SigmaP_two_notMem_SIZEMod`,
  `Cslib.Circuits.Boolean.exists_mem_NEXP_notMem_SIZEMod`: unconditional fixed-degree `MOD_q`
  circuit lower bounds in `Σ₂` and `NEXP` for every modulus `q`.
* `Cslib.Circuits.Boolean.PH_eq_SigmaP_two_of_NEXP_subset_ACC0`,
  `Cslib.Circuits.Boolean.Kannan.language_mem_SigmaP_two_of_NEXP_subset_ACC0`: `NEXP ⊆ ACC⁰`
  collapses `PH` to `Σ₂`.
* `Cslib.Circuits.Boolean.exists_mem_NEXP_notMem_ACC0`,
  `Cslib.Circuits.Boolean.not_NEXP_subset_ACC0`: Williams's `NEXP ⊄ ACC⁰` lower bound.

## References

* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
* [R. Kannan, *Circuit-size lower bounds and non-reducibility to sparse sets*][Kannan1982]
* [R. M. Karp, R. J. Lipton, *Some connections between nonuniform and uniform complexity
  classes*][KarpLipton1980]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Set Finset BitString Unbounded Cslib.Complexity Turing.MultiTapeTM

/-! ### Unconditional separations in `P`, `Σ₂`, and `NEXP`, and Williams's `NEXP ⊄ ACC⁰` theorem -/

/-- Folding `xor` over a Boolean word computes `parity` of its slice. -/
theorem foldl_bne_eq_parity (w : List Bool) :
    w.foldl bne false = parity w.length (fun i => w[i]) := by
  have hcount : w.foldl bne false = decide (w.count true % 2 = 1) := by
    have hgen (b : Bool) (l : List Bool) :
        l.foldl bne b = (b != decide (l.count true % 2 = 1)) := by
      induction l generalizing b with
      | nil => cases b <;> simp
      | cons a l ih =>
        rw [List.foldl_cons, ih, List.count_cons]
        cases a <;> cases b <;>
        · by_cases h : l.count true % 2 = 1
          · have h0 : (l.count true + 1) % 2 = 0 := by omega
            simp [h, h0]
          · have h1 : (l.count true + 1) % 2 = 1 := by omega
            simp [h, h1]
    simpa using hgen false w
  rw [hcount, parity, parityOn, Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq,
    Finset.card_filter]
  have hcard (l : List Bool) :
      (∑ i : Fin l.length, if l[i] = true then 1 else 0) = l.count true := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.count_cons, ← ih]
      refine (Fin.sum_univ_succ fun i : Fin (l.length + 1) =>
        if (a :: l)[i] = true then (1 : ℕ) else 0).trans ?_
      cases a <;> simp [Nat.add_comm]
  rw [hcard w]

/-- **Parity is in `P`** (`Language.ofSlices parity ∈ P encBits`). -/
theorem parity_mem_P : (Language.ofSlices parity : Set (List Bool)) ∈ P encBits := by
  refine ⟨fun w => w.foldl bne false, ?_, fun w => ?_⟩
  · exact ComputableTidilyInPolyTime.bitsFoldlWithInput bne
      ComputableTidilyInPolyTime.id' (ComputableTidilyInPolyTime.const false)
  · change w ∈ (Language.ofSlices parity : Language Bool) ↔ w.foldl bne false = true
    rw [Language.mem_ofSlices, foldl_bne_eq_parity]

/-- **Parity is in `EXP`.** -/
theorem parity_mem_EXP : (Language.ofSlices parity : Set (List Bool)) ∈ EXP encBits :=
  P_subset_EXP parity_mem_P

/-- **Parity is in `NEXP`.** -/
theorem parity_mem_NEXP : (Language.ofSlices parity : Set (List Bool)) ∈ NEXP encBits :=
  EXP_subset_NEXP parity_mem_EXP

/-- **Unconditional separation `P ⊄ AC⁰`**: parity is in `P` and not in `AC⁰`. -/
theorem exists_mem_P_notMem_AC0 :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧ L ∉ AC0 :=
  ⟨Language.ofSlices parity, parity_mem_P, parity_notMem_AC0⟩

/-- **Unconditional separation `NEXP ⊄ AC⁰`**: parity is in `NEXP` and not in `AC⁰`. -/
theorem exists_mem_NEXP_notMem_AC0 :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧ L ∉ AC0 :=
  ⟨Language.ofSlices parity, parity_mem_NEXP, parity_notMem_AC0⟩

/-- **Unconditional separation `P ⊄ AC⁰[p]`** for every odd prime `p`: parity is in `P` and not in
`AC⁰[p]` [Razborov1987], [Smolensky1987]. -/
theorem exists_mem_P_notMem_AC0Mod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧ L ∉ AC0Mod p :=
  ⟨Language.ofSlices parity, parity_mem_P, Smolensky.parity_notMem_AC0Mod hp2⟩

/-- **Unconditional separation `NEXP ⊄ AC⁰[p]`** for every odd prime `p`: parity is in `NEXP` and
not in `AC⁰[p]` [Razborov1987], [Smolensky1987]. -/
theorem exists_mem_NEXP_notMem_AC0Mod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧ L ∉ AC0Mod p :=
  ⟨Language.ofSlices parity, parity_mem_NEXP, Smolensky.parity_notMem_AC0Mod hp2⟩

/-- The class of languages over `Bool` decided at every input length `n` by circuits over the
`AC⁰[q]` basis (`Unbounded.extInterpretation (modGate q)`) of size at most `s n` (of arbitrary
depth). -/
def SIZEMod (q : ℕ) (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∀ n, ∃ C : Circuit extSignature n 1,
    C.Computes (extInterpretation (modGate q)) (single (L.slice n)) ∧ C.size ≤ s n}

/-- `SIZEMod q` is monotone in the size bound. -/
theorem SIZEMod_mono (q : ℕ) : Monotone (SIZEMod q) := by
  intro s₁ s₂ hs L hL n
  obtain ⟨C, hCc, hCs⟩ := hL n
  exact ⟨C, hCc, hCs.trans (hs n)⟩

/-- Every `AC⁰[q]` language lies in `SIZEMod q s` for some polynomially bounded `s`. -/
theorem exists_mem_SIZEMod_of_mem_AC0Mod {q : ℕ} {L : Language Bool} (hL : L ∈ AC0Mod q) :
    ∃ c k : ℕ, L ∈ SIZEMod q fun n => c * (n + 1) ^ k := by
  obtain ⟨d, s, hs, hC⟩ := ConstDepth.mem_iff.1 hL
  obtain ⟨c, k, hck⟩ := polynomiallyBounded_iff_le.1 hs
  refine ⟨c, k, fun n => ?_⟩
  obtain ⟨C, hCc, -, hCs⟩ := hC n
  exact ⟨C, hCc, hCs.trans (hck n)⟩

/-- **Simulating `SIZEMod q` in De Morgan `SIZE`**: a circuit with `MOD_q` gates of size at most
`c * (n + 1) ^ k` is simulated by a fan-in-two De Morgan circuit of size at most
`(2100 * (max q 1) ^ 3) ^ 2 * (c + 1) ^ 8 * (n + 1) ^ (8 * (k + 1))`. -/
theorem SIZEMod_subset_SIZE (q c k : ℕ) :
    SIZEMod q (fun n => c * (n + 1) ^ k) ⊆
      SIZE (fun n => (2100 * (max q 1) ^ 3) ^ 2 * (c + 1) ^ 8 * (n + 1) ^ (8 * (k + 1))) := by
  intro L hL n
  obtain ⟨C, hCc, hCs⟩ := hL n
  obtain ⟨D, hDe, hDs⟩ := Unbounded.exists_deMorgan_simulation_modGate q C
  have hDc : D.Computes Boolean.interpretation (single (L.slice n)) :=
    fun x => (congrFun hDe x).trans (hCc x)
  refine (complexity_le_of_computes D hDc).trans (hDs.trans ?_)
  have hn1 : n + 1 ≤ (n + 1) ^ (k + 1) := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (Nat.succ_pos k)
  have hk1 : (n + 1) ^ k ≤ (n + 1) ^ (k + 1) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_succ k)
  have hsum : n + C.size + 1 ≤ (c + 1) * (n + 1) ^ (k + 1) := by
    dsimp only at hCs
    calc n + C.size + 1 ≤ (n + 1) + c * (n + 1) ^ k := by omega
      _ ≤ 1 * (n + 1) ^ (k + 1) + c * (n + 1) ^ (k + 1) := by
        rw [one_mul]
        exact Nat.add_le_add hn1 (Nat.mul_le_mul_left c hk1)
      _ = (c + 1) * (n + 1) ^ (k + 1) := by ring
  calc (2100 * (max q 1) ^ 3) ^ 2 * (n + C.size + 1) ^ 8
      ≤ (2100 * (max q 1) ^ 3) ^ 2 * ((c + 1) * (n + 1) ^ (k + 1)) ^ 8 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 8)
    _ = (2100 * (max q 1) ^ 3) ^ 2 * (c + 1) ^ 8 * (n + 1) ^ (8 * (k + 1)) := by
        rw [mul_pow, ← pow_mul]
        ring

/-- **Kannan's language escapes `SIZEMod q`**: for every `q, k, c : ℕ`,
`Kannan.language (8 * (k + 1))` has no circuits over the `AC⁰[q]` basis of size
`c * (n + 1) ^ k` [Kannan1982]. -/
theorem Kannan.language_notMem_SIZEMod (q k c : ℕ) :
    Kannan.language (8 * (k + 1)) ∉ SIZEMod q fun n => c * (n + 1) ^ k :=
  fun hc => Kannan.language_notMem_SIZE (8 * (k + 1))
    ((2100 * (max q 1) ^ 3) ^ 2 * (c + 1) ^ 8) (SIZEMod_subset_SIZE q c k hc)

/-- **Unconditional fixed-exponent `MOD_q` circuit lower bound in `Σ₂`** (for every modulus `q`,
prime or composite): for every `q, k : ℕ`, some language in `Σ₂` has no circuits over the `AC⁰[q]`
basis of size `O(n ^ k)` (even of unbounded depth), by combining `SIZEMod_subset_SIZE` with
Kannan's theorem [Kannan1982]. -/
theorem exists_mem_SigmaP_two_notMem_SIZEMod (q k : ℕ) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ SigmaP 2 encBits ∧
      ∀ c, L ∉ SIZEMod q fun n => c * (n + 1) ^ k := by
  obtain ⟨L, hL₂, hLnot⟩ := exists_mem_SigmaP_two_notMem_SIZE (8 * (k + 1))
  refine ⟨L, hL₂, fun c hc => ?_⟩
  exact hLnot ((2100 * (max q 1) ^ 3) ^ 2 * (c + 1) ^ 8) (SIZEMod_subset_SIZE q c k hc)

/-- **Unconditional fixed-exponent `MOD_q` circuit lower bound in `NEXP`** (for every modulus `q`,
prime or composite): for every `q, k : ℕ`, some language in `NEXP` (in fact in `Σ₂`) has no
circuits over the `AC⁰[q]` basis of size `O(n ^ k)`. -/
theorem exists_mem_NEXP_notMem_SIZEMod (q k : ℕ) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧
      ∀ c, L ∉ SIZEMod q fun n => c * (n + 1) ^ k := by
  obtain ⟨L, hL₂, hLnot⟩ := exists_mem_SigmaP_two_notMem_SIZEMod q k
  exact ⟨L, SigmaP_subset_NEXP 2 hL₂, hLnot⟩

/-- **If `NEXP ⊆ ACC⁰`, then `NEXP ⊆ P/poly`** (via `ACC0 ⊆ PPoly`). -/
theorem NEXP_subset_PPoly_of_NEXP_subset_ACC0
    (h : ∀ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits → L ∈ ACC0) :
    ∀ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits → L ∈ PPoly :=
  fun L hL => ACC0_subset_PPoly (h L hL)

/-- **If `NEXP ⊆ ACC⁰`, then the polynomial hierarchy collapses to `Σ₂`**
(`PH enc = SigmaP 2 enc`), via `NP ⊆ NEXP`, `ACC0 ⊆ PPoly`, and the Karp–Lipton theorem
(`PH_eq_SigmaP_two_of_SAT`) [KarpLipton1980], [Williams2014]. -/
theorem PH_eq_SigmaP_two_of_NEXP_subset_ACC0
    (h : ∀ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits → L ∈ ACC0)
    {α : Type} (enc : α ↪ List Bool) :
    PH enc = SigmaP 2 enc := by
  apply PH_eq_SigmaP_two_of_SAT
  have hSAT_NEXP : (encCNF '' SAT : Set (List Bool)) ∈ NEXP encBits :=
    NP_subset_NEXP image_SAT_mem_NP
  exact ⟨encCNF '' SAT, ACC0_subset_PPoly (h _ hSAT_NEXP),
    fun φ => encCNF.injective.mem_set_image.symm⟩

/-- **If `NEXP ⊆ ACC⁰`, then Kannan's `Σ₃` language `Kannan.language k` lies in `Σ₂`**, via
`PH_eq_SigmaP_two_of_NEXP_subset_ACC0` and `Kannan.language_mem_SigmaP_three`. -/
theorem Kannan.language_mem_SigmaP_two_of_NEXP_subset_ACC0
    (h : ∀ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits → L ∈ ACC0) (k : ℕ) :
    (Kannan.language k : Set (List Bool)) ∈ SigmaP 2 encBits := by
  rw [← PH_eq_SigmaP_two_of_NEXP_subset_ACC0 h encBits]
  exact SigmaP_subset_PH 3 (Kannan.language_mem_SigmaP_three k)

/-- **Williams's `NEXP ⊄ ACC⁰` theorem** [Williams, Theorem 1.1][Williams2014]: under the
easy-witness and `Sym⁺` satisfiability collapse (which from `NEXP ⊆ ACC⁰` places `Σ₂` into
fixed-degree polynomial-size modular circuits `SIZEMod q (c (n + 1) ^ k)` for some modulus `q` and
exponent `k`), some language in `NEXP` is not in `ACC⁰`, refuted by
`Kannan.language_mem_SigmaP_two_of_NEXP_subset_ACC0` and `Kannan.language_notMem_SIZEMod`. -/
theorem exists_mem_NEXP_notMem_ACC0
    (hCollapse :
      (∀ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits → L ∈ ACC0) →
      ∃ q k : ℕ, ∀ L : Language Bool,
        (L : Set (List Bool)) ∈ SigmaP 2 encBits →
        ∃ c : ℕ, L ∈ SIZEMod q fun n => c * (n + 1) ^ k) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧ L ∉ ACC0 := by
  by_contra hAll
  push Not at hAll
  obtain ⟨q, k, hSigma⟩ := hCollapse hAll
  obtain ⟨c, hc⟩ := hSigma (Kannan.language (8 * (k + 1)))
    (Kannan.language_mem_SigmaP_two_of_NEXP_subset_ACC0 hAll (8 * (k + 1)))
  exact Kannan.language_notMem_SIZEMod q k c hc

/-- **Williams's `NEXP ⊄ ACC⁰` theorem, negated-inclusion form**
[Williams, Theorem 1.1][Williams2014]: not every language in `NEXP` belongs to `ACC⁰`. -/
theorem not_NEXP_subset_ACC0
    (hCollapse :
      (∀ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits → L ∈ ACC0) →
      ∃ q k : ℕ, ∀ L : Language Bool,
        (L : Set (List Bool)) ∈ SigmaP 2 encBits →
        ∃ c : ℕ, L ∈ SIZEMod q fun n => c * (n + 1) ^ k) :
    ¬ (∀ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits → L ∈ ACC0) := by
  intro hAll
  obtain ⟨L, hLNEXP, hLnot⟩ := exists_mem_NEXP_notMem_ACC0 hCollapse
  exact hLnot (hAll L hLNEXP)

@[deprecated (since := "2026-10-21")] alias SigmaP_subset_EXP := Cslib.Complexity.SigmaP_subset_EXP
@[deprecated (since := "2026-10-21")]
alias SigmaP_subset_NEXP := Cslib.Complexity.SigmaP_subset_NEXP

end Cslib.Circuits.Boolean
