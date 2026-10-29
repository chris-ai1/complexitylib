/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Arithmetic
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.ZipTransducer
import Mathlib.Data.Nat.Bitwise

/-!
# Binary addition and bitwise disjunction in linear time

Addition and bitwise disjunction are computed by zip transducers
(`Turing.MultiTapeTM.ZipTransducer`) that read both operands in lockstep, least significant digit
first. The addition transducer keeps the carry as its state, emits one digit of the word adder
`NatAdd.addBits` per pair of digits and the final carry at the end. The disjunction transducer
emits the disjunction of each pair of digits; the longer operand ends in a one, so the output has
no trailing zero. Both run in linear time and in work space linear in the first operand.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_natAdd`: binary addition within
  `3 * (encPair encNat encNat p).length + 1` steps and `(encNat p.1).length + 2` work-tape cells.
* `Turing.MultiTapeTM.computableInTimeAndSpace_natOr`: bitwise disjunction within the same bounds.
* `Turing.MultiTapeTM.ComputableInLinearTimeAndSpace.natAdd`, `.natOr`: their linear forms.
* `Turing.MultiTapeTM.ComputableInO.natAdd`: binary addition in quadratic time and linear charged
  workspace.
-/

public section

namespace Turing.MultiTapeTM

/-- Binary addition as a zip transducer; the state is the carry. -/
private def addZip : ZipTransducer Bool where
  q₀ := false
  step c x := (NatAdd.carry (x.1.getD false) (x.2.getD false) c,
    [x.1.getD false ^^ (x.2.getD false ^^ c)])
  final c := if c then [true] else []
  length_step_le _ _ := by simp
  length_final_le c := by cases c <;> simp

private lemma run_addZip (c : Bool) (u v : List Bool) :
    addZip.run c u v = NatAdd.addBits c u v := by
  induction u generalizing c v with
  | nil =>
    rw [NatAdd.addBits]
    induction v generalizing c with
    | nil => cases c <;> simp [addZip, NatSucc.incr]
    | cons b v ih =>
      rw [ZipTransducer.run_nil_cons, ih]
      cases b <;> cases c <;> simp [addZip, NatSucc.incr, NatAdd.carry]
  | cons a u ih =>
    cases v <;> simp only [ZipTransducer.run_cons_nil, ZipTransducer.run_cons_cons, ih] <;>
      simp [addZip, NatAdd.addBits]

private lemma encNat_natAdd (p : ℕ × ℕ) :
    encNat (p.1 + p.2) = addZip.run addZip.q₀ (encNat p.1) (encNat p.2) := by
  rw [encNat_apply, encNat_apply, encNat_apply, run_addZip, NatAdd.addBits_bits]
  rfl

/-- **Binary addition in linear time.** One zip transducer computes `a + b` from
`encPair encNat encNat (a, b)` within `3 * (encPair encNat encNat p).length + 1` steps and
`(encNat p.1).length + 2` work-tape cells. -/
public theorem computableInTimeAndSpace_natAdd :
    ComputableInTimeAndSpace (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat
      (fun p => 3 * (encPair encNat encNat p).length + 1) (fun p => (encNat p.1).length + 2) :=
  addZip.computableInTimeAndSpace encNat_natAdd

/-- Binary addition in linear time and work space, from `computableInTimeAndSpace_natAdd`. -/
public theorem ComputableInLinearTimeAndSpace.natAdd :
    ComputableInLinearTimeAndSpace (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat :=
  addZip.computableInLinearTimeAndSpace encNat_natAdd

/-- Bitwise disjunction as a zip transducer with a single state. -/
private def orZip : ZipTransducer Unit where
  q₀ := ()
  step _ x := ((), [x.1.getD false || x.2.getD false])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private lemma run_orZip (m n : ℕ) : orZip.run () m.bits n.bits = (m ||| n).bits := by
  have hnil (u : List Bool) : orZip.run () u [] = u ∧ orZip.run () [] u = u := by
    induction u <;> simp_all [orZip]
  induction m using Nat.binaryRec' generalizing n with
  | zero => simp [hnil]
  | bit a m hm ih =>
    induction n using Nat.binaryRec' with
    | zero => simp [hnil]
    | bit b n hn _ =>
      rw [Nat.bits_append_bit _ _ hm, Nat.bits_append_bit _ _ hn, ZipTransducer.run_cons_cons, ih,
        Nat.lor_bit, Nat.bits_append_bit _ _ fun h => by simp [hm (Nat.or_eq_zero_iff.mp h).1]]
      rfl

/-- **Bitwise disjunction in linear time.** One zip transducer computes `a ||| b` from
`encPair encNat encNat (a, b)` within `3 * (encPair encNat encNat p).length + 1` steps and
`(encNat p.1).length + 2` work-tape cells. -/
public theorem computableInTimeAndSpace_natOr :
    ComputableInTimeAndSpace (fun p : ℕ × ℕ => p.1 ||| p.2) (encPair encNat encNat) encNat
      (fun p => 3 * (encPair encNat encNat p).length + 1) (fun p => (encNat p.1).length + 2) :=
  orZip.computableInTimeAndSpace fun p => (run_orZip p.1 p.2).symm

/-- Bitwise disjunction in linear time and work space, from `computableInTimeAndSpace_natOr`. -/
public theorem ComputableInLinearTimeAndSpace.natOr :
    ComputableInLinearTimeAndSpace (fun p : ℕ × ℕ => p.1 ||| p.2) (encPair encNat encNat) encNat :=
  orZip.computableInLinearTimeAndSpace fun p => (run_orZip p.1 p.2).symm

end Turing.MultiTapeTM

namespace Turing.MultiTapeTM.ComputableInO

/-- **Binary addition** within the quadratic clock and linear charged workspace used by its
clients, from the linear zip-transducer certificate `computableInTimeAndSpace_natAdd`. -/
theorem natAdd :
    ComputableInO (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat
      (fun p => ((encPair encNat encNat p).length + 1) ^ 2)
      (fun p => (encPair encNat encNat p).length + 1) :=
  (of_linear ComputableInLinearTimeAndSpace.natAdd).mono 1
    (fun p => by have := Nat.le_self_pow two_ne_zero ((encPair encNat encNat p).length + 1); omega)
    (fun _ => by omega)

end Turing.MultiTapeTM.ComputableInO
