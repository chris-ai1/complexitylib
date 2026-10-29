/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Mathlib.Data.List.DropRight
import Complexity.Foundations.Data.List.Append
import Complexity.Foundations.Data.Nat.Bits
import Mathlib.Data.Nat.Size

/-!
# Reading arbitrary little-endian natural-number words

The existing word interpretation and normalization identity are independent of machine or
complexity certificates. Trailing false symbols are ignored, and the empty word represents zero.

## Main definitions

* `Turing.MultiTapeTM.ofBits`: read little-endian digits as a natural number.
* `Turing.MultiTapeTM.bitsOfWidth`: the word of a fixed width with a given value.

## Main results

* `Turing.MultiTapeTM.bits_ofBits`: normalize a word by removing its trailing false symbols.
* `Turing.MultiTapeTM.ofBits_bitsOfWidth`, `Turing.MultiTapeTM.bits_add_two_pow`: the word of
  width `W` with value `x < 2 ^ W`, and the binary digits of `x + 2 ^ W`.
-/

@[expose] public section
namespace Turing.MultiTapeTM

/-- Binary digits, least significant first, read as a number. -/
def ofBits (w : List Bool) : ℕ := w.foldr Nat.bit 0

/-- The binary digits of a word read as a number are the word up to its last `true`. -/
theorem bits_ofBits (w : List Bool) : (ofBits w).bits = w.rdropWhile (!·) := by
  induction w with
  | nil => simp [ofBits]
  | cons b w ih =>
    rw [ofBits, List.foldr_cons, ← ofBits, ← List.singleton_append, List.rdropWhile_append, ← ih]
    by_cases h : ofBits w = 0 ∧ b = false
    · obtain ⟨h₀, rfl⟩ := h
      simp [h₀]
    · rw [Nat.bits_append_bit _ _ fun h₀ => by simpa [h₀] using h]
      by_cases h₀ : ofBits w = 0
      · obtain rfl : b = true := by simpa [h₀] using h
        simp [h₀, List.rdropWhile_singleton]
      · simp only [Nat.bits_eq_nil_iff, h₀, ↓reduceIte]
        rfl

/-- The word of width `W` with value `x`, for `x < 2 ^ W`: its binary digits, least significant
first, padded to width `W`. -/
def bitsOfWidth : ℕ → ℕ → List Bool
  | 0, _ => []
  | W + 1, x => x.bodd :: bitsOfWidth W x.div2

/-- The word `bitsOfWidth W x` has width `W`. -/
theorem length_bitsOfWidth (W x : ℕ) : (bitsOfWidth W x).length = W := by
  induction W generalizing x with
  | zero => rfl
  | succ W ih => simp [bitsOfWidth, ih]

/-- The value of a word, one digit at a time. -/
theorem ofBits_cons (b : Bool) (u : List Bool) : ofBits (b :: u) = Nat.bit b (ofBits u) := rfl

/-- The word `bitsOfWidth W x` has value `x`, for `x < 2 ^ W`. -/
theorem ofBits_bitsOfWidth {W x : ℕ} (hx : x < 2 ^ W) : ofBits (bitsOfWidth W x) = x := by
  induction W generalizing x with
  | zero => simp only [pow_zero, Nat.lt_one_iff] at hx; subst hx; rfl
  | succ W ih =>
    rw [bitsOfWidth, ofBits_cons, ih (by rw [Nat.div2_val]; rw [pow_succ] at hx; omega),
      Nat.bit_bodd_div2]

/-- The binary digits of `x + 2 ^ W`, for `x < 2 ^ W`, are the word of width `W` with value `x`,
followed by a one. -/
theorem bits_add_two_pow {W x : ℕ} (hx : x < 2 ^ W) :
    (x + 2 ^ W).bits = bitsOfWidth W x ++ [true] := by
  induction W generalizing x with
  | zero => simp only [pow_zero, Nat.lt_one_iff] at hx; subst hx; simp [bitsOfWidth]
  | succ W ih =>
    have hx' : x.div2 < 2 ^ W := by rw [Nat.div2_val]; rw [pow_succ] at hx; omega
    have hbit : x + 2 ^ (W + 1) = Nat.bit x.bodd (x.div2 + 2 ^ W) := by
      conv_lhs => rw [← Nat.bit_bodd_div2 x]
      rw [Nat.bit_val, Nat.bit_val, pow_succ]
      omega
    rw [hbit, Nat.bits_append_bit _ _ fun h => by have := Nat.one_le_two_pow (n := W); omega,
      ih hx', bitsOfWidth, List.cons_append]

/-- The word of width `W` with value `x < 2 ^ W` is `(x + 2 ^ W).bits` without its last
digit. -/
theorem dropLast_bits_add_two_pow {W x : ℕ} (hx : x < 2 ^ W) :
    (x + 2 ^ W).bits.dropLast = bitsOfWidth W x := by
  rw [bits_add_two_pow hx, List.dropLast_concat]

/-- The word of `W` ones has value `2 ^ W - 1`. -/
theorem ofBits_replicate_true (W : ℕ) : ofBits (List.replicate W true) = 2 ^ W - 1 := by
  induction W with
  | zero => rfl
  | succ W ih =>
    rw [List.replicate_succ, ofBits_cons, ih, Nat.bit_val, pow_succ]
    have := Nat.one_le_two_pow (n := W)
    simp only [Bool.toNat_true]
    omega

end Turing.MultiTapeTM
