/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Frontier.Extractor.Distributional
public import Complexity.Computability.Circuit.Frontier.FanInTwo
public import Complexity.Foundations.Data.BitString.AffineDisperser
public import Complexity.Foundations.Data.BitString.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Affine dispersion of sumset dispersers and balanced padding

Every sumset disperser on the Boolean cube `BitString n` at threshold `K ≤ 2 ^ d` (and hence every
`(k, δ)`-sumset extractor with `δ < 1 / 2` and `k ≤ d`) is an affine disperser for dimension `d`
(`SumsetDisperser.isAffineDisperser`, `IsSumsetExtractor.isAffineDisperser`).

Given any `f : (Fin n → Bool) → Bool`, its one-bit *balanced padding*
`balancePad f x = f (Fin.tail x) ^^ x 0` accepts `2 ^ n` out of `2 ^ (n + 1)` inputs
(`ncard_setOf_balancePad`) while preserving sumset dispersion at threshold `2 * K`
(`SumsetDisperser.balancePad`). Consequently, any sumset-disperser family `D` with sublinear
log-threshold `log (K n) = o(n)` satisfies all worst-case frontier hypotheses after one-bit
balanced padding (`frontierHypotheses_balancePadFamily`,
`eventually_456249_div_100000_sub_mul_lt_size_balancePadFamily`) without any quantitative bias
hypothesis.

## Main definitions

* `Cslib.Circuits.Frontier.balancePad`, `Cslib.Circuits.Frontier.balancePadFamily`: one-bit
  balanced padding of a Boolean function or family by XORing with the first coordinate.
* `Cslib.Circuits.Frontier.tailFiber`: tail strings in the fiber of `A ⊆ Fin (n + 1) → Bool` where
  coordinate `0` equals `b`.

## Main results

* `Cslib.Circuits.Frontier.SumsetDisperser.isAffineDisperser`,
  `Cslib.Circuits.Frontier.IsSumsetExtractor.isAffineDisperser`: every sumset disperser at
  threshold `K ≤ 2 ^ d` (and every `(k, δ)`-sumset extractor with `δ < 1 / 2` and `k ≤ d`) is an
  affine disperser for dimension `d`.
* `Cslib.Circuits.Frontier.SumsetDisperser.balancePad`,
  `Cslib.Circuits.Frontier.frontierHypotheses_balancePadFamily`,
  `Cslib.Circuits.Frontier.eventually_456249_div_100000_sub_mul_lt_size_balancePadFamily`:
  balanced padding accepts `2 ^ n` inputs, preserves sumset dispersion at threshold `2 * K`, and
  satisfies all worst-case frontier hypotheses without a quantitative bias assumption.

## References

* [E. Chattopadhyay and J.-J. Liao, *Extractors for Sum of Two Sources*][ChattopadhyayLiao2022]
* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
* [S. Schlesinger, *Frontier circuit lower bounds and two-source sumset extractors in
  Complexitylib*][Schlesinger2026FrontierExtractor]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Filter Asymptotics Real

/-! ### Sumset dispersers are affine dispersers -/

section AffineDisperser

open Cslib.BitString

/-- **Every sumset disperser on the Boolean cube is an affine disperser.** If `{z | f z = true}` is
a `K`-sumset disperser on `BitString n` with `K ≤ 2 ^ d`, then `f` is an affine disperser for
dimension `d` (`IsAffineDisperser f d`). Indeed, for any injective affine map
`g : BitString d → BitString n`, the sets `A = range g` and `B = range (fun y => g y + g 0)` both
have cardinality `2 ^ d ≥ K`, and every sum `g x + (g y + g 0) = g (x + y + 0) = g (x + y)` lies in
`range g`. -/
theorem SumsetDisperser.isAffineDisperser {n K d : ℕ} {f : BitString n → Bool}
    (h : SumsetDisperser {z | f z = true} K) (hK : K ≤ 2 ^ d) :
    IsAffineDisperser f d := by
  intro g hg hinj
  have hcard_d : Nat.card (BitString d) = 2 ^ d := by
    simp [BitString]
  have hA : K ≤ (Set.range g).ncard := by
    rw [Set.ncard_range_of_injective hinj, hcard_d]
    exact hK
  have hinj_shift : Function.Injective (fun y : BitString d => g y + g 0) :=
    fun y₁ y₂ hyeq => hinj (add_right_cancel hyeq)
  have hB : K ≤ (Set.range (fun y : BitString d => g y + g 0)).ncard := by
    rw [Set.ncard_range_of_injective hinj_shift, hcard_d]
    exact hK
  obtain ⟨⟨a₁, ⟨x₁, rfl⟩, b₁, ⟨y₁, rfl⟩, h1⟩, ⟨a₀, ⟨x₀, rfl⟩, b₀, ⟨y₀, rfl⟩, h0⟩⟩ :=
    h (Set.range g) (Set.range (fun y => g y + g 0)) hA hB
  have hsum (x y : BitString d) : g x + (g y + g 0) = g (x + y) := by
    rw [← add_assoc, ← hg x y 0, add_zero]
  simp only [Set.mem_ofPred_eq, hsum] at h1 h0
  exact ⟨x₁ + y₁, x₀ + y₀, fun heq => h0 (heq ▸ h1)⟩

/-- **A Boolean function with sumset bias `< 1 / 2` at threshold `K ≤ 2 ^ d` is an affine disperser
for dimension `d`.** -/
theorem SumsetBias.isAffineDisperser {n K d : ℕ} {f : BitString n → Bool} {b : ℝ}
    (h : SumsetBias {z | f z = true} K b) (hKpos : 0 < K) (hb : b < 1 / 2) (hK : K ≤ 2 ^ d) :
    IsAffineDisperser f d :=
  (h.sumsetDisperser hKpos hb).isAffineDisperser hK

/-- **Every `(k, δ)`-sumset extractor with `δ < 1 / 2` and `k ≤ d` is an affine disperser for
dimension `d`.** -/
theorem IsSumsetExtractor.isAffineDisperser {n d : ℕ} {f : BitString n → Bool} {k δ : ℝ}
    (h : IsSumsetExtractor f k δ) (hδ : δ < 1 / 2) (hk : k ≤ d) :
    IsAffineDisperser f d := by
  refine h.sumsetBias_ceil.isAffineDisperser (Nat.ceil_pos.mpr (by positivity)) hδ ?_
  rw [Nat.ceil_le, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two hk

end AffineDisperser

/-! ### Balanced padding of sumset dispersers -/

section BalancePad

/-- **Balanced padding** of an `n`-bit Boolean function to `n + 1` bits by XORing with the first
input bit: `balancePad f x = f (Fin.tail x) ^^ x 0`. One fresh bit makes the function accept
exactly half of the `(n + 1)`-cube while preserving sumset dispersion at twice the threshold. -/
def balancePad {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin (n + 1) → Bool) : Bool :=
  f (Fin.tail x) ^^ x 0

@[simp]
theorem balancePad_apply {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin (n + 1) → Bool) :
    balancePad f x = (f (Fin.tail x) ^^ x 0) :=
  rfl

theorem balancePad_cons {n : ℕ} (f : (Fin n → Bool) → Bool) (b : Bool) (x : Fin n → Bool) :
    balancePad f (Fin.cons b x) = (f x ^^ b) := by
  simp

theorem balancePad_add {n : ℕ} (f : (Fin n → Bool) → Bool) (x y : Fin (n + 1) → Bool) :
    balancePad f (x + y) = (f (Fin.tail x + Fin.tail y) ^^ (x 0 ^^ y 0)) := by
  have htail : Fin.tail (x + y) = Fin.tail x + Fin.tail y := rfl
  have hzero : (x + y) 0 = (x 0 ^^ y 0) := rfl
  rw [balancePad, htail, hzero]

/-- **Balanced padding accepts `2 ^ n` inputs** out of `2 ^ (n + 1)`: for each `y : Fin n → Bool`,
`Fin.cons (!f y) y` is the unique accepting extension. -/
theorem ncard_setOf_balancePad {n : ℕ} (f : (Fin n → Bool) → Bool) :
    {x : Fin (n + 1) → Bool | balancePad f x = true}.ncard = 2 ^ n := by
  have hbij : Set.BijOn (fun y : Fin n → Bool => Fin.cons (!f y) y) Set.univ
      {x : Fin (n + 1) → Bool | balancePad f x = true} := by
    refine ⟨fun y _ => ?_, fun y₁ _ y₂ _ h => ?_, fun x hx => ?_⟩
    · simp only [Set.mem_ofPred_eq, balancePad_cons]
      cases f y <;> rfl
    · simpa only [Fin.tail_cons] using congrArg Fin.tail h
    · refine ⟨Fin.tail x, Set.mem_univ _, ?_⟩
      simp only [Set.mem_ofPred_eq, balancePad] at hx
      have h0 : (!f (Fin.tail x)) = x 0 := by
        revert hx
        cases f (Fin.tail x) <;> cases x 0 <;> decide
      dsimp only
      rw [h0, Fin.cons_self_tail]
  rw [← hbij.ncard_eq, Set.ncard_univ]
  simp

/-- The tail strings in the fiber of `A ⊆ Fin (n + 1) → Bool` where coordinate `0` equals `b`. -/
def tailFiber {n : ℕ} (A : Set (Fin (n + 1) → Bool)) (b : Bool) : Set (Fin n → Bool) :=
  Fin.tail '' {x ∈ A | x 0 = b}

theorem ncard_tailFiber {n : ℕ} (A : Set (Fin (n + 1) → Bool)) (b : Bool) :
    (tailFiber A b).ncard = {x ∈ A | x 0 = b}.ncard := by
  refine Set.InjOn.ncard_image fun x hx y hy htail => ?_
  have h0 : x 0 = y 0 := hx.2.trans hy.2.symm
  rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, h0, htail]

theorem ncard_tailFiber_false_add_true {n : ℕ} (A : Set (Fin (n + 1) → Bool)) :
    (tailFiber A false).ncard + (tailFiber A true).ncard = A.ncard := by
  rw [ncard_tailFiber, ncard_tailFiber]
  have hunion : {x ∈ A | x 0 = false} ∪ {x ∈ A | x 0 = true} = A := by
    ext x
    simp only [Set.mem_union, Set.mem_sep_iff]
    rcases Bool.dichotomy (x 0) with h | h <;> simp [h]
  have hdisj : Disjoint {x ∈ A | x 0 = false} {x ∈ A | x 0 = true} := by
    rw [Set.disjoint_left]
    intro x hxfalse hxtrue
    exact Bool.false_ne_true (hxfalse.2.symm.trans hxtrue.2)
  rw [← Set.ncard_union_eq hdisj, hunion]

theorem exists_le_ncard_tailFiber {n K : ℕ} {A : Set (Fin (n + 1) → Bool)}
    (hA : 2 * K ≤ A.ncard) : ∃ b : Bool, K ≤ (tailFiber A b).ncard := by
  have hsum := ncard_tailFiber_false_add_true A
  by_cases hfalse : K ≤ (tailFiber A false).ncard
  · exact ⟨false, hfalse⟩
  · exact ⟨true, by omega⟩

/-- **Balanced padding preserves sumset dispersion** with a factor-two threshold loss: if
`{z | f z = true}` is a `K`-sumset disperser on `Fin n → Bool`, then `{z | balancePad f z = true}`
is a `(2 * K)`-sumset disperser on `Fin (n + 1) → Bool`. -/
theorem SumsetDisperser.balancePad {n K : ℕ} {f : (Fin n → Bool) → Bool}
    (h : SumsetDisperser {z | f z = true} K) :
    SumsetDisperser {z | Frontier.balancePad f z = true} (2 * K) := by
  intro A B hA hB
  obtain ⟨p, hp⟩ := exists_le_ncard_tailFiber hA
  obtain ⟨q, hq⟩ := exists_le_ncard_tailFiber hB
  obtain ⟨⟨u₁, hu₁, v₁, hv₁, htrue⟩, ⟨u₀, hu₀, v₀, hv₀, hfalse⟩⟩ :=
    h (tailFiber A p) (tailFiber B q) hp hq
  rcases hu₁ with ⟨a₁, ⟨ha₁A, ha₁0⟩, rfl⟩
  rcases hv₁ with ⟨b₁, ⟨hb₁B, hb₁0⟩, rfl⟩
  rcases hu₀ with ⟨a₀, ⟨ha₀A, ha₀0⟩, rfl⟩
  rcases hv₀ with ⟨b₀, ⟨hb₀B, hb₀0⟩, rfl⟩
  simp only [Set.mem_ofPred_eq] at htrue hfalse
  cases hpq : (p ^^ q)
  · refine ⟨⟨a₁, ha₁A, b₁, hb₁B, ?_⟩, ⟨a₀, ha₀A, b₀, hb₀B, ?_⟩⟩
    · simp only [Set.mem_ofPred_eq, balancePad_add, ha₁0, hb₁0, hpq, htrue, Bool.xor_false]
    · simp only [Set.mem_ofPred_eq, balancePad_add, ha₀0, hb₀0, hpq, Bool.xor_false]
      exact hfalse
  · refine ⟨⟨a₀, ha₀A, b₀, hb₀B, ?_⟩, ⟨a₁, ha₁A, b₁, hb₁B, ?_⟩⟩
    · simp only [Set.mem_ofPred_eq, balancePad_add, ha₀0, hb₀0, hpq]
      revert hfalse
      cases f (Fin.tail a₀ + Fin.tail b₀) <;> decide
    · simp only [Set.mem_ofPred_eq, balancePad_add, ha₁0, hb₁0, hpq, htrue]
      decide

/-- **Balanced padding of a `K`-sumset disperser is `(2 * K)`-rectangle-free**, without any
assumption on the accepting density of `f`. -/
theorem SumsetDisperser.balancePad_rectangleFree {n K : ℕ} {f : (Fin n → Bool) → Bool}
    (h : SumsetDisperser {z | f z = true} K) :
    RectangleFree {z | Frontier.balancePad f z = true} (2 * K) :=
  h.balancePad.rectangleFree

/-- **Balanced padding of a `(k, δ)`-sumset extractor (`δ < 1 / 2`) is a `(2 * ⌈2^k⌉₊)`-sumset
disperser.** -/
theorem IsSumsetExtractor.balancePad_sumsetDisperser {n : ℕ} {f : (Fin n → Bool) → Bool}
    {k δ : ℝ} (h : IsSumsetExtractor f k δ) (hδ : δ < 1 / 2) :
    SumsetDisperser {z | Frontier.balancePad f z = true} (2 * ⌈(2 : ℝ) ^ k⌉₊) :=
  (h.sumsetBias_ceil.sumsetDisperser (Nat.ceil_pos.mpr (by positivity)) hδ).balancePad

/-- **Balanced padding of a `(k, δ)`-sumset extractor (`δ < 1 / 2`) is `(2 * ⌈2^k⌉₊)`-rectangle-free
and accepts exactly `2 ^ n` inputs.** -/
theorem IsSumsetExtractor.balancePad_rectangleFree {n : ℕ} {f : (Fin n → Bool) → Bool}
    {k δ : ℝ} (h : IsSumsetExtractor f k δ) (hδ : δ < 1 / 2) :
    RectangleFree {z | Frontier.balancePad f z = true} (2 * ⌈(2 : ℝ) ^ k⌉₊) :=
  (IsSumsetExtractor.balancePad_sumsetDisperser h hδ).rectangleFree

/-- **The balanced-padded Boolean family**: at input length `0` it returns `false`, and at input
length `n + 1` it applies `balancePad` to `f n`. -/
def balancePadFamily (f : ∀ n, (Fin n → Bool) → Bool) : ∀ n, (Fin n → Bool) → Bool
  | 0 => fun _ => false
  | n + 1 => balancePad (f n)

@[simp]
theorem balancePadFamily_zero (f : ∀ n, (Fin n → Bool) → Bool) :
    balancePadFamily f 0 = fun _ => false :=
  rfl

@[simp]
theorem balancePadFamily_succ (f : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) :
    balancePadFamily f (n + 1) = balancePad (f n) :=
  rfl

/-- **Exact logarithmic density of `balancePadFamily`:** its logarithmic density deficit on the
Boolean cube is `log 2` for every `n ≥ 1`, hence `o(n)`. -/
theorem isLittleO_sub_log_ncard_balancePadFamily (f : ∀ n, (Fin n → Bool) → Bool) :
    (fun n : ℕ => n * Real.log (Nat.card Bool) -
      Real.log {z | balancePadFamily f n z = true}.ncard) =o[atTop] fun n : ℕ => (n : ℝ) := by
  have hconst : (fun _ : ℕ => Real.log 2) =o[atTop] fun n : ℕ => (n : ℝ) :=
    (isLittleO_const_id_atTop (Real.log 2)).natCast_atTop
  refine hconst.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [balancePadFamily_succ, ncard_setOf_balancePad, Nat.card_eq_fintype_card, Fintype.card_bool]
  push_cast
  rw [Real.log_pow]
  ring

/-- **Any sumset-disperser family with sublinear log-threshold satisfies all worst-case frontier
hypotheses after one-bit balanced padding**, with no quantitative bias assumption. -/
theorem frontierHypotheses_balancePadFamily {D : ∀ n, (Fin n → Bool) → Bool} {K : ℕ → ℕ}
    (hD : ∀ᶠ n in atTop, SumsetDisperser {z | D n z = true} (K n))
    (hKpos : ∀ᶠ n in atTop, 0 < K n)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n : ℕ => (n : ℝ)) :
    (∀ᶠ n in atTop,
      RectangleFree {z | balancePadFamily D n z = true} (2 * K (n - 1))) ∧
    ((fun n => Real.log (2 * K (n - 1) : ℕ)) =o[atTop] fun n : ℕ => (n : ℝ)) ∧
    ((fun n => n * Real.log (Nat.card Bool) -
      Real.log {z | balancePadFamily D n z = true}.ncard) =o[atTop] fun n : ℕ => (n : ℝ)) := by
  refine ⟨?_, ?_, isLittleO_sub_log_ncard_balancePadFamily D⟩
  · filter_upwards [(tendsto_sub_atTop_nat 1).eventually hD, eventually_ge_atTop 1] with n hn hn1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    dsimp only [Nat.add_sub_cancel, balancePadFamily_succ] at hn ⊢
    exact hn.balancePad_rectangleFree
  · have hKshift : (fun n : ℕ => Real.log (K (n - 1))) =o[atTop] fun n : ℕ => (n : ℝ) := by
      refine (hK.comp_tendsto (tendsto_sub_atTop_nat 1)).trans_isBigO (IsBigO.of_bound 1 ?_)
      filter_upwards with n
      simp only [Function.comp_apply, Real.norm_natCast, one_mul, Nat.cast_le]
      omega
    have hconst : (fun _ : ℕ => Real.log 2) =o[atTop] fun n : ℕ => (n : ℝ) :=
      (isLittleO_const_id_atTop (Real.log 2)).natCast_atTop
    refine (hconst.add hKshift).congr' ?_ EventuallyEq.rfl
    filter_upwards [(tendsto_sub_atTop_nat 1).eventually hKpos] with n hn
    have hKn_pos : (0 : ℝ) < K (n - 1) := by exact_mod_cast hn
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.log_mul two_ne_zero hKn_pos.ne']

/-- **Conditional `(4.56249 - ε) n` worst-case circuit size lower bound over `fullSignature 2 Bool`
for `balancePadFamily D` from a sumset-disperser family `D`**, without any quantitative bias
hypothesis. -/
theorem eventually_456249_div_100000_sub_mul_lt_size_balancePadFamily
    {D : ∀ n, (Fin n → Bool) → Bool} {K : ℕ → ℕ}
    (hD : ∀ᶠ n in atTop, SumsetDisperser {z | D n z = true} (K n))
    (hKpos : ∀ᶠ n in atTop, 0 < K n)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n : ℕ => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (I : Interpretation (fullSignature 2 Bool) Bool) (Acc : Set Bool)
      (c : Circuit (fullSignature 2 Bool) n 1),
        c.Decides I Acc {z | balancePadFamily D n z = true} →
          (456249 / 100000 - ε) * n < c.size := by
  obtain ⟨hfree, hK', hdense⟩ := frontierHypotheses_balancePadFamily hD hKpos hK
  filter_upwards [eventually_456249_div_100000_sub_mul_lt_innerSize.{0, 0} hfree hK' hdense hε]
    with n hn I Acc c hdec
  exact (hn (fullSignature 2 Bool) I Acc c c.fanInAtMost_fullSignature hdec).trans_le
    (by exact_mod_cast c.innerSize_le_size)

end BalancePad

end Cslib.Circuits.Frontier
