/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Frontier.Extractor.BalancePad
public import Complexity.Computability.Circuit.Frontier.Extractor.Distributional
public import Complexity.Computability.Circuit.Frontier.Extractor.LowerBounds
public import Complexity.Computability.Circuit.Frontier.Extractor.Sumset

/-!
# Sumset extractors, sumset dispersers, and frontier circuit lower bounds

This top-level module re-exports the four components of the sumset-extractor frontier lower-bound
bridge:

* `Complexity.Computability.Circuit.Frontier.Extractor.Sumset`: zero-extension `zeroPad`,
  `SumsetDisperser`, `SumsetBias`, and rectangle-freeness / rectangle-bias bridges.
* `Complexity.Computability.Circuit.Frontier.Extractor.Distributional`: distributional
  `(k, δ)`-sumset extractors (`IsSumsetExtractor`), the Chor–Goldreich flat-source equivalence
  `isSumsetExtractor_iff_sumsetBias_two_pow`, and asymptotic threshold / density-deficit lemmas.
* `Complexity.Computability.Circuit.Frontier.Extractor.LowerBounds`:
  `frontierHypotheses_of_isSumsetExtractor` and conditional average-case and worst-case frontier
  circuit lower bounds across fan-in two, general fan-in `r ≥ 2`, nondeterministic verifier
  circuits, and circuits with `o(n)` monoid-aggregate gates.
* `Complexity.Computability.Circuit.Frontier.Extractor.BalancePad`: affine dispersion of sumset
  dispersers (`SumsetDisperser.isAffineDisperser`, `IsSumsetExtractor.isAffineDisperser`) and
  one-bit balanced padding (`balancePad`, `balancePadFamily`, `frontierHypotheses_balancePadFamily`,
  `eventually_456249_div_100000_sub_mul_lt_size_balancePadFamily`).

## Main definitions

* `Cslib.Circuits.Frontier.zeroPad`: extend `a : X → U` by `0` outside `X`.
* `Cslib.Circuits.Frontier.SumsetDisperser`: neither `S` nor `Sᶜ` contains `A + B` for
  `|A|, |B| ≥ K`.
* `Cslib.Circuits.Frontier.SumsetBias`: `a + b ∈ S` has bias at most `b` on `A ×ˢ B` for
  `|A|, |B| ≥ K`.
* `Cslib.Circuits.Frontier.IsSumsetExtractor`: `E (X + Y)` is `δ`-close to uniform for independent
  `k`-sources `X, Y`.
* `Cslib.Circuits.Frontier.balancePad`, `balancePadFamily`: one-bit balanced padding of a Boolean
  function or family by XORing with the first coordinate.

## Main results

* `Cslib.Circuits.Frontier.SumsetDisperser.rectangleFree`: a sumset disperser is rectangle-free.
* `Cslib.Circuits.Frontier.SumsetBias.rectangleBias`: sumset bias bounds rectangle bias.
* `Cslib.Circuits.Frontier.IsSumsetExtractor.rectangleBias_ceil`: a `(k, δ)`-sumset extractor has
  rectangle bias at most `δ` at threshold `⌈2^k⌉₊`.
* `Cslib.Circuits.Frontier.isSumsetExtractor_iff_sumsetBias_two_pow`: flat-source equivalence for
  Boolean sumset extractors.
* `Cslib.Circuits.Frontier.SumsetDisperser.isAffineDisperser`,
  `IsSumsetExtractor.isAffineDisperser`: every sumset disperser at threshold `K ≤ 2 ^ d` (and every
  `(k, δ)`-sumset extractor with `δ < 1 / 2` and `k ≤ d`) is an affine disperser for dimension `d`.
* `Cslib.Circuits.Frontier.SumsetDisperser.balancePad`,
  `frontierHypotheses_balancePadFamily`: balanced padding accepts `2 ^ n` inputs, preserves sumset
  dispersion at threshold `2 * K`, and satisfies all worst-case frontier hypotheses without a
  quantitative bias assumption.
* `Cslib.Circuits.Frontier.eventually_agreement_le_of_isSumsetExtractor`: conditional Gaussian
  frontier average-case lower bound from a sumset extractor family.
* `Cslib.Circuits.Frontier.eventually_456249_div_100000_sub_mul_lt_size_of_isSumsetExtractor`,
  `eventually_degreeCoefficient_lt_mul_innerSize_of_isSumsetExtractor`,
  `eventually_456249_div_100000_sub_mul_lt_innerSize_nondeterministic_of_isSumsetExtractor`,
  `eventually_456249_div_100000_sub_mul_lt_card_of_aggregates_of_isSumsetExtractor`:
  conditional `(4.56249 - ε) n` worst-case circuit lower bounds over `fullSignature 2 Bool`, for
  bounded fan-in `r ≥ 2`, for nondeterministic verifier circuits, and for circuits with `o(n)`
  monoid-aggregate gates of unbounded fan-in.

## References

* [B. Chor and O. Goldreich, *Unbiased bits from sources of weak randomness and probabilistic
  communication complexity*][ChorGoldreich1988]
* [E. Chattopadhyay and J.-J. Liao, *Extractors for Sum of Two Sources*][ChattopadhyayLiao2022]
* [E. Chattopadhyay and D. Zuckerman, *Explicit Two-Source Extractors and Resilient
  Functions*][ChattopadhyayZuckerman2019]
* [X. Li, *Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More*][Li2023]
* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
* [S. Schlesinger, *Frontier circuit lower bounds and two-source sumset extractors in
  Complexitylib*][Schlesinger2026FrontierExtractor]
-/

@[expose] public section
