/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Arithmetic.PIT
public import Complexity.Computability.Circuit.Boolean.PPoly
public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.Inclusions
public import Complexity.Computability.Complexity.Classes.PH
import Complexity.Computability.Complexity.Classes.PH.Kannan
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Permanent downward self-reducibility and the Kabanets–Impagliazzo theorem

Building on `Complexity.Computability.Circuit.Arithmetic.PIT` (the multivariate Schwartz–Zippel
lemma, the encoding `encArithCircuitInt` of `PITInt`, Laplace expansion of the permanent, and
arithmetic circuit combinators), this module develops:

1. **Downward self-reducibility of the permanent to `PITInt`**
   [Kabanets and Impagliazzo, Lemma 4.2][KabanetsImpagliazzo2004],
   [Arora and Barak, Theorem 20.16][AroraBarak09]: on the generic matrix `genericMatrix R (m + 1)`,
   each `(0, j)`-minor is a variable reindexing of `genericMatrix R m`
   (`permanent_genericMatrix_succ`). Using the arithmetic circuit combinators of
   `Complexity.Computability.Circuit.Arithmetic.PIT`, we construct the base test circuit
   `permBaseDiff` and the Laplace step test circuit `permStepDiff` with explicit polynomial
   gate-size bounds (`size_permBaseDiff`, `size_permStepDiff`). A candidate family
   `C : ∀ m, Circuit (arithSignature ℤ) (m * m) 1` computes `(genericMatrix ℤ m).permanent` for all
   `m ≤ n` if and only if `⟨0, permBaseDiff (C 0)⟩ ∈ PITInt` and
   `⟨(m + 1) * (m + 1), permStepDiff m (C m) (C (m + 1))⟩ ∈ PITInt` for all `m < n`
   (`forall_polynomial_eq_permanent_iff_mem_PITInt`). When `PITInt ∈ P encArithCircuitInt` and the
   integer permanent family `intPermFamily` lies in `VP ℤ`, a polynomial-time decider for `PITInt`
   soundly and completely certifies permanent circuit chains
   (`exists_certified_perm_family_of_PITInt_mem_P_of_mem_VP`).
2. **`NEXP` circuit lower bounds and the Kabanets–Impagliazzo theorem**
   [Kabanets and Impagliazzo, Theorem 4.1][KabanetsImpagliazzo2004],
   [Arora and Barak, Theorem 20.16][AroraBarak09]:
   - Unconditionally, combining Kannan's theorem (`exists_mem_SigmaP_two_notMem_SIZE`) with
     `SigmaP_subset_NEXP` shows that for every fixed degree `k`, `NEXP` contains a language outside
     `SIZE (c (n + 1) ^ k)` (`exists_mem_NEXP_notMem_SIZE`).
   - Conditionally on `PITInt ∈ P encArithCircuitInt` and the Impagliazzo–Kabanets–Wigderson /
     Valiant–Toda collapse from a polynomial-time PIT-certified permanent circuit family under
     `NEXP ⊆ P/poly`, either `NEXP ⊄ P/poly` or `intPermFamily ∉ VP ℤ`
     (`kabanets_impagliazzo`, `kabanets_impagliazzo_of_EXP_subset_P`).

## Main definitions

* `Cslib.Circuits.Arithmetic.permFamily`, `Cslib.Circuits.Arithmetic.intPermFamily`: the permanent
  family `n ↦ (genericMatrix R n).permanent` and its integer specialization.
* `Cslib.Circuits.Arithmetic.minorVar`, `permBaseDiff`, `permStepDiff`, `laplacePermCircuit`,
  `IsLaplacePermChain`: the Laplace cofactor difference circuits, explicit recursive permanent
  circuit family, and Laplace permanent chain predicate reducing permanent verification to `PITInt`.
* `Cslib.Circuits.Arithmetic.PermPITCertified`: existence of a polynomial-time `PITInt` decider and
  a polynomially bounded arithmetic circuit family certified by it on all Laplace permanent
  identities.

## Main results

* `Cslib.Circuits.Arithmetic.permanent_genericMatrix_zero`,
  `Cslib.Circuits.Arithmetic.permanent_genericMatrix_succ`: Laplace recurrence for the generic
  permanent polynomial.
* `Cslib.Circuits.Arithmetic.forall_polynomial_eq_permanent_iff_mem_PITInt`: Kabanets–Impagliazzo
  Lemma 4.2, characterizing permanent circuits up to dimension `n` via `n + 1` instances of
  `PITInt`.
* `Cslib.Circuits.Arithmetic.exists_certified_perm_family_of_PITInt_mem_P_of_mem_VP`:
  `PITInt ∈ P` and `intPermFamily ∈ VP ℤ` yield a `PermPITCertified` permanent tester.
* `Cslib.Complexity.exists_mem_NEXP_notMem_SIZE`: unconditional fixed-degree circuit lower bound
  in `NEXP`.
* `Cslib.Circuits.Arithmetic.kabanets_impagliazzo`,
  `Cslib.Circuits.Arithmetic.kabanets_impagliazzo_of_EXP_subset_P`: the Kabanets–Impagliazzo
  derandomization-to-lower-bounds theorem.

## References

* [V. Kabanets, R. Impagliazzo, *Derandomizing polynomial identity tests means proving circuit
  lower bounds*][KabanetsImpagliazzo2004]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 20.16][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial Turing.MultiTapeTM

universe u

/-! ### The permanent family and Laplace self-reducibility via `PITInt` -/

section Permanent

variable {R : Type u} [CommRing R]

/-- The generic permanent has total degree at most `n`. -/
theorem totalDegree_permanent_genericMatrix_le (n : ℕ) :
    (genericMatrix R n).permanent.totalDegree ≤ n := by
  rw [Matrix.permanent]
  refine totalDegree_finsetSum_le fun σ _ => ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  calc _ ≤ ∑ _i : Fin n, 1 :=
        Finset.sum_le_sum fun i _ => (totalDegree_monomial_le _ _).trans (by simp)
    _ = n := by simp

/-- The permanent family over `R`: its `n`-th member is the permanent of `genericMatrix R n`, a
polynomial in `n * n` variables. -/
noncomputable def permFamily (R : Type u) [CommSemiring R] : PolynomialFamily R where
  vars n := n * n
  poly n := (genericMatrix R n).permanent

/-- The permanent family over `R` is a p-family (`vars n = n ^ 2` and `totalDegree ≤ n`). -/
theorem isPFamily_permFamily : (permFamily R).IsPFamily :=
  ⟨PolynomiallyBounded.id.mul PolynomiallyBounded.id,
    PolynomiallyBounded.id.mono_of_le (totalDegree_permanent_genericMatrix_le (R := R))⟩

/-- The permanent family over `ℤ`: its `n`-th member is the permanent of `genericMatrix ℤ n`, a
polynomial in `n * n` variables. -/
noncomputable abbrev intPermFamily : PolynomialFamily ℤ :=
  permFamily ℤ

/-- The integer permanent family is a p-family (`vars n = n ^ 2` and `totalDegree ≤ n`). -/
theorem isPFamily_intPermFamily : intPermFamily.IsPFamily :=
  isPFamily_permFamily

/-- Reindexing map sending the `(i, k)` variable of an `m × m` matrix to the
`(i.succ, j.succAbove k)` variable of an `(m + 1) × (m + 1)` matrix (the `(0, j)`-minor). -/
def minorVar {m : ℕ} (j : Fin (m + 1)) (idx : Fin (m * m)) : Fin ((m + 1) * (m + 1)) :=
  let pq := finProdFinEquiv.symm idx
  finProdFinEquiv (pq.1.succ, j.succAbove pq.2)

/-- The `(0, j)`-submatrix of `genericMatrix R (m + 1)` is `genericMatrix R m` with variables
renamed along `minorVar j`. -/
theorem submatrix_genericMatrix_eq_map_rename {m : ℕ} (j : Fin (m + 1)) :
    (genericMatrix R (m + 1)).submatrix Fin.succ j.succAbove =
      (genericMatrix R m).map (MvPolynomial.rename (minorVar j)) := by
  ext i k
  simp [genericMatrix, minorVar]

/-- The permanent of the `(0, j)`-minor of `genericMatrix R (m + 1)` is the generic `m × m`
permanent with variables renamed along `minorVar j`. -/
theorem permanent_submatrix_genericMatrix {m : ℕ} (j : Fin (m + 1)) :
    ((genericMatrix R (m + 1)).submatrix Fin.succ j.succAbove).permanent =
      MvPolynomial.rename (minorVar j) (genericMatrix R m).permanent := by
  rw [submatrix_genericMatrix_eq_map_rename, Matrix.permanent, Matrix.permanent, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_prod]
  rfl

/-- The permanent of the `0 × 0` generic matrix is `1`. -/
@[simp] theorem permanent_genericMatrix_zero : (genericMatrix R 0).permanent = 1 :=
  Matrix.permanent_isEmpty

/-- **Laplace recurrence for the generic permanent polynomial**: the `(m + 1) × (m + 1)` generic
permanent expands along row 0 in terms of the `m × m` generic permanent renamed along `minorVar j`.
-/
theorem permanent_genericMatrix_succ (m : ℕ) :
    (genericMatrix R (m + 1)).permanent =
      ∑ j : Fin (m + 1),
        X (finProdFinEquiv (0, j)) *
          MvPolynomial.rename (minorVar j) (genericMatrix R m).permanent := by
  rw [Matrix.permanent_succ_row_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [permanent_submatrix_genericMatrix]
  rfl

/-- Base-case identity-test circuit for the `0 × 0` permanent: computes `c₀.polynomial 0 - 1`. -/
def permBaseDiff (c₀ : Circuit (arithSignature R) 0 1) : Circuit (arithSignature R) 0 1 :=
  subCircuit c₀ (constCircuit 1)

@[simp] theorem size_permBaseDiff (c₀ : Circuit (arithSignature R) 0 1) :
    (permBaseDiff c₀).size = c₀.size + 4 := by
  simp [permBaseDiff]

@[simp] theorem polynomial_permBaseDiff (c₀ : Circuit (arithSignature R) 0 1) :
    (permBaseDiff c₀).polynomial 0 = c₀.polynomial 0 - 1 := by
  simp [permBaseDiff]

/-- Inductive Laplace step identity-test circuit for the `(m + 1) × (m + 1)` permanent from a
candidate `m × m` permanent circuit `cm` and a candidate `(m + 1) × (m + 1)` permanent circuit
`cm1`: computes
`cm1.polynomial 0 - ∑ j : Fin (m + 1), X (0, j) * rename (minorVar j) (cm.polynomial 0)`. -/
def permStepDiff (m : ℕ) (cm : Circuit (arithSignature R) (m * m) 1)
    (cm1 : Circuit (arithSignature R) ((m + 1) * (m + 1)) 1) :
    Circuit (arithSignature R) ((m + 1) * (m + 1)) 1 :=
  subCircuit cm1 (finSumCircuit fun j : Fin (m + 1) =>
    mulCircuit (varCircuit (finProdFinEquiv (0, j))) (reindexCircuit (minorVar j) cm))

@[simp] theorem size_permStepDiff (m : ℕ) (cm : Circuit (arithSignature R) (m * m) 1)
    (cm1 : Circuit (arithSignature R) ((m + 1) * (m + 1)) 1) :
    (permStepDiff m cm cm1).size = cm1.size + (m + 1) * (cm.size + 2) + 4 := by
  simp only [permStepDiff, size_subCircuit, size_finSumCircuit, size_mulCircuit, size_varCircuit,
    size_reindexCircuit, zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  ring

@[simp] theorem polynomial_permStepDiff (m : ℕ) (cm : Circuit (arithSignature R) (m * m) 1)
    (cm1 : Circuit (arithSignature R) ((m + 1) * (m + 1)) 1) :
    (permStepDiff m cm cm1).polynomial 0 =
      cm1.polynomial 0 -
        ∑ j : Fin (m + 1),
          X (finProdFinEquiv (0, j)) * MvPolynomial.rename (minorVar j) (cm.polynomial 0) := by
  simp [permStepDiff]

/-- `permBaseDiff c₀` lies in `PITInt` if and only if `c₀` computes the `0 × 0` generic permanent.
-/
theorem mem_PITInt_permBaseDiff_iff (c₀ : Circuit (arithSignature ℤ) 0 1) :
    (⟨0, permBaseDiff c₀⟩ : Σ n, Circuit (arithSignature ℤ) n 1) ∈ PITInt ↔
      c₀.polynomial 0 = (genericMatrix ℤ 0).permanent := by
  rw [mem_PITInt_iff, polynomial_permBaseDiff, permanent_genericMatrix_zero, sub_eq_zero]

/-- Given that `cm` computes the `m × m` generic permanent, `permStepDiff m cm cm1` lies in `PITInt`
if and only if `cm1` computes the `(m + 1) × (m + 1)` generic permanent. -/
theorem mem_PITInt_permStepDiff_iff {m : ℕ} {cm : Circuit (arithSignature ℤ) (m * m) 1}
    (hcm : cm.polynomial 0 = (genericMatrix ℤ m).permanent)
    (cm1 : Circuit (arithSignature ℤ) ((m + 1) * (m + 1)) 1) :
    (⟨(m + 1) * (m + 1), permStepDiff m cm cm1⟩ :
        Σ n, Circuit (arithSignature ℤ) n 1) ∈ PITInt ↔
      cm1.polynomial 0 = (genericMatrix ℤ (m + 1)).permanent := by
  rw [mem_PITInt_iff, polynomial_permStepDiff, hcm, ← permanent_genericMatrix_succ, sub_eq_zero]

/-- **Downward self-reducibility of the permanent to `PITInt`**
([Kabanets and Impagliazzo, Lemma 4.2][KabanetsImpagliazzo2004];
[Arora and Barak, Theorem 20.16][AroraBarak09]): a family of arithmetic circuits
`C : ∀ m, Circuit (arithSignature ℤ) (m * m) 1` computes `(genericMatrix ℤ m).permanent` for every
`m ≤ n` if and only if `permBaseDiff (C 0)` and `permStepDiff m (C m) (C (m + 1))` for all `m < n`
belong to `PITInt`. -/
theorem forall_polynomial_eq_permanent_iff_mem_PITInt
    (C : ∀ m, Circuit (arithSignature ℤ) (m * m) 1) (n : ℕ) :
    (∀ m ≤ n, (C m).polynomial 0 = (genericMatrix ℤ m).permanent) ↔
      (⟨0, permBaseDiff (C 0)⟩ : Σ k, Circuit (arithSignature ℤ) k 1) ∈ PITInt ∧
        ∀ m < n,
          (⟨(m + 1) * (m + 1), permStepDiff m (C m) (C (m + 1))⟩ :
            Σ k, Circuit (arithSignature ℤ) k 1) ∈ PITInt := by
  induction n with
  | zero =>
    rw [mem_PITInt_permBaseDiff_iff]
    simp
  | succ n ih =>
    constructor
    · intro h
      have hn : ∀ m ≤ n, (C m).polynomial 0 = (genericMatrix ℤ m).permanent :=
        fun m hm => h m (Nat.le_succ_of_le hm)
      obtain ⟨h0, hstep⟩ := (ih).mp hn
      refine ⟨h0, fun m hm => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | rfl
      · exact hstep m hlt
      · exact (mem_PITInt_permStepDiff_iff (h m (Nat.le_succ m)) (C (m + 1))).mpr
          (h (m + 1) le_rfl)
    · rintro ⟨h0, hstep⟩
      have hn : ∀ m ≤ n, (C m).polynomial 0 = (genericMatrix ℤ m).permanent :=
        (ih).mpr ⟨h0, fun m hm => hstep m (Nat.lt_succ_of_lt hm)⟩
      intro m hm
      rcases Nat.le_iff_lt_or_eq.mp hm with hlt | rfl
      · exact hn m (Nat.le_of_lt_succ hlt)
      · exact (mem_PITInt_permStepDiff_iff (hn n le_rfl) (C (n + 1))).mp
          (hstep n (Nat.lt_succ_self n))

/-- A family of integer arithmetic circuits `C : ∀ m, Circuit (arithSignature ℤ) (m * m) 1` forms a
*Laplace permanent chain* up to dimension `n` when its base circuit `C 0` and its consecutive pairs
`(C m, C (m + 1))` for `m < n` satisfy the `PITInt` identities `permBaseDiff` and `permStepDiff`
([Kabanets and Impagliazzo, Lemma 4.2][KabanetsImpagliazzo2004]). -/
structure IsLaplacePermChain (C : ∀ m, Circuit (arithSignature ℤ) (m * m) 1) (n : ℕ) : Prop where
  /-- The `0 × 0` circuit satisfies `permBaseDiff (C 0) ∈ PITInt`. -/
  base_mem : (⟨0, permBaseDiff (C 0)⟩ : Σ k, Circuit (arithSignature ℤ) k 1) ∈ PITInt
  /-- Every step `m < n` satisfies `permStepDiff m (C m) (C (m + 1)) ∈ PITInt`. -/
  step_mem : ∀ m < n,
    (⟨(m + 1) * (m + 1), permStepDiff m (C m) (C (m + 1))⟩ :
      Σ k, Circuit (arithSignature ℤ) k 1) ∈ PITInt

/-- A candidate integer arithmetic circuit family `C` computes `(genericMatrix ℤ m).permanent` for
all `m ≤ n` if and only if `IsLaplacePermChain C n` holds. -/
theorem forall_polynomial_eq_permanent_iff_isLaplacePermChain
    (C : ∀ m, Circuit (arithSignature ℤ) (m * m) 1) (n : ℕ) :
    (∀ m ≤ n, (C m).polynomial 0 = (genericMatrix ℤ m).permanent) ↔
      IsLaplacePermChain C n := by
  rw [forall_polynomial_eq_permanent_iff_mem_PITInt]
  exact ⟨fun ⟨h0, hs⟩ => ⟨h0, hs⟩, fun ⟨h0, hs⟩ => ⟨h0, hs⟩⟩

/-- Explicit arithmetic circuit family computing the `m × m` generic permanent by recursive Laplace
expansion along row 0. Its gate count grows factorially, witnessing unconditionally that the
Laplace `PITInt` identities `permBaseDiff` and `permStepDiff` are satisfiable at every dimension
`m`. -/
def laplacePermCircuit : ∀ m : ℕ, Circuit (arithSignature R) (m * m) 1
  | 0 => constCircuit 1
  | m + 1 =>
    finSumCircuit fun j : Fin (m + 1) =>
      mulCircuit (varCircuit (finProdFinEquiv (0, j)))
        (reindexCircuit (minorVar j) (laplacePermCircuit m))

@[simp] theorem polynomial_laplacePermCircuit :
    ∀ m : ℕ, (laplacePermCircuit (R := R) m).polynomial 0 = (genericMatrix R m).permanent
  | 0 => by
    rw [laplacePermCircuit, polynomial_constCircuit, map_one, permanent_genericMatrix_zero]
  | m + 1 => by
    rw [laplacePermCircuit, polynomial_finSumCircuit, permanent_genericMatrix_succ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [polynomial_mulCircuit, polynomial_varCircuit, polynomial_reindexCircuit,
      polynomial_laplacePermCircuit m]

/-- `laplacePermCircuit` forms a valid Laplace permanent chain up to every dimension `n`. -/
theorem isLaplacePermChain_laplacePermCircuit (n : ℕ) :
    IsLaplacePermChain (laplacePermCircuit (R := ℤ)) n :=
  (forall_polynomial_eq_permanent_iff_isLaplacePermChain _ n).mp
    fun m _ => polynomial_laplacePermCircuit m

end Permanent

/-! ### Certified permanent circuit families from `PITInt ∈ P` and `intPermFamily ∈ VP ℤ` -/

/-- Existence of a polynomial-time `PITInt` certification package for the integer permanent: a
polynomial-time decider `decidePIT` for `PITInt` together with a polynomially bounded arithmetic
circuit family `C` whose Laplace expansion identities `permBaseDiff` and `permStepDiff` are accepted
by `decidePIT`, and such that any candidate family `C'` accepted by `decidePIT` on those identities
up to dimension `n` computes `(genericMatrix ℤ m).permanent` for all `m ≤ n`. -/
structure PermPITCertified : Prop where
  /-- Existence of a polynomial-time decider and certified polynomially bounded circuit family. -/
  exists_tester :
    ∃ (decidePIT : (Σ n, Circuit (arithSignature ℤ) n 1) → Bool)
      (C : ∀ m, Circuit (arithSignature ℤ) (m * m) 1),
      ComputableTidilyInPolyTime decidePIT encArithCircuitInt encBool ∧
      PolynomiallyBounded (fun m => (C m).size) ∧
      PolynomiallyBounded (fun m => (permStepDiff m (C m) (C (m + 1))).size) ∧
      (∀ c, c ∈ PITInt ↔ decidePIT c = true) ∧
      decidePIT ⟨0, permBaseDiff (C 0)⟩ = true ∧
      (∀ m, decidePIT ⟨(m + 1) * (m + 1), permStepDiff m (C m) (C (m + 1))⟩ = true) ∧
      ∀ (C' : ∀ m, Circuit (arithSignature ℤ) (m * m) 1) (n : ℕ),
        (∀ m ≤ n, (C' m).polynomial 0 = (genericMatrix ℤ m).permanent) ↔
          decidePIT ⟨0, permBaseDiff (C' 0)⟩ = true ∧
            ∀ m < n, decidePIT ⟨(m + 1) * (m + 1), permStepDiff m (C' m) (C' (m + 1))⟩ = true

/-- **If `PITInt ∈ P` and `intPermFamily ∈ VP ℤ`, then the integer permanent has a polynomial-time
PIT-certified circuit family** (`PermPITCertified`)
[Kabanets and Impagliazzo, Lemma 4.2][KabanetsImpagliazzo2004]. -/
theorem exists_certified_perm_family_of_PITInt_mem_P_of_mem_VP
    (hPIT : PITInt ∈ Cslib.Complexity.P encArithCircuitInt) (hPerm : intPermFamily ∈ VP ℤ) :
    PermPITCertified := by
  obtain ⟨decidePIT, hdec_poly, hdec_iff⟩ := hPIT
  obtain ⟨_, C, hC_size, hC_poly⟩ := hPerm
  change ∀ m, Circuit (arithSignature ℤ) (m * m) 1 at C
  change ∀ m, (C m).polynomial 0 = (genericMatrix ℤ m).permanent at hC_poly
  have hstep_size : PolynomiallyBounded (fun m => (permStepDiff m (C m) (C (m + 1))).size) := by
    have hC1 : PolynomiallyBounded (fun m => (C (m + 1)).size) :=
      hC_size.comp (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))
    have hmul : PolynomiallyBounded
        (fun m => (C (m + 1)).size + (m + 1) * ((C m).size + 2) + 4) := by
      fun_prop
    exact hmul.mono_of_le fun m => (size_permStepDiff m (C m) (C (m + 1))).le
  have hsound (C' : ∀ m, Circuit (arithSignature ℤ) (m * m) 1) (n : ℕ) :
      (∀ m ≤ n, (C' m).polynomial 0 = (genericMatrix ℤ m).permanent) ↔
        decidePIT ⟨0, permBaseDiff (C' 0)⟩ = true ∧
          ∀ m < n, decidePIT ⟨(m + 1) * (m + 1), permStepDiff m (C' m) (C' (m + 1))⟩ = true := by
    rw [forall_polynomial_eq_permanent_iff_mem_PITInt]
    simp only [hdec_iff]
  have hC_all (n : ℕ) : ∀ m ≤ n, (C m).polynomial 0 = (genericMatrix ℤ m).permanent :=
    fun m _ => hC_poly m
  have hC0 : decidePIT ⟨0, permBaseDiff (C 0)⟩ = true :=
    ((hsound C 0).mp (hC_all 0)).1
  have hCm (m : ℕ) : decidePIT ⟨(m + 1) * (m + 1), permStepDiff m (C m) (C (m + 1))⟩ = true :=
    ((hsound C (m + 1)).mp (hC_all (m + 1))).2 m (Nat.lt_succ_self m)
  exact ⟨⟨decidePIT, C, hdec_poly, hC_size, hstep_size, hdec_iff, hC0, hCm, hsound⟩⟩

end Cslib.Circuits.Arithmetic

/-! ### `NEXP` circuit lower bounds and the Kabanets–Impagliazzo theorem -/

namespace Cslib.Complexity

open Turing.MultiTapeTM Circuits Circuits.Boolean

variable {α : Type} {enc : α ↪ List Bool}

/-- If `NEXP` collapses into `Σₖ`, then `NEXP = EXP`. -/
theorem NEXP_eq_EXP_of_NEXP_subset_SigmaP {k : ℕ} (h : NEXP enc ⊆ SigmaP k enc) :
    NEXP enc = EXP enc :=
  Set.Subset.antisymm (h.trans (SigmaP_subset_EXP k)) EXP_subset_NEXP

/-- **Unconditional fixed-exponent circuit lower bound in `NEXP`**: for every `k : ℕ`, some
language in `NEXP` (in fact in `Σ₂`) has no Boolean circuits of size `O(n ^ k)`
([Kannan][Kannan1982]). -/
theorem exists_mem_NEXP_notMem_SIZE (k : ℕ) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧
      ∀ c, L ∉ SIZE fun n => c * (n + 1) ^ k := by
  obtain ⟨L, hL₂, hLsize⟩ := exists_mem_SigmaP_two_notMem_SIZE k
  exact ⟨L, SigmaP_subset_NEXP 2 hL₂, hLsize⟩

end Cslib.Complexity

namespace Cslib.Circuits.Arithmetic

open Turing.MultiTapeTM Cslib.Complexity Cslib.Circuits.Boolean

/-- **The Kabanets–Impagliazzo derandomization-to-lower-bounds theorem**
([Kabanets and Impagliazzo, Theorem 4.1][KabanetsImpagliazzo2004];
[Arora and Barak, Theorem 20.16][AroraBarak09]): if Polynomial Identity Testing over `ℤ` is in `P`
(`PITInt ∈ P encArithCircuitInt`), then under the Impagliazzo–Kabanets–Wigderson / Valiant–Toda
collapse (stating that if `NEXP ⊆ P/poly` and `PermPITCertified` holds, then `Σ₂` has Boolean
circuits of some fixed polynomial degree `O(n ^ k)`), either `NEXP ⊄ P/poly` or the integer
permanent family `intPermFamily` is not in `VP ℤ`.

The downward self-reducibility of the permanent to `PITInt`
(`forall_polynomial_eq_permanent_iff_mem_PITInt` and
`exists_certified_perm_family_of_PITInt_mem_P_of_mem_VP`) and the `Σ₂` fixed-degree circuit lower
bound (`exists_mem_SigmaP_two_notMem_SIZE`) are proved unconditionally; `hCollapse` supplies the
external collapse from `NEXP ⊆ P/poly` and the PIT-certified permanent circuit family. -/
theorem kabanets_impagliazzo
    (hPIT : PITInt ∈ Cslib.Complexity.P encArithCircuitInt)
    (hCollapse :
      (∀ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits → L ∈ PPoly) →
      PermPITCertified →
      ∃ k : ℕ, ∀ L : Language Bool,
        (L : Set (List Bool)) ∈ SigmaP 2 encBits → ∃ c, L ∈ SIZE fun n => c * (n + 1) ^ k) :
    (∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧ L ∉ PPoly) ∨
      intPermFamily ∉ VP ℤ := by
  by_cases hNEXP : ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧ L ∉ PPoly
  · exact Or.inl hNEXP
  · refine Or.inr fun hPerm => ?_
    push Not at hNEXP
    have hCert : PermPITCertified :=
      exists_certified_perm_family_of_PITInt_mem_P_of_mem_VP hPIT hPerm
    obtain ⟨k, hSigmaSize⟩ := hCollapse hNEXP hCert
    obtain ⟨L, hL₂, hLnot⟩ := exists_mem_SigmaP_two_notMem_SIZE k
    obtain ⟨c, hc⟩ := hSigmaSize L hL₂
    exact hLnot c hc

/-- **The Kabanets–Impagliazzo theorem via time-hierarchy collapse (`EXP ⊆ P`)**
([Kabanets and Impagliazzo, Theorem 4.1][KabanetsImpagliazzo2004];
[Arora and Barak, Theorem 20.16][AroraBarak09]): if `PITInt ∈ P encArithCircuitInt`, then under the
collapse from `NEXP ⊆ P/poly` and `PermPITCertified` to `EXP ⊆ P`, either `NEXP ⊄ P/poly` or
`intPermFamily ∉ VP ℤ`, refuting `EXP ⊆ P` by the time hierarchy theorem (`P_ssubset_EXP`). -/
theorem kabanets_impagliazzo_of_EXP_subset_P
    (hPIT : PITInt ∈ Cslib.Complexity.P encArithCircuitInt)
    (hCollapse :
      (∀ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits → L ∈ PPoly) →
      PermPITCertified →
      EXP encBits ⊆ Cslib.Complexity.P encBits) :
    (∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧ L ∉ PPoly) ∨
      intPermFamily ∉ VP ℤ := by
  by_cases hNEXP : ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧ L ∉ PPoly
  · exact Or.inl hNEXP
  · refine Or.inr fun hPerm => ?_
    push Not at hNEXP
    have hCert : PermPITCertified :=
      exists_certified_perm_family_of_PITInt_mem_P_of_mem_VP hPIT hPerm
    exact P_ssubset_EXP.not_subset (hCollapse hNEXP hCert)

end Cslib.Circuits.Arithmetic
