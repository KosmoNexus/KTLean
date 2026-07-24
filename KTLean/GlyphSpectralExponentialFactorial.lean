import KTLean.GlyphSpectralExponentialSeriesBridge
import Mathlib.Tactic

/-!
# Factorial Form of the Triadic Exponential Stream

## Formal status

**Level 2 — Exact finite identification of the recurrence terms.**

The previously derived term sequence satisfies

    T₀ = 1
    Tₙ₊₁ = Tₙ / (n + 1).

This module proves by induction that

    Tₙ = 1 / n!.

Consequently, the accumulated state is exactly the finite sum

    Sₙ = ∑ k in range (n + 1), 1 / k!.

This supplies the standard finite exponential series in a form suitable
for analytic identification with `Real.exp 1`.
-/

namespace GlyphSpectralExponentialFactorial

open Finset

open GlyphSpectralExponentialKernel
open GlyphSpectralExponentialSeriesBridge
open scoped BigOperators

/--
The rational reciprocal factorial term.
-/
def reciprocalFactorial
    (n : Nat) :
    ℚ :=

  1 / (n.factorial : ℚ)

/--
The zeroth reciprocal factorial is one.
-/
@[simp]
theorem reciprocalFactorial_zero :
    reciprocalFactorial 0 = 1 := by
  simp [reciprocalFactorial]

/--
The reciprocal factorial recurrence.
-/
theorem reciprocalFactorial_succ
    (n : Nat) :
    reciprocalFactorial (n + 1) =
      reciprocalFactorial n / (n + 1) := by

  unfold reciprocalFactorial

  rw [Nat.factorial_succ]

  push_cast

  have hFactorial :
      (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n

  have hSucc :
      ((n + 1 : Nat) : ℚ) ≠ 0 := by
    positivity

  field_simp [hFactorial, hSucc]

/--
Every recursively generated exponential term is exactly `1 / n!`.
-/
theorem unitExpTerm_eq_reciprocalFactorial
    (n : Nat) :
    unitExpTerm n =
      reciprocalFactorial n := by

  induction n with

  | zero =>
      simp

  | succ n ih =>
      rw [
        unitExpTerm_succ,
        reciprocalFactorial_succ,
        ih
      ]

/--
The increment component of the original orbit is exactly `1 / n!`.
-/
theorem orbit_increment_eq_reciprocalFactorial
    (n : Nat) :
    (orbit n).increment =
      reciprocalFactorial n := by

  rw [
    orbit_increment_eq_unitExpTerm,
    unitExpTerm_eq_reciprocalFactorial
  ]

/--
The canonical finite exponential series through term `n`.
-/
def factorialPartialSum
    (n : Nat) :
    ℚ :=

  Finset.sum
    (Finset.range (n + 1))
    reciprocalFactorial

/--
The zeroth factorial partial sum is one.
-/
@[simp]
theorem factorialPartialSum_zero :
    factorialPartialSum 0 =
      1 := by

  norm_num [
    factorialPartialSum,
    reciprocalFactorial
  ]

/--
Each successor factorial partial sum appends the next reciprocal
factorial.
-/
theorem factorialPartialSum_succ
    (n : Nat) :
    factorialPartialSum (n + 1) =
      factorialPartialSum n
        +
      reciprocalFactorial (n + 1) := by

  unfold factorialPartialSum
  rw [sum_range_succ]


/--
The recursively generated accumulated sequence is exactly the finite
factorial series.
-/
theorem unitExpPartialSum_eq_factorialPartialSum
    (n : Nat) :
    unitExpPartialSum n =
      factorialPartialSum n := by

  induction n with

  | zero =>
      simp

  | succ n ih =>
      rw [
        unitExpPartialSum_succ,
        factorialPartialSum_succ,
        ih,
        unitExpTerm_eq_reciprocalFactorial
      ]

/--
The accumulated component of the original orbit is the finite
factorial series.
-/
theorem orbit_accumulated_eq_factorialPartialSum
    (n : Nat) :
    (orbit n).accumulated =
      factorialPartialSum n := by

  rw [
    orbit_accumulated_eq_unitExpPartialSum,
    unitExpPartialSum_eq_factorialPartialSum
  ]

/--
Every reciprocal-factorial term is positive.
-/
theorem reciprocalFactorial_positive
    (n : Nat) :
    0 <
      reciprocalFactorial n := by

  unfold reciprocalFactorial

  positivity

/--
The first four reciprocal factorials are `1, 1, 1/2, 1/6`.
-/
theorem first_four_reciprocalFactorials :
    reciprocalFactorial 0 =
        1
      ∧
    reciprocalFactorial 1 =
        1
      ∧
    reciprocalFactorial 2 =
        1 / 2
      ∧
    reciprocalFactorial 3 =
        1 / 6 := by

  norm_num [
    reciprocalFactorial
  ]

/--
Capstone theorem.

The triadically generated exponential recurrence is exactly the
reciprocal-factorial series.
-/
theorem triadic_exponential_stream_is_factorial_series :
    (∀ n : Nat,
      (orbit n).increment =
        1 / (n.factorial : ℚ))
      ∧
        (∀ n : Nat,
      (orbit n).accumulated =
        Finset.sum
          (Finset.range (n + 1))
          (fun k =>
            1 / (k.factorial : ℚ)))
      ∧
    (∀ n : Nat,
      0 <
        reciprocalFactorial n) := by

  refine
    ⟨
      ?_,
      ?_,
      reciprocalFactorial_positive
    ⟩

  · intro n

    simpa [
      reciprocalFactorial
    ] using
      orbit_increment_eq_reciprocalFactorial n

  · intro n

    simpa [
      factorialPartialSum,
      reciprocalFactorial
    ] using
      orbit_accumulated_eq_factorialPartialSum n

end GlyphSpectralExponentialFactorial

#check GlyphSpectralExponentialFactorial.reciprocalFactorial
#check GlyphSpectralExponentialFactorial.reciprocalFactorial_succ
#check GlyphSpectralExponentialFactorial.unitExpTerm_eq_reciprocalFactorial
#check GlyphSpectralExponentialFactorial.orbit_increment_eq_reciprocalFactorial
#check GlyphSpectralExponentialFactorial.factorialPartialSum
#check GlyphSpectralExponentialFactorial.factorialPartialSum_succ
#check GlyphSpectralExponentialFactorial.unitExpPartialSum_eq_factorialPartialSum
#check GlyphSpectralExponentialFactorial.orbit_accumulated_eq_factorialPartialSum
#check GlyphSpectralExponentialFactorial.triadic_exponential_stream_is_factorial_series
