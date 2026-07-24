import KTLean.GlyphSpectralExponentialKernel
import Mathlib.Tactic

/-!
# The Exponential Recurrence as a Canonical Series

## Formal status

**Level 2 — Exact finite identification of the exponential orbit with
its recursively generated term and partial-sum sequences.**

The exponential kernel already established the deterministic recurrence

    T₀ = 1
    Tₙ₊₁ = Tₙ / (n + 1)

and

    S₀ = 1
    Sₙ₊₁ = Sₙ + Tₙ₊₁.

This module defines those sequences independently and proves that they
are exactly the increment and accumulated components of the previously
derived exponential orbit.

No convergence theorem and no identification with `Real.exp 1` occur
here.
-/

namespace GlyphSpectralExponentialSeriesBridge

open GlyphSpectralExponentialKernel

/--
The canonical unit-exponential term sequence.
-/
def unitExpTerm :
    Nat →
      ℚ

  | 0 =>
      1

  | n + 1 =>
      unitExpTerm n / (n + 1)

/--
The canonical finite partial sums.
-/
def unitExpPartialSum :
    Nat →
      ℚ

  | 0 =>
      1

  | n + 1 =>
      unitExpPartialSum n
        +
      unitExpTerm (n + 1)

/--
The zeroth term is one.
-/
@[simp]
theorem unitExpTerm_zero :
    unitExpTerm 0 =
      1 := by

  rfl

/--
Each successor term is forced from the previous term and stage index.
-/
@[simp]
theorem unitExpTerm_succ
    (n : Nat) :
    unitExpTerm (n + 1) =
      unitExpTerm n / (n + 1) := by

  rfl

/--
The zeroth partial sum is one.
-/
@[simp]
theorem unitExpPartialSum_zero :
    unitExpPartialSum 0 =
      1 := by

  rfl

/--
Each successor partial sum adjoins the newly forced term.
-/
@[simp]
theorem unitExpPartialSum_succ
    (n : Nat) :
    unitExpPartialSum (n + 1) =
      unitExpPartialSum n
        +
      unitExpTerm (n + 1) := by

  rfl

/--
The recursively generated term sequence is exactly the increment
component of the exponential orbit.
-/
theorem orbit_increment_eq_unitExpTerm
    (n : Nat) :
    (orbit n).increment =
      unitExpTerm n := by

  induction n with

  | zero =>
      rfl

  | succ n ih =>
      rw [
        orbit_increment_succ,
        unitExpTerm_succ,
        ih
      ]

/--
The recursively generated partial sums are exactly the accumulated
component of the exponential orbit.
-/
theorem orbit_accumulated_eq_unitExpPartialSum
    (n : Nat) :
    (orbit n).accumulated =
      unitExpPartialSum n := by

  induction n with

  | zero =>
      rfl

  | succ n ih =>
      rw [
        orbit_accumulated_succ,
        unitExpPartialSum_succ,
        ih,
        orbit_increment_eq_unitExpTerm
      ]

/--
Every canonical exponential term is positive.
-/
theorem unitExpTerm_positive
    (n : Nat) :
    0 <
      unitExpTerm n := by

  rw [
    ← orbit_increment_eq_unitExpTerm
  ]

  exact
    orbit_increment_positive n

/--
Every canonical exponential partial sum is positive.
-/
theorem unitExpPartialSum_positive
    (n : Nat) :
    0 <
      unitExpPartialSum n := by

  rw [
    ← orbit_accumulated_eq_unitExpPartialSum
  ]

  exact
    orbit_accumulated_positive n

/--
The canonical partial sums increase strictly.
-/
theorem unitExpPartialSum_strictly_increases
    (n : Nat) :
    unitExpPartialSum n
      <
    unitExpPartialSum (n + 1) := by

  rw [
    ← orbit_accumulated_eq_unitExpPartialSum,
    ← orbit_accumulated_eq_unitExpPartialSum
  ]

  exact
    orbit_accumulated_strictly_increases n

/--
The first four canonical terms are

    1, 1, 1/2, 1/6.
-/
theorem first_four_unitExpTerms :
    unitExpTerm 0 =
        1
      ∧
    unitExpTerm 1 =
        1
      ∧
    unitExpTerm 2 =
        1 / 2
      ∧
    unitExpTerm 3 =
        1 / 6 := by

  norm_num [
    unitExpTerm
  ]

/--
The first four canonical partial sums are

    1, 2, 5/2, 8/3.
-/
theorem first_four_unitExpPartialSums :
    unitExpPartialSum 0 =
        1
      ∧
    unitExpPartialSum 1 =
        2
      ∧
    unitExpPartialSum 2 =
        5 / 2
      ∧
    unitExpPartialSum 3 =
        8 / 3 := by

  norm_num [
    unitExpPartialSum,
    unitExpTerm
  ]

/--
Every partial-sum successor is the unique additive completion of its
predecessor and the newly forced term.
-/
theorem partialSum_successor_is_unique_completion
    (n : Nat) :
    ∃! next : ℚ,
      next =
        unitExpPartialSum n
          +
        unitExpTerm (n + 1) := by

  exact
    ⟨
      unitExpPartialSum n
        +
      unitExpTerm (n + 1),
      rfl,
      by
        intro next h
        exact h
    ⟩

/--
Capstone theorem.

The previously derived exponential orbit is exactly the independently
defined canonical term-and-partial-sum system.
-/
theorem exponential_orbit_is_canonical_series :
    (∀ n : Nat,
      (orbit n).increment =
        unitExpTerm n)
      ∧
    (∀ n : Nat,
      (orbit n).accumulated =
        unitExpPartialSum n)
      ∧
    (∀ n : Nat,
      0 <
        unitExpTerm n)
      ∧
    (∀ n : Nat,
      unitExpPartialSum n
        <
      unitExpPartialSum (n + 1)) := by

  exact
    ⟨
      orbit_increment_eq_unitExpTerm,
      orbit_accumulated_eq_unitExpPartialSum,
      unitExpTerm_positive,
      unitExpPartialSum_strictly_increases
    ⟩

end GlyphSpectralExponentialSeriesBridge

#check GlyphSpectralExponentialSeriesBridge.unitExpTerm
#check GlyphSpectralExponentialSeriesBridge.unitExpPartialSum
#check GlyphSpectralExponentialSeriesBridge.orbit_increment_eq_unitExpTerm
#check GlyphSpectralExponentialSeriesBridge.orbit_accumulated_eq_unitExpPartialSum
#check GlyphSpectralExponentialSeriesBridge.unitExpTerm_positive
#check GlyphSpectralExponentialSeriesBridge.unitExpPartialSum_positive
#check GlyphSpectralExponentialSeriesBridge.unitExpPartialSum_strictly_increases
#check GlyphSpectralExponentialSeriesBridge.first_four_unitExpTerms
#check GlyphSpectralExponentialSeriesBridge.first_four_unitExpPartialSums
#check GlyphSpectralExponentialSeriesBridge.partialSum_successor_is_unique_completion
#check GlyphSpectralExponentialSeriesBridge.exponential_orbit_is_canonical_series
