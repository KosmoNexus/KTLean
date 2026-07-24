import KTLean.GlyphSpectralExponentialFactorial
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
# Analytic Limit of the Triadic Exponential Stream

## Formal status

**Level 2 — Analytic identification of the generated stream.**

The preceding modules established that the triadically generated
increment sequence is

    Tₙ = 1 / n!

and that the accumulated state is the finite sum

    Sₙ = ∑ k in range (n + 1), 1 / k!.

This module transports those rational partial sums into `ℝ` and proves
that they converge to `Real.exp 1`.

Thus the generated exponential stream is analytically identified with
Euler's number.
-/

namespace GlyphSpectralExponentialLimit

open Finset
open Filter
open scoped BigOperators Topology

open GlyphSpectralExponentialKernel
open GlyphSpectralExponentialSeriesBridge
open GlyphSpectralExponentialFactorial

/--
The real-valued form of the finite factorial partial sum.
-/
def realFactorialPartialSum
    (n : Nat) :
    ℝ :=

  (factorialPartialSum n : ℝ)

/--
The coerced rational partial sum is the corresponding finite real
reciprocal-factorial series.
-/
theorem realFactorialPartialSum_eq_sum
    (n : Nat) :
    realFactorialPartialSum n =
      Finset.sum
        (Finset.range (n + 1))
        (fun k =>
          1 / (k.factorial : ℝ)) := by

  unfold realFactorialPartialSum
  unfold factorialPartialSum
  unfold reciprocalFactorial

  push_cast
  rfl

/--
The standard real reciprocal-factorial series has sum `Real.exp 1`.
-/
theorem reciprocalFactorial_hasSum_exp_one :
    HasSum
      (fun n : Nat =>
        1 / (n.factorial : ℝ))
      (Real.exp 1) := by

  have hExp :
      HasSum
        (fun n : Nat =>
          ((n.factorial : ℝ)⁻¹) •
            (1 : ℝ) ^ n)
        (NormedSpace.exp (1 : ℝ)) := by

    exact
      NormedSpace.exp_series_hasSum_exp'
        (𝕂 := ℝ)
        (𝔸 := ℝ)
        (1 : ℝ)

  simpa [
    Real.exp_eq_exp_ℝ,
    div_eq_mul_inv
  ] using hExp

/--
The finite real factorial partial sums converge to `Real.exp 1`.
-/
theorem realFactorialPartialSum_tendsto_exp_one :
    Tendsto
      realFactorialPartialSum
      atTop
      (𝓝 (Real.exp 1)) := by

  have hBase :
      Tendsto
        (fun n : Nat =>
          Finset.sum
            (Finset.range n)
            (fun k =>
              1 / (k.factorial : ℝ)))
        atTop
        (𝓝 (Real.exp 1)) :=

    reciprocalFactorial_hasSum_exp_one.tendsto_sum_nat

  have hEquality :
      realFactorialPartialSum
        =
      (fun n : Nat =>
        Finset.sum
          (Finset.range (n + 1))
          (fun k =>
            1 / (k.factorial : ℝ))) := by

    funext n
    exact realFactorialPartialSum_eq_sum n

  rw [hEquality]

  exact
    (tendsto_add_atTop_iff_nat 1).mpr
      hBase

/--
The accumulated component of the original orbit, coerced to `ℝ`,
converges to Euler's number.
-/
theorem orbit_accumulated_tendsto_exp_one :
    Tendsto
      (fun n : Nat =>
        ((orbit n).accumulated : ℝ))
      atTop
      (𝓝 (Real.exp 1)) := by

  have hEquality :
      (fun n : Nat =>
        ((orbit n).accumulated : ℝ))
        =
      realFactorialPartialSum := by

    funext n

    rw [
      orbit_accumulated_eq_factorialPartialSum
    ]

    rfl

  rw [hEquality]

  exact
    realFactorialPartialSum_tendsto_exp_one

/--
Capstone theorem.

The triadically generated exponential stream has reciprocal-factorial
increments, exact finite factorial partial sums, and accumulated state
converging to Euler's number.
-/
theorem triadic_exponential_stream_converges_to_e :
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
    Tendsto
      (fun n : Nat =>
        ((orbit n).accumulated : ℝ))
      atTop
      (𝓝 (Real.exp 1)) := by

  refine
    ⟨
      ?_,
      ?_,
      orbit_accumulated_tendsto_exp_one
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

end GlyphSpectralExponentialLimit

#check GlyphSpectralExponentialLimit.realFactorialPartialSum
#check GlyphSpectralExponentialLimit.realFactorialPartialSum_eq_sum
#check GlyphSpectralExponentialLimit.reciprocalFactorial_hasSum_exp_one
#check GlyphSpectralExponentialLimit.realFactorialPartialSum_tendsto_exp_one
#check GlyphSpectralExponentialLimit.orbit_accumulated_tendsto_exp_one
#check GlyphSpectralExponentialLimit.triadic_exponential_stream_converges_to_e
