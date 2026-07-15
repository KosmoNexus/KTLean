import KTLean.PrimitiveRecurrence
import Mathlib.Data.Nat.Prime.Defs

/-!
# Spinorial Irreducibility

`PrimitiveRecurrence` established that temporal primitiveness
alone does not imply arithmetic primality. A primitive
four-cycle provides a counterexample.

This module introduces a stronger, genuinely dynamical
notion of decomposition.

If a period factors as

    period = blockLength × blockCount,

then the original evolution may be viewed as repeated
application of a block step, where one block consists of
`blockLength` elementary spinor steps.

A nontrivial block decomposition requires:

1. block length greater than one;
2. block count greater than one;
3. the block moves the base state;
4. repeated block evolution closes the orbit.

The principal theorem proves:

    primitive return
    + spinorial indecomposability
    + period at least two
    → arithmetic primality.

Thus primality is obtained from the absence of a
nontrivial compositional structure in the spinor orbit.
-/

namespace SpinorIrreducibility


open SpinorOrbit
open SpinorOrbit.System
open PrimitiveRecurrence


/-
## Block evolution
-/

/--
One block step consists of `blockLength` elementary spinor
steps.
-/
def blockStep
    (S : SpinorOrbit.System)
    (blockLength : Nat) :
    S.State → S.State :=

  fun state =>
    SpinorOrbit.advance
      S.step
      blockLength
      state


/--
Advancing by `blockCount` block steps is equivalent to
advancing by the product of block count and block length.
-/
theorem advance_blockStep
    (S : SpinorOrbit.System)
    (blockLength blockCount : Nat)
    (state : S.State) :

    SpinorOrbit.advance
        (blockStep S blockLength)
        blockCount
        state =

      SpinorOrbit.advance
        S.step
        (blockCount * blockLength)
        state := by

  induction blockCount with

  | zero =>
      simp

  | succ blockCount ih =>

      rw [
        SpinorOrbit.advance_succ,
        ih,
        Nat.succ_mul,
        SpinorOrbit.advance_add
      ]

      rfl


/-
## Dynamical block decomposition
-/

/--
A nontrivial spinorial block decomposition of one return
period.

The complete orbit is assembled from more than one
nontrivial block, and each block itself contains more than
one elementary step.
-/
structure BlockDecomposition
    (S : SpinorOrbit.System)
    (period : Nat) where

  blockLength :
    Nat

  blockCount :
    Nat

  blockLength_gt_one :
    1 < blockLength

  blockCount_gt_one :
    1 < blockCount

  period_eq :
    period =
      blockLength * blockCount

  block_moves :
    blockStep S blockLength S.base ≠
      S.base

  block_closes :

    SpinorOrbit.advance
        (blockStep S blockLength)
        blockCount
        S.base =

      S.base


/--
A recurrence is spinorially indecomposable when no
nontrivial block decomposition exists.
-/
def Indecomposable
    (S : SpinorOrbit.System)
    (period : Nat) :
    Prop :=

  ∀ _decomposition :
      BlockDecomposition S period,

    False


/--
Every block decomposition supplies a nontrivial arithmetic
factorization of its period.
-/
theorem BlockDecomposition.hasNontrivialFactorization
    {S : SpinorOrbit.System}
    {period : Nat}
    (decomposition :
      BlockDecomposition S period) :

    PrimitiveRecurrence.HasNontrivialFactorization
      period := by

  exact
    ⟨
      decomposition.blockLength,
      decomposition.blockCount,
      decomposition.blockLength_gt_one,
      decomposition.blockCount_gt_one,
      decomposition.period_eq
    ⟩


/--
Spinorial indecomposability forbids every dynamically
realized nontrivial period factorization.
-/
theorem indecomposable_no_block_factorization
    {S : SpinorOrbit.System}
    {period : Nat}
    (hindecomposable :
      Indecomposable S period) :

    ¬ Nonempty
        (BlockDecomposition S period) := by

  intro hnonempty

  exact
    hnonempty.elim
      hindecomposable


/-
## Composite primitive periods decompose
-/

/--
A proper nontrivial divisor of a primitive return period
induces a nontrivial spinorial block decomposition.

This is the key bridge from arithmetic factorization to
dynamical composition.
-/
theorem blockDecomposition_of_proper_divisor
    (S : SpinorOrbit.System)
    (period divisor : Nat)
    (hprimitive :
      S.PrimitiveReturn period)
    (hdivisor_two :
      2 ≤ divisor)
    (hdivisor_lt :
      divisor < period)
    (hdivisor_dvd :
      divisor ∣ period) :

    Nonempty
      (BlockDecomposition S period) := by

  rcases hdivisor_dvd with
    ⟨blockCount, hperiod⟩

  have hdivisor_positive :
      0 < divisor := by

    omega

  have hcount_ne_zero :
      blockCount ≠ 0 := by

    intro hzero

    subst blockCount

    simp at hperiod

    omega

  have hcount_positive :
      0 < blockCount :=

    Nat.pos_of_ne_zero
      hcount_ne_zero

  have hcount_ne_one :
      blockCount ≠ 1 := by

    intro hone

    subst blockCount

    simp at hperiod

    exact
      hdivisor_lt.ne
        hperiod.symm

  have hcount_gt_one :
      1 < blockCount := by

    omega

  have hblock_moves :

      blockStep S divisor S.base ≠
        S.base := by

    intro hfixed

    apply
      hprimitive.no_earlier_return
        hdivisor_positive
        hdivisor_lt

    exact hfixed

  have hblock_closes :

      SpinorOrbit.advance
          (blockStep S divisor)
          blockCount
          S.base =

        S.base := by

    rw [
      advance_blockStep,
      Nat.mul_comm,
      ← hperiod
    ]

    exact
      hprimitive.returns

  exact
    ⟨
      {
        blockLength :=
          divisor

        blockCount :=
          blockCount

        blockLength_gt_one := by
          omega

        blockCount_gt_one :=
          hcount_gt_one

        period_eq :=
          hperiod

        block_moves :=
          hblock_moves

        block_closes :=
          hblock_closes
      }
    ⟩

/-
## Spinorial irreducibility forces primality
-/

/--
A primitive, spinorially indecomposable return period of at
least two is arithmetically prime.
-/
theorem prime_of_primitive_indecomposable
    (S : SpinorOrbit.System)
    (period : Nat)
    (hperiod_two :
      2 ≤ period)
    (hprimitive :
      S.PrimitiveReturn period)
    (hindecomposable :
      Indecomposable S period) :

    Nat.Prime period := by

  rw [Nat.prime_def_lt']

  refine
    ⟨
      hperiod_two,
      ?_
    ⟩

  intro divisor
  intro hdivisor_two
  intro hdivisor_lt
  intro hdivisor_dvd

  have hdecomposition :

      Nonempty
        (BlockDecomposition S period) :=

    blockDecomposition_of_proper_divisor
      S
      period
      divisor
      hprimitive
      hdivisor_two
      hdivisor_lt
      hdivisor_dvd

  exact
    hdecomposition.elim
      hindecomposable


/--
A prime mode packages the three properties required to
derive a number-theoretic prime from spinorial evolution.
-/
structure PrimeMode
    (S : SpinorOrbit.System) where

  period :
    Nat

  period_two_le :
    2 ≤ period

  primitive :
    S.PrimitiveReturn period

  indecomposable :
    Indecomposable S period


namespace PrimeMode


/--
The recurrence period of every spinorial prime mode is a
natural-number prime.
-/
theorem period_prime
    {S : SpinorOrbit.System}
    (mode : PrimeMode S) :

    Nat.Prime mode.period := by

  exact
    prime_of_primitive_indecomposable
      S
      mode.period
      mode.period_two_le
      mode.primitive
      mode.indecomposable


/--
A spinorial prime mode has period greater than one.
-/
theorem period_gt_one
    {S : SpinorOrbit.System}
    (mode : PrimeMode S) :

    1 < mode.period := by

  exact
    mode.period_prime.one_lt


/--
A spinorial prime mode has no proper divisor greater than
one.
-/
theorem no_proper_nontrivial_divisor
    {S : SpinorOrbit.System}
    (mode : PrimeMode S)
    (divisor : Nat)
    (hdivisor_two :
      2 ≤ divisor)
    (hdivisor_lt :
      divisor < mode.period) :

    ¬ divisor ∣ mode.period := by

  exact
    (
      Nat.prime_def_lt'.mp
        mode.period_prime
    ).2
      divisor
      hdivisor_two
      hdivisor_lt


end PrimeMode


/-
## The unit spinor double cover
-/

/--
A primitive unit-half double cover has full period two.
-/
theorem unit_half_period_two
    {S : SpinorOrbit.System}
    (halfClosure :
      S.HalfClosure)
    (hunit :
      halfClosure.halfPeriod = 1) :

    halfClosure.fullPeriod = 2 := by

  exact
    PrimitiveRecurrence.fullPeriod_eq_two_of_unit_half
      halfClosure
      hunit

/--
The number two is the prime period generated by a primitive
unit-half spinorial double cover.
-/
theorem unit_half_period_prime
    {S : SpinorOrbit.System}
    (halfClosure :
      S.HalfClosure)
    (hunit :
      halfClosure.halfPeriod = 1) :

    Nat.Prime
      halfClosure.fullPeriod := by

  rw [
    unit_half_period_two
      halfClosure
      hunit
  ]

  exact Nat.prime_two


/-
## Formal boundary
-/

/--
The distinction between primitive recurrence and prime
recurrence is now explicit:

- primitiveness excludes earlier returns;
- indecomposability excludes repeated nontrivial block
  structure;
- together they force arithmetic primality.
-/
theorem spinor_prime_boundary :

    ∀
      (S : SpinorOrbit.System)
      (period : Nat),

      2 ≤ period →

      S.PrimitiveReturn period →

      Indecomposable S period →

      Nat.Prime period := by

  intro S
  intro period
  intro hperiod_two
  intro hprimitive
  intro hindecomposable

  exact
    prime_of_primitive_indecomposable
      S
      period
      hperiod_two
      hprimitive
      hindecomposable


end SpinorIrreducibility
