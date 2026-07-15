import KTLean.SpinorOrbit

/-!
# Primitive Spinorial Recurrence

`SpinorOrbit` established the double-cover mechanism:

    base --halfPeriod--> deck base
    deck base --halfPeriod--> base.

This module develops the arithmetic of return times.

The main results are:

1. a return period may be repeated any finite number of
   times;

2. a primitive return period divides every other return
   time;

3. a primitive return period is unique;

4. primitive dynamical recurrence does not, by itself,
   imply arithmetic primality.

The final point is demonstrated by an explicit spinorial
four-cycle whose primitive return period is four.

Thus an additional irreducibility condition is required to
derive number-theoretic primes from spinorial recurrence.
-/

namespace PrimitiveRecurrence


open SpinorOrbit
open SpinorOrbit.System


/-
## Repeated return periods
-/

/--
If `n` is a return period, then advancing by `q * n`
returns to the base for every natural number `q`.
-/
theorem advance_mul_period
    (S : SpinorOrbit.System)
    (n : Nat)
    (hreturn :
      S.ReturnsAt n) :

    ∀ q : Nat,

      SpinorOrbit.advance
          S.step
          (q * n)
          S.base =

        S.base := by

  intro q

  induction q with

  | zero =>
      simp

  | succ q ih =>

      rw [Nat.succ_mul]

      rw [
        SpinorOrbit.advance_add
      ]

      rw [ih]

      exact hreturn


/--
Every natural multiple of a return period is itself a
return period.
-/
theorem returnsAt_mul
    (S : SpinorOrbit.System)
    (n q : Nat)
    (hreturn :
      S.ReturnsAt n) :

    S.ReturnsAt
      (q * n) := by

  unfold SpinorOrbit.System.ReturnsAt
  unfold SpinorOrbit.System.stateAt

  exact
    advance_mul_period
      S
      n
      hreturn
      q


/--
The sum of two return periods is a return period.
-/
theorem returnsAt_add
    (S : SpinorOrbit.System)
    (n m : Nat)
    (hn :
      S.ReturnsAt n)
    (hm :
      S.ReturnsAt m) :

    S.ReturnsAt
      (n + m) := by

  unfold SpinorOrbit.System.ReturnsAt at *

  unfold SpinorOrbit.System.stateAt at *

  rw [
    SpinorOrbit.advance_add,
    hn,
    hm
  ]


/-
## Return-time decomposition
-/

/--
If `n` is a return period and

    m = q * n + r,

then a return at time `m` forces a return at time `r`.
-/
theorem remainder_returns_of_decomposition
    (S : SpinorOrbit.System)
    (n m q r : Nat)
    (hn :
      S.ReturnsAt n)
    (hm :
      S.ReturnsAt m)
    (hdecomposition :
      m = q * n + r) :

    S.ReturnsAt r := by

  unfold SpinorOrbit.System.ReturnsAt at *

  unfold SpinorOrbit.System.stateAt at *

  rw [hdecomposition] at hm

  rw [
    SpinorOrbit.advance_add
  ] at hm

  have hmultiple :

      SpinorOrbit.advance
          S.step
          (q * n)
          S.base =

        S.base :=

    advance_mul_period
      S
      n
      hn
      q

  rw [hmultiple] at hm

  exact hm


/--
For a positive period `n`, every return time has a
returning remainder modulo `n`.
-/
theorem modulo_remainder_returns
    (S : SpinorOrbit.System)
    (n m : Nat)
    (hn :
      S.ReturnsAt n)
    (hm :
      S.ReturnsAt m) :

    S.ReturnsAt
      (m % n) := by

  have hdivision :
      m =
        (m / n) * n +
          (m % n) := by

    simpa [Nat.mul_comm] using
      (Nat.div_add_mod m n).symm

  exact
    remainder_returns_of_decomposition
      S
      n
      m
      (m / n)
      (m % n)
      hn
      hm
      hdivision



/-
## Primitive periods divide all returns
-/

/--
The remainder of any return time modulo a primitive return
period is zero.
-/
theorem mod_eq_zero_of_primitive_return
    (S : SpinorOrbit.System)
    (n m : Nat)
    (hprimitive :
      S.PrimitiveReturn n)
    (hm :
      S.ReturnsAt m) :

    m % n = 0 := by

  have hn_positive :
      0 < n :=

    hprimitive.positive

  have hremainder :

      S.ReturnsAt
        (m % n) :=

    modulo_remainder_returns
      S
      n
      m

      hprimitive.returns
      hm

  by_contra hnonzero

  have hremainder_positive :
      0 < m % n :=

    Nat.pos_of_ne_zero
      hnonzero

  have hremainder_less :
      m % n < n :=

    Nat.mod_lt
      m
      hn_positive

  exact
    hprimitive.no_earlier_return
      hremainder_positive
      hremainder_less
      hremainder


/--
A primitive return period divides every other return time.
-/
theorem primitive_period_dvd_return
    (S : SpinorOrbit.System)
    (n m : Nat)
    (hprimitive :
      S.PrimitiveReturn n)
    (hm :
      S.ReturnsAt m) :

    n ∣ m := by

  have hmod :
      m % n = 0 :=

    mod_eq_zero_of_primitive_return
      S
      n
      m
      hprimitive
      hm

  refine
    ⟨
      m / n,
      ?_
    ⟩

  have hdivision :
      m =
        n * (m / n) +
          (m % n) :=

    (Nat.div_add_mod m n).symm

  rw [
    hmod,
    Nat.add_zero
  ] at hdivision

  exact hdivision


/--
Every positive return time is at least as large as a
primitive return period.
-/
theorem primitive_period_le_return
    (S : SpinorOrbit.System)
    (n m : Nat)
    (hprimitive :
      S.PrimitiveReturn n)
    (hm_positive :
      0 < m)
    (hm :
      S.ReturnsAt m) :

    n ≤ m := by

  exact
    Nat.le_of_dvd
      hm_positive
      (
        primitive_period_dvd_return
          S
          n
          m
          hprimitive
          hm
      )


/--
Two primitive return periods of the same spinor system are
equal.
-/
theorem primitive_period_unique
    (S : SpinorOrbit.System)
    (n m : Nat)
    (hn :
      S.PrimitiveReturn n)
    (hm :
      S.PrimitiveReturn m) :

    n = m := by

  apply Nat.le_antisymm

  · exact
      primitive_period_le_return
        S
        n
        m
        hn
        hm.positive
        hm.returns

  · exact
      primitive_period_le_return
        S
        m
        n
        hm
        hn.positive
        hn.returns


/--
A primitive period is the unique least positive return
time.
-/
theorem primitive_is_least_positive_return
    (S : SpinorOrbit.System)
    (n : Nat)
    (hprimitive :
      S.PrimitiveReturn n) :

    S.ReturnsAt n
      ∧

    0 < n
      ∧

    ∀ m : Nat,

      S.ReturnsAt m →

      0 < m →

      n ≤ m := by

  exact
    ⟨
      hprimitive.returns,
      hprimitive.positive,
      fun m hm hm_positive =>

        primitive_period_le_return
          S
          n
          m
          hprimitive
          hm_positive
          hm
    ⟩


/-
## Arithmetic factorization
-/

/--
A natural number has a nontrivial factorization when it is
the product of two numbers strictly greater than one.
-/
def HasNontrivialFactorization
    (n : Nat) :
    Prop :=

  ∃ a b : Nat,

    1 < a
      ∧

    1 < b
      ∧

    n = a * b


/--
A natural number is arithmetically irreducible when it has
no nontrivial factorization.
-/
def ArithmeticallyIrreducible
    (n : Nat) :
    Prop :=

  ¬ HasNontrivialFactorization n


/--
The number two is arithmetically irreducible.
-/
theorem two_arithmetically_irreducible :

    ArithmeticallyIrreducible 2 := by

  unfold ArithmeticallyIrreducible
  unfold HasNontrivialFactorization

  intro hfactorization

  rcases hfactorization with
    ⟨a, b, ha, hb, hab⟩

  have ha_two :
      2 ≤ a := by
    omega

  have hb_two :
      2 ≤ b := by
    omega

  have hproduct :
      4 ≤ a * b := by

    exact
      Nat.mul_le_mul
        ha_two
        hb_two

  rw [← hab] at hproduct

  omega


/-
## Double-cover arithmetic
-/

/--
A unit half-period produces full period two.
-/
theorem fullPeriod_eq_two_of_unit_half
    {S : SpinorOrbit.System}
    (H :
      S.HalfClosure)
    (hunit :
      H.halfPeriod = 1) :

    H.fullPeriod = 2 := by

  rw [
    H.fullPeriod_eq_two_mul,
    hunit
  ]


/--
A spinor double-cover with unit half-period has an
arithmetically irreducible full period.
-/
theorem unit_half_fullPeriod_irreducible
    {S : SpinorOrbit.System}
    (H :
      S.HalfClosure)
    (hunit :
      H.halfPeriod = 1) :

    ArithmeticallyIrreducible
      H.fullPeriod := by

  rw [
    fullPeriod_eq_two_of_unit_half
      H
      hunit
  ]

  exact
    two_arithmetically_irreducible


/--
Every half-period greater than one gives the full period a
nontrivial factorization:

    fullPeriod = 2 × halfPeriod.
-/
theorem fullPeriod_factorization_of_nonunit_half
    {S : SpinorOrbit.System}
    (H :
      S.HalfClosure)
    (hnonunit :
      1 < H.halfPeriod) :

    HasNontrivialFactorization
      H.fullPeriod := by

  refine
    ⟨
      2,
      H.halfPeriod,
      by decide,
      hnonunit,
      ?_
    ⟩

  exact
    H.fullPeriod_eq_two_mul


/--
The double-cover full period is arithmetically irreducible
when the half-period is one, while every larger half-period
produces a composite full period.
-/
theorem double_cover_arithmetic_dichotomy
    {S : SpinorOrbit.System}
    (H :
      S.HalfClosure) :

    (
      H.halfPeriod = 1
        ∧
      ArithmeticallyIrreducible
        H.fullPeriod
    )

    ∨

    (
      1 < H.halfPeriod
        ∧
      HasNontrivialFactorization
        H.fullPeriod
    ) := by

  have hpositive :
      0 < H.halfPeriod :=

    H.positive

  by_cases hunit :
      H.halfPeriod = 1

  · exact
      Or.inl
        ⟨
          hunit,
          unit_half_fullPeriod_irreducible
            H
            hunit
        ⟩

  · have hgreater :
        1 < H.halfPeriod := by

      omega

    exact
      Or.inr
        ⟨
          hgreater,
          fullPeriod_factorization_of_nonunit_half
            H
            hgreater
        ⟩


/-
## A composite primitive recurrence
-/

/--
A concrete four-state spinorial cycle.

The deck transformation advances by two positions, while
the lawful step advances by one.
-/
def fourCycle :
    SpinorOrbit.System where

  State :=
    Fin 4

  step :=
    fun state =>
      state + 1

  base :=
    0

  deck :=
    fun state =>
      state + 2

  deck_involutive := by

    intro state

    fin_cases state <;>
      rfl

  base_ne_deck := by

    decide

  step_deck_commute := by

    intro state

    fin_cases state <;>
      rfl


/--
The four-cycle returns after four steps.
-/
theorem fourCycle_returns_four :

    fourCycle.ReturnsAt 4 := by

  change
    SpinorOrbit.advance
        (fun state : Fin 4 => state + 1)
        4
        0 =
      0

  decide


/--
The four-cycle has no positive return before four.
-/
theorem fourCycle_no_earlier_return :

    ∀ m : Nat,

      0 < m →

      m < 4 →

      ¬ fourCycle.ReturnsAt m := by

  intro m hm_positive hm_less

  interval_cases m <;>

    simp [
      SpinorOrbit.System.ReturnsAt,
      SpinorOrbit.System.stateAt,
      SpinorOrbit.advance,
      fourCycle
    ]


/--
Four is the primitive return period of the concrete
spinorial four-cycle.
-/
theorem fourCycle_primitive_four :

    fourCycle.PrimitiveReturn 4 := by

  exact
    ⟨
      fourCycle_returns_four,
      by decide,
      fourCycle_no_earlier_return
    ⟩


/--
The primitive period four has a nontrivial arithmetic
factorization.
-/
theorem four_has_nontrivial_factorization :

    HasNontrivialFactorization 4 := by

  exact
    ⟨
      2,
      2,
      by decide,
      by decide,
      by decide
    ⟩


/--
Primitive dynamical recurrence does not imply arithmetic
irreducibility.

The concrete four-cycle has primitive period four, while
four factors nontrivially as two times two.
-/
theorem primitive_recurrence_not_sufficient_for_primality :

    ∃ S : SpinorOrbit.System.{0},

      S.PrimitiveReturn 4
        ∧

      HasNontrivialFactorization 4 := by

  exact
    ⟨
      fourCycle,
      fourCycle_primitive_four,
      four_has_nontrivial_factorization
    ⟩


/-
## Formal conclusion
-/

/--
The current recurrence theory establishes both:

1. primitive periods divide all return times;
2. primitive recurrence alone does not force arithmetic
   primality.

The missing ingredient must therefore be a stronger
spinorial irreducibility law.
-/
theorem recurrence_boundary :

    (
      ∀
        (S : SpinorOrbit.System.{0})
        (n m : Nat),

        S.PrimitiveReturn n →

        S.ReturnsAt m →

        n ∣ m
    )

    ∧

    (
      ∃ S : SpinorOrbit.System.{0},

        S.PrimitiveReturn 4
          ∧

        HasNontrivialFactorization 4
    ) := by

  constructor

  · intro S n m hprimitive hm

    exact
      primitive_period_dvd_return
        S
        n
        m
        hprimitive
        hm

  · exact
      primitive_recurrence_not_sufficient_for_primality


end PrimitiveRecurrence
