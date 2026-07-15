import KTLean.Monad

/-!
# Spinor Orbits and Double-Cover Closure

This module begins the prime-generating layer of KT.

The earlier development used factors of size two, three,
and seven in finite normal forms. Here we begin to derive
such factors from recurrence structure instead of merely
counting coordinate types.

A spinor orbit contains:

1. a state space;
2. a lawful step;
3. a base state;
4. an involutive deck transformation;
5. a proof that the base state differs from its deck
   partner;
6. compatibility of the step with the deck action.

A half-closure reaches the deck partner after `n` steps.

The central result proves that two such traversals return
to the original state:

    base --n--> deck base --n--> base.

Thus the binary factor arises from the double-cover
geometry itself.
-/

universe u

namespace SpinorOrbit


/-
## Iterated evolution
-/

/--
Apply a state transition `n` times.
-/
def advance
    {State : Type u}
    (step : State → State) :
    Nat → State → State

  | 0, state =>
      state

  | Nat.succ n, state =>
      step
        (advance step n state)


@[simp]
theorem advance_zero
    {State : Type u}
    (step : State → State)
    (state : State) :

    advance step 0 state =
      state := by

  rfl


@[simp]
theorem advance_succ
    {State : Type u}
    (step : State → State)
    (n : Nat)
    (state : State) :

    advance step (Nat.succ n) state =

      step
        (advance step n state) := by

  rfl


/--
Advancing by `n + m` is equivalent to first advancing by
`n` and then by `m`.
-/
theorem advance_add
    {State : Type u}
    (step : State → State)
    (n m : Nat)
    (state : State) :

    advance step (n + m) state =

      advance step m
        (advance step n state) := by

  induction m with

  | zero =>
      simp

  | succ m ih =>

      rw [Nat.add_succ]

      change
        step
          (advance step (n + m) state) =
        step
          (
            advance step m
              (advance step n state)
          )

      rw [ih]


/-
## Spinor system
-/

/--
A spinor system with an involutive deck transformation.

The deck transformation represents the distinction between
a spinor state and its partner under one projected
rotation.
-/
structure System where

  State :
    Type u

  step :
    State → State

  base :
    State

  deck :
    State → State

  deck_involutive :
    Function.Involutive deck

  base_ne_deck :
    base ≠ deck base

  step_deck_commute :
    ∀ state : State,

      step (deck state) =
        deck (step state)


namespace System


/--
The state reached after `n` spinor steps from the base.
-/
def stateAt
    (S : System) :
    Nat → S.State :=

  fun n =>
    advance S.step n S.base


/--
The orbit returns at time `n` when the evolved state is
the original base state.
-/
def ReturnsAt
    (S : System)
    (n : Nat) :
    Prop :=

  S.stateAt n =
    S.base


/--
The orbit reaches its deck partner at time `n`.
-/
def ReachesDeckAt
    (S : System)
    (n : Nat) :
    Prop :=

  S.stateAt n =
    S.deck S.base


/--
Every orbit returns at time zero.
-/
@[simp]
theorem returnsAt_zero
    (S : System) :

    S.ReturnsAt 0 := by

  rfl


/--
Iterated evolution commutes with the deck transformation.
-/
theorem advance_deck_commute
    (S : System)
    (n : Nat)
    (state : S.State) :

    advance S.step n
        (S.deck state) =

      S.deck
        (advance S.step n state) := by

  induction n with

  | zero =>
      rfl

  | succ n ih =>

      change
        S.step
          (
            advance S.step n
              (S.deck state)
          ) =

        S.deck
          (
            S.step
              (advance S.step n state)
          )

      rw [ih]

      exact
        S.step_deck_commute
          (
            advance S.step n state
          )


/-
## Half-closure
-/

/--
A spinorial half-closure reaches the deck partner after a
positive number of steps.
-/
structure HalfClosure
    (S : System) where

  halfPeriod :
    Nat

  positive :
    0 < halfPeriod

  reaches_deck :
    S.ReachesDeckAt halfPeriod


namespace HalfClosure


/--
A half-period cannot already be a return to the base state.
-/
theorem not_returns_at_half
    {S : System}
    (H : HalfClosure S) :

    ¬ S.ReturnsAt H.halfPeriod := by

  intro hreturn

  have hdeck :
      S.base =
        S.deck S.base := by

    calc

      S.base =
          S.stateAt H.halfPeriod :=

        hreturn.symm

      _ =
          S.deck S.base :=

        H.reaches_deck

  exact
    S.base_ne_deck
      hdeck


/--
Two half-period traversals return to the original state.

This is the formal double-cover closure theorem.
-/
theorem returns_at_double
    {S : System}
    (H : HalfClosure S) :

    S.ReturnsAt
      (H.halfPeriod + H.halfPeriod) := by

  unfold System.ReturnsAt
  unfold System.stateAt

  rw [
    advance_add
  ]

  have hhalf :
      advance S.step H.halfPeriod S.base =
        S.deck S.base :=

    H.reaches_deck

  rw [hhalf]

  rw [
    S.advance_deck_commute
  ]

  rw [hhalf]

  exact
    S.deck_involutive
      S.base


/--
The full spinorial return time associated with a
half-closure.
-/
def fullPeriod
    {S : System}
    (H : HalfClosure S) :
    Nat :=

  H.halfPeriod +
    H.halfPeriod


/--
The full period is twice the half-period.
-/
theorem fullPeriod_eq_two_mul
    {S : System}
    (H : HalfClosure S) :

    H.fullPeriod =
      2 * H.halfPeriod := by

  unfold fullPeriod

  exact
    (two_mul H.halfPeriod).symm


/--
The full spinorial period is positive.
-/
theorem fullPeriod_positive
    {S : System}
    (H : HalfClosure S) :

    0 < H.fullPeriod := by

  rw [
    H.fullPeriod_eq_two_mul
  ]

  exact
    Nat.mul_pos
      (by decide)
      H.positive


/--
Every half-closure supplies a lawful positive full return.
-/
theorem fullPeriod_returns
    {S : System}
    (H : HalfClosure S) :

    S.ReturnsAt H.fullPeriod := by

  exact
    H.returns_at_double


end HalfClosure


/-
## Primitive recurrence
-/

/--
A positive return is primitive when no smaller positive
time is also a return.
-/
def PrimitiveReturn
    (S : System)
    (n : Nat) :
    Prop :=

  S.ReturnsAt n
    ∧

  0 < n
    ∧

  ∀ m : Nat,

    0 < m →

    m < n →

    ¬ S.ReturnsAt m


/--
A primitive return is necessarily positive.
-/
theorem PrimitiveReturn.positive
    {S : System}
    {n : Nat}
    (hprimitive :
      S.PrimitiveReturn n) :

    0 < n := by

  exact
    hprimitive.2.1


/--
A primitive return is a genuine return.
-/
theorem PrimitiveReturn.returns
    {S : System}
    {n : Nat}
    (hprimitive :
      S.PrimitiveReturn n) :

    S.ReturnsAt n := by

  exact
    hprimitive.1


/--
A primitive return has no smaller positive return time.
-/
theorem PrimitiveReturn.no_earlier_return
    {S : System}
    {n m : Nat}
    (hprimitive :
      S.PrimitiveReturn n)
    (hm_positive :
      0 < m)
    (hm_less :
      m < n) :

    ¬ S.ReturnsAt m := by

  exact
    hprimitive.2.2
      m
      hm_positive
      hm_less


/-
## Spinorial conclusion
-/

/--
A spinor half-closure exhibits a strict distinction between
half-return and full return:

- the half-period reaches the deck partner but not the base;
- the doubled period returns to the base.
-/
theorem double_cover_separation
    {S : System}
    (H : HalfClosure S) :

    S.ReachesDeckAt H.halfPeriod
      ∧

    ¬ S.ReturnsAt H.halfPeriod
      ∧

    S.ReturnsAt H.fullPeriod := by

  exact
    ⟨
      H.reaches_deck,
      H.not_returns_at_half,
      H.fullPeriod_returns
    ⟩


end System

end SpinorOrbit
