import KTLean.Reversibility

/-!
Finite-depth memory recovery in reversible Kosmoplex dynamics.

One-step recovery establishes that the immediately preceding
state can be reconstructed from its successor.

This module extends that result to arbitrary finite depth.
-/

universe u


namespace ReversibleStep


/--
Apply the recovery operation `k` times.

* `recoverN r 0` leaves the state unchanged.
* `recoverN r (k + 1)` performs one recovery and then
  continues recovering through the remaining `k` steps.
-/
def recoverN
    {State : Type u}
    (r : ReversibleStep State) :
    Nat → State → State
  | 0 => fun state => state
  | Nat.succ k =>
      fun state =>
        recoverN r k (r.recover state)


@[simp]
theorem recoverN_zero
    {State : Type u}
    (r : ReversibleStep State)
    (state : State) :
    recoverN r 0 state = state := by
  rfl


@[simp]
theorem recoverN_succ
    {State : Type u}
    (r : ReversibleStep State)
    (k : Nat)
    (state : State) :
    recoverN r (Nat.succ k) state =
      recoverN r k (r.recover state) := by
  rfl


/--
A state located `k` steps after a recorded state can be
returned to that earlier state by applying recovery `k`
times.

This is finite-depth memory escrow.
-/
theorem history_recovers_after
    {State : Type u}
    (r : ReversibleStep State)
    (initial : State)
    (n k : Nat) :
    recoverN r k
        (history r initial (n + k)) =
      history r initial n := by
  induction k with
  | zero =>
      rfl

  | succ k ih =>
      rw [Nat.add_succ]

      change
        recoverN r k
          (r.recover
            (history r initial
              (Nat.succ (n + k)))) =
        history r initial n

      rw [history_recovers_previous]

      exact ih


/--
Recovering from the `k`th recorded state returns the
initial state.
-/
theorem history_recovers_initial
    {State : Type u}
    (r : ReversibleStep State)
    (initial : State)
    (k : Nat) :
    recoverN r k
        (history r initial k) =
      initial := by
  simpa using
    history_recovers_after r initial 0 k


end ReversibleStep


#check ReversibleStep.recoverN
#check ReversibleStep.recoverN_zero
#check ReversibleStep.recoverN_succ
#check ReversibleStep.history_recovers_after
#check ReversibleStep.history_recovers_initial

namespace ReversibleStep


/--
Apply the forward transition `k` times.
-/
def stepN
    {State : Type u}
    (r : ReversibleStep State) :
    Nat → State → State
  | 0 => fun state => state
  | Nat.succ k =>
      fun state =>
        r.step (stepN r k state)


@[simp]
theorem stepN_zero
    {State : Type u}
    (r : ReversibleStep State)
    (state : State) :
    stepN r 0 state = state := by
  rfl


@[simp]
theorem stepN_succ
    {State : Type u}
    (r : ReversibleStep State)
    (k : Nat)
    (state : State) :
    stepN r (Nat.succ k) state =
      r.step (stepN r k state) := by
  rfl


/--
Recovering `k` times after advancing `k` times
returns the original state.
-/
theorem recoverN_stepN
    {State : Type u}
    (r : ReversibleStep State)
    (k : Nat)
    (state : State) :
    recoverN r k (stepN r k state) = state := by
  induction k generalizing state with
  | zero =>
      rfl

  | succ k ih =>
      change
        recoverN r k
          (r.recover
            (r.step (stepN r k state))) =
        state

      rw [r.recover_step]

      exact ih state


/--
Advancing `k` times after recovering `k` times
returns the original state.
-/
theorem stepN_recoverN
    {State : Type u}
    (r : ReversibleStep State)
    (k : Nat)
    (state : State) :
    stepN r k (recoverN r k state) = state := by
  induction k generalizing state with
  | zero =>
      rfl

  | succ k ih =>
      change
        r.step
          (stepN r k
            (recoverN r k
              (r.recover state))) =
        state

      rw [ih]

      exact r.step_recover state


/--
A reversible history is precisely repeated application
of the forward transition to its initial state.
-/
theorem history_eq_stepN
    {State : Type u}
    (r : ReversibleStep State)
    (initial : State)
    (n : Nat) :
    history r initial n =
      stepN r n initial := by
  induction n with
  | zero =>
      rfl

  | succ n ih =>
      rw [history_succ, stepN_succ, ih]


end ReversibleStep


#check ReversibleStep.stepN
#check ReversibleStep.recoverN_stepN
#check ReversibleStep.stepN_recoverN
#check ReversibleStep.history_eq_stepN
