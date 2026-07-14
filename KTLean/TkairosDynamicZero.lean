import KTLean.Tkairos
import KTLean.TkairosLocality

/-!
# Tkairos and the Dynamic Zero

This module formalizes the dynamic zero as the structured
local resolution underlying one concrete Flux Tkairos step.

The dynamic zero is not identified with the literal Flux
state `Flux.zero`.

Instead, it is a transition-bearing object containing:

1. the locally available current state;
2. the locally available context;
3. the successor selected by triadic completion;
4. a proof that the successor is lawful.

The principal factorization is:

    Flux state
        → dynamic-zero event
        → resolved successor

and the resolved successor is exactly the already-defined
fixed-context Flux Tkairos step.

Thus this module introduces no new dynamics. It exposes the
internal triadic structure already present in axiom-derived
Tkairos succession.
-/

namespace TkairosDynamicZero


/--
The finite local information available to one elementary
Flux transition.

A local input contains only:

- the current Flux state;
- the contextual Flux state.

It does not contain a global state of the Kosmoplex.
-/
structure LocalInput where

  state :
    Flux

  context :
    Flux

  deriving DecidableEq, Repr


/--
A dynamic-zero event records one locally constrained
triadic resolution.

The field `successor` is not chosen freely. The proof
`lawful` certifies that it is exactly the third-state
completion determined by the current state and context.
-/
structure Event where

  input :
    LocalInput

  successor :
    Flux

  lawful :
    successor =
      triadicCompletion
        input.state
        input.context


namespace Event


/--
The prior state entering a dynamic-zero event.
-/
def prior
    (event : Event) :
    Flux :=

  event.input.state


/--
The local context carried by a dynamic-zero event.
-/
def context
    (event : Event) :
    Flux :=

  event.input.context


/--
The resolved state leaving a dynamic-zero event.
-/
def resolved
    (event : Event) :
    Flux :=

  event.successor


/--
Every dynamic-zero event resolves according to triadic
completion.
-/
theorem resolved_eq_triadicCompletion
    (event : Event) :

    event.resolved =

      triadicCompletion
        event.prior
        event.context := by

  exact event.lawful


end Event


/--
Enter the dynamic zero from a current Flux state and a
locally available context.

The resulting event carries the lawful successor together
with its proof.
-/
def enter
    (context state : Flux) :
    Event where

  input :=
    {
      state := state
      context := context
    }

  successor :=
    triadicCompletion
      state
      context

  lawful :=
    rfl


/--
Resolve a dynamic-zero event into its successor state.
-/
def resolve
    (event : Event) :
    Flux :=

  event.resolved


@[simp]
theorem enter_prior
    (context state : Flux) :

    (enter context state).prior =
      state := by

  rfl


@[simp]
theorem enter_context
    (context state : Flux) :

    (enter context state).context =
      context := by

  rfl


@[simp]
theorem resolve_enter
    (context state : Flux) :

    resolve
        (enter context state) =

      triadicCompletion
        state
        context := by

  rfl


/--
Resolving the dynamic zero is exactly the established
fixed-context Flux transition.
-/
theorem resolve_enter_eq_fluxStep
    (context state : Flux) :

    resolve
        (enter context state) =

      fluxStep
        context
        state := by

  rfl


/--
Resolving the dynamic zero is exactly one concrete Flux
Tkairos step.
-/
theorem resolve_enter_eq_tkairosStep
    (context state : Flux) :

    resolve
        (enter context state) =

      (Tkairos.System.flux context).step
        state := by

  rfl


/--
The fixed-context Flux Tkairos operation factors through
the dynamic zero.

This is the principal factorization theorem of the module.
-/
theorem tkairos_factors_through_dynamicZero
    (context : Flux) :

    (Tkairos.System.flux context).step =

      fun state =>
        resolve
          (enter context state) := by

  funext state
  rfl


/--
The dynamic-zero construction is total.

Every local Flux state and context determine one event.
-/
theorem dynamicZero_total
    (context state : Flux) :

    ∃ event : Event,

      event.prior = state ∧
      event.context = context ∧
      resolve event =
        fluxStep context state := by

  refine
    ⟨
      enter context state,
      ?_,
      ?_,
      ?_
    ⟩

  · rfl

  · rfl

  · rfl


/--
The event created from a local input has one uniquely
determined resolved successor.
-/
theorem resolved_successor_unique
    (context state : Flux) :

    ∃! successor : Flux,

      successor =
        resolve
          (enter context state) := by

  refine
    ⟨
      resolve (enter context state),
      rfl,
      ?_
    ⟩

  intro successor hsuccessor

  exact hsuccessor


/-
## Diagonal and active resolution
-/

/--
When current state and context agree, dynamic-zero
resolution leaves the state fixed.
-/
@[simp]
theorem resolve_diagonal
    (state : Flux) :

    resolve
        (enter state state) =
      state := by

  exact
    fluxStep_diagonal
      state


/--
When the current state and context are distinct, the
resolved state is neither input.

It is therefore the unique third member of the triflux.
-/
theorem resolve_distinct
    (context state : Flux)
    (hdistinct :
      state ≠ context) :

    resolve
        (enter context state) ≠
        state
      ∧

    resolve
        (enter context state) ≠
        context := by

  exact
    fluxStep_distinct
      state
      context
      hdistinct


/--
A dynamic-zero event is active when its current state and
context are distinct.

Diagonal events are fixed points rather than transitions to
the third Flux state.
-/
def IsActive
    (event : Event) :
    Prop :=

  event.prior ≠
    event.context


/--
An entered event is active exactly when the supplied state
and context are distinct.
-/
@[simp]
theorem enter_isActive_iff
    (context state : Flux) :

    IsActive
        (enter context state) ↔

      state ≠ context := by

  rfl


/--
Every active dynamic-zero event resolves to neither its
prior state nor its context.
-/
theorem active_resolves_to_third
    (event : Event)
    (hactive :
      IsActive event) :

    resolve event ≠
        event.prior
      ∧

    resolve event ≠
        event.context := by

  have hresolve :
      resolve event =
        triadicCompletion
          event.prior
          event.context := by

    exact
      Event.resolved_eq_triadicCompletion
        event

  rw [hresolve]

  exact
    completion_satisfies_axiom6.2
      event.prior
      event.context
      hactive

/-
## Literal zero versus dynamic zero
-/

/--
Opposite Flux poles resolve to the literal zero state.
-/
@[simp]
theorem opposite_poles_resolve_zero_forward :

    resolve
        (enter Flux.pos Flux.neg) =
      Flux.zero := by

  rfl


@[simp]
theorem opposite_poles_resolve_zero_reverse :

    resolve
        (enter Flux.neg Flux.pos) =
      Flux.zero := by

  rfl


/--
The literal zero state and positive context resolve to the
negative pole.
-/
@[simp]
theorem literal_zero_positive_resolves_negative :

    resolve
        (enter Flux.pos Flux.zero) =
      Flux.neg := by

  rfl


/--
The literal zero state and negative context resolve to the
positive pole.
-/
@[simp]
theorem literal_zero_negative_resolves_positive :

    resolve
        (enter Flux.neg Flux.zero) =
      Flux.pos := by

  rfl


/--
The dynamic-zero event is a structured transition object,
not a synonym for the literal Flux constructor `zero`.

This witness exhibits an event whose resolved state is
positive.
-/
theorem dynamicZero_not_always_literal_zero :

    ∃ event : Event,

      resolve event ≠
        Flux.zero := by

  refine
    ⟨
      enter Flux.neg Flux.zero,
      ?_
    ⟩

  decide


/--
Another dynamic-zero event resolves to the negative pole.

Dynamic zero therefore denotes the resolution mechanism,
not one fixed output value.
-/
theorem dynamicZero_has_negative_resolution :

    ∃ event : Event,

      resolve event =
        Flux.neg := by

  exact
    ⟨
      enter Flux.pos Flux.zero,
      rfl
    ⟩


/-
## Dynamic zero along Tkairos history
-/

/--
The dynamic-zero event occurring at stage `n` of a
fixed-context Flux Tkairos history.
-/
def eventAt
    (context initial : Flux)
    (n : Nat) :
    Event :=

  enter
    context
    (
      (Tkairos.System.flux context).history
        initial
        n
    )


/--
The prior state of the event at stage `n` is the state
recorded at that stage of Tkairos history.
-/
@[simp]
theorem eventAt_prior
    (context initial : Flux)
    (n : Nat) :

    (eventAt context initial n).prior =

      (Tkairos.System.flux context).history
        initial
        n := by

  rfl


/--
Resolving the event at stage `n` yields the successor entry
of the Tkairos history.
-/
theorem resolve_eventAt
    (context initial : Flux)
    (n : Nat) :

    resolve
        (eventAt context initial n) =

      (Tkairos.System.flux context).history
        initial
        (Nat.succ n) := by

  rw [
    Tkairos.System.history_succ
  ]

  rfl


/--
Every successor entry in a fixed-context Flux Tkairos
history is produced by one dynamic-zero resolution.
-/
theorem history_successor_exists_as_resolution
    (context initial : Flux)
    (n : Nat) :

    ∃ event : Event,

      event.prior =

          (Tkairos.System.flux context).history
            initial
            n
        ∧

      resolve event =

          (Tkairos.System.flux context).history
            initial
            (Nat.succ n) := by

  refine
    ⟨
      eventAt context initial n,
      ?_,
      ?_
    ⟩

  · rfl

  · exact
      resolve_eventAt
        context
        initial
        n


/--
For fixed-context Flux dynamics, applying the same Tkairos
operation to the resolved successor recovers the prior
state.

Thus the dynamic-zero resolution participates in the
already-proved reversible history.
-/
theorem resolved_event_recovers_prior
    (context initial : Flux)
    (n : Nat) :

    (Tkairos.System.flux context).step
        (
          resolve
            (eventAt context initial n)
        ) =

      (eventAt context initial n).prior := by

  rw [
    resolve_eventAt
  ]

  exact
    Tkairos.System.flux_recovers_previous
      context
      initial
      n


/-
## Locality
-/

/--
The resolution depends only on the finite local input.

Two entered events with identical local inputs have
identical resolved successors.
-/
theorem resolution_local
    (input₁ input₂ : LocalInput)
    (hinput :
      input₁ = input₂) :

    resolve
        (enter input₁.context input₁.state) =

      resolve
        (enter input₂.context input₂.state) := by

  rw [hinput]


/--
The dynamic-zero resolution map on local inputs.
-/
def localResolution :
    LocalInput → Flux :=

  fun input =>
    resolve
      (
        enter
          input.context
          input.state
      )


/--
Local resolution is exactly triadic completion of the
finite local state and context.
-/
theorem localResolution_eq_triadicCompletion
    (input : LocalInput) :

    localResolution input =

      triadicCompletion
        input.state
        input.context := by

  rfl


/--
Local resolution is exactly the corresponding concrete
Flux Tkairos step.
-/
theorem localResolution_eq_tkairosStep
    (input : LocalInput) :

    localResolution input =

      (Tkairos.System.flux input.context).step
        input.state := by

  rfl


/-
## Reversible event package
-/

/--
For a fixed context, dynamic-zero resolution defines a
reversible step because the underlying Flux Tkairos
operation is involutive.
-/
def reversibleResolution
    (context : Flux) :
    ReversibleStep Flux :=

  ReversibleStep.ofInvolution
    (
      fun state =>
        resolve
          (enter context state)
    )
    (
      fun state => by

        change
          fluxStep context
              (fluxStep context state) =
            state

        exact
          fluxStep_involutive
            context
            state
    )


@[simp]
theorem reversibleResolution_step
    (context state : Flux) :

    (reversibleResolution context).step
        state =

      resolve
        (enter context state) := by

  rfl


/--
The reversible event package generates exactly the same
history as fixed-context Flux Tkairos.
-/
theorem reversibleResolution_history
    (context initial : Flux) :

    (reversibleResolution context).history
        initial =

      (Tkairos.System.flux context).history
        initial := by

  rfl


/--
The recovery map of the reversible event package is the
same dynamic-zero resolution map.
-/
@[simp]
theorem reversibleResolution_recover
    (context state : Flux) :

    (reversibleResolution context).recover
        state =

      resolve
        (enter context state) := by

  rfl


/--
Dynamic-zero resolution therefore recovers both forward
and backward state under fixed local context.
-/
theorem dynamicZero_recovery
    (context state : Flux) :

    (reversibleResolution context).recover
        (
          resolve
            (enter context state)
        ) =

      state := by

  exact
    (reversibleResolution context).recover_step
      state


end TkairosDynamicZero


#check TkairosDynamicZero.LocalInput
#check TkairosDynamicZero.Event
#check TkairosDynamicZero.Event.prior
#check TkairosDynamicZero.Event.context
#check TkairosDynamicZero.Event.resolved
#check TkairosDynamicZero.enter
#check TkairosDynamicZero.resolve
#check TkairosDynamicZero.resolve_enter
#check TkairosDynamicZero.resolve_enter_eq_fluxStep
#check TkairosDynamicZero.resolve_enter_eq_tkairosStep
#check TkairosDynamicZero.tkairos_factors_through_dynamicZero
#check TkairosDynamicZero.dynamicZero_total
#check TkairosDynamicZero.resolved_successor_unique
#check TkairosDynamicZero.resolve_diagonal
#check TkairosDynamicZero.resolve_distinct
#check TkairosDynamicZero.IsActive
#check TkairosDynamicZero.active_resolves_to_third
#check TkairosDynamicZero.opposite_poles_resolve_zero_forward
#check TkairosDynamicZero.opposite_poles_resolve_zero_reverse
#check TkairosDynamicZero.dynamicZero_not_always_literal_zero
#check TkairosDynamicZero.eventAt
#check TkairosDynamicZero.resolve_eventAt
#check TkairosDynamicZero.history_successor_exists_as_resolution
#check TkairosDynamicZero.resolved_event_recovers_prior
#check TkairosDynamicZero.localResolution
#check TkairosDynamicZero.localResolution_eq_tkairosStep
#check TkairosDynamicZero.reversibleResolution
#check TkairosDynamicZero.reversibleResolution_history
#check TkairosDynamicZero.dynamicZero_recovery
