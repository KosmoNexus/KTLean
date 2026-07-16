import KTLean.Glyph
import KTLean.RoutedTokenization
import Mathlib.Data.Fintype.Card

/-!
# Four-State Fibers over KT Glyphs

The glyph modules established a lawful local operation space
with exactly 42 elements:

    Fano address × triadic role × orientation.

This module constructs a candidate dynamical fiber over each
glyph from two binary distinctions already present in the
formal architecture:

1. temporal direction:
      forward / recovered;

2. information phase:
      visible / escrow.

Their product has four elements.

A glyph state therefore has the form

    glyph × temporal direction × information phase.

The total candidate state space has cardinality

    42 × 2 × 2 = 168.

This module does not yet name these states `Monad`.
That name should be introduced only after the four-state
fiber is connected explicitly to lawful Tkairos evolution
and recovery.
-/

namespace GlyphState


/-
## Temporal direction
-/

/--
The two directions present in reversible Tkairos history.

`forward` follows the lawful successor operation.

`recovered` follows the recovery operation toward a prior
state.
-/
inductive TemporalDirection where

  | forward
  | recovered

  deriving
    DecidableEq,
    Repr


/--
Explicit finite enumeration of temporal direction.
-/
instance temporalDirectionFintype :
    Fintype TemporalDirection where

  elems :=
    {
      TemporalDirection.forward,
      TemporalDirection.recovered
    }

  complete := by

    intro direction

    cases direction <;>
      simp


/--
There are exactly two temporal directions.
-/
theorem temporalDirection_card :

    Fintype.card TemporalDirection = 2 := by

  decide


/-
## Information phase
-/

/--
The two information phases exposed by routed Memory
Escrow.

`visible` denotes the locally projected component.

`escrow` denotes the hidden route record required for exact
reconstruction.
-/
inductive InformationPhase where

  | visible
  | escrow

  deriving
    DecidableEq,
    Repr


/--
Explicit finite enumeration of information phase.
-/
instance informationPhaseFintype :
    Fintype InformationPhase where

  elems :=
    {
      InformationPhase.visible,
      InformationPhase.escrow
    }

  complete := by

    intro phase

    cases phase <;>
      simp


/--
There are exactly two information phases.
-/
theorem informationPhase_card :

    Fintype.card InformationPhase = 2 := by

  decide


/-
## Four-state fiber
-/

/--
The candidate dynamical fiber carried by one glyph.
-/
abbrev Fiber :=

  TemporalDirection ×
    InformationPhase


/--
The four canonical fiber states.
-/
def forwardVisible :
    Fiber :=

  (
    TemporalDirection.forward,
    InformationPhase.visible
  )


def forwardEscrow :
    Fiber :=

  (
    TemporalDirection.forward,
    InformationPhase.escrow
  )


def recoveredVisible :
    Fiber :=

  (
    TemporalDirection.recovered,
    InformationPhase.visible
  )


def recoveredEscrow :
    Fiber :=

  (
    TemporalDirection.recovered,
    InformationPhase.escrow
  )


/--
The candidate glyph fiber has exactly four elements.
-/
theorem fiber_card :

    Fintype.card Fiber = 4 := by

  rw [
    Fintype.card_prod,
    temporalDirection_card,
    informationPhase_card
  ]


/--
The forward-visible and forward-escrow states are
distinct.
-/
theorem forwardVisible_ne_forwardEscrow :

    forwardVisible ≠
      forwardEscrow := by

  decide


/--
The forward-visible and recovered-visible states are
distinct.
-/
theorem forwardVisible_ne_recoveredVisible :

    forwardVisible ≠
      recoveredVisible := by

  decide


/--
The recovered-visible and recovered-escrow states are
distinct.
-/
theorem recoveredVisible_ne_recoveredEscrow :

    recoveredVisible ≠
      recoveredEscrow := by

  decide


/--
Every fiber state is one of the four canonical states.
-/
theorem fiber_exhaustive
    (fiber : Fiber) :

    fiber = forwardVisible
      ∨
    fiber = forwardEscrow
      ∨
    fiber = recoveredVisible
      ∨
    fiber = recoveredEscrow := by

  rcases fiber with
    ⟨direction, phase⟩

  cases direction <;>
    cases phase <;>
    simp [
      forwardVisible,
      forwardEscrow,
      recoveredVisible,
      recoveredEscrow
    ]


/-
## Glyph states
-/

/--
One glyph together with one element of its candidate
four-state dynamical fiber.
-/
structure State where

  glyph :
    KTGlyph.Glyph

  direction :
    TemporalDirection

  phase :
    InformationPhase


/--
The product representation of a glyph state.
-/
abbrev StateProduct :=

  KTGlyph.Glyph × Fiber


/--
Convert a glyph state into explicit product form.
-/
def toProduct
    (state : State) :
    StateProduct :=

  (
    state.glyph,
    state.direction,
    state.phase
  )


/--
Construct a glyph state from product-form data.
-/
def ofProduct
    (data : StateProduct) :
    State where

  glyph :=
    data.1

  direction :=
    data.2.1

  phase :=
    data.2.2


/--
Product conversion followed by reconstruction returns the
original glyph state.
-/
@[simp]
theorem ofProduct_toProduct
    (state : State) :

    ofProduct
        (toProduct state) =
      state := by

  cases state

  rfl


/--
Reconstruction followed by product conversion returns the
original product data.
-/
@[simp]
theorem toProduct_ofProduct
    (data : StateProduct) :

    toProduct
        (ofProduct data) =
      data := by

  rcases data with
    ⟨glyph, direction, phase⟩

  rfl


/--
Glyph states are equivalent to glyphs paired with the
four-state fiber.
-/
def stateEquiv :

    State ≃ StateProduct where

  toFun :=
    toProduct

  invFun :=
    ofProduct

  left_inv :=
    ofProduct_toProduct

  right_inv :=
    toProduct_ofProduct


/--
The glyph-state space is finite.
-/
noncomputable instance stateFintype :
    Fintype State :=

  Fintype.ofEquiv
    StateProduct
    stateEquiv.symm


/-
## Structural projections
-/

/--
The temporal direction of a glyph state.
-/
def temporalDirection
    (state : State) :
    TemporalDirection :=

  state.direction


/--
The information phase of a glyph state.
-/
def informationPhase
    (state : State) :
    InformationPhase :=

  state.phase


/--
The fiber coordinate of a glyph state.
-/
def fiber
    (state : State) :
    Fiber :=

  (
    state.direction,
    state.phase
  )


/--
Construct a state over a glyph from one fiber coordinate.
-/
def over
    (glyph : KTGlyph.Glyph)
    (fiber : Fiber) :
    State where

  glyph :=
    glyph

  direction :=
    fiber.1

  phase :=
    fiber.2


@[simp]
theorem over_glyph
    (glyph : KTGlyph.Glyph)
    (fiber : Fiber) :

    (over glyph fiber).glyph =
      glyph := by

  rfl


@[simp]
theorem over_fiber
    (glyph : KTGlyph.Glyph)
    (fiber : Fiber) :

    GlyphState.fiber
        (over glyph fiber) =
      fiber := by

  rcases fiber with
    ⟨direction, phase⟩

  rfl


/-
## Equality and independence
-/

/--
Two glyph states are equal when their glyph and both fiber
coordinates agree.
-/
theorem State.ext
    {left right : State}
    (hglyph :
      left.glyph =
        right.glyph)
    (hdirection :
      left.direction =
        right.direction)
    (hphase :
      left.phase =
        right.phase) :

    left = right := by

  cases left

  cases right

  cases hglyph
  cases hdirection
  cases hphase

  rfl


/--
Changing temporal direction changes the glyph state.
-/
theorem ne_of_direction_ne
    {left right : State}
    (hdirection :
      left.direction ≠
        right.direction) :

    left ≠ right := by

  intro hstate

  exact
    hdirection
      (
        congrArg State.direction
          hstate
      )


/--
Changing information phase changes the glyph state.
-/
theorem ne_of_phase_ne
    {left right : State}
    (hphase :
      left.phase ≠
        right.phase) :

    left ≠ right := by

  intro hstate

  exact
    hphase
      (
        congrArg State.phase
          hstate
      )


/--
Changing the underlying glyph changes the glyph state.
-/
theorem ne_of_glyph_ne
    {left right : State}
    (hglyph :
      left.glyph ≠
        right.glyph) :

    left ≠ right := by

  intro hstate

  exact
    hglyph
      (
        congrArg State.glyph
          hstate
      )


/-
## The fiber over one fixed glyph
-/

/--
The subtype of all glyph states lying over one fixed glyph.
-/
abbrev StatesOver
    (glyph : KTGlyph.Glyph) :=

  {
    state : State //
      state.glyph = glyph
  }


/--
The states over one fixed glyph are equivalent to the
four-state fiber.
-/
def statesOverEquiv
    (glyph : KTGlyph.Glyph) :

    StatesOver glyph ≃ Fiber where

  toFun :=
    fun state =>
      fiber state.1

  invFun :=
    fun fiberState =>
      ⟨
        over glyph fiberState,
        rfl
      ⟩

  left_inv := by

    intro state

    rcases state with
      ⟨
        ⟨stateGlyph, direction, phase⟩,
        hglyph
      ⟩

    dsimp at hglyph

    subst stateGlyph

    rfl

  right_inv := by

    intro fiberState

    rcases fiberState with
      ⟨direction, phase⟩

    rfl


/--
The fiber over each glyph is finite.
-/
noncomputable instance statesOverFintype
    (glyph : KTGlyph.Glyph) :

    Fintype (StatesOver glyph) :=

  Fintype.ofEquiv
    Fiber
    (statesOverEquiv glyph).symm


/--
Every individual glyph carries exactly four candidate
dynamical states.
-/
theorem states_over_glyph_card
    (glyph : KTGlyph.Glyph) :

    Fintype.card
        (StatesOver glyph) =
      4 := by

  rw [
    Fintype.card_congr
      (statesOverEquiv glyph)
  ]

  exact fiber_card


/-
## Total cardinality
-/

/--
The total glyph-state space contains exactly 168 elements.
-/
theorem state_card :

    Fintype.card State = 168 := by

  rw [
    Fintype.card_congr stateEquiv,
    Fintype.card_prod,
    KTGlyph.card_glyph,
    fiber_card
  ]


/--
The total state count factors as 42 glyphs, two temporal
directions, and two information phases.
-/
theorem state_card_factorization :

    Fintype.card State =
      42 * 2 * 2 := by

  calc

    Fintype.card State =
        168 :=

      state_card

    _ =
        42 * 2 * 2 := by

      decide


/--
The prime factorization of the total candidate state space
is inherited from the glyph structure and the two binary
fiber coordinates.
-/
theorem state_card_prime_structure :

    Fintype.card State =
      7 * 3 * 2 * 2 * 2 := by

  calc

    Fintype.card State =
        168 :=

      state_card

    _ =
        7 * 3 * 2 * 2 * 2 := by

      decide


end GlyphState
