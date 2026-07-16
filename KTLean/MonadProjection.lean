import KTLean.MonadTrivialization

/-!
# Monad projection

A monad lives on the substrate side, before tokenization.

This module formalizes lawful maps from complete monads into
pre-tokenized output spaces.

Scalar physical projections must be invariant under lawful substrate
frame transport. Frame-bearing projections may instead be equivariant
under an explicit action on their codomain.

No dimensional units are introduced here.
-/

namespace KTLean

universe u v w

namespace MonadProjection

variable
  {Frame : Type u}
  [Group Frame]

variable
  (A : MonadAction.FrameAction Frame)

/-!
## Scalar projection
-/

/--
A lawful scalar projection from complete substrate monads into a
pre-tokenized output type.

The projection is required to be invariant under every lawful
substrate-frame transformation.
-/
structure ScalarProjection
    (Output : Type v) where

  project :
    KTMonad.Monad →
      Output

  invariant :
    MonadInvariant.InvariantObservable
      A
      project

namespace ScalarProjection

variable
  {Output : Type v}

variable
  (P : ScalarProjection A Output)

/--
A scalar projection is physically admissible by construction.
-/
theorem physicallyAdmissible :

    MonadInvariant.PhysicallyAdmissible
      A
      P.project := by

  exact P.invariant

/--
A scalar projection is constant on every lawful monad orbit.
-/
theorem constant_on_orbit
    {left right : KTMonad.Monad}
    (horbit :
      MonadOrbit.OrbitEquivalent
        A
        left
        right) :

    P.project left =
      P.project right := by

  exact
    MonadOrbit.invariantObservable_constant_on_orbit
      A
      P.invariant
      horbit

/--
A scalar projection descends canonically to the monad orbit space.
-/
def onOrbitSpace :

    MonadOrbit.OrbitSpace A →
      Output :=

  MonadOrbit.descend
    A
    P.project
    P.invariant

/--
The descended projection agrees with the original projection on every
monad representative.
-/
@[simp]
theorem onOrbitSpace_classOf
    (monad : KTMonad.Monad) :

    P.onOrbitSpace A
        (MonadOrbit.classOf A monad) =
      P.project monad := by

  exact
    MonadOrbit.descend_classOf
      A
      P.project
      P.invariant
      monad

/--
A scalar projection cannot distinguish two monads belonging to the same
lawful substrate-frame orbit.
-/
theorem eq_of_same_orbit_class
    {left right : KTMonad.Monad}
    (hclass :
      MonadOrbit.classOf A left =
        MonadOrbit.classOf A right) :

    P.project left =
      P.project right := by

  have horbit :
      MonadOrbit.OrbitEquivalent
        A
        left
        right :=
    MonadOrbit.orbitEquivalent_of_classOf_eq
      A
      hclass

  exact
    P.constant_on_orbit
      A
      horbit

/-!
## Trivialization independence
-/

/--
Represent the scalar projection in a chosen monad trivialization.
-/
def inCoordinates
    {Coordinates : Type v}
    (T :
      MonadTrivialization.Trivialization
        Coordinates) :

    Coordinates →
      Output :=

  MonadTrivialization.Trivialization.coordinateObservable
    T
    P.project

/--
The coordinate expression of a scalar projection is unchanged under
lawful transport of the trivialization.
-/
theorem inCoordinates_transport
    {Coordinates : Type v}
    (T :
      MonadTrivialization.Trivialization
        Coordinates)
    (frame : Frame)
    (coordinates : Coordinates) :

    inCoordinates
        A
        P
        (T.transport A frame)
        coordinates =
      inCoordinates
        A
        P
        T
        coordinates := by

  exact
    MonadTrivialization.Trivialization.invariant_coordinateObservable_transport
      A
      T
      P.project
      P.invariant
      frame
      coordinates

/-!
## Postprocessing
-/

/--
Deterministic postprocessing of a scalar projection remains a lawful
scalar projection.

This remains pre-tokenized unless the transform itself belongs to a
later tokenization module.
-/
def map
    {NewOutput : Type w}
    (transform :
      Output →
        NewOutput) :

    ScalarProjection A NewOutput where

  project :=
    fun monad =>
      transform
        (P.project monad)

  invariant :=
    MonadInvariant.InvariantObservable.comp
      A
      P.invariant
      transform

@[simp]
theorem map_project
    {NewOutput : Type w}
    (transform :
      Output →
        NewOutput)
    (monad : KTMonad.Monad) :

    (P.map A transform).project monad =
      transform (P.project monad) := by

  rfl

end ScalarProjection

/-!
## Covariant projection
-/

/--
A frame-bearing projection from monads into an output space equipped
with an explicitly declared frame action.

Unlike a scalar projection, the output need not remain numerically
unchanged. It must transform coherently.
-/
structure CovariantProjection
    (Output : Type v) where

  actOutput :
    Frame →
      Output →
        Output

  project :
    KTMonad.Monad →
      Output

  equivariant :
    MonadInvariant.EquivariantObservable
      A
      actOutput
      project

namespace CovariantProjection

variable
  {Output : Type v}

variable
  (P : CovariantProjection A Output)

/--
The defining covariance law for a frame-bearing monad projection.
-/
theorem project_act
    (frame : Frame)
    (monad : KTMonad.Monad) :

    P.project
        (A.act frame monad) =
      P.actOutput frame
        (P.project monad) := by

  exact
    P.equivariant
      frame
      monad

/--
Postcomposition by an intertwining map preserves covariance.
-/
def map
    {NewOutput : Type w}
    (actNew :
      Frame →
        NewOutput →
          NewOutput)
    (transform :
      Output →
        NewOutput)
    (hintertwines :
      ∀
        (frame : Frame)
        (output : Output),
          transform
              (P.actOutput frame output) =
            actNew frame
              (transform output)) :

    CovariantProjection A NewOutput where

  actOutput :=
    actNew

  project :=
    fun monad =>
      transform
        (P.project monad)

  equivariant :=
    MonadInvariant.EquivariantObservable.comp
      A
      P.equivariant
      transform
      hintertwines

end CovariantProjection

/-!
## Scalar projections as covariant projections
-/

/--
Every scalar projection is a covariant projection under the trivial
action on its output space.
-/
def ScalarProjection.toCovariant
    {Output : Type v}
    (P :
      ScalarProjection A Output) :

    CovariantProjection A Output where

  actOutput :=
    fun _frame output =>
      output

  project :=
    P.project

  equivariant :=
    MonadInvariant.InvariantObservable.equivariant_trivial
      A
      P.invariant

/-!
## Identity substrate projection
-/

/--
The identity map on monads is a covariant substrate projection.

It is not a scalar physical projection, because the complete monad
itself transforms under a frame change.
-/
def identityCovariantProjection :

    CovariantProjection
      A
      KTMonad.Monad where

  actOutput :=
    A.act

  project :=
    fun monad =>
      monad

  equivariant :=
    MonadInvariant.equivariantObservable_identity
      A

end MonadProjection

end KTLean
