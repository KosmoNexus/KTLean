import KTLean.MonadInvariant
import Mathlib.Logic.Relation

/-!
# Monad orbits

A lawful substrate-frame action partitions the complete monad space into
orbits.

Two monads are orbit-equivalent when one is obtained from the other by a
lawful frame transformation. Scalar physical observables must be constant
on these orbits.
-/

namespace KTLean

universe u v

namespace MonadOrbit

variable
  {Frame : Type u}
  [Group Frame]

variable
  (A : MonadAction.FrameAction Frame)

/-!
## Orbit relation
-/

/--
Two monads are orbit-equivalent when a lawful substrate-frame
transformation carries the first monad to the second.
-/
def OrbitEquivalent
    (left right : KTMonad.Monad) :
    Prop :=

  ∃ frame : Frame,
    A.act frame left = right

/--
Every monad lies in its own orbit.
-/
theorem orbitEquivalent_refl
    (monad : KTMonad.Monad) :

    OrbitEquivalent A monad monad := by

  refine ⟨1, ?_⟩

  exact A.one_act monad

/--
Orbit equivalence is symmetric.
-/
theorem orbitEquivalent_symm
    {left right : KTMonad.Monad}
    (h :
      OrbitEquivalent A left right) :

    OrbitEquivalent A right left := by

  rcases h with
    ⟨frame, hframe⟩

  refine
    ⟨frame⁻¹, ?_⟩

  calc
    A.act frame⁻¹ right =
        A.act frame⁻¹
          (A.act frame left) := by
            rw [hframe]

    _ = left := by
          exact
            A.inverse_recovers
              frame
              left

/--
Orbit equivalence is transitive.
-/
theorem orbitEquivalent_trans
    {first second third : KTMonad.Monad}
    (hfirst :
      OrbitEquivalent A first second)
    (hsecond :
      OrbitEquivalent A second third) :

    OrbitEquivalent A first third := by

  rcases hfirst with
    ⟨frame₁, hframe₁⟩

  rcases hsecond with
    ⟨frame₂, hframe₂⟩

  refine
    ⟨frame₂ * frame₁, ?_⟩

  calc
    A.act (frame₂ * frame₁) first =
        A.act frame₂
          (A.act frame₁ first) := by
            exact
              A.mul_act
                frame₂
                frame₁
                first

    _ = A.act frame₂ second := by
          rw [hframe₁]

    _ = third := by
          exact hframe₂

/--
Orbit equivalence is an equivalence relation.
-/
def orbitSetoid :
    Setoid KTMonad.Monad where

  r :=
    OrbitEquivalent A

  iseqv :=
    ⟨
      orbitEquivalent_refl A,
      by
        intro left right h
        exact orbitEquivalent_symm A h,
      by
        intro first second third hfirst hsecond
        exact
          orbitEquivalent_trans
            A
            hfirst
            hsecond
    ⟩

/-!
## Orbit quotient
-/

/--
The quotient of complete monads by lawful substrate-frame transport.
-/
abbrev OrbitSpace :=
  Quotient (orbitSetoid A)

/--
The orbit class of a complete monad.
-/
def classOf
    (monad : KTMonad.Monad) :
    OrbitSpace A :=

  Quotient.mk
    (orbitSetoid A)
    monad

/--
Transporting a monad does not change its orbit class.
-/
theorem classOf_act
    (frame : Frame)
    (monad : KTMonad.Monad) :

    classOf A (A.act frame monad) =
      classOf A monad := by

  apply
    @Quotient.sound
      KTMonad.Monad
      (orbitSetoid A)
      (A.act frame monad)
      monad

  exact
    orbitEquivalent_symm
      A
      ⟨frame, rfl⟩
/--
Orbit-equivalent monads determine the same orbit class.
-/
theorem classOf_eq_of_orbitEquivalent
    {left right : KTMonad.Monad}
    (h :
      OrbitEquivalent A left right) :

    classOf A left =
      classOf A right := by

  exact
    @Quotient.sound
      KTMonad.Monad
      (orbitSetoid A)
      left
      right
      h

/--
Equality of orbit classes implies orbit equivalence.
-/
theorem orbitEquivalent_of_classOf_eq
    {left right : KTMonad.Monad}
    (h :
      classOf A left =
        classOf A right) :

    OrbitEquivalent A left right := by

  exact
    @Quotient.exact
      KTMonad.Monad
      (orbitSetoid A)
      left
      right
      h
/--
Two monads have the same orbit class exactly when they are related by
lawful frame transport.
-/
theorem classOf_eq_iff
    {left right : KTMonad.Monad} :

    classOf A left =
        classOf A right
      ↔
    OrbitEquivalent A left right := by

  constructor

  · intro h
    exact
      orbitEquivalent_of_classOf_eq
        A
        h

  · intro h
    exact
      classOf_eq_of_orbitEquivalent
        A
        h

/-!
## Invariants are constant on orbits
-/

/--
An invariant scalar observable has the same value on orbit-equivalent
monads.
-/
theorem invariantObservable_constant_on_orbit
    {Value : Type v}
    {observable :
      KTMonad.Monad → Value}
    (hinvariant :
      MonadInvariant.InvariantObservable
        A
        observable)
    {left right : KTMonad.Monad}
    (horbit :
      OrbitEquivalent A left right) :

    observable left =
      observable right := by

  rcases horbit with
    ⟨frame, hframe⟩

  calc
    observable left =
        observable (A.act frame left) := by
          exact
            (hinvariant frame left).symm

    _ = observable right := by
          rw [hframe]

/--
An invariant predicate has the same truth value throughout an orbit.
-/
theorem invariantPredicate_constant_on_orbit
    {P : KTMonad.Monad → Prop}
    (hinvariant :
      MonadInvariant.InvariantPredicate
        A
        P)
    {left right : KTMonad.Monad}
    (horbit :
      OrbitEquivalent A left right) :

    P left ↔ P right := by

  rcases horbit with
    ⟨frame, hframe⟩

  calc
    P left ↔
        P (A.act frame left) := by
          exact
            hinvariant frame left

    _ ↔ P right := by
          rw [hframe]

/-!
## Descent to orbit space
-/

/--
Every invariant scalar observable descends canonically to the monad
orbit space.
-/
def descend
    {Value : Type v}
    (observable :
      KTMonad.Monad → Value)
    (hinvariant :
      MonadInvariant.InvariantObservable
        A
        observable) :

    OrbitSpace A →
      Value :=

  Quotient.lift
    observable
    (by
      intro left right horbit

      exact
        invariantObservable_constant_on_orbit
          A
          hinvariant
          horbit)

/--
The descended observable agrees with the original observable on every
representative.
-/
@[simp]
theorem descend_classOf
    {Value : Type v}
    (observable :
      KTMonad.Monad → Value)
    (hinvariant :
      MonadInvariant.InvariantObservable
        A
        observable)
    (monad : KTMonad.Monad) :

    descend A observable hinvariant
        (classOf A monad) =
      observable monad := by

  simp [descend, classOf]

/--
Every physically admissible scalar monad observable factors through the
orbit quotient.
-/
theorem physicallyAdmissible_factors_through_orbit
    {Value : Type v}
    (observable :
      KTMonad.Monad → Value)
    (hadmissible :
      MonadInvariant.PhysicallyAdmissible
        A
        observable) :

    ∃ orbitObservable :
        OrbitSpace A → Value,
      ∀ monad : KTMonad.Monad,
        orbitObservable (classOf A monad) =
          observable monad := by

  refine
    ⟨
      descend A observable hadmissible,
      ?_
    ⟩

  intro monad

  exact
    descend_classOf
      A
      observable
      hadmissible
      monad

/-!
## Orbit membership
-/

/--
The orbit of a monad as a predicate on complete monads.
-/
def InOrbit
    (center candidate : KTMonad.Monad) :
    Prop :=

  OrbitEquivalent A center candidate

/--
The center of an orbit belongs to its own orbit.
-/
theorem center_in_orbit
    (monad : KTMonad.Monad) :

    InOrbit A monad monad := by

  exact
    orbitEquivalent_refl
      A
      monad

/--
Frame transport remains inside the original orbit.
-/
theorem act_in_orbit
    (frame : Frame)
    (monad : KTMonad.Monad) :

    InOrbit A monad
      (A.act frame monad) := by

  exact
    ⟨frame, rfl⟩

end MonadOrbit

end KTLean
