import KTLean.SevenForcingPairing
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Two-Point Orbits of Complement Completion

## Formal status

**Level 2 — Consequence of global triadic closure.**

For a chosen point `x`, completion by `x` acts on the complement of
`x` as a fixed-point-free involution.

This module defines the corresponding orbit relation:

    y ~ z  iff  z = y or z = complete x y.

Because the action is involutive, this is an equivalence relation.
Because it is fixed-point-free, each equivalence class is intended to
contain exactly two elements.

The exact class-cardinality theorem and the resulting parity theorem
are proved in the next module.
-/

namespace SevenForcingOrbit

universe u

variable {Point : Type u}

/--
The complement involution associated with a chosen point.
-/
abbrev partner
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    SevenForcingPairing.PointComplement x →
      SevenForcingPairing.PointComplement x :=
  SevenForcingPairing.complementCompletion S x

/--
Two complement points belong to the same two-element orbit when one is
either the other point itself or its completion partner.
-/
def OrbitRel
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (y z : SevenForcingPairing.PointComplement x) :
    Prop :=
  z = y ∨ z = partner S x y

/--
Orbit membership is reflexive.
-/
theorem orbitRel_refl
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (y : SevenForcingPairing.PointComplement x) :
    OrbitRel S x y y := by

  exact Or.inl rfl

/--
Orbit membership is symmetric.
-/
theorem orbitRel_symm
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    {y z : SevenForcingPairing.PointComplement x}
    (hyz : OrbitRel S x y z) :
    OrbitRel S x z y := by

  rcases hyz with rfl | hz

  · exact Or.inl rfl

  · right

    have hinvolutive :
        partner S x (partner S x y) = y :=
      SevenForcingPairing.complementCompletion_involutive
        S
        x
        y

    rw [hz]

    exact hinvolutive.symm

/--
Orbit membership is transitive.
-/

theorem orbitRel_trans
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    {y z w : SevenForcingPairing.PointComplement x}
    (hyz : OrbitRel S x y z)
    (hzw : OrbitRel S x z w) :
    OrbitRel S x y w := by

  rcases hyz with rfl | hz

  · exact hzw

  · rcases hzw with rfl | hw

    · exact Or.inr hz

    · left

      calc
        w = partner S x z := hw
        _ = partner S x (partner S x y) := by
              exact congrArg (partner S x) hz
        _ = y := by
              exact
                SevenForcingPairing.complementCompletion_involutive
                  S
                  x
                  y
/--
The two-point orbit relation as a setoid.
-/
def orbitSetoid
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    Setoid (SevenForcingPairing.PointComplement x) where

  r :=
    OrbitRel S x

  iseqv := by
    constructor

    · intro y
      exact orbitRel_refl S x y

    · intro y z hyz
      exact orbitRel_symm S x hyz

    · intro y z w hyz hzw
      exact orbitRel_trans S x hyz hzw

/--
The quotient carrier of complement-completion orbits.
-/
abbrev OrbitQuotient
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :=
  Quotient (orbitSetoid S x)

/--
Send a complement point to its orbit.
-/
def orbitOf
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (y : SevenForcingPairing.PointComplement x) :
    OrbitQuotient S x :=
  Quotient.mk (orbitSetoid S x) y

/--
A point and its completion partner determine the same orbit.
-/
theorem orbitOf_partner
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (y : SevenForcingPairing.PointComplement x) :
    orbitOf S x (partner S x y) =
      orbitOf S x y := by

  apply Quotient.sound

  exact
    orbitRel_symm S x
      (show
        OrbitRel S x y (partner S x y)
       from Or.inr rfl)

/--
Equality of quotient classes is exactly the orbit relation.
-/
theorem orbitOf_eq_iff
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (y z : SevenForcingPairing.PointComplement x) :
    orbitOf S x y = orbitOf S x z ↔
      OrbitRel S x y z := by

  change
    Quotient.mk (orbitSetoid S x) y =
        Quotient.mk (orbitSetoid S x) z
      ↔
    OrbitRel S x y z

  exact Quotient.eq

end SevenForcingOrbit

#check SevenForcingOrbit.partner
#check SevenForcingOrbit.OrbitRel
#check SevenForcingOrbit.orbitSetoid
#check SevenForcingOrbit.OrbitQuotient
#check SevenForcingOrbit.orbitOf
#check SevenForcingOrbit.orbitOf_partner
#check SevenForcingOrbit.orbitOf_eq_iff
