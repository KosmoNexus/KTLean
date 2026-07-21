import KTLean.SevenForcingOrbitCardinality

/-!
# Fibers of the Complement-Completion Orbit Quotient

## Formal status

**Level 2 — Consequence of global triadic closure.**

Every quotient class of the fixed-point-free complement involution has
exactly two inhabitants: a chosen representative and its completion
partner.

This module packages that statement as an explicit equivalence

    PUnit ⊕ PUnit ≃ OrbitFiber.

The subsequent parity module will use this equivalence to count all
complement points as a sum of two-element fibers.
-/

namespace SevenForcingOrbitFiber

noncomputable section

universe u

variable {Point : Type u} [DecidableEq Point]

/--
The fiber of the orbit projection over a quotient class.
-/
abbrev OrbitFiber
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (q : SevenForcingOrbit.OrbitQuotient S x) :=
  {
    y : SevenForcingPairing.PointComplement x //
      SevenForcingOrbit.orbitOf S x y = q
  }

/--
The representative selected by `Quotient.out`, regarded as an element
of its own orbit fiber.
-/
def fiberRepresentative
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (q : SevenForcingOrbit.OrbitQuotient S x) :
    OrbitFiber S x q :=

  ⟨
    q.out,
    by
      change
        Quotient.mk (SevenForcingOrbit.orbitSetoid S x) q.out =
          q
      exact Quotient.out_eq q
  ⟩

/--
The completion partner of the selected representative belongs to the
same quotient fiber.
-/
def fiberPartner
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (q : SevenForcingOrbit.OrbitQuotient S x) :
    OrbitFiber S x q :=

  ⟨
    SevenForcingOrbit.partner S x q.out,
    by
      calc
        SevenForcingOrbit.orbitOf S x
            (SevenForcingOrbit.partner S x q.out)
          =
        SevenForcingOrbit.orbitOf S x q.out :=
          SevenForcingOrbit.orbitOf_partner S x q.out

        _ = q := by
          change
            Quotient.mk
                (SevenForcingOrbit.orbitSetoid S x)
                q.out =
              q
          exact Quotient.out_eq q
  ⟩

/--
The representative and its partner are distinct.
-/
theorem fiberRepresentative_ne_partner
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (q : SevenForcingOrbit.OrbitQuotient S x) :
    fiberRepresentative S x q ≠
      fiberPartner S x q := by

  intro h

  have hval :
      q.out =
        SevenForcingOrbit.partner S x q.out := by
    exact congrArg Subtype.val h

  exact
    (Ne.symm
      (SevenForcingOrbitCardinality.partner_ne
        S
        x
        q.out))
      hval
