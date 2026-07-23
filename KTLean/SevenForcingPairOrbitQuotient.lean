import KTLean.SevenForcingPairOrbitEquivalence
import KTLean.SevenForcingPairOrbitCardinality

/-!
# Quotient Classes of Rotation–Reversal Pair Orbits

## Formal status

**Level 2 — Consequence of global triadic closure.**

Rotation–reversal reachability defines an equivalence relation on the
carrier of distinct ordered pairs. This module forms the quotient by
that relation and identifies the fiber over the class of a selected
seed with the previously defined generated pair orbit.

Consequently, every quotient fiber over a represented class has natural
cardinality six.

No minimality assumption and no cardinality-seven conclusion enters
this module.
-/

namespace SevenForcingPairOrbitQuotient

noncomputable section

universe u

variable {Point : Type u}

open SevenForcingDistinctPairs
open SevenForcingPairOrbit
open SevenForcingPairOrbitEquivalence
open SevenForcingPairOrbitCardinality

/--
The quotient carrier of distinct ordered pairs modulo rotation and
reversal.
-/
def PairOrbitQuotient
    (S : SevenForcing.GlobalTriadicClosure Point) :=
  Quotient (pairOrbitSetoid S)

/--
The quotient class represented by a distinct ordered pair.
-/
def pairOrbitClass
    (S : SevenForcing.GlobalTriadicClosure Point)
    (pair : DistinctPair (Point := Point)) :
    PairOrbitQuotient S :=
  Quotient.mk
    (pairOrbitSetoid S)
    pair

/--
The fiber of the quotient map over a selected quotient class.
-/
def PairOrbitFiber
    (S : SevenForcing.GlobalTriadicClosure Point)
    (orbitClass : PairOrbitQuotient S) :=
  {
    pair : DistinctPair (Point := Point) //
      pairOrbitClass S pair = orbitClass
  }

/--
An element reachable from a seed lies in the quotient fiber over the
seed's class.
-/
def pairOrbitToFiber
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    PairOrbit S seed →
      PairOrbitFiber S (pairOrbitClass S seed)

  | ⟨pair, hpair⟩ =>
      ⟨
        pair,
        by
          exact
            (
              Quotient.sound
                hpair
            ).symm
      ⟩

/--
An element of the quotient fiber over a seed's class is reachable from
that seed.
-/
def fiberToPairOrbit
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    PairOrbitFiber S (pairOrbitClass S seed) →
      PairOrbit S seed

  | ⟨pair, hclass⟩ =>
      ⟨
        pair,
        by
          exact
            Quotient.exact
              hclass.symm
      ⟩

/--
The generated pair orbit of a seed is equivalent to the quotient fiber
over the seed's class.
-/
def pairOrbitEquivFiber
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    PairOrbit S seed ≃
      PairOrbitFiber S (pairOrbitClass S seed) where

  toFun :=
    pairOrbitToFiber S seed

  invFun :=
    fiberToPairOrbit S seed

  left_inv := by
    intro pair

    apply Subtype.ext
    rfl

  right_inv := by
    intro pair

    apply Subtype.ext
    rfl

/--
The quotient fiber over the class represented by any distinct ordered
pair has natural cardinality six.
-/
theorem natCard_pairOrbitFiber
    (S : SevenForcing.GlobalTriadicClosure Point)
    (seed : DistinctPair (Point := Point)) :
    Nat.card
        (
          PairOrbitFiber
            S
            (pairOrbitClass S seed)
        ) =
      6 := by

  calc
    Nat.card
        (
          PairOrbitFiber
            S
            (pairOrbitClass S seed)
        ) =
        Nat.card (PairOrbit S seed) := by
      exact
        Nat.card_congr
          (pairOrbitEquivFiber S seed).symm

    _ = 6 :=
      natCard_pairOrbit S seed

end

end SevenForcingPairOrbitQuotient

#check SevenForcingPairOrbitQuotient.PairOrbitQuotient
#check SevenForcingPairOrbitQuotient.pairOrbitClass
#check SevenForcingPairOrbitQuotient.PairOrbitFiber
#check SevenForcingPairOrbitQuotient.pairOrbitToFiber
#check SevenForcingPairOrbitQuotient.fiberToPairOrbit
#check SevenForcingPairOrbitQuotient.pairOrbitEquivFiber
#check SevenForcingPairOrbitQuotient.natCard_pairOrbitFiber
