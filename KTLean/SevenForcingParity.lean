import KTLean.SevenForcingOrbitFiber
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Even Cardinality of the Point Complement

## Formal status

**Level 2 — Consequence of global triadic closure.**

For a fixed point `x`, completion partitions every other point into
two-element orbit fibers. Therefore the complement of `x` has even
cardinality.

No minimality assumption and no cardinality-seven conclusion enters
this module.
-/

namespace SevenForcingParity

noncomputable section

universe u

variable {Point : Type u}
variable [Fintype Point]
variable [DecidableEq Point]

/--
The complement is equivalent to the sigma type of all fibers of the
orbit projection.
-/
def complementEquivSigmaOrbitFibers
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    SevenForcingPairing.PointComplement x ≃
      Sigma (SevenForcingOrbitFiber.OrbitFiber S x) :=

  (
    Equiv.sigmaFiberEquiv
      (SevenForcingOrbit.orbitOf S x)
  ).symm

/--
The cardinality of the complement is twice the number of
completion-orbits.
-/
theorem natCard_complement_eq_two_mul_orbitQuotient
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    Nat.card (SevenForcingPairing.PointComplement x) =
      2 * Nat.card (SevenForcingOrbit.OrbitQuotient S x) := by

  letI :
      Fintype (SevenForcingOrbit.OrbitQuotient S x) :=
    Fintype.ofFinite _

  calc
    Nat.card (SevenForcingPairing.PointComplement x)
        =
      Nat.card
        (Sigma (SevenForcingOrbitFiber.OrbitFiber S x)) :=
      Nat.card_congr
        (complementEquivSigmaOrbitFibers S x)

    _ =
      ∑ q : SevenForcingOrbit.OrbitQuotient S x,
        Nat.card
          (SevenForcingOrbitFiber.OrbitFiber S x q) :=
      Nat.card_sigma

    _ =
      ∑ _q : SevenForcingOrbit.OrbitQuotient S x,
        2 := by
      apply Finset.sum_congr rfl
      intro q _
      exact
        SevenForcingOrbitFiber.natCard_orbitFiber
          S
          x
          q

    _ =
      2 * Nat.card
        (SevenForcingOrbit.OrbitQuotient S x) := by
      simp [
        Nat.card_eq_fintype_card,
        Nat.mul_comm
      ]

/--
The number of points outside any selected point is even.
-/
theorem even_natCard_pointComplement
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    Even
      (Nat.card
        (SevenForcingPairing.PointComplement x)) := by

  refine
    ⟨
      Nat.card
        (SevenForcingOrbit.OrbitQuotient S x),
      ?_
    ⟩

  simpa [two_mul] using
    natCard_complement_eq_two_mul_orbitQuotient
      S
      x

/--
The same parity theorem expressed using `Fintype.card`.
-/
theorem even_card_pointComplement
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point) :
    Even
      (Fintype.card
        (SevenForcingPairing.PointComplement x)) := by

  simpa [Nat.card_eq_fintype_card] using
    even_natCard_pointComplement S x

end

end SevenForcingParity

#check SevenForcingParity.complementEquivSigmaOrbitFibers
#check SevenForcingParity.natCard_complement_eq_two_mul_orbitQuotient
#check SevenForcingParity.even_natCard_pointComplement
#check SevenForcingParity.even_card_pointComplement
