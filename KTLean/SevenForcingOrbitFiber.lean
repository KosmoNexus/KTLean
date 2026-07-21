import KTLean.SevenForcingOrbitCardinality

/-!
# Fibers of the Complement-Completion Orbit Quotient

## Formal status

**Level 2 — Consequence of global triadic closure.**

Every quotient class of the fixed-point-free complement involution has
exactly two inhabitants:

1. a selected representative;
2. its completion partner.

The result is packaged as an explicit equivalence

    Bool ≃ OrbitFiber.

The subsequent parity module may therefore count the complement as a
sum of two-element fibers.
-/

namespace SevenForcingOrbitFiber

noncomputable section

universe u

variable {Point : Type u}
variable [DecidableEq Point]

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
        Quotient.mk
            (SevenForcingOrbit.orbitSetoid S x)
            q.out =
          q

      exact Quotient.out_eq q
  ⟩

/--
The completion partner of the selected representative belongs to the
same orbit fiber.
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
          SevenForcingOrbit.orbitOf_partner
            S
            x
            q.out

        _ = q := by
          change
            Quotient.mk
                (SevenForcingOrbit.orbitSetoid S x)
                q.out =
              q

          exact Quotient.out_eq q
  ⟩

/--
The selected representative and its completion partner are distinct.
-/
theorem fiberRepresentative_ne_partner
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (q : SevenForcingOrbit.OrbitQuotient S x) :
    fiberRepresentative S x q ≠
      fiberPartner S x q := by

  intro h

  have hvalues :
      q.out =
        SevenForcingOrbit.partner S x q.out :=
    congrArg Subtype.val h

  have hdistinct :
      q.out ≠
        SevenForcingOrbit.partner S x q.out :=
    Ne.symm
      (SevenForcingOrbitCardinality.partner_ne
        S
        x
        q.out)

  exact hdistinct hvalues

/--
Every member of an orbit fiber is either the selected representative
or its completion partner.
-/
theorem fiber_eq_representative_or_partner
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (q : SevenForcingOrbit.OrbitQuotient S x)
    (z : OrbitFiber S x q) :
    z = fiberRepresentative S x q ∨
      z = fiberPartner S x q := by

  have hrepresentative :
      SevenForcingOrbit.orbitOf S x q.out = q := by

    change
      Quotient.mk
          (SevenForcingOrbit.orbitSetoid S x)
          q.out =
        q

    exact Quotient.out_eq q

  have hsameOrbit :
      SevenForcingOrbit.orbitOf S x q.out =
        SevenForcingOrbit.orbitOf S x z.1 :=
    hrepresentative.trans z.2.symm

  have hrelation :
      SevenForcingOrbit.OrbitRel S x q.out z.1 :=
    (
      SevenForcingOrbit.orbitOf_eq_iff
        S
        x
        q.out
        z.1
    ).1 hsameOrbit

  rcases hrelation with hrepresentativeValue | hpartnerValue

  · left
    apply Subtype.ext
    exact hrepresentativeValue

  · right
    apply Subtype.ext
    exact hpartnerValue

/--
The canonical map from the two-element Boolean type into an orbit
fiber.

`false` selects the representative and `true` selects its partner.
-/
def fiberFromBool
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (q : SevenForcingOrbit.OrbitQuotient S x) :
    Bool → OrbitFiber S x q
  | false =>
      fiberRepresentative S x q
  | true =>
      fiberPartner S x q

/--
The canonical Boolean map into an orbit fiber is injective.
-/
theorem fiberFromBool_injective
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (q : SevenForcingOrbit.OrbitQuotient S x) :
    Function.Injective
      (fiberFromBool S x q) := by

  intro left right h

  cases left <;> cases right

  · rfl

  · exact
      False.elim
        (
          fiberRepresentative_ne_partner S x q
            h
        )

  · exact
      False.elim
        (
          fiberRepresentative_ne_partner S x q
            h.symm
        )

  · rfl

/--
The canonical Boolean map into an orbit fiber is surjective.
-/
theorem fiberFromBool_surjective
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (q : SevenForcingOrbit.OrbitQuotient S x) :
    Function.Surjective
      (fiberFromBool S x q) := by

  intro z

  rcases
    fiber_eq_representative_or_partner
      S
      x
      q
      z
    with hrepresentative | hpartner

  · refine ⟨false, ?_⟩
    exact hrepresentative.symm

  · refine ⟨true, ?_⟩
    exact hpartner.symm

/--
Each orbit fiber is explicitly equivalent to `Bool`.
-/
def boolEquivOrbitFiber
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (q : SevenForcingOrbit.OrbitQuotient S x) :
    Bool ≃ OrbitFiber S x q :=

  Equiv.ofBijective
    (fiberFromBool S x q)
    ⟨
      fiberFromBool_injective S x q,
      fiberFromBool_surjective S x q
    ⟩

/--
Every complement-completion orbit fiber has cardinality two.
-/
theorem natCard_orbitFiber
    (S : SevenForcing.GlobalTriadicClosure Point)
    (x : Point)
    (q : SevenForcingOrbit.OrbitQuotient S x) :
    Nat.card (OrbitFiber S x q) = 2 := by

  calc
    Nat.card (OrbitFiber S x q) =
        Nat.card Bool :=
      Nat.card_congr
        (boolEquivOrbitFiber S x q).symm

    _ = 2 := by
      simp [Nat.card_eq_fintype_card]

end

end SevenForcingOrbitFiber

#check SevenForcingOrbitFiber.OrbitFiber
#check SevenForcingOrbitFiber.fiberRepresentative
#check SevenForcingOrbitFiber.fiberPartner
#check SevenForcingOrbitFiber.fiberRepresentative_ne_partner
#check SevenForcingOrbitFiber.fiber_eq_representative_or_partner
#check SevenForcingOrbitFiber.fiberFromBool
#check SevenForcingOrbitFiber.fiberFromBool_injective
#check SevenForcingOrbitFiber.fiberFromBool_surjective
#check SevenForcingOrbitFiber.boolEquivOrbitFiber
#check SevenForcingOrbitFiber.natCard_orbitFiber
