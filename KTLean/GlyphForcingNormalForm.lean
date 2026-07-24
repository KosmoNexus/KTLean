import KTLean.GlyphForcingPrimitiveWalk
import KTLean.Glyph

/-!
# Forced Glyph Normal Form

## Formal status

**Level 2 — Canonical identification of the forced primitive-walk
carrier with the existing glyph coordinate implementation.**

The preceding forcing modules derived, independently of the existing
glyph definition:

* seven Fano addresses;
* three local roles;
* two reversible orientations;
* a 42-state primitive framed-walk carrier;
* a canonical fixed-point-free companion involution;
* a two-to-one observable projection onto 21 visible walks.

This module now identifies that forced carrier with the pre-existing
glyph coordinate type.

The identification is componentwise:

    forced Fano address       ↦ existing Fano address
    forced triadic role       ↦ existing TriadicRole
    forced orientation        ↦ existing Orientation

No new multiplicity is introduced here.
-/

namespace GlyphForcingNormalForm

open AdmissibleOperation
open GlyphForcingTriadicRole
open GlyphForcingOrientation
open GlyphForcingOrientedRole
open GlyphForcingPrimitiveWalk

/--
Convert one forced primitive walk into the existing glyph coordinate
representation.
-/
def toExistingCoordinates
    (walk : PrimitiveWalk) :
    AdmissibleOperation.Operation where

  address :=
    walk.1

  role :=
    toExistingRole
      walk.2.1

  orientation :=
    toExistingOrientation
      walk.2.2

/--
Recover the forced primitive walk represented by an existing glyph
coordinate triple.
-/
def fromExistingCoordinates
    (coordinates : AdmissibleOperation.Operation) :
    PrimitiveWalk :=

  (
    coordinates.address,
    (
      fromExistingRole
        coordinates.role,
      fromExistingOrientation
        coordinates.orientation
    )
  )

/--
Recovering a forced primitive walk after converting it to existing
coordinates returns the original walk.
-/
@[simp]
theorem fromExistingCoordinates_toExistingCoordinates
    (walk : PrimitiveWalk) :
    fromExistingCoordinates
        (toExistingCoordinates walk) =
      walk := by

  rcases walk with
    ⟨address, role, orientation⟩

  simp [
    toExistingCoordinates,
    fromExistingCoordinates
  ]

/--
Converting recovered forced coordinates returns the original existing
coordinate triple.
-/
@[simp]
theorem toExistingCoordinates_fromExistingCoordinates
    (coordinates : AdmissibleOperation.Operation) :
    toExistingCoordinates
        (fromExistingCoordinates coordinates) =
      coordinates := by

  cases coordinates with
  | mk address role orientation =>

      simp [
        toExistingCoordinates,
        fromExistingCoordinates
      ]

/--
The forced primitive-walk carrier is canonically equivalent to the
existing glyph coordinate implementation.
-/
def primitiveWalkEquivExistingCoordinates :
    PrimitiveWalk ≃
      AdmissibleOperation.Operation where

  toFun :=
    toExistingCoordinates

  invFun :=
    fromExistingCoordinates

  left_inv :=
    fromExistingCoordinates_toExistingCoordinates

  right_inv :=
    toExistingCoordinates_fromExistingCoordinates

/--
The forward normal-form map is injective.
-/
theorem toExistingCoordinates_injective :
    Function.Injective
      toExistingCoordinates := by

  exact
    primitiveWalkEquivExistingCoordinates.injective

/--
Every existing coordinate triple is represented by one forced
primitive walk.
-/
theorem toExistingCoordinates_surjective :
    Function.Surjective
      toExistingCoordinates := by

  exact
    primitiveWalkEquivExistingCoordinates.surjective

/--
Every existing coordinate triple has one unique forced primitive-walk
normal form.
-/
theorem existsUnique_primitiveWalk
    (coordinates : AdmissibleOperation.Operation) :
    ∃! walk : PrimitiveWalk,
      toExistingCoordinates walk =
        coordinates := by

  refine
    ⟨
      fromExistingCoordinates coordinates,
      ?_,
      ?_
    ⟩

  · exact
      toExistingCoordinates_fromExistingCoordinates
        coordinates

  · intro otherWalk hOther

    exact
      toExistingCoordinates_injective
        (
          hOther.trans
            (
              toExistingCoordinates_fromExistingCoordinates
                coordinates
            ).symm
        )

/--
Construct the existing glyph represented by a forced primitive walk.
-/
def toExistingGlyph
    (walk : PrimitiveWalk) :
    KTGlyph.Glyph :=

  KTGlyph.ofCoordinates
    (
      toExistingCoordinates
        walk
    )

/--
Recover the forced primitive walk represented by an existing glyph.
-/
noncomputable def fromExistingGlyph
    (glyph : KTGlyph.Glyph) :
    PrimitiveWalk :=

  fromExistingCoordinates
    (
      KTGlyph.coordinates
        glyph
    )

/--
Recovering a forced walk from its constructed glyph returns the
original walk.
-/
@[simp]
theorem fromExistingGlyph_toExistingGlyph
    (walk : PrimitiveWalk) :
    fromExistingGlyph
        (toExistingGlyph walk) =
      walk := by

  unfold fromExistingGlyph
  unfold toExistingGlyph

  rw [
    KTGlyph.coordinates_ofCoordinates
  ]

  exact
    fromExistingCoordinates_toExistingCoordinates
      walk

/--
Constructing a glyph from its recovered forced walk returns the
original glyph.
-/
@[simp]
theorem toExistingGlyph_fromExistingGlyph
    (glyph : KTGlyph.Glyph) :
    toExistingGlyph
        (fromExistingGlyph glyph) =
      glyph := by

  unfold fromExistingGlyph
  unfold toExistingGlyph

  rw [
    toExistingCoordinates_fromExistingCoordinates
  ]

  exact
    KTGlyph.ofCoordinates_coordinates
      glyph

/--
The forced primitive-walk carrier is canonically equivalent to the
existing glyph implementation.
-/
noncomputable def primitiveWalkEquivExistingGlyph :
    PrimitiveWalk ≃
      KTGlyph.Glyph where

  toFun :=
    toExistingGlyph

  invFun :=
    fromExistingGlyph

  left_inv :=
    fromExistingGlyph_toExistingGlyph

  right_inv :=
    toExistingGlyph_fromExistingGlyph

/--
The existing glyph space has 42 elements because it is equivalent to
the independently derived primitive-walk carrier.
-/
theorem card_existingGlyph_from_forced :
    Fintype.card KTGlyph.Glyph =
      42 := by

  calc
    Fintype.card KTGlyph.Glyph =
        Fintype.card PrimitiveWalk := by
      exact
        Fintype.card_congr
          primitiveWalkEquivExistingGlyph.symm

    _ =
        42 := by
      exact
        card_primitiveWalk

/--
Every existing glyph has one unique forced primitive-walk normal form.
-/
theorem existsUnique_forced_normalForm
    (glyph : KTGlyph.Glyph) :
    ∃! walk : PrimitiveWalk,
      toExistingGlyph walk =
        glyph := by

  refine
    ⟨
      fromExistingGlyph glyph,
      ?_,
      ?_
    ⟩

  · exact
      toExistingGlyph_fromExistingGlyph
        glyph

  · intro otherWalk hOther

    exact
      primitiveWalkEquivExistingGlyph.injective
        (
          hOther.trans
            (
              toExistingGlyph_fromExistingGlyph
                glyph
            ).symm
        )

/--
Capstone normal-form statement.

The independently forced 42-state primitive-walk carrier and the
existing glyph implementation are canonically equivalent.
-/
theorem forced_normalForm_identifies_existing_glyphs :
    Nonempty
      (
        PrimitiveWalk ≃
          KTGlyph.Glyph
      )
      ∧
    Fintype.card PrimitiveWalk =
        42
      ∧
    Fintype.card KTGlyph.Glyph =
        42 := by

  exact
    ⟨
      ⟨primitiveWalkEquivExistingGlyph⟩,
      card_primitiveWalk,
      card_existingGlyph_from_forced
    ⟩

end GlyphForcingNormalForm

#check GlyphForcingNormalForm.toExistingCoordinates
#check GlyphForcingNormalForm.fromExistingCoordinates
#check GlyphForcingNormalForm.primitiveWalkEquivExistingCoordinates
#check GlyphForcingNormalForm.toExistingCoordinates_injective
#check GlyphForcingNormalForm.toExistingCoordinates_surjective
#check GlyphForcingNormalForm.existsUnique_primitiveWalk
#check GlyphForcingNormalForm.toExistingGlyph
#check GlyphForcingNormalForm.fromExistingGlyph
#check GlyphForcingNormalForm.primitiveWalkEquivExistingGlyph
#check GlyphForcingNormalForm.card_existingGlyph_from_forced
#check GlyphForcingNormalForm.existsUnique_forced_normalForm
#check GlyphForcingNormalForm.forced_normalForm_identifies_existing_glyphs
