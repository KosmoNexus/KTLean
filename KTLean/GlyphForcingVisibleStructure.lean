import KTLean.GlyphForcingVisibleQuotient

/-!
# Intrinsic Structure of the Visible Glyph Quotient

## Formal status

**Level 2 — Coordinate classification of the intrinsic 21-state
glyph quotient.**

The previous module proved that the visible glyph object is
intrinsically the quotient of the 42-state glyph space by its free
binary deck action.

This module now proves that every quotient point possesses exactly two
recoverable coordinates:

* one forced Fano address;
* one forced visible triadic role.

Thus the quotient is canonically equivalent to

    Fano.Point × ForcedRole,

and its cardinality factors intrinsically as

    21 = 7 × 3.

No orientation coordinate survives the quotient.
-/

namespace GlyphForcingVisibleStructure

open AdmissibleOperation
open GlyphForcingTriadicRole
open GlyphForcingPrimitiveWalk
open GlyphForcingDoubleCover
open GlyphForcingVisibleQuotient

/--
The intrinsic Fano address of one visible-quotient point.
-/
noncomputable def visibleAddress
    (visible : GlyphObservationQuotient) :
    Fano.Point :=

  (
    quotientToVisible
      visible
  ).1

/--
The intrinsic visible triadic role of one quotient point.
-/
noncomputable def visibleRole
    (visible : GlyphObservationQuotient) :
    ForcedRole :=

  (
    quotientToVisible
      visible
  ).2

/--
Construct one intrinsic visible-quotient point from a Fano address and
visible triadic role.
-/
noncomputable def ofAddressRole
    (address : Fano.Point)
    (role : ForcedRole) :
    GlyphObservationQuotient :=

  quotientEquivVisible.symm
    (
      address,
      role
    )

/--
The visible address of a directly constructed quotient point is the
supplied address.
-/
@[simp]
theorem visibleAddress_ofAddressRole
    (address : Fano.Point)
    (role : ForcedRole) :
    visibleAddress
        (ofAddressRole address role) =
      address := by

  unfold visibleAddress
  unfold ofAddressRole

  change
    (
      quotientEquivVisible
        (
          quotientEquivVisible.symm
            (address, role)
        )
    ).1 =
      address

  rw [
    Equiv.apply_symm_apply
  ]

/--
The visible role of a directly constructed quotient point is the
supplied role.
-/
@[simp]
theorem visibleRole_ofAddressRole
    (address : Fano.Point)
    (role : ForcedRole) :
    visibleRole
        (ofAddressRole address role) =
      role := by

  unfold visibleRole
  unfold ofAddressRole

  change
    (
      quotientEquivVisible
        (
          quotientEquivVisible.symm
            (address, role)
        )
    ).2 =
      role

  rw [
    Equiv.apply_symm_apply
  ]

/--
Reconstructing a quotient point from its intrinsic address and role
returns the original point.
-/
@[simp]
theorem ofAddressRole_visibleCoordinates
    (visible : GlyphObservationQuotient) :
    ofAddressRole
        (visibleAddress visible)
        (visibleRole visible) =
      visible := by

  apply
    quotientEquivVisible.injective

  unfold ofAddressRole
  unfold visibleAddress
  unfold visibleRole

  rw [
    Equiv.apply_symm_apply
  ]

  rfl

/--
Two intrinsic visible points are equal when both recoverable
coordinates agree.
-/
theorem ext
    {left right : GlyphObservationQuotient}
    (hAddress :
      visibleAddress left =
        visibleAddress right)
    (hRole :
      visibleRole left =
        visibleRole right) :
    left =
      right := by

  apply
    quotientEquivVisible.injective

  apply Prod.ext

  · exact
      hAddress

  · exact
      hRole

/--
Equality of quotient points forces equality of their Fano addresses.
-/
theorem address_eq_of_eq
    {left right : GlyphObservationQuotient}
    (hEqual :
      left =
        right) :
    visibleAddress left =
      visibleAddress right := by

  exact
    congrArg
      visibleAddress
      hEqual

/--
Equality of quotient points forces equality of their visible roles.
-/
theorem role_eq_of_eq
    {left right : GlyphObservationQuotient}
    (hEqual :
      left =
        right) :
    visibleRole left =
      visibleRole right := by

  exact
    congrArg
      visibleRole
      hEqual

/--
Two intrinsic visible points are equal exactly when both structural
coordinates agree.
-/
theorem eq_iff_coordinates
    (left right : GlyphObservationQuotient) :
    left =
        right
      ↔
    visibleAddress left =
        visibleAddress right
      ∧
    visibleRole left =
        visibleRole right := by

  constructor

  · intro hEqual

    exact
      ⟨
        address_eq_of_eq hEqual,
        role_eq_of_eq hEqual
      ⟩

  · intro hCoordinates

    exact
      ext
        hCoordinates.1
        hCoordinates.2

/--
The intrinsic quotient is canonically equivalent to its address-role
coordinate product.
-/
noncomputable def visibleStructureEquiv :
    GlyphObservationQuotient ≃
      Fano.Point × ForcedRole :=

  quotientEquivVisible

/--
Every intrinsic quotient point possesses one unique address-role
coordinate pair.
-/
theorem existsUnique_coordinates
    (visible : GlyphObservationQuotient) :
    ∃! coordinates : Fano.Point × ForcedRole,
      ofAddressRole
          coordinates.1
          coordinates.2 =
        visible := by

  refine
    ⟨
      (
        visibleAddress visible,
        visibleRole visible
      ),
      ?_,
      ?_
    ⟩

  · exact
      ofAddressRole_visibleCoordinates
        visible

  · intro coordinates hCoordinates

    apply Prod.ext

    · have hAddress :=
        congrArg
          visibleAddress
          hCoordinates

      simpa using
        hAddress

    · have hRole :=
        congrArg
          visibleRole
          hCoordinates

      simpa using
        hRole

/--
The intrinsic quotient cardinality factors as the product of its
forced Fano-address and visible-role carriers.
-/
theorem card_visible_structure_product :
    Fintype.card GlyphObservationQuotient =
      Fintype.card Fano.Point
        *
      Fintype.card ForcedRole := by

  calc
    Fintype.card GlyphObservationQuotient =
        Fintype.card
          (Fano.Point × ForcedRole) := by

      exact
        Fintype.card_congr
          visibleStructureEquiv

    _ =
        Fintype.card Fano.Point
          *
        Fintype.card ForcedRole := by

      exact
        Fintype.card_prod
          Fano.Point
          ForcedRole

/--
The intrinsic quotient contains 21 states because its two forced
coordinate factors contain seven and three states.
-/
theorem card_visible_structure :
    Fintype.card GlyphObservationQuotient =
      7 * 3 := by

  calc
    Fintype.card GlyphObservationQuotient =
        Fintype.card Fano.Point
          *
        Fintype.card ForcedRole := by

      exact
        card_visible_structure_product

    _ =
        7 * 3 := by

      rw [
        AdmissibleOperation.fanoPoint_card,
        card_forcedRole
      ]

/--
No orientation coordinate survives observational quotienting.

Every visible quotient point is determined exactly by one Fano address
and one visible triadic role.
-/
theorem orientation_is_exactly_quotiented_out :
    (∀ visible : GlyphObservationQuotient,
      ofAddressRole
          (visibleAddress visible)
          (visibleRole visible) =
        visible)
      ∧
    (∀ left right : GlyphObservationQuotient,
      left =
          right
        ↔
      visibleAddress left =
          visibleAddress right
        ∧
      visibleRole left =
          visibleRole right) := by

  exact
    ⟨
      ofAddressRole_visibleCoordinates,
      eq_iff_coordinates
    ⟩

/--
Capstone statement.

The intrinsic observational quotient of the 42 glyphs is exactly the
21-state product of seven forced Fano addresses and three forced
visible roles.
-/
theorem visible_quotient_is_seven_times_three :
    Nonempty
      (
        GlyphObservationQuotient ≃
          Fano.Point × ForcedRole
      )
      ∧
    Fintype.card GlyphObservationQuotient =
        7 * 3
      ∧
    Fintype.card GlyphObservationQuotient =
        21 := by

  exact
    ⟨
      ⟨visibleStructureEquiv⟩,
      card_visible_structure,
      card_glyphObservationQuotient
    ⟩

end GlyphForcingVisibleStructure

#check GlyphForcingVisibleStructure.visibleAddress
#check GlyphForcingVisibleStructure.visibleRole
#check GlyphForcingVisibleStructure.ofAddressRole
#check GlyphForcingVisibleStructure.visibleAddress_ofAddressRole
#check GlyphForcingVisibleStructure.visibleRole_ofAddressRole
#check GlyphForcingVisibleStructure.ofAddressRole_visibleCoordinates
#check GlyphForcingVisibleStructure.ext
#check GlyphForcingVisibleStructure.eq_iff_coordinates
#check GlyphForcingVisibleStructure.visibleStructureEquiv
#check GlyphForcingVisibleStructure.existsUnique_coordinates
#check GlyphForcingVisibleStructure.card_visible_structure_product
#check GlyphForcingVisibleStructure.card_visible_structure
#check GlyphForcingVisibleStructure.orientation_is_exactly_quotiented_out
#check GlyphForcingVisibleStructure.visible_quotient_is_seven_times_three
