import KTLean.GlyphForcingFrobeniusIdentification

/-!
# Glyph Forcing Capstone

## Formal status

**Level 2 — Forced finite normal-form classification.**

The preceding modules establish independently:

1. the seven-point Fano carrier is forced by minimal nondegenerate
   global triadic closure;
2. the local woven state has exactly three active roles;
3. those roles possess the intrinsic Frobenius cycle

       1 → 2 → 4 → 1  modulo 7;

4. reversible framing supplies a binary orientation carrier;
5. the resulting 42-state primitive-walk carrier is canonically
   equivalent to the existing glyph implementation;
6. the binary companion action is free and transitive on every
   visible fiber;
7. quotienting by that action produces an intrinsic 21-state object.

This module packages the glyph conclusion.

The 42 glyphs are therefore not introduced by a cardinality
postulate. They are the unique finite normal forms of the forced
Fano-role-orientation carrier.

This capstone deliberately distinguishes:

* **normal-form completeness**, proved here;

from

* **dynamical attraction of arbitrary histories**, which requires a
  later normalization or convergence theorem.
-/

namespace GlyphForcingCapstone

open GlyphForcingTriadicRole
open GlyphForcingOrientation
open GlyphForcingOrientedRole
open GlyphForcingPrimitiveWalk
open GlyphForcingNormalForm
open GlyphForcingDoubleCover
open GlyphForcingDeckAction
open GlyphForcingVisibleQuotient
open GlyphForcingVisibleStructure
open GlyphForcingFrobeniusIdentification

/--
The independently forced primitive-walk carrier contains exactly
42 states.
-/
theorem forced_glyph_carrier_card :
    Fintype.card PrimitiveWalk =
      42 := by

  exact
    card_primitiveWalk

/--
The forced primitive-walk carrier is canonically equivalent to the
existing glyph implementation.
-/
noncomputable def forcedGlyphEquivExisting :
    PrimitiveWalk ≃
      KTGlyph.Glyph :=

  primitiveWalkEquivExistingGlyph

/--
The existing glyph implementation contains exactly 42 states because
it realizes the independently forced primitive-walk carrier.
-/
theorem existing_glyph_card_from_forcing :
    Fintype.card KTGlyph.Glyph =
      42 := by

  exact
    card_existingGlyph_from_forced

/--
Every existing glyph possesses one unique forced primitive-walk
normal form.
-/
theorem every_glyph_has_unique_forced_normalForm
    (glyph : KTGlyph.Glyph) :
    ∃! walk : PrimitiveWalk,
      toExistingGlyph walk =
        glyph := by

  exact
    existsUnique_forced_normalForm
      glyph

/--
The canonical companion transformation on glyphs is involutive and
fixed-point free.
-/
theorem glyph_companion_is_free_involution :
    Function.Involutive companionGlyph
      ∧
    ∀ glyph : KTGlyph.Glyph,
      companionGlyph glyph ≠
        glyph := by

  exact
    ⟨
      companionGlyph_involutive,
      companionGlyph_ne
    ⟩

/--
Every visible glyph fiber is a free and transitive binary torsor.
-/
theorem visible_fibers_are_binary_torsors :
    (∀ glyph sheet,
      deckAct sheet glyph =
          glyph
        →
      sheet = false)
      ∧
    (∀ left right,
      observeGlyph left =
          observeGlyph right
        →
      ∃! sheet,
        deckAct sheet left =
          right) := by

  exact
    glyph_fibers_are_binary_torsors

/--
The intrinsic observational quotient contains exactly 21 states.
-/
theorem intrinsic_visible_quotient_card :
    Fintype.card GlyphObservationQuotient =
      21 := by

  exact
    card_glyphObservationQuotient

/--
The intrinsic quotient is exactly the seven-by-three visible
coordinate product.
-/
noncomputable def visibleQuotientEquivSevenTimesThree :
    GlyphObservationQuotient ≃
      Fano.Point × ForcedRole :=

  visibleStructureEquiv

/--
The intrinsic quotient is also exactly the product of the Fano carrier
with the canonical three-step Frobenius orbit.
-/
noncomputable def visibleQuotientEquivFanoFrobenius :
    GlyphObservationQuotient ≃
      Fano.Point × FrobeniusOrbit.Step :=

  visibleQuotientEquivFrobenius

/--
The forced local role dynamics is the Frobenius cycle.
-/
theorem role_advance_is_frobenius
    (role : ForcedRole) :
    stepOfForcedRole
        (nextRole role) =
      FrobeniusOrbit.next
        (stepOfForcedRole role) := by

  exact
    stepOfForcedRole_nextRole
      role

/--
Numerically, advancing the forced role multiplies its Frobenius value
by two modulo seven.
-/
theorem role_advance_multiplies_by_two
    (role : ForcedRole) :
    (
      stepOfForcedRole
        (nextRole role)
    ).value =
      (
        stepOfForcedRole role
      ).value * 2 := by

  exact
    forcedRole_value_next
      role

/--
The 42-state glyph carrier is a binary framed lift of the intrinsic
21-state visible quotient.
-/
theorem glyphs_are_binary_lift_of_visible_quotient :
    Fintype.card KTGlyph.Glyph =
        42
      ∧
    Fintype.card GlyphObservationQuotient =
        21
      ∧
    Function.Involutive companionGlyph
      ∧
    (∀ glyph,
      companionGlyph glyph ≠ glyph)
      ∧
    (∀ glyph,
      quotientGlyph
          (companionGlyph glyph) =
        quotientGlyph glyph)
      ∧
    (∀ left right,
      quotientGlyph left =
          quotientGlyph right
        ↔
      ∃! sheet : Deck,
        deckAct sheet left =
          right) := by

  exact
    ⟨
      existing_glyph_card_from_forcing,
      intrinsic_visible_quotient_card,
      companionGlyph_involutive,
      companionGlyph_ne,
      quotientGlyph_companionGlyph,
      quotient_eq_iff_unique_deck
    ⟩

/--
The glyph carrier has the forced prime structural decomposition

    42 = 7 × 3 × 2.
-/
theorem glyph_card_forced_factorization :
    Fintype.card KTGlyph.Glyph =
      7 * 3 * 2 := by

  calc
    Fintype.card KTGlyph.Glyph =
        42 := by
      exact
        existing_glyph_card_from_forcing

    _ =
        7 * 3 * 2 := by
      decide

/--
The visible quotient removes exactly the binary framing coordinate,
leaving the seven Fano addresses and three Frobenius roles.
-/
theorem quotient_removes_exactly_framing :
    Nonempty
      (
        GlyphObservationQuotient ≃
          Fano.Point × FrobeniusOrbit.Step
      )
      ∧
    Fintype.card GlyphObservationQuotient =
        21
      ∧
    (∀ glyph,
      quotientGlyph
          (companionGlyph glyph) =
        quotientGlyph glyph) := by

  exact
    ⟨
      ⟨visibleQuotientEquivFanoFrobenius⟩,
      intrinsic_visible_quotient_card,
      quotientGlyph_companionGlyph
    ⟩

/--
Normal-form completeness theorem.

The forced 42-state primitive-walk carrier is equivalent to the
existing glyph implementation, and every glyph has one unique forced
normal form.
-/
theorem glyphs_form_complete_finite_normalForm_basis :
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
        42
      ∧
    (∀ glyph : KTGlyph.Glyph,
      ∃! walk : PrimitiveWalk,
        toExistingGlyph walk =
          glyph) := by

  exact
    ⟨
      ⟨forcedGlyphEquivExisting⟩,
      forced_glyph_carrier_card,
      existing_glyph_card_from_forcing,
      every_glyph_has_unique_forced_normalForm
    ⟩

/--
Glyph forcing capstone.

The forced Fano carrier, Frobenius role dynamics, and binary reversible
framing determine a complete 42-state glyph normal-form basis. Its
intrinsic observational quotient is the 21-state Fano–Frobenius
carrier, and every quotient fiber is a free binary torsor.
-/
theorem glyph_structure_is_forced :
    Nonempty
      (
        PrimitiveWalk ≃
          KTGlyph.Glyph
      )
      ∧
    Fintype.card KTGlyph.Glyph =
        7 * 3 * 2
      ∧
    Nonempty
      (
        GlyphObservationQuotient ≃
          Fano.Point × FrobeniusOrbit.Step
      )
      ∧
    Fintype.card GlyphObservationQuotient =
        7 * 3
      ∧
    (∀ role,
      stepOfForcedRole
          (nextRole role) =
        FrobeniusOrbit.next
          (stepOfForcedRole role))
      ∧
    (∀ left right,
      quotientGlyph left =
          quotientGlyph right
        ↔
      ∃! sheet : Deck,
        deckAct sheet left =
          right) := by

  exact
    ⟨
      ⟨forcedGlyphEquivExisting⟩,
      glyph_card_forced_factorization,
      ⟨visibleQuotientEquivFanoFrobenius⟩,
      card_visible_structure,
      role_advance_is_frobenius,
      quotient_eq_iff_unique_deck
    ⟩

end GlyphForcingCapstone

#check GlyphForcingCapstone.forced_glyph_carrier_card
#check GlyphForcingCapstone.forcedGlyphEquivExisting
#check GlyphForcingCapstone.existing_glyph_card_from_forcing
#check GlyphForcingCapstone.every_glyph_has_unique_forced_normalForm
#check GlyphForcingCapstone.glyph_companion_is_free_involution
#check GlyphForcingCapstone.visible_fibers_are_binary_torsors
#check GlyphForcingCapstone.intrinsic_visible_quotient_card
#check GlyphForcingCapstone.visibleQuotientEquivSevenTimesThree
#check GlyphForcingCapstone.visibleQuotientEquivFanoFrobenius
#check GlyphForcingCapstone.role_advance_is_frobenius
#check GlyphForcingCapstone.role_advance_multiplies_by_two
#check GlyphForcingCapstone.glyphs_are_binary_lift_of_visible_quotient
#check GlyphForcingCapstone.glyph_card_forced_factorization
#check GlyphForcingCapstone.quotient_removes_exactly_framing
#check GlyphForcingCapstone.glyphs_form_complete_finite_normalForm_basis
#check GlyphForcingCapstone.glyph_structure_is_forced
