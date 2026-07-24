import KTLean.GlyphForcingDeckAction

/-!
# The Intrinsic Visible-Glyph Quotient

## Formal status

**Level 2 — Quotient classification of glyphs by visible behavior.**

The forced glyph space contains 42 framed states. A canonical
fixed-point-free binary deck action pairs glyphs having the same
visible readout.

This module no longer treats the 21-state visible carrier merely as a
separately defined target.

Instead, it defines observational equivalence directly on glyphs:

    two glyphs are equivalent exactly when their visible readouts agree.

The quotient of the 42 glyphs by this relation is then proved
canonically equivalent to the 21-state visible carrier.

Thus the 21-state object is intrinsic to the glyph space:

    VisibleGlyph ≃ Glyph / observational equivalence.

The companion transformation becomes invisible precisely because it
lies within one quotient class.
-/

namespace GlyphForcingVisibleQuotient

open GlyphForcingDoubleCover
open GlyphForcingDeckAction

/--
Two glyphs are observationally equivalent when they possess the same
visible readout.
-/
def SameObservation
    (left right : KTGlyph.Glyph) :
    Prop :=

  observeGlyph left =
    observeGlyph right

/--
Observational equivalence is reflexive.
-/
theorem sameObservation_refl
    (glyph : KTGlyph.Glyph) :
    SameObservation glyph glyph := by

  rfl

/--
Observational equivalence is symmetric.
-/
theorem sameObservation_symm
    {left right : KTGlyph.Glyph}
    (hObserved :
      SameObservation left right) :
    SameObservation right left := by

  exact
    hObserved.symm

/--
Observational equivalence is transitive.
-/
theorem sameObservation_trans
    {first second third : KTGlyph.Glyph}
    (hFirst :
      SameObservation first second)
    (hSecond :
      SameObservation second third) :
    SameObservation first third := by

  exact
    hFirst.trans
      hSecond

/--
The visible-readout relation defines a setoid on glyphs.
-/
instance glyphObservationSetoid :
    Setoid KTGlyph.Glyph where

  r :=
    SameObservation

  iseqv :=
    ⟨
      sameObservation_refl,
      sameObservation_symm,
      sameObservation_trans
    ⟩

/--
The intrinsic visible glyph object is the quotient of the full glyph
space by observational equivalence.
-/
abbrev GlyphObservationQuotient :=
  Quotient glyphObservationSetoid

/--
Project one glyph into its intrinsic observational quotient.
-/
def quotientGlyph
    (glyph : KTGlyph.Glyph) :
    GlyphObservationQuotient :=

  Quotient.mk
    glyphObservationSetoid
    glyph

/--
The visible readout descends to the observational quotient.
-/
noncomputable def quotientToVisible :
    GlyphObservationQuotient →
      VisibleGlyph :=

  Quotient.lift
    observeGlyph
    (
      by
        intro left right hObserved
        exact hObserved
    )

/--
The descended quotient map agrees with direct glyph observation.
-/
@[simp]
theorem quotientToVisible_quotientGlyph
    (glyph : KTGlyph.Glyph) :
    quotientToVisible
        (quotientGlyph glyph) =
      observeGlyph glyph := by

  rfl

/--
The quotient-to-visible map is surjective.
-/
theorem quotientToVisible_surjective :
    Function.Surjective
      quotientToVisible := by

  intro visible

  obtain
    ⟨glyph, hGlyph⟩ :=
      observeGlyph_surjective
        visible

  refine
    ⟨
      quotientGlyph glyph,
      ?_
    ⟩

  exact
    hGlyph

/--
The quotient-to-visible map is injective.
-/
theorem quotientToVisible_injective :
    Function.Injective
      quotientToVisible := by

  intro left right hVisible

  induction left using Quotient.inductionOn with
  | _ leftGlyph =>

      induction right using Quotient.inductionOn with
      | _ rightGlyph =>

          apply Quotient.sound

          exact
            hVisible

/--
The intrinsic glyph quotient is canonically equivalent to the
21-state visible carrier.
-/
noncomputable def quotientEquivVisible :
    GlyphObservationQuotient ≃
      VisibleGlyph :=

  Equiv.ofBijective
    quotientToVisible
    ⟨
      quotientToVisible_injective,
      quotientToVisible_surjective
    ⟩

/--
The observational quotient inherits a finite structure from its
canonical equivalence with the visible carrier.
-/
noncomputable instance glyphObservationQuotientFintype :
    Fintype GlyphObservationQuotient :=

  Fintype.ofEquiv
    VisibleGlyph
    quotientEquivVisible.symm

/--
The intrinsic observational quotient contains exactly 21 elements.
-/
theorem card_glyphObservationQuotient :
    Fintype.card GlyphObservationQuotient =
      21 := by

  calc
    Fintype.card GlyphObservationQuotient =
        Fintype.card VisibleGlyph := by

      exact
        Fintype.card_congr
          quotientEquivVisible

    _ =
        21 := by

      exact
        card_visibleGlyph

/--
Two glyphs determine the same quotient point exactly when their
visible readouts agree.
-/
theorem quotientGlyph_eq_iff
    (left right : KTGlyph.Glyph) :
    quotientGlyph left =
        quotientGlyph right
      ↔
    SameObservation left right := by

  constructor

  · intro hQuotient

    have hVisible :=
      congrArg
        quotientToVisible
        hQuotient

    exact
      hVisible

  · intro hObserved

    exact
      Quotient.sound
        hObserved

/--
Every glyph and its canonical companion determine the same intrinsic
visible-quotient point.
-/
theorem quotientGlyph_companionGlyph
    (glyph : KTGlyph.Glyph) :
    quotientGlyph
        (companionGlyph glyph) =
      quotientGlyph
        glyph := by

  exact
    Quotient.sound
      (
        observeGlyph_companionGlyph
          glyph
      )

/--
Every deck transformation acts trivially on the intrinsic visible
quotient.
-/
theorem quotientGlyph_deckAct
    (sheet : Deck)
    (glyph : KTGlyph.Glyph) :
    quotientGlyph
        (deckAct sheet glyph) =
      quotientGlyph
        glyph := by

  apply
    (
      quotientGlyph_eq_iff
        (deckAct sheet glyph)
        glyph
    ).2

  exact
    observeGlyph_deckAct
      sheet
      glyph

/--
Two glyphs represent the same quotient point exactly when one is
obtained from the other by a unique deck transformation.
-/
theorem quotient_eq_iff_unique_deck
    (left right : KTGlyph.Glyph) :
    quotientGlyph left =
        quotientGlyph right
      ↔
    ∃! sheet : Deck,
      deckAct sheet left =
        right := by

  constructor

  · intro hQuotient

    have hObserved :
        observeGlyph left =
          observeGlyph right :=
      (
        quotientGlyph_eq_iff
          left
          right
      ).1
        hQuotient

    exact
      deck_unique
        left
        right
        hObserved

  · intro hDeck

    obtain
      ⟨sheet, hSheet, _⟩ :=
        hDeck

    calc
      quotientGlyph left =
          quotientGlyph
            (deckAct sheet left) := by

        exact
          (
            quotientGlyph_deckAct
              sheet
              left
          ).symm

      _ =
          quotientGlyph right := by

        rw [hSheet]

/--
Capstone theorem.

The 21-state visible glyph object is intrinsically the quotient of the
42-state glyph space by its free binary deck action.
-/
theorem visibleGlyph_is_intrinsic_binary_quotient :
    Fintype.card KTGlyph.Glyph =
        42
      ∧
    Fintype.card GlyphObservationQuotient =
        21
      ∧
    Nonempty
      (
        GlyphObservationQuotient ≃
          VisibleGlyph
      )
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
      GlyphForcingNormalForm.card_existingGlyph_from_forced,
      card_glyphObservationQuotient,
      ⟨quotientEquivVisible⟩,
      quotientGlyph_companionGlyph,
      quotient_eq_iff_unique_deck
    ⟩

end GlyphForcingVisibleQuotient

#check GlyphForcingVisibleQuotient.SameObservation
#check GlyphForcingVisibleQuotient.GlyphObservationQuotient
#check GlyphForcingVisibleQuotient.quotientGlyph
#check GlyphForcingVisibleQuotient.quotientToVisible
#check GlyphForcingVisibleQuotient.quotientEquivVisible
#check GlyphForcingVisibleQuotient.card_glyphObservationQuotient
#check GlyphForcingVisibleQuotient.quotientGlyph_eq_iff
#check GlyphForcingVisibleQuotient.quotientGlyph_companionGlyph
#check GlyphForcingVisibleQuotient.quotientGlyph_deckAct
#check GlyphForcingVisibleQuotient.quotient_eq_iff_unique_deck
#check GlyphForcingVisibleQuotient.visibleGlyph_is_intrinsic_binary_quotient
