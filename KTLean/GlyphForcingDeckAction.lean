import KTLean.GlyphForcingDoubleCover

/-!
# The Glyph Deck Action

## Formal status

**Level 2 — Free and transitive binary action on every visible-glyph
fiber.**

The forced glyph space is a two-sheeted cover of the 21-state visible
operation space.

This module strengthens that statement.

The Boolean carrier acts on glyphs by:

    false ↦ identity
    true  ↦ canonical companion.

The action is free: no nontrivial sheet change fixes a glyph.

The action is fiberwise transitive: any two glyphs with the same
visible readout differ by exactly one Boolean sheet transformation.

Therefore each visible-glyph fiber is not merely a two-element set.
It is canonically a torsor for the two-element deck group.
-/

namespace GlyphForcingDeckAction

open GlyphForcingDoubleCover

/--
The two-element deck carrier.
-/
abbrev Deck :=
  Bool

/--
The binary deck action on existing glyphs.

`false` leaves a glyph unchanged.
`true` moves it to its canonical companion.
-/
noncomputable def deckAct
    (sheet : Deck)
    (glyph : KTGlyph.Glyph) :
    KTGlyph.Glyph :=

  if sheet then
    companionGlyph glyph
  else
    glyph

/--
The trivial sheet acts as the identity.
-/
@[simp]
theorem deckAct_false
    (glyph : KTGlyph.Glyph) :
    deckAct false glyph =
      glyph := by

  rfl

/--
The nontrivial sheet acts by the companion transformation.
-/
@[simp]
theorem deckAct_true
    (glyph : KTGlyph.Glyph) :
    deckAct true glyph =
      companionGlyph glyph := by

  rfl

/--
Applying the same deck transformation twice returns the original
glyph.
-/
theorem deckAct_self_inverse
    (sheet : Deck)
    (glyph : KTGlyph.Glyph) :
    deckAct sheet
        (deckAct sheet glyph) =
      glyph := by

  cases sheet

  · rfl

  · exact
      companionGlyph_involutive
        glyph

/--
Every deck transformation preserves the visible glyph readout.
-/
theorem observeGlyph_deckAct
    (sheet : Deck)
    (glyph : KTGlyph.Glyph) :
    observeGlyph
        (deckAct sheet glyph) =
      observeGlyph glyph := by

  cases sheet

  · rfl

  · exact
      observeGlyph_companionGlyph
        glyph

/--
The nontrivial deck transformation fixes no glyph.
-/
theorem deckAct_true_ne
    (glyph : KTGlyph.Glyph) :
    deckAct true glyph ≠
      glyph := by

  exact
    companionGlyph_ne
      glyph

/--
A deck transformation fixes a glyph exactly when it is the trivial
sheet.
-/
theorem deckAct_eq_self_iff
    (sheet : Deck)
    (glyph : KTGlyph.Glyph) :
    deckAct sheet glyph =
        glyph
      ↔
    sheet = false := by

  cases sheet

  · simp

  · constructor

    · intro hFixed

      exact
        False.elim
          (
            deckAct_true_ne glyph
              hFixed
          )

    · intro hImpossible

      cases hImpossible

/--
Two glyphs have the same visible readout exactly when one is obtained
from the other by a deck transformation.
-/
theorem same_observation_iff_exists_deck
    (left right : KTGlyph.Glyph) :
    observeGlyph left =
        observeGlyph right
      ↔
    ∃ sheet : Deck,
      deckAct sheet left =
        right := by

  constructor

  · intro hObserved

    have hClassification :=
      (
        observeGlyph_eq_iff
          left
          right
      ).1
        hObserved

    rcases hClassification with
      hSame | hCompanion

    · exact
        ⟨
          false,
          hSame.symm
        ⟩

    · exact
        ⟨
          true,
          hCompanion.symm
        ⟩

  · intro hDeck

    rcases hDeck with
      ⟨sheet, hSheet⟩

    calc
      observeGlyph left =
          observeGlyph
            (deckAct sheet left) := by
        exact
          (
            observeGlyph_deckAct
              sheet
              left
          ).symm

      _ =
          observeGlyph right := by
        rw [hSheet]

/--
The deck transformation relating two glyphs in the same visible fiber
is unique.
-/
theorem deck_unique
    (left right : KTGlyph.Glyph)
    (hObserved :
      observeGlyph left =
        observeGlyph right) :
    ∃! sheet : Deck,
      deckAct sheet left =
        right := by

  obtain
    ⟨sheet, hSheet⟩ :=
      (
        same_observation_iff_exists_deck
          left
          right
      ).1
        hObserved

  refine
    ⟨
      sheet,
      hSheet,
      ?_
    ⟩

  intro otherSheet hOther

  cases sheet <;>
    cases otherSheet

  · rfl

  · exfalso

    have hCompanionFixed :
        companionGlyph left =
          left := by

      calc
        companionGlyph left =
            right := by
          exact hOther

        _ =
            left := by
          exact hSheet.symm

    exact
      companionGlyph_ne left
        hCompanionFixed

  · exfalso

    have hCompanionFixed :
        companionGlyph left =
          left := by

      calc
        companionGlyph left =
            right := by
          exact hSheet

        _ =
            left := by
          exact hOther.symm

    exact
      companionGlyph_ne left
        hCompanionFixed

  · rfl

/--
Every visible fiber is transitive under the deck action.
-/
theorem fiber_transitive
    (left right : KTGlyph.Glyph)
    (hObserved :
      observeGlyph left =
        observeGlyph right) :
    ∃ sheet : Deck,
      deckAct sheet left =
        right := by

  exact
    (
      same_observation_iff_exists_deck
        left
        right
    ).1
      hObserved

/--
The deck action is free.
-/
theorem deck_action_free :
    ∀ glyph : KTGlyph.Glyph,
      ∀ sheet : Deck,
        deckAct sheet glyph =
            glyph
          →
        sheet = false := by

  intro glyph sheet hFixed

  exact
    (
      deckAct_eq_self_iff
        sheet
        glyph
    ).1
      hFixed

/--
Capstone theorem.

Every visible-glyph fiber is a free and transitive torsor for the
two-element deck carrier.
-/
theorem glyph_fibers_are_binary_torsors :
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
    ⟨
      deck_action_free,
      deck_unique
    ⟩

end GlyphForcingDeckAction

#check GlyphForcingDeckAction.Deck
#check GlyphForcingDeckAction.deckAct
#check GlyphForcingDeckAction.deckAct_self_inverse
#check GlyphForcingDeckAction.observeGlyph_deckAct
#check GlyphForcingDeckAction.deckAct_eq_self_iff
#check GlyphForcingDeckAction.same_observation_iff_exists_deck
#check GlyphForcingDeckAction.deck_unique
#check GlyphForcingDeckAction.fiber_transitive
#check GlyphForcingDeckAction.deck_action_free
#check GlyphForcingDeckAction.glyph_fibers_are_binary_torsors
