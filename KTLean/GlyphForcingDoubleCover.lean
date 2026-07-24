import KTLean.GlyphForcingNormalForm

/-!
# The Existing Glyph Space as a Double Cover

## Formal status

**Level 2 — Transport of the forced double-cover structure to the
existing glyph implementation.**

The independently derived primitive-walk carrier possesses:

* 42 framed states;
* a fixed-point-free companion involution;
* a 21-state observable quotient;
* exactly two framed states over each observable state.

The previous module established a canonical equivalence between that
carrier and the existing glyph implementation.

This module transports the double-cover structure across that
equivalence.

Consequently, the existing glyph space is not merely a 42-element
set. It is canonically a two-sheeted cover of a 21-element visible
operation space.
-/

namespace GlyphForcingDoubleCover

open GlyphForcingTriadicRole
open GlyphForcingOrientation
open GlyphForcingOrientedRole
open GlyphForcingPrimitiveWalk
open GlyphForcingNormalForm

/--
The visible readout of an existing glyph.
-/
abbrev VisibleGlyph :=
  VisibleWalk

/--
Recover the forced primitive walk represented by a glyph and forget
its hidden frame.
-/
noncomputable def observeGlyph
    (glyph : KTGlyph.Glyph) :
    VisibleGlyph :=

  observe
    (
      fromExistingGlyph
        glyph
    )

/--
The canonical hidden companion of an existing glyph.
-/
noncomputable def companionGlyph
    (glyph : KTGlyph.Glyph) :
    KTGlyph.Glyph :=

  toExistingGlyph
    (
      GlyphForcingPrimitiveWalk.companion
        (
          fromExistingGlyph
            glyph
        )
    )

/--
Taking the companion glyph twice returns the original glyph.
-/
theorem companionGlyph_involutive :
    Function.Involutive
      companionGlyph := by

  intro glyph

  unfold companionGlyph

  rw [
    fromExistingGlyph_toExistingGlyph
  ]

  rw [
    GlyphForcingPrimitiveWalk.companion_involutive
  ]

  exact
    toExistingGlyph_fromExistingGlyph
      glyph

/--
No glyph is equal to its canonical companion.
-/
theorem companionGlyph_ne
    (glyph : KTGlyph.Glyph) :
    companionGlyph glyph ≠
      glyph := by

  intro hEqual

  have hWalk :
      GlyphForcingPrimitiveWalk.companion
          (fromExistingGlyph glyph) =
        fromExistingGlyph glyph := by

    have h :=
      congrArg
        fromExistingGlyph
        hEqual

    simpa [
      companionGlyph
    ] using h

  exact
    GlyphForcingPrimitiveWalk.companion_ne
      (fromExistingGlyph glyph)
      hWalk

/--
A glyph and its companion have the same visible readout.
-/
theorem observeGlyph_companionGlyph
    (glyph : KTGlyph.Glyph) :
    observeGlyph
        (companionGlyph glyph) =
      observeGlyph
        glyph := by

  unfold observeGlyph
  unfold companionGlyph

  rw [
    fromExistingGlyph_toExistingGlyph
  ]

  exact
    observe_companion
      (
        fromExistingGlyph
          glyph
      )

/--
Two glyphs have equal visible readout exactly when they are equal or
canonical companions.
-/
theorem observeGlyph_eq_iff
    (left right : KTGlyph.Glyph) :
    observeGlyph left =
        observeGlyph right
      ↔
    right = left
      ∨
    right = companionGlyph left := by

  constructor

  · intro hObserved

    have hWalks :
        observe
            (fromExistingGlyph left) =
          observe
            (fromExistingGlyph right) := by
      exact hObserved

    have hClassification :=
      (
        observe_eq_iff
          (fromExistingGlyph left)
          (fromExistingGlyph right)
      ).1
        hWalks

    rcases hClassification with
      hSame | hCompanion

    · left

      have hGlyphs :=
        congrArg
          toExistingGlyph
          hSame

      simpa using hGlyphs

    · right

      have hGlyphs :=
        congrArg
          toExistingGlyph
          hCompanion

      simpa [
        companionGlyph
      ] using hGlyphs

  · intro hGlyphs

    rcases hGlyphs with
      hSame | hCompanion

    · subst right
      rfl

    · subst right

      exact
        (
          observeGlyph_companionGlyph
            left
        ).symm

/--
The glyph observable is surjective onto the 21-state visible carrier.
-/
theorem observeGlyph_surjective :
    Function.Surjective
      observeGlyph := by

  intro visible

  obtain ⟨walk, hWalk⟩ :=
    observe_surjective
      visible

  refine
    ⟨
      toExistingGlyph walk,
      ?_
    ⟩

  unfold observeGlyph

  rw [
    fromExistingGlyph_toExistingGlyph
  ]

  exact
    hWalk

/--
The glyph observable is not injective.
-/
theorem observeGlyph_not_injective :
    ¬ Function.Injective
        observeGlyph := by

  intro hInjective

  let glyph : KTGlyph.Glyph :=
    toExistingGlyph
      (
        0,
        (
          0,
          ForcedOrientation.forward
        )
      )

  have hObserved :
      observeGlyph
          (companionGlyph glyph) =
        observeGlyph glyph :=
    observeGlyph_companionGlyph
      glyph

  have hGlyph :
      companionGlyph glyph =
        glyph :=
    hInjective
      hObserved

  exact
    companionGlyph_ne glyph
      hGlyph

/--
Every visible glyph state has two distinct glyph realizations.
-/
theorem every_visibleGlyph_has_two_glyphs
    (visible : VisibleGlyph) :
    ∃ first second : KTGlyph.Glyph,
      first ≠ second
        ∧
      observeGlyph first =
        visible
        ∧
      observeGlyph second =
        visible := by

  obtain
    ⟨
      firstWalk,
      secondWalk,
      hDistinct,
      hFirst,
      hSecond
    ⟩ :=
      every_visibleWalk_has_two_frames
        visible

  refine
    ⟨
      toExistingGlyph firstWalk,
      toExistingGlyph secondWalk,
      ?_,
      ?_,
      ?_
    ⟩

  · intro hEqual

    have hWalks :=
      congrArg
        fromExistingGlyph
        hEqual

    simp only [
      fromExistingGlyph_toExistingGlyph
    ] at hWalks

    exact
      hDistinct
        hWalks

  · unfold observeGlyph

    rw [
      fromExistingGlyph_toExistingGlyph
    ]

    exact
      hFirst

  · unfold observeGlyph

    rw [
      fromExistingGlyph_toExistingGlyph
    ]

    exact
      hSecond

/--
The visible glyph carrier has 21 elements.
-/
theorem card_visibleGlyph :
    Fintype.card VisibleGlyph =
      21 := by

  exact
    card_visibleWalk

/--
The existing glyph space has 42 elements and forms a fixed-point-free
double cover of the 21-state visible carrier.
-/
theorem existing_glyphs_form_double_cover :
    Fintype.card KTGlyph.Glyph =
        42
      ∧
    Fintype.card VisibleGlyph =
        21
      ∧
    Function.Involutive companionGlyph
      ∧
    (∀ glyph, companionGlyph glyph ≠ glyph)
      ∧
    (∀ glyph,
      observeGlyph (companionGlyph glyph) =
        observeGlyph glyph)
      ∧
    Function.Surjective observeGlyph
      ∧
    ¬ Function.Injective observeGlyph := by

  exact
    ⟨
      card_existingGlyph_from_forced,
      card_visibleGlyph,
      companionGlyph_involutive,
      companionGlyph_ne,
      observeGlyph_companionGlyph,
      observeGlyph_surjective,
      observeGlyph_not_injective
    ⟩

end GlyphForcingDoubleCover

#check GlyphForcingDoubleCover.VisibleGlyph
#check GlyphForcingDoubleCover.observeGlyph
#check GlyphForcingDoubleCover.companionGlyph
#check GlyphForcingDoubleCover.companionGlyph_involutive
#check GlyphForcingDoubleCover.companionGlyph_ne
#check GlyphForcingDoubleCover.observeGlyph_companionGlyph
#check GlyphForcingDoubleCover.observeGlyph_eq_iff
#check GlyphForcingDoubleCover.observeGlyph_surjective
#check GlyphForcingDoubleCover.observeGlyph_not_injective
#check GlyphForcingDoubleCover.every_visibleGlyph_has_two_glyphs
#check GlyphForcingDoubleCover.card_visibleGlyph
#check GlyphForcingDoubleCover.existing_glyphs_form_double_cover
