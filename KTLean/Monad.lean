import KTLean.DirectedTkairosWitness

/-!
# KT Monads

The preceding development established:

1. exactly 42 lawful KT glyphs;
2. a four-state fiber over every glyph;
3. a concrete moving routed token at which all four
   temporal-information views are distinctly realized.

A monad is therefore defined here as one glyph together
with one realized fourfold semantic state.

No new cardinality is introduced:

    Monad ≃ Glyph × DirectedTkairos.View

and therefore:

    |Monad| = 42 × 4 = 168.
-/

namespace KTMonad


/--
A KT monad is the already-derived glyph state.

Its components are:

- one lawful KT glyph;
- one temporal orientation;
- one information phase.
-/
abbrev Monad :=
  GlyphState.State


/--
The fourfold semantic view carried by a monad.
-/
def view
    (monad : Monad) :
    DirectedTkairos.View where

  direction :=
    monad.direction

  phase :=
    monad.phase


/--
Construct a monad from one glyph and one semantic view.
-/
def ofGlyphView
    (glyph : KTGlyph.Glyph)
    (semanticView : DirectedTkairos.View) :
    Monad where

  glyph :=
    glyph

  direction :=
    semanticView.direction

  phase :=
    semanticView.phase


@[simp]
theorem ofGlyphView_glyph
    (glyph : KTGlyph.Glyph)
    (semanticView : DirectedTkairos.View) :

    (ofGlyphView glyph semanticView).glyph =
      glyph := by

  rfl


@[simp]
theorem view_ofGlyphView
    (glyph : KTGlyph.Glyph)
    (semanticView : DirectedTkairos.View) :

    view
        (ofGlyphView glyph semanticView) =
      semanticView := by

  cases semanticView

  rfl


@[simp]
theorem ofGlyphView_view
    (monad : Monad) :

    ofGlyphView
        monad.glyph
        (view monad) =
      monad := by

  cases monad

  rfl


/-
## Product normal form
-/

/--
The explicit normal form of a monad.
-/
abbrev MonadProduct :=

  KTGlyph.Glyph ×
    DirectedTkairos.View


/--
Convert a monad to glyph-view product form.
-/
def toProduct
    (monad : Monad) :
    MonadProduct :=

  (
    monad.glyph,
    view monad
  )


/--
Construct a monad from glyph-view product form.
-/
def ofProduct
    (data : MonadProduct) :
    Monad :=

  ofGlyphView
    data.1
    data.2


@[simp]
theorem ofProduct_toProduct
    (monad : Monad) :

    ofProduct
        (toProduct monad) =
      monad := by

  exact
    ofGlyphView_view monad


@[simp]
theorem toProduct_ofProduct
    (data : MonadProduct) :

    toProduct
        (ofProduct data) =
      data := by

  rcases data with
    ⟨glyph, semanticView⟩

  cases semanticView

  rfl


/--
Monads are equivalent to glyphs paired with directed
fourfold semantic views.
-/
def monadEquivGlyphView :

    Monad ≃ MonadProduct where

  toFun :=
    toProduct

  invFun :=
    ofProduct

  left_inv :=
    ofProduct_toProduct

  right_inv :=
    toProduct_ofProduct


/-
## Equality and unique normal form
-/

/--
A monad is determined by its glyph and semantic view.
-/
theorem ext
    {left right : Monad}
    (hglyph :
      left.glyph =
        right.glyph)
    (hview :
      view left =
        view right) :

    left = right := by

  have hdirection :
      left.direction =
        right.direction :=

    congrArg
      DirectedTkairos.View.direction
      hview

  have hphase :
      left.phase =
        right.phase :=

    congrArg
      DirectedTkairos.View.phase
      hview

  exact
    GlyphState.State.ext
      hglyph
      hdirection
      hphase
/--
Every monad possesses one unique glyph-view normal form.
-/
theorem unique_normal_form
    (monad : Monad) :

    ∃! data : MonadProduct,

      ofProduct data =
        monad := by

  refine
    ⟨
      toProduct monad,
      ofProduct_toProduct monad,
      ?_
    ⟩

  intro data hdata

  have h :=
    congrArg toProduct hdata

  simpa using h


/--
Distinct product coordinates determine distinct monads.
-/
theorem ne_of_product_ne
    {left right : MonadProduct}
    (hdata :
      left ≠ right) :

    ofProduct left ≠
      ofProduct right := by

  intro hmonad

  have h :=
    congrArg toProduct hmonad

  rw [
    toProduct_ofProduct,
    toProduct_ofProduct
  ] at h

  exact hdata h


/-
## Four monads over every glyph
-/

/--
The subtype of monads lying over one fixed glyph.
-/
abbrev MonadsOver
    (glyph : KTGlyph.Glyph) :=

  {
    monad : Monad //
      monad.glyph = glyph
  }


/--
Monads over one fixed glyph are equivalent to the
fourfold directed semantic view space.
-/
def monadsOverEquivView
    (glyph : KTGlyph.Glyph) :

    MonadsOver glyph ≃
      DirectedTkairos.View where

  toFun :=
    fun monad =>
      view monad.1

  invFun :=
    fun semanticView =>
      ⟨
        ofGlyphView glyph semanticView,
        rfl
      ⟩

  left_inv := by

    intro monad

    rcases monad with
      ⟨
        ⟨monadGlyph, direction, phase⟩,
        hglyph
      ⟩

    dsimp at hglyph

    subst monadGlyph

    rfl

  right_inv := by

    intro semanticView

    exact
      view_ofGlyphView
        glyph
        semanticView


/--
The monads over a fixed glyph form a finite type.
-/
noncomputable instance monadsOverFintype
    (glyph : KTGlyph.Glyph) :

    Fintype (MonadsOver glyph) :=

  Fintype.ofEquiv
    DirectedTkairos.View
    (monadsOverEquivView glyph).symm


/--
Every glyph carries exactly four monads.
-/
theorem monads_over_glyph_card
    (glyph : KTGlyph.Glyph) :

    Fintype.card
        (MonadsOver glyph) =
      4 := by

  rw [
    Fintype.card_congr
      (monadsOverEquivView glyph)
  ]

  exact
    DirectedTkairos.view_card


/-
## Total cardinality
-/

/--
The total monad space contains exactly 168 elements.
-/
theorem card_monad :

    Fintype.card Monad = 168 := by

  exact
    GlyphState.state_card


/--
The monad count factors as 42 glyphs times four semantic
states.
-/
theorem card_monad_eq_glyph_times_four :

    Fintype.card Monad =
      Fintype.card KTGlyph.Glyph * 4 := by

  rw [
    card_monad,
    KTGlyph.card_glyph
  ]


/--
The monad count has the explicit factorization

    42 × 4 = 168.
-/
theorem card_monad_factorization :

    Fintype.card Monad =
      42 * 4 := by

  rw [card_monad]


/--
The prime structural factorization of the monad count is

    7 × 3 × 2 × 2 × 2.
-/
theorem card_monad_prime_structure :

    Fintype.card Monad =
      7 * 3 * 2 * 2 * 2 := by

  exact
    GlyphState.state_card_prime_structure


/-
## Concrete semantic realization
-/

/--
Realize the semantic view of a monad at the concrete moving
routed token.

The glyph itself remains the local structural identity;
the view selects one of the four directed information
states.
-/
def realize
    (monad : Monad) :
    DirectedTkairosWitness.RealizedView :=

  DirectedTkairosWitness.realizeView
    DirectedTkairosWitness.movingToken
    (view monad)


/--
For one fixed glyph, concrete realization is injective.

Thus the four monads over that glyph correspond to four
distinct realized directed-information states.
-/
theorem realize_injective_over_glyph
    (glyph : KTGlyph.Glyph)
    {left right : MonadsOver glyph}
    (hrealized :
      realize left.1 =
        realize right.1) :

    left = right := by

  apply Subtype.ext

  apply KTMonad.ext

  · exact
      left.2.trans
        right.2.symm

  · exact
      DirectedTkairosWitness.concrete_realizeView_injective
        hrealized


/--
The four semantic states used in the monad definition are
concretely realized by the routed Tkairos witness.
-/
theorem monad_fourfold_realized :

    ∃ token : RoutedTokenization.Token,

      DirectedTkairos.IsMoving token
        ∧

      Function.Injective
        (
          DirectedTkairosWitness.realizeView
            token
        )
        ∧

      DirectedTkairosWitness.realizedViews.card =
        4 := by

  exact
    DirectedTkairosWitness.fourfold_semantic_realization


/-
## Canonical constructor
-/

/--
Construct a monad directly from:

- one glyph;
- one temporal direction;
- one information phase.
-/
def mk
    (glyph : KTGlyph.Glyph)
    (direction :
      GlyphState.TemporalDirection)
    (phase :
      GlyphState.InformationPhase) :
    Monad where

  glyph :=
    glyph

  direction :=
    direction

  phase :=
    phase


@[simp]
theorem mk_glyph
    (glyph : KTGlyph.Glyph)
    (direction :
      GlyphState.TemporalDirection)
    (phase :
      GlyphState.InformationPhase) :

    (mk glyph direction phase).glyph =
      glyph := by

  rfl


@[simp]
theorem mk_view
    (glyph : KTGlyph.Glyph)
    (direction :
      GlyphState.TemporalDirection)
    (phase :
      GlyphState.InformationPhase) :

    view
        (mk glyph direction phase) =

      ({
        direction := direction
        phase := phase
      } : DirectedTkairos.View) := by

  rfl


/--
The direct monad constructor is injective in glyph,
temporal direction, and information phase.
-/
theorem mk_eq_mk_iff
    {glyph₁ glyph₂ : KTGlyph.Glyph}
    {direction₁ direction₂ :
      GlyphState.TemporalDirection}
    {phase₁ phase₂ :
      GlyphState.InformationPhase} :

    mk glyph₁ direction₁ phase₁ =
        mk glyph₂ direction₂ phase₂
      ↔

    glyph₁ = glyph₂
      ∧
    direction₁ = direction₂
      ∧
    phase₁ = phase₂ := by

  constructor

  · intro hmonad

    exact
      ⟨
        congrArg GlyphState.State.glyph hmonad,

        congrArg GlyphState.State.direction hmonad,

        congrArg GlyphState.State.phase hmonad
      ⟩

  · intro hcoordinates

    rcases hcoordinates with
      ⟨hglyph, hdirection, hphase⟩

    subst glyph₂
    subst direction₂
    subst phase₂

    rfl


end KTMonad
