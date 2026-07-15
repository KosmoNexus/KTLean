import KTLean.Monad
import Mathlib.Algebra.Group.Defs

namespace KTLean

universe u

namespace MonadAction

/--
A lawful substrate-frame action on monads.

A frame transformation acts separately but coherently on:

1. the glyph coordinate;
2. the fourfold directed walk realization.

The laws require both actions to respect the identity frame and frame
composition.
-/
structure FrameAction
    (Frame : Type u)
    [Group Frame] where

  actGlyph :
    Frame →
      KTGlyph.Glyph →
        KTGlyph.Glyph

  actView :
    Frame →
      DirectedTkairos.View →
        DirectedTkairos.View

  actGlyph_one :
    ∀ glyph : KTGlyph.Glyph,
      actGlyph 1 glyph = glyph

  actGlyph_mul :
    ∀
      (left right : Frame)
      (glyph : KTGlyph.Glyph),
      actGlyph (left * right) glyph =
        actGlyph left
          (actGlyph right glyph)

  actView_one :
    ∀ semanticView : DirectedTkairos.View,
      actView 1 semanticView =
        semanticView

  actView_mul :
    ∀
      (left right : Frame)
      (semanticView : DirectedTkairos.View),
      actView (left * right) semanticView =
        actView left
          (actView right semanticView)

namespace FrameAction

variable
  {Frame : Type u}
  [Group Frame]

variable
  (A : FrameAction Frame)

/--
Transport a complete monad under a substrate-frame transformation.

Both the glyph and its directed walk realization are transported.
-/
def act
    (frame : Frame)
    (monad : KTMonad.Monad) :
    KTMonad.Monad :=

  KTMonad.ofGlyphView
    (A.actGlyph frame monad.glyph)
    (A.actView frame (KTMonad.view monad))

/--
The glyph component of a transported monad is the transported glyph.
-/
@[simp]
theorem act_glyph
    (frame : Frame)
    (monad : KTMonad.Monad) :

    (A.act frame monad).glyph =
      A.actGlyph frame monad.glyph := by

  rfl

/--
The walk realization of a transported monad is the transported walk
realization.
-/
@[simp]
theorem view_act
    (frame : Frame)
    (monad : KTMonad.Monad) :

    KTMonad.view (A.act frame monad) =
      A.actView frame (KTMonad.view monad) := by

  exact
    KTMonad.view_ofGlyphView
      (A.actGlyph frame monad.glyph)
      (A.actView frame (KTMonad.view monad))

/--
The identity substrate frame fixes every monad.
-/
@[simp]
theorem one_act
    (monad : KTMonad.Monad) :

    A.act 1 monad = monad := by

  apply KTMonad.ext

  · rw [act_glyph]
    exact A.actGlyph_one monad.glyph

  · rw [view_act]
    exact A.actView_one (KTMonad.view monad)

/--
Composition of substrate-frame transformations agrees with successive
transport of the complete monad.
-/
@[simp]
theorem mul_act
    (left right : Frame)
    (monad : KTMonad.Monad) :

    A.act (left * right) monad =
      A.act left (A.act right monad) := by

  apply KTMonad.ext

  · rw [act_glyph, act_glyph, act_glyph]
    exact
      A.actGlyph_mul
        left
        right
        monad.glyph

  · rw [view_act, view_act, view_act]
    exact
      A.actView_mul
        left
        right
        (KTMonad.view monad)

/--
Every frame transformation has an inverse action on monads.
-/
theorem inverse_recovers
    (frame : Frame)
    (monad : KTMonad.Monad) :

    A.act frame⁻¹ (A.act frame monad) =
      monad := by

  calc
    A.act frame⁻¹ (A.act frame monad) =
        A.act (frame⁻¹ * frame) monad := by
          exact
            (A.mul_act frame⁻¹ frame monad).symm

    _ = A.act 1 monad := by
          simp

    _ = monad := by
          exact A.one_act monad

/--
Frame transport is injective on complete monads.
-/
theorem act_injective
    (frame : Frame) :

    Function.Injective
      (A.act frame) := by

  intro left right h

  have hinverse :=
    congrArg
      (A.act frame⁻¹)
      h

  simpa [A.inverse_recovers] using hinverse

/--
Frame transport is surjective on complete monads.
-/
theorem act_surjective
    (frame : Frame) :

    Function.Surjective
      (A.act frame) := by

  intro monad

  refine
    ⟨A.act frame⁻¹ monad, ?_⟩

  calc
    A.act frame
        (A.act frame⁻¹ monad) =
      A.act (frame * frame⁻¹) monad := by
        exact
          (A.mul_act
            frame
            frame⁻¹
            monad).symm

    _ = A.act 1 monad := by
          simp

    _ = monad := by
          exact A.one_act monad

/--
Each frame transformation acts bijectively on the complete monad space.
-/
def actEquiv
    (frame : Frame) :

    KTMonad.Monad ≃
      KTMonad.Monad where

  toFun :=
    A.act frame

  invFun :=
    A.act frame⁻¹

  left_inv :=
    A.inverse_recovers frame

  right_inv := by
    intro monad

    calc
      A.act frame
          (A.act frame⁻¹ monad) =
        A.act (frame * frame⁻¹) monad := by
          exact
            (A.mul_act
              frame
              frame⁻¹
              monad).symm

      _ = A.act 1 monad := by
            simp

      _ = monad := by
            exact A.one_act monad

/--
A lawful monad action never transports the glyph while silently leaving
the walk realization outside the transformation law.

Both components are explicitly accounted for.
-/
theorem transported_components
    (frame : Frame)
    (monad : KTMonad.Monad) :

    (A.act frame monad).glyph =
        A.actGlyph frame monad.glyph
      ∧
    KTMonad.view (A.act frame monad) =
        A.actView frame (KTMonad.view monad) := by

  exact
    ⟨
      A.act_glyph frame monad,
      A.view_act frame monad
    ⟩

end FrameAction

end MonadAction

end KTLean
