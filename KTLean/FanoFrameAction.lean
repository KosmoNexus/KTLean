import KTLean.FanoAutomorphismFrameEquiv

/-!
# The Fano automorphism action on ordered frames

Every intrinsic Fano automorphism acts pointwise on an
ordered noncollinear frame.

Because automorphisms preserve the Fano completion law,
they preserve generated blocks and therefore preserve
noncollinearity.

This module defines the action and proves its identity and
composition laws. The previously defined `imageFrame` map
is recovered as the action on the fixed reference frame.
-/

namespace FanoFrameAction

/--
Apply a Fano automorphism pointwise to an ordered frame.
-/
def act
    (σ : FanoAutomorphism.Automorphism)
    (f : FanoFrame.Frame) :
    FanoFrame.Frame :=
  ⟨
    (
      σ.1 (FanoFrame.first f),
      σ.1 (FanoFrame.second f),
      σ.1 (FanoFrame.third f)
    ),
    by
      constructor

      · intro h

        have h' :
            FanoFrame.first f =
              FanoFrame.second f :=
          σ.1.injective h

        exact
          FanoFrame.first_ne_second f h'

      · intro h

        have h' :
            FanoFrame.third f ∈
              Fano.system.block
                (FanoFrame.first f)
                (FanoFrame.second f) :=
          (FanoAutomorphismFrame.map_mem_block_iff
            σ
            (FanoFrame.first f)
            (FanoFrame.second f)
            (FanoFrame.third f)).mp h

        exact
          FanoFrame.third_not_mem_generated_block f h'
  ⟩

/--
The first point transforms pointwise.
-/
@[simp]
theorem act_first
    (σ : FanoAutomorphism.Automorphism)
    (f : FanoFrame.Frame) :
    FanoFrame.first (act σ f) =
      σ.1 (FanoFrame.first f) := by
  rfl

/--
The second point transforms pointwise.
-/
@[simp]
theorem act_second
    (σ : FanoAutomorphism.Automorphism)
    (f : FanoFrame.Frame) :
    FanoFrame.second (act σ f) =
      σ.1 (FanoFrame.second f) := by
  rfl

/--
The third point transforms pointwise.
-/
@[simp]
theorem act_third
    (σ : FanoAutomorphism.Automorphism)
    (f : FanoFrame.Frame) :
    FanoFrame.third (act σ f) =
      σ.1 (FanoFrame.third f) := by
  rfl

/--
The identity automorphism fixes every frame.
-/
theorem one_act
    (f : FanoFrame.Frame) :
    act
      (1 : FanoAutomorphism.Automorphism)
      f = f := by
  apply Subtype.ext
  rfl

/--
Composition of automorphisms agrees with successive action.
-/
theorem mul_act
    (σ τ : FanoAutomorphism.Automorphism)
    (f : FanoFrame.Frame) :
    act (σ * τ) f =
      act σ (act τ f) := by
  apply Subtype.ext
  rfl

/--
The earlier image-frame map is precisely the action on the
fixed reference frame.
-/
theorem act_referenceFrame
    (σ : FanoAutomorphism.Automorphism) :
    act σ
        FanoAutomorphismFrame.referenceFrame =
      FanoAutomorphismFrame.imageFrame σ := by
  apply Subtype.ext
  rfl

end FanoFrameAction
