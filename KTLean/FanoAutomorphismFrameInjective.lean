import KTLean.FanoAutomorphismFrame
import Mathlib.Tactic.FinCases

/-!
# A Fano automorphism is determined by one frame

The reference frame contains the points `0`, `1`, and `2`.

Every remaining Fano point is generated from these by the
completion law:

    3 = complete 0 1
    4 = complete 1 2
    6 = complete 0 2
    5 = complete 0 4

Because Fano automorphisms preserve completion, two
automorphisms agreeing on the reference frame agree on
all seven points.

Thus the map from Fano automorphisms to image frames is
injective.
-/

namespace FanoAutomorphismFrameInjective

/--
Agreement at two points is inherited by their Fano
completion.
-/
theorem agree_on_completion
    {σ τ : FanoAutomorphism.Automorphism}
    {x y : Fano.Point}
    (hx : σ.1 x = τ.1 x)
    (hy : σ.1 y = τ.1 y) :
    σ.1 (Fano.complete x y) =
      τ.1 (Fano.complete x y) := by
  rw [
    FanoAutomorphism.map_complete σ x y,
    FanoAutomorphism.map_complete τ x y,
    hx,
    hy
  ]

/--
Two automorphisms with the same image frame agree at the
three reference points.
-/
theorem agree_on_reference_points
    {σ τ : FanoAutomorphism.Automorphism}
    (h :
      FanoAutomorphismFrame.imageFrame σ =
        FanoAutomorphismFrame.imageFrame τ) :
    σ.1 0 = τ.1 0 ∧
    σ.1 1 = τ.1 1 ∧
    σ.1 2 = τ.1 2 := by
  constructor

  · exact
      congrArg FanoFrame.first h

  · constructor

    · exact
        congrArg FanoFrame.second h

    · exact
        congrArg FanoFrame.third h

/--
The image-frame map is injective.
-/
theorem imageFrame_injective :
    Function.Injective
      FanoAutomorphismFrame.imageFrame := by
  intro σ τ hframe

  obtain ⟨h0, h1, h2⟩ :=
    agree_on_reference_points hframe

  have h3 :
      σ.1 3 = τ.1 3 := by
    have h :=
      agree_on_completion
        (σ := σ)
        (τ := τ)
        h0
        h1

    change σ.1 3 = τ.1 3 at h
    exact h

  have h4 :
      σ.1 4 = τ.1 4 := by
    have h :=
      agree_on_completion
        (σ := σ)
        (τ := τ)
        h1
        h2

    change σ.1 4 = τ.1 4 at h
    exact h

  have h6 :
      σ.1 6 = τ.1 6 := by
    have h :=
      agree_on_completion
        (σ := σ)
        (τ := τ)
        h0
        h2

    change σ.1 6 = τ.1 6 at h
    exact h

  have h5 :
      σ.1 5 = τ.1 5 := by
    have h :=
      agree_on_completion
        (σ := σ)
        (τ := τ)
        h0
        h4

    change σ.1 5 = τ.1 5 at h
    exact h

  apply Subtype.ext
  apply Equiv.ext
  intro x

  fin_cases x

  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

end FanoAutomorphismFrameInjective
