import KTLean.FanoAutomorphismCardinality
import KTLean.FanoFrame
import KTLean.FanoAutomorphismFrameInjective
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Equivalence between Fano automorphisms and ordered frames

The intrinsic Fano automorphism group and the type of
ordered noncollinear Fano frames both have cardinality 168.

The image-frame map is already known to be injective.
Because its finite domain and codomain have equal cardinality,
it is bijective.

Thus every ordered noncollinear Fano frame is the image of
the reference frame under exactly one Fano automorphism.
-/

namespace FanoAutomorphismFrameEquiv

/--
Preservation of Fano completion is decidable.
-/
local instance preservesCompletionDecidable :
    DecidablePred
      FanoAutomorphism.PreservesCompletion := by
  intro σ
  unfold FanoAutomorphism.PreservesCompletion
  infer_instance

/--
Membership in the intrinsic Fano automorphism subgroup
is decidable.
-/
local instance groupMembershipDecidable :
    DecidablePred
      (fun σ : Equiv.Perm Fano.Point =>
        σ ∈ FanoAutomorphism.group) := by
  intro σ
  change Decidable
    (FanoAutomorphism.PreservesCompletion σ)
  infer_instance

/--
The automorphism and frame types have equal cardinality.
-/
theorem card_automorphism_eq_card_frame :
    Fintype.card FanoAutomorphism.Automorphism =
      Fintype.card FanoFrame.Frame := by
  rw [
    FanoAutomorphismCardinality.card_automorphism,
    FanoFrame.card_frame
  ]

/--
The image-frame map is bijective.
-/
theorem imageFrame_bijective :
    Function.Bijective
      FanoAutomorphismFrame.imageFrame := by
  rw [Fintype.bijective_iff_injective_and_card]

  exact
    ⟨
      FanoAutomorphismFrameInjective.imageFrame_injective,
      card_automorphism_eq_card_frame
    ⟩

/--
The intrinsic Fano automorphism group is equivalent, as a
finite type, to the ordered noncollinear Fano frames.
-/
noncomputable def automorphismEquivFrame :
    FanoAutomorphism.Automorphism ≃
      FanoFrame.Frame :=
  Equiv.ofBijective
    FanoAutomorphismFrame.imageFrame
    imageFrame_bijective

/--
The forward direction of the equivalence is exactly the
image-frame map.
-/
@[simp]
theorem automorphismEquivFrame_apply
    (σ : FanoAutomorphism.Automorphism) :
    automorphismEquivFrame σ =
      FanoAutomorphismFrame.imageFrame σ := by
  rfl

/--
Every ordered noncollinear frame is the image of the
reference frame under a unique Fano automorphism.
-/
theorem existsUnique_automorphism_for_frame
    (f : FanoFrame.Frame) :
    ∃! σ : FanoAutomorphism.Automorphism,
      FanoAutomorphismFrame.imageFrame σ = f := by
  obtain ⟨σ, hσ⟩ :=
    imageFrame_bijective.2 f

  refine ⟨σ, hσ, ?_⟩

  intro τ hτ

  exact
    imageFrame_bijective.1
      (hτ.trans hσ.symm)

end FanoAutomorphismFrameEquiv
