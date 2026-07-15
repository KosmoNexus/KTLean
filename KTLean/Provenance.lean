import KTLean.LocalView

namespace KTLean

universe u v w

/--
A `Provenance Complete Visible Residue` gives an exact accounting of
how a complete state decomposes into:

1. what is visible in a local frame, and
2. the residue omitted from that local view.

The residue is not arbitrary: together with the visible state it
reconstructs the complete state exactly.
-/
structure Provenance
    (Complete : Type u)
    (Visible : Type v)
    (Residue : Type w) where

  /-- The local observation map. -/
  view : LocalView Complete Visible

  /-- The component omitted from the local observation. -/
  residue : Complete → Residue

  /-- Reconstruction from visible state and residue. -/
  rebuild : Visible → Residue → Complete

  /-- Reconstruction preserves the visible component. -/
  observe_rebuild :
    ∀ visible residueValue,
      view.observe (rebuild visible residueValue) = visible

  /-- Reconstruction preserves the residue component. -/
  residue_rebuild :
    ∀ visible residueValue,
      residue (rebuild visible residueValue) = residueValue

  /-- Every complete state is recovered from its two components. -/
  rebuild_parts :
    ∀ complete,
      rebuild
        (view.observe complete)
        (residue complete) =
      complete
namespace Provenance

variable {Complete : Type u}
variable {Visible : Type v}
variable {Residue : Type w}

variable (P : Provenance Complete Visible Residue)

/--
Decompose a complete state into its locally visible component and its
provenance residue.
-/
def decompose (x : Complete) : Visible × Residue :=
  (P.view.observe x, P.residue x)

/--
Reconstruct a complete state from a visible component and residue.
-/
def reconstruct (parts : Visible × Residue) : Complete :=
  P.rebuild parts.1 parts.2

/--
Decomposing and then reconstructing returns the original complete state.
-/
theorem reconstruct_decompose
    (x : Complete) :
    P.reconstruct (P.decompose x) = x := by
  exact P.rebuild_parts x

/--
Reconstructing and then decomposing returns the original pair of parts.
-/
theorem decompose_reconstruct
    (parts : Visible × Residue) :
    P.decompose (P.reconstruct parts) = parts := by
  cases parts with
  | mk visible residue =>
      apply Prod.ext
      · exact P.observe_rebuild visible residue
      · exact P.residue_rebuild visible residue

/--

The decomposition map is injective.
-/
theorem decompose_injective
    (P : Provenance Complete Visible Residue) :
    Function.Injective (decompose P) := by
  intro x y hxy
  have h :=
    congrArg (reconstruct P) hxy
  rw [reconstruct_decompose P x,
      reconstruct_decompose P y] at h
  exact h
/--
Two complete states are equal when both their visible components and
their residues agree.
-/
theorem eq_of_same_observation_and_residue
    {x y : Complete}
    (hvisible : P.view.observe x = P.view.observe y)
    (hresidue : P.residue x = P.residue y) :
    x = y := by
  calc
    x =
        P.rebuild
          (P.view.observe x)
          (P.residue x) := by
            exact (P.rebuild_parts x).symm
    _ =
        P.rebuild
          (P.view.observe y)
          (P.residue y) := by
            rw [hvisible, hresidue]
    _ = y := by
          exact P.rebuild_parts y

/--
Observationally equivalent states are equal when their provenance
residues also agree.
-/
theorem eq_of_observationallyEquivalent_of_residue_eq
    {x y : Complete}
    (hvisible : P.view.ObservationallyEquivalent x y)
    (hresidue : P.residue x = P.residue y) :
    x = y := by
  exact P.eq_of_same_observation_and_residue hvisible hresidue

/--
A locally hidden difference is a genuine difference between complete
states that cannot be detected through the local observation map.
-/
def LocallyHiddenDifference (x y : Complete) : Prop :=
  P.view.ObservationallyEquivalent x y ∧ x ≠ y

/--
If two complete states differ while appearing identical locally, their
provenance residues must differ.
-/
theorem residue_ne_of_locallyHiddenDifference
    {x y : Complete}
    (h : P.LocallyHiddenDifference x y) :
    P.residue x ≠ P.residue y := by
  intro hresidue
  apply h.2
  exact
    P.eq_of_observationallyEquivalent_of_residue_eq
      h.1
      hresidue

/--
No difference between complete states can disappear simultaneously from
both the visible component and the provenance residue.
-/
theorem visible_or_residue_differs
    {x y : Complete}
    (hxy : x ≠ y) :
    P.view.observe x ≠ P.view.observe y ∨
      P.residue x ≠ P.residue y := by
  by_cases hvisible :
      P.view.observe x = P.view.observe y
  · right
    intro hresidue
    exact hxy
      (P.eq_of_same_observation_and_residue
        hvisible
        hresidue)
  · left
    exact hvisible

end Provenance

end KTLean
