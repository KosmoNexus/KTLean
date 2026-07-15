import KTLean.Provenance

namespace KTLean

universe u v w

/--
An `AdmissibleProjection` is a local view together with an exact
provenance account of everything omitted from that view.

The projection may hide information locally, but it may not hide
information arbitrarily.
-/
structure AdmissibleProjection
    (Complete : Type u)
    (Visible : Type v)
    (Residue : Type w) where

  provenance : Provenance Complete Visible Residue

namespace AdmissibleProjection

variable {Complete : Type u}
variable {Visible : Type v}
variable {Residue : Type w}

variable (A : AdmissibleProjection Complete Visible Residue)

/--
The local view associated with an admissible projection.
-/
def view : LocalView Complete Visible :=
  A.provenance.view

/--
The locally visible component of a complete state.
-/
def observe (x : Complete) : Visible :=
  A.view.observe x

/--
The provenance residue associated with a complete state.
-/
def residue (x : Complete) : Residue :=
  A.provenance.residue x

/--
Two complete states are observationally equivalent under an admissible
projection when their visible components agree.
-/
def ObservationallyEquivalent
    (x y : Complete) : Prop :=
  A.view.ObservationallyEquivalent x y

/--
Two complete states differ only in locally hidden provenance when they
appear identical locally but are not equal as complete states.
-/
def LocallyHiddenDifference
    (x y : Complete) : Prop :=
  A.ObservationallyEquivalent x y ∧ x ≠ y

/--
Any locally hidden difference must appear in the provenance residue.
-/
theorem residue_ne_of_locallyHiddenDifference
    {x y : Complete}
    (h : A.LocallyHiddenDifference x y) :
    A.residue x ≠ A.residue y := by
  exact
    A.provenance.residue_ne_of_locallyHiddenDifference h

/--
Two complete states are equal whenever both their local observations
and their provenance residues agree.
-/
theorem eq_of_observation_eq_and_residue_eq
    {x y : Complete}
    (hvisible : A.observe x = A.observe y)
    (hresidue : A.residue x = A.residue y) :
    x = y := by
  exact
    A.provenance.eq_of_same_observation_and_residue
      hvisible
      hresidue

/--
Any difference between complete states appears either locally or in
the provenance residue.
-/
theorem observable_or_residual_difference
    {x y : Complete}
    (hxy : x ≠ y) :
    A.observe x ≠ A.observe y ∨
      A.residue x ≠ A.residue y := by
  exact
    A.provenance.visible_or_residue_differs hxy

/--
A projection is locally faithful when observational equivalence already
implies equality of complete states.
-/
def LocallyFaithful : Prop :=
  ∀ ⦃x y : Complete⦄,
    A.ObservationallyEquivalent x y →
    x = y

/--
An admissible projection is locally faithful exactly when its observation
map is injective.
-/
theorem locallyFaithful_iff_observe_injective :
    A.LocallyFaithful ↔
      Function.Injective A.observe := by
  constructor
  · intro hfaithful x y hxy
    apply hfaithful
    exact hxy
  · intro hinjective x y hxy
    apply hinjective
    exact hxy

/--
If the observation map is injective, there are no locally hidden
differences.
-/
theorem no_locallyHiddenDifference_of_injective
    (hinjective : Function.Injective A.observe)
    {x y : Complete} :
    ¬ A.LocallyHiddenDifference x y := by
  intro h
  apply h.2
  exact hinjective h.1

end AdmissibleProjection

end KTLean
