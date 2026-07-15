import KTLean.AdmissibleProjection

namespace KTLean

universe u v w

/--
`ProjectionDynamics` describes evolution on a complete state together
with the local observation of that evolution.

The visible dynamics are not assumed to be closed. Closure is expressed
separately by the existence of a visible step making the projection
diagram commute.
-/
structure ProjectionDynamics
    (Complete : Type u)
    (Visible : Type v)
    (Residue : Type w) where

  projection :
    AdmissibleProjection Complete Visible Residue

  completeStep :
    Complete → Complete

namespace ProjectionDynamics

variable {Complete : Type u}
variable {Visible : Type v}
variable {Residue : Type w}

variable (D : ProjectionDynamics Complete Visible Residue)

/--
The locally visible component of a complete state.
-/
def observe (x : Complete) : Visible :=
  D.projection.observe x

/--
The provenance residue of a complete state.
-/
def residue (x : Complete) : Residue :=
  D.projection.residue x

/--
A proposed local evolution law is compatible with the complete dynamics
when observing after complete evolution gives the same result as evolving
the visible state directly.
-/
def CommutesWithProjection
    (visibleStep : Visible → Visible) : Prop :=
  ∀ x : Complete,
    D.observe (D.completeStep x) =
      visibleStep (D.observe x)

/--
The visible dynamics are closed when some evolution law on visible
states makes the projection diagram commute.
-/
def VisiblyClosed : Prop :=
  ∃ visibleStep : Visible → Visible,
    D.CommutesWithProjection visibleStep

/--
A visible successor is determined by a proposed visible evolution law.
-/
def visibleSuccessor
    (visibleStep : Visible → Visible)
    (x : Complete) : Visible :=
  visibleStep (D.observe x)

/--
For commuting dynamics, the visible successor obtained locally agrees
with observation of the evolved complete state.
-/
theorem visibleSuccessor_eq_observe_completeStep
    (visibleStep : Visible → Visible)
    (hcommutes : D.CommutesWithProjection visibleStep)
    (x : Complete) :
    D.visibleSuccessor visibleStep x =
      D.observe (D.completeStep x) := by
  exact (hcommutes x).symm

/--
If two complete states are locally indistinguishable and the dynamics
are visibly closed, then they remain locally indistinguishable after one
complete evolution step.
-/
theorem observationalEquivalence_preserved
    (visibleStep : Visible → Visible)
    (hcommutes : D.CommutesWithProjection visibleStep)
    {x y : Complete}
    (hxy :
      D.projection.ObservationallyEquivalent x y) :
    D.projection.ObservationallyEquivalent
      (D.completeStep x)
      (D.completeStep y) := by
  have hobserve : D.observe x = D.observe y := by
    simpa [
      ProjectionDynamics.observe,
      AdmissibleProjection.observe,
      AdmissibleProjection.ObservationallyEquivalent,
      AdmissibleProjection.view,
      LocalView.ObservationallyEquivalent
    ] using hxy

  change
    D.observe (D.completeStep x) =
      D.observe (D.completeStep y)

  calc
    D.observe (D.completeStep x) =
        visibleStep (D.observe x) := hcommutes x
    _ = visibleStep (D.observe y) := congrArg visibleStep hobserve
    _ = D.observe (D.completeStep y) := (hcommutes y).symm

/--
A hidden dynamical split occurs when two states appear identical now
but become locally distinguishable after one complete evolution step.
-/
def HiddenDynamicalSplit
    (x y : Complete) : Prop :=
  D.projection.ObservationallyEquivalent x y ∧
  D.projection.LocallyHiddenDifference x y ∧
  D.observe (D.completeStep x) ≠
    D.observe (D.completeStep y)

/--
A hidden dynamical split is incompatible with visibly closed dynamics.
-/
theorem not_visiblyClosed_of_hiddenDynamicalSplit
    {x y : Complete}
    (hsplit : D.HiddenDynamicalSplit x y) :
    ¬ D.VisiblyClosed := by
  intro hclosed
  rcases hclosed with ⟨visibleStep, hcommutes⟩
  apply hsplit.2.2
  rw [hcommutes x, hcommutes y]
  exact congrArg visibleStep hsplit.1

/--
If visible dynamics are closed, observationally equivalent states cannot
produce different next observations.
-/
theorem next_observation_eq_of_visiblyClosed
    (hclosed : D.VisiblyClosed)
    {x y : Complete}
    (hxy :
      D.projection.ObservationallyEquivalent x y) :
    D.observe (D.completeStep x) =
      D.observe (D.completeStep y) := by
  rcases hclosed with ⟨visibleStep, hcommutes⟩
  rw [hcommutes x, hcommutes y]
  exact congrArg visibleStep hxy

/--
A residue-sensitive transition is one in which equal visible states with
different provenance residues can evolve to different visible successors.
-/
def ResidueSensitive : Prop :=
  ∃ x y : Complete,
    D.projection.ObservationallyEquivalent x y ∧
    D.residue x ≠ D.residue y ∧
    D.observe (D.completeStep x) ≠
      D.observe (D.completeStep y)

/--
Residue-sensitive dynamics cannot be represented by a closed evolution
law on visible states alone.
-/
theorem not_visiblyClosed_of_residueSensitive
    (hsensitive : D.ResidueSensitive) :
    ¬ D.VisiblyClosed := by
  rcases hsensitive with
    ⟨x, y, hvisible, _hresidue, hnext⟩
  intro hclosed
  apply hnext
  exact
    D.next_observation_eq_of_visiblyClosed
      hclosed
      hvisible

/--
When visible dynamics are not closed, no function of the current visible
state alone reproduces the next visible observation for every complete
state.
-/
theorem no_visibleStep_of_not_visiblyClosed
    (hnotclosed : ¬ D.VisiblyClosed) :
    ∀ visibleStep : Visible → Visible,
      ¬ D.CommutesWithProjection visibleStep := by
  intro visibleStep hcommutes
  apply hnotclosed
  exact ⟨visibleStep, hcommutes⟩

end ProjectionDynamics

end KTLean
