import KTLean.ViewRefinement

namespace KTLean

universe u v w

/--
A `MeasurementRefinement` combines:

1. a refinement from a coarse view to a finer view, and
2. a complete-state transition associated with performing the measurement.

The transition is explicit so that passive observation and physically
interactive measurement are not conflated.
-/
structure MeasurementRefinement
    (Complete : Type u)
    (Coarse : Type v)
    (Fine : Type w) where

  refinement :
    ViewRefinement Complete Coarse Fine

  measureStep :
    Complete → Complete

namespace MeasurementRefinement

variable {Complete : Type u}
variable {Coarse : Type v}
variable {Fine : Type w}

variable (M : MeasurementRefinement Complete Coarse Fine)

/--
The coarse observation before measurement.
-/
def coarseBefore (x : Complete) : Coarse :=
  M.refinement.coarseView.observe x

/--
The fine observation after the measurement interaction.
-/
def fineAfter (x : Complete) : Fine :=
  M.refinement.fineView.observe (M.measureStep x)

/--
The coarse observation after the measurement interaction.
-/
def coarseAfter (x : Complete) : Coarse :=
  M.refinement.coarseView.observe (M.measureStep x)

/--
The fine post-measurement observation reduces to the coarse
post-measurement observation.
-/
theorem forget_fineAfter
    (x : Complete) :
    M.refinement.forget (M.fineAfter x) =
      M.coarseAfter x := by
  exact M.refinement.commutes (M.measureStep x)

/--
A measurement is passive when it does not alter the complete state.
-/
def Passive : Prop :=
  ∀ x : Complete,
    M.measureStep x = x

/--
A measurement is interactive when it changes at least one complete
state.
-/
def Interactive : Prop :=
  ∃ x : Complete,
    M.measureStep x ≠ x

/--
Passive and interactive measurement are mutually exclusive.
-/
theorem not_interactive_of_passive
    (hpassive : M.Passive) :
    ¬ M.Interactive := by
  intro hinteractive
  rcases hinteractive with ⟨x, hx⟩
  exact hx (hpassive x)

/--
A non-passive measurement is interactive.
-/
theorem interactive_of_not_passive
    (hnotpassive : ¬ M.Passive) :
    M.Interactive := by
  unfold Passive at hnotpassive
  unfold Interactive
  exact Classical.not_forall.mp hnotpassive

/--
For a passive measurement, the complete state after measurement is the
same complete state that existed before measurement.
-/
theorem complete_state_unchanged
    (hpassive : M.Passive)
    (x : Complete) :
    M.measureStep x = x := by
  exact hpassive x

/--
For a passive measurement, the coarse observation after measurement is
the same as the coarse observation before measurement.
-/
theorem coarseAfter_eq_coarseBefore
    (hpassive : M.Passive)
    (x : Complete) :
    M.coarseAfter x =
      M.coarseBefore x := by
  unfold coarseAfter coarseBefore
  rw [hpassive x]

/--
For a passive measurement, the fine observation after measurement is
simply the fine view of the original complete state.
-/
theorem fineAfter_eq_fineView
    (hpassive : M.Passive)
    (x : Complete) :
    M.fineAfter x =
      M.refinement.fineView.observe x := by
  unfold fineAfter
  rw [hpassive x]

/--
A passive measurement can refine observational access without changing
the complete state.
-/
theorem passive_refines_without_state_change
    (hpassive : M.Passive)
    (x : Complete) :
    M.measureStep x = x ∧
    M.refinement.forget
        (M.refinement.fineView.observe x) =
      M.refinement.coarseView.observe x := by
  constructor
  · exact hpassive x
  · exact M.refinement.commutes x

/--
If a passive measurement is a strict refinement, then it reveals at
least one distinction that was hidden in the coarse view while leaving
the complete states unchanged.
-/
theorem passive_strict_measurement_reveals_hidden_difference
    (hpassive : M.Passive)
    (hstrict : M.refinement.Strict) :
    ∃ x y : Complete,
      M.refinement.coarseView.ObservationallyEquivalent x y ∧
      M.refinement.fineView.Distinguishable x y ∧
      M.measureStep x = x ∧
      M.measureStep y = y := by
  rcases hstrict with ⟨x, y, hcoarse, hfine⟩
  exact
    ⟨x, y, hcoarse, hfine, hpassive x, hpassive y⟩

/--
Interactive measurement may change both the complete state and the
observer's access to it. Any such disturbance is represented explicitly
by `measureStep`.
-/
theorem interactive_has_state_change
    (hinteractive : M.Interactive) :
    ∃ x : Complete,
      M.measureStep x ≠ x := by
  exact hinteractive

end MeasurementRefinement

end KTLean
