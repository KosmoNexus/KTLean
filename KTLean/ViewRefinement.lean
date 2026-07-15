import KTLean.LocalView

namespace KTLean

universe u v w

/--
A `ViewRefinement` relates a coarse local view to a finer local view.

The finer observation contains at least enough information to recover
the coarse observation through `forget`.
-/
structure ViewRefinement
    (Complete : Type u)
    (Coarse : Type v)
    (Fine : Type w) where

  coarseView :
    LocalView Complete Coarse

  fineView :
    LocalView Complete Fine

  forget :
    Fine → Coarse

  commutes :
    ∀ x : Complete,
      forget (fineView.observe x) =
        coarseView.observe x

namespace ViewRefinement

variable {Complete : Type u}
variable {Coarse : Type v}
variable {Fine : Type w}

variable (R : ViewRefinement Complete Coarse Fine)

/--
Two states that are indistinguishable under the fine view are also
indistinguishable under the coarse view.
-/
theorem fine_equivalence_implies_coarse_equivalence
    {x y : Complete}
    (hfine :
      R.fineView.ObservationallyEquivalent x y) :
    R.coarseView.ObservationallyEquivalent x y := by
  unfold LocalView.ObservationallyEquivalent at hfine ⊢
  calc
    R.coarseView.observe x =
        R.forget (R.fineView.observe x) := by
          exact (R.commutes x).symm
    _ =
        R.forget (R.fineView.observe y) := by
          exact congrArg R.forget hfine
    _ =
        R.coarseView.observe y := by
          exact R.commutes y

/--
If two states are distinguishable in the coarse view, then they are
also distinguishable in the fine view.
-/
theorem coarse_distinguishable_implies_fine_distinguishable
    {x y : Complete}
    (hcoarse :
      R.coarseView.Distinguishable x y) :
    R.fineView.Distinguishable x y := by
  intro hfine
  exact hcoarse
    (R.fine_equivalence_implies_coarse_equivalence hfine)

/--
A refinement never loses distinctions already available in the coarse
view.
-/
theorem preserves_coarse_distinctions
    {x y : Complete}
    (hcoarse :
      R.coarseView.observe x ≠
        R.coarseView.observe y) :
    R.fineView.observe x ≠
      R.fineView.observe y := by
  intro hfine
  apply hcoarse
  calc
    R.coarseView.observe x =
        R.forget (R.fineView.observe x) := by
          exact (R.commutes x).symm
    _ =
        R.forget (R.fineView.observe y) := by
          exact congrArg R.forget hfine
    _ =
        R.coarseView.observe y := by
          exact R.commutes y

/--
A refinement is strict when it distinguishes at least one pair of
states that the coarse view cannot distinguish.
-/
def Strict : Prop :=
  ∃ x y : Complete,
    R.coarseView.ObservationallyEquivalent x y ∧
    R.fineView.Distinguishable x y

/--
A strict refinement exposes a distinction that was locally hidden in
the coarse view.
-/
theorem strict_exposes_hidden_difference
    (hstrict : R.Strict) :
    ∃ x y : Complete,
      R.coarseView.ObservationallyEquivalent x y ∧
      x ≠ y := by
  rcases hstrict with ⟨x, y, hcoarse, hfine⟩
  refine ⟨x, y, hcoarse, ?_⟩
  intro hxy
  subst y
  exact hfine
    (R.fineView.observationallyEquivalent_refl x)

/--
A refinement changes the observer's access map, not the complete state
being observed.
-/
def observeCoarse (x : Complete) : Coarse :=
  R.coarseView.observe x

/--
The same complete state viewed through the finer observation map.
-/
def observeFine (x : Complete) : Fine :=
  R.fineView.observe x

/--
The fine observation of a state always reduces to its coarse
observation.
-/
theorem forget_observeFine
    (x : Complete) :
    R.forget (R.observeFine x) =
      R.observeCoarse x := by
  exact R.commutes x

end ViewRefinement

end KTLean
