import KTLean.ProjectionDynamics

namespace KTLean

universe u v w

namespace ProjectionDynamics

variable {Complete : Type u}
variable {Visible : Type v}
variable {Residue : Type w}

variable (D : ProjectionDynamics Complete Visible Residue)

/--
The local observation map is non-injective when two distinct complete
states appear identical in the visible frame.
-/
def NoninjectiveView : Prop :=
  ∃ x y : Complete,
    x ≠ y ∧
    D.observe x = D.observe y

/--
A projection dynamics is quasi-stochastic when:

1. the local view is non-injective, and
2. hidden provenance can affect a later visible outcome.

The complete evolution remains an ordinary deterministic function.
The apparent stochasticity arises from incomplete local state.
-/
def QuasiStochastic : Prop :=
  D.NoninjectiveView ∧
  D.ResidueSensitive

/--
A quasi-stochastic system has at least two distinct complete states
that are observationally identical in the current local frame.
-/
theorem exists_hidden_complete_difference
    (hquasi : D.QuasiStochastic) :
    ∃ x y : Complete,
      x ≠ y ∧
      D.observe x = D.observe y := by
  exact hquasi.1

/--
A quasi-stochastic system contains a residue-sensitive pair: two
currently indistinguishable complete states with different provenance
and different next visible observations.
-/
theorem exists_residue_sensitive_pair
    (hquasi : D.QuasiStochastic) :
    ∃ x y : Complete,
      D.projection.ObservationallyEquivalent x y ∧
      D.residue x ≠ D.residue y ∧
      D.observe (D.completeStep x) ≠
        D.observe (D.completeStep y) := by
  exact hquasi.2

/--
Quasi-stochastic visible dynamics cannot be represented by a closed
evolution law on visible states alone.
-/
theorem not_visiblyClosed_of_quasiStochastic
    (hquasi : D.QuasiStochastic) :
    ¬ D.VisiblyClosed := by
  exact
    ProjectionDynamics.not_visiblyClosed_of_residueSensitive
      D
      hquasi.2

/--
No function of the present visible state alone can reproduce every
next visible observation in a quasi-stochastic system.
-/
theorem no_visibleStep_of_quasiStochastic
    (hquasi : D.QuasiStochastic) :
    ∀ visibleStep : Visible → Visible,
      ¬ D.CommutesWithProjection visibleStep := by
  exact
    ProjectionDynamics.no_visibleStep_of_not_visiblyClosed
      D
      (D.not_visiblyClosed_of_quasiStochastic hquasi)

/--
A residue-sensitive pair is necessarily a hidden dynamical split.
-/
theorem hiddenDynamicalSplit_of_residueSensitive_pair
    {x y : Complete}
    (hvisible :
      D.projection.ObservationallyEquivalent x y)
    (hresidue :
      D.residue x ≠ D.residue y)
    (hnext :
      D.observe (D.completeStep x) ≠
        D.observe (D.completeStep y)) :
    D.HiddenDynamicalSplit x y := by
  refine ⟨hvisible, ?_, hnext⟩

  constructor
  · exact hvisible
  · intro hxy
    apply hresidue
    rw [hxy]

/--
Every quasi-stochastic system contains a hidden dynamical split.
-/
theorem exists_hiddenDynamicalSplit
    (hquasi : D.QuasiStochastic) :
    ∃ x y : Complete,
      D.HiddenDynamicalSplit x y := by
  rcases hquasi.2 with
    ⟨x, y, hvisible, hresidue, hnext⟩

  refine ⟨x, y, ?_⟩

  exact
    D.hiddenDynamicalSplit_of_residueSensitive_pair
      hvisible
      hresidue
      hnext

/--
Visible closure excludes quasi-stochasticity.
-/
theorem not_quasiStochastic_of_visiblyClosed
    (hclosed : D.VisiblyClosed) :
    ¬ D.QuasiStochastic := by
  intro hquasi

  exact
    (D.not_visiblyClosed_of_quasiStochastic hquasi)
      hclosed

/--
Quasi-stochasticity does not mean that complete evolution is
multivalued. Every complete state still has exactly one successor,
because `completeStep` is a function.
-/
theorem complete_successor_exists_unique
    (x : Complete) :
    ∃ y : Complete,
      y = D.completeStep x ∧
      ∀ z : Complete,
        z = D.completeStep x →
        z = y := by
  refine ⟨D.completeStep x, rfl, ?_⟩
  intro z hz
  exact hz

end ProjectionDynamics

end KTLean
