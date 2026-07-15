import Mathlib.Logic.Relation

namespace KTLean

universe u v

/--
A `LocalView Complete Visible` describes what a local observer can access
from a complete state.

The complete state is not assumed to be locally recoverable.
-/
structure LocalView (Complete : Type u) (Visible : Type v) where
  observe : Complete → Visible

namespace LocalView

variable {Complete : Type u}
variable {Visible : Type v}

variable {V : LocalView Complete Visible}

/--
Two complete states are observationally equivalent when they produce
the same local observation.
-/
def ObservationallyEquivalent (x y : Complete) : Prop :=
  V.observe x = V.observe y

@[refl]
theorem observationallyEquivalent_refl
    (x : Complete) :
    V.ObservationallyEquivalent x x := by
  rfl

@[symm]
theorem observationallyEquivalent_symm
    {x y : Complete}
    (h : V.ObservationallyEquivalent x y) :
    V.ObservationallyEquivalent y x := by
  exact h.symm

@[trans]
theorem observationallyEquivalent_trans
    {x y z : Complete}
    (hxy : V.ObservationallyEquivalent x y)
    (hyz : V.ObservationallyEquivalent y z) :
    V.ObservationallyEquivalent x z := by
  exact hxy.trans hyz



/--
Observational equivalence defines an equivalence relation on complete
states.
-/
instance observationalSetoid :
    Setoid Complete where
  r := V.ObservationallyEquivalent
  iseqv := by
    constructor
    · intro x
      exact V.observationallyEquivalent_refl x
    · intro x y hxy
      exact V.observationallyEquivalent_symm hxy
    · intro x y z hxy hyz
      exact V.observationallyEquivalent_trans hxy hyz


/--
Two complete states are locally distinguishable when their observations
differ.
-/
def Distinguishable (x y : Complete) : Prop :=
  ¬ V.ObservationallyEquivalent x y

theorem observationallyEquivalent_iff_observe_eq
    {x y : Complete} :
    V.ObservationallyEquivalent x y ↔
      V.observe x = V.observe y := by
  rfl

theorem distinguishable_iff_observe_ne
    {x y : Complete} :
    V.Distinguishable x y ↔
      V.observe x ≠ V.observe y := by
  rfl

theorem equal_states_observationallyEquivalent
    {x y : Complete}
    (h : x = y) :
    V.ObservationallyEquivalent x y := by
  subst y
  rfl

theorem distinguishable_symm
    {x y : Complete}
    (h : V.Distinguishable x y) :
    V.Distinguishable y x := by
  exact Ne.symm h

theorem not_distinguishable_self
    (x : Complete) :
    ¬ V.Distinguishable x x := by
  intro h
  exact h rfl

/--
The observational quotient identifies complete states that are
indistinguishable in the local frame.
-/
abbrev ObservationClass :=
  Quotient V.observationalSetoid

/--
The observational class represented by a complete state.
-/
def classOf (x : Complete) :
    V.ObservationClass :=
  Quotient.mk V.observationalSetoid x

theorem classOf_eq_iff
    {x y : Complete} :
    V.classOf x = V.classOf y ↔
      V.ObservationallyEquivalent x y := by
  exact Quotient.eq

end LocalView

end KTLean