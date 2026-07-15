import KTLean.MeasurementRefinement

namespace KTLean

universe u v w

/--
A `ContextualView` assigns a local observation map to each measurement
context.

Changing context changes how the same complete state is read. It does
not, by itself, imply any change in the complete state.
-/
structure ContextualView
    (Complete : Type u)
    (Context : Type v)
    (Visible : Type w) where

  observe :
    Context → Complete → Visible

namespace ContextualView

variable {Complete : Type u}
variable {Context : Type v}
variable {Visible : Type w}

variable (C : ContextualView Complete Context Visible)

/--
The local view selected by a particular context.
-/
def localView
    (context : Context) :
    LocalView Complete Visible where
  observe := C.observe context

/--
Two complete states are observationally equivalent relative to a chosen
measurement context.
-/
def EquivalentAt
    (context : Context)
    (x y : Complete) : Prop :=
  C.observe context x =
    C.observe context y

/--
Two complete states are distinguishable relative to a chosen
measurement context.
-/
def DistinguishableAt
    (context : Context)
    (x y : Complete) : Prop :=
  C.observe context x ≠
    C.observe context y

/--
Observational equivalence at a fixed context is reflexive.
-/
theorem equivalentAt_refl
    (context : Context)
    (x : Complete) :
    C.EquivalentAt context x x := by
  rfl

/--
Observational equivalence at a fixed context is symmetric.
-/
theorem equivalentAt_symm
    (context : Context)
    {x y : Complete}
    (h : C.EquivalentAt context x y) :
    C.EquivalentAt context y x := by
  exact h.symm

/--
Observational equivalence at a fixed context is transitive.
-/
theorem equivalentAt_trans
    (context : Context)
    {x y z : Complete}
    (hxy : C.EquivalentAt context x y)
    (hyz : C.EquivalentAt context y z) :
    C.EquivalentAt context x z := by
  exact hxy.trans hyz

/--
The same complete state may yield different visible values under
different measurement contexts.
-/
def ContextSensitive
    (x : Complete) : Prop :=
  ∃ context₁ context₂ : Context,
    C.observe context₁ x ≠
      C.observe context₂ x

/--
A context change compares two readings of one unchanged complete state.
-/
def ContextChange
    (context₁ context₂ : Context)
    (x : Complete) :
    Visible × Visible :=
  (C.observe context₁ x,
   C.observe context₂ x)

/--
The first component of a context change is the observation in the first
context.
-/
theorem contextChange_fst
    (context₁ context₂ : Context)
    (x : Complete) :
    (C.ContextChange context₁ context₂ x).1 =
      C.observe context₁ x := by
  rfl

/--
The second component of a context change is the observation in the
second context.
-/
theorem contextChange_snd
    (context₁ context₂ : Context)
    (x : Complete) :
    (C.ContextChange context₁ context₂ x).2 =
      C.observe context₂ x := by
  rfl

/--
Changing measurement context alone requires no complete-state
transition.
-/
theorem context_change_preserves_complete_state
    (_context₁ _context₂ : Context)
    (x : Complete) :
    x = x := by
  rfl

/--
Contextual sensitivity means that one unchanged complete state has at
least two distinct visible readings.
-/
theorem contextSensitive_iff
    (x : Complete) :
    C.ContextSensitive x ↔
      ∃ context₁ context₂ : Context,
        C.observe context₁ x ≠
          C.observe context₂ x := by
  rfl

/--
Two contexts are observationally equivalent when they give the same
result on every complete state.
-/
def ContextEquivalent
    (context₁ context₂ : Context) : Prop :=
  ∀ x : Complete,
    C.observe context₁ x =
      C.observe context₂ x

/--
Context equivalence is reflexive.
-/
theorem contextEquivalent_refl
    (context : Context) :
    C.ContextEquivalent context context := by
  intro x
  rfl

/--
Context equivalence is symmetric.
-/
theorem contextEquivalent_symm
    {context₁ context₂ : Context}
    (h :
      C.ContextEquivalent context₁ context₂) :
    C.ContextEquivalent context₂ context₁ := by
  intro x
  exact (h x).symm

/--
Context equivalence is transitive.
-/
theorem contextEquivalent_trans
    {context₁ context₂ context₃ : Context}
    (h₁₂ :
      C.ContextEquivalent context₁ context₂)
    (h₂₃ :
      C.ContextEquivalent context₂ context₃) :
    C.ContextEquivalent context₁ context₃ := by
  intro x
  exact (h₁₂ x).trans (h₂₃ x)

/--
A pair of contexts is genuinely distinct observationally when some
complete state receives different readings in the two contexts.
-/
def ContextuallyDistinct
    (context₁ context₂ : Context) : Prop :=
  ∃ x : Complete,
    C.observe context₁ x ≠
      C.observe context₂ x

/--
Contextual distinction is incompatible with context equivalence.
-/
theorem not_contextEquivalent_of_contextuallyDistinct
    {context₁ context₂ : Context}
    (h :
      C.ContextuallyDistinct context₁ context₂) :
    ¬ C.ContextEquivalent context₁ context₂ := by
  intro heq
  rcases h with ⟨x, hx⟩
  exact hx (heq x)

/--
A contextually sensitive state witnesses that two contexts are
observationally distinct.
-/
theorem contextuallyDistinct_of_contextSensitive
    {x : Complete}
    (h : C.ContextSensitive x) :
    ∃ context₁ context₂ : Context,
      C.ContextuallyDistinct context₁ context₂ := by
  rcases h with ⟨context₁, context₂, hdiff⟩
  refine ⟨context₁, context₂, ?_⟩
  exact ⟨x, hdiff⟩

end ContextualView

end KTLean
