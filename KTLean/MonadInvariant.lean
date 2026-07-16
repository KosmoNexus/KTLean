import KTLean.MonadAction

/-!
# Monad invariants

A complete monad contains both a glyph and one realized walk state.
A physical substrate statement may not depend on a preferred
trivialization of that monad.

This module separates three kinds of construction:

1. invariant predicates;
2. invariant scalar observables;
3. equivariant, frame-covariant observables.

Invariant outputs are unchanged by substrate-frame transport.
Equivariant outputs may change, but only according to an explicitly
declared action on their codomain.
-/

namespace KTLean

universe u v w

namespace MonadInvariant

variable
  {Frame : Type u}
  [Group Frame]

variable
  (A : MonadAction.FrameAction Frame)

/-!
## Invariant predicates
-/

/--
A predicate on complete monads is invariant when its truth value is
unchanged by every lawful substrate-frame transformation.
-/
def InvariantPredicate
    (P : KTMonad.Monad → Prop) :
    Prop :=

  ∀
    (frame : Frame)
    (monad : KTMonad.Monad),
      P monad ↔
        P (A.act frame monad)

/--
The always-true predicate is invariant.
-/
theorem invariantPredicate_true :

    InvariantPredicate A
      (fun _monad => True) := by

  intro frame monad

  constructor

  · intro _
    trivial

  · intro _
    trivial

/--
The always-false predicate is invariant.
-/
theorem invariantPredicate_false :

    InvariantPredicate A
      (fun _monad => False) := by

  intro frame monad

  constructor

  · intro h
    exact h

  · intro h
    exact h

/--
Conjunction preserves monad invariance.
-/
theorem InvariantPredicate.and
    {P Q : KTMonad.Monad → Prop}
    (hP : InvariantPredicate A P)
    (hQ : InvariantPredicate A Q) :

    InvariantPredicate A
      (fun monad =>
        P monad ∧ Q monad) := by

  intro frame monad

  constructor

  · intro h

    exact
      ⟨
        (hP frame monad).mp h.1,
        (hQ frame monad).mp h.2
      ⟩

  · intro h

    exact
      ⟨
        (hP frame monad).mpr h.1,
        (hQ frame monad).mpr h.2
      ⟩

/--
Disjunction preserves monad invariance.
-/
theorem InvariantPredicate.or
    {P Q : KTMonad.Monad → Prop}
    (hP : InvariantPredicate A P)
    (hQ : InvariantPredicate A Q) :

    InvariantPredicate A
      (fun monad =>
        P monad ∨ Q monad) := by

  intro frame monad

  constructor

  · intro h

    cases h with

    | inl hleft =>
        exact
          Or.inl
            ((hP frame monad).mp hleft)

    | inr hright =>
        exact
          Or.inr
            ((hQ frame monad).mp hright)

  · intro h

    cases h with

    | inl hleft =>
        exact
          Or.inl
            ((hP frame monad).mpr hleft)

    | inr hright =>
        exact
          Or.inr
            ((hQ frame monad).mpr hright)

/--
Negation preserves monad invariance.
-/
theorem InvariantPredicate.not
    {P : KTMonad.Monad → Prop}
    (hP : InvariantPredicate A P) :

    InvariantPredicate A
      (fun monad =>
        ¬ P monad) := by

  intro frame monad

  constructor

  · intro hnot htransported

    exact
      hnot
        ((hP frame monad).mpr htransported)

  · intro hnot horiginal

    exact
      hnot
        ((hP frame monad).mp horiginal)

/--
Implication between invariant predicates is invariant.
-/
theorem InvariantPredicate.imp
    {P Q : KTMonad.Monad → Prop}
    (hP : InvariantPredicate A P)
    (hQ : InvariantPredicate A Q) :

    InvariantPredicate A
      (fun monad =>
        P monad → Q monad) := by

  intro frame monad

  constructor

  · intro himp hPtransported

    have hPoriginal :
        P monad :=
      (hP frame monad).mpr hPtransported

    have hQoriginal :
        Q monad :=
      himp hPoriginal

    exact
      (hQ frame monad).mp hQoriginal

  · intro himp hPoriginal

    have hPtransported :
        P (A.act frame monad) :=
      (hP frame monad).mp hPoriginal

    have hQtransported :
        Q (A.act frame monad) :=
      himp hPtransported

    exact
      (hQ frame monad).mpr hQtransported

/--
Bi-implication between invariant predicates is invariant.
-/
theorem InvariantPredicate.iff
    {P Q : KTMonad.Monad → Prop}
    (hP : InvariantPredicate A P)
    (hQ : InvariantPredicate A Q) :

    InvariantPredicate A
      (fun monad =>
        P monad ↔ Q monad) := by

  intro frame monad

  constructor

  · intro hiff

    constructor

    · intro hPtransported

      have hPoriginal :
          P monad :=
        (hP frame monad).mpr hPtransported

      have hQoriginal :
          Q monad :=
        hiff.mp hPoriginal

      exact
        (hQ frame monad).mp hQoriginal

    · intro hQtransported

      have hQoriginal :
          Q monad :=
        (hQ frame monad).mpr hQtransported

      have hPoriginal :
          P monad :=
        hiff.mpr hQoriginal

      exact
        (hP frame monad).mp hPoriginal

  · intro hiff

    constructor

    · intro hPoriginal

      have hPtransported :
          P (A.act frame monad) :=
        (hP frame monad).mp hPoriginal

      have hQtransported :
          Q (A.act frame monad) :=
        hiff.mp hPtransported

      exact
        (hQ frame monad).mpr hQtransported

    · intro hQoriginal

      have hQtransported :
          Q (A.act frame monad) :=
        (hQ frame monad).mp hQoriginal

      have hPtransported :
          P (A.act frame monad) :=
        hiff.mpr hQtransported

      exact
        (hP frame monad).mpr hPtransported

/-!
## Invariant scalar observables
-/

/--
A scalar observable is invariant when every lawful frame transformation
leaves its value unchanged.
-/
def InvariantObservable
    {Value : Type v}
    (observable :
      KTMonad.Monad → Value) :
    Prop :=

  ∀
    (frame : Frame)
    (monad : KTMonad.Monad),
      observable (A.act frame monad) =
        observable monad

/--
Every constant observable is invariant.
-/
theorem invariantObservable_const
    {Value : Type v}
    (value : Value) :

    InvariantObservable A
      (fun _monad => value) := by

  intro frame monad

  rfl

/--
Postcomposition preserves invariance.

A frame-invariant substrate quantity remains invariant after any
deterministic reinterpretation of its value.
-/
theorem InvariantObservable.comp
    {Value : Type v}
    {Output : Type w}
    {observable :
      KTMonad.Monad → Value}
    (hinvariant :
      InvariantObservable A observable)
    (transform :
      Value → Output) :

    InvariantObservable A
      (fun monad =>
        transform (observable monad)) := by

  intro frame monad

  exact
    congrArg transform
      (hinvariant frame monad)

/--
Pairs of invariant observables are invariant.
-/
theorem InvariantObservable.prod
    {Left : Type v}
    {Right : Type w}
    {left :
      KTMonad.Monad → Left}
    {right :
      KTMonad.Monad → Right}
    (hleft :
      InvariantObservable A left)
    (hright :
      InvariantObservable A right) :

    InvariantObservable A
      (fun monad =>
        (left monad, right monad)) := by

  intro frame monad

  apply Prod.ext

  · exact
      hleft frame monad

  · exact
      hright frame monad

/--
Equality of two invariant observables defines an invariant predicate.
-/
theorem invariantPredicate_eq
    {Value : Type v}
    {left right :
      KTMonad.Monad → Value}
    (hleft :
      InvariantObservable A left)
    (hright :
      InvariantObservable A right) :

    InvariantPredicate A
      (fun monad =>
        left monad = right monad) := by

  intro frame monad

  constructor

  · intro heq

    calc
      left (A.act frame monad) =
          left monad := by
            exact hleft frame monad

      _ = right monad := heq

      _ = right (A.act frame monad) := by
            exact
              (hright frame monad).symm

  · intro heq

    calc
      left monad =
          left (A.act frame monad) := by
            exact
              (hleft frame monad).symm

      _ = right (A.act frame monad) := heq

      _ = right monad := by
            exact hright frame monad

/--
Pulling a predicate back along an invariant observable produces an
invariant monad predicate.
-/
theorem invariantPredicate_of_observable
    {Value : Type v}
    {observable :
      KTMonad.Monad → Value}
    (hinvariant :
      InvariantObservable A observable)
    (P : Value → Prop) :

    InvariantPredicate A
      (fun monad =>
        P (observable monad)) := by

  intro frame monad

  change
    P (observable monad) ↔
      P (observable (A.act frame monad))

  rw [hinvariant frame monad]

/-!
## Equivariant observables
-/

/--
An observable is equivariant when transporting the input monad is
equivalent to transporting the output by an explicitly declared
codomain action.

This is the lawful alternative to scalar invariance for quantities that
carry frame-dependent components.
-/
def EquivariantObservable
    {Value : Type v}
    (actValue :
      Frame → Value → Value)
    (observable :
      KTMonad.Monad → Value) :
    Prop :=

  ∀
    (frame : Frame)
    (monad : KTMonad.Monad),
      observable (A.act frame monad) =
        actValue frame (observable monad)

/--
Invariant observables are equivariant under the trivial action on their
codomain.
-/
theorem InvariantObservable.equivariant_trivial
    {Value : Type v}
    {observable :
      KTMonad.Monad → Value}
    (hinvariant :
      InvariantObservable A observable) :

    EquivariantObservable A
      (fun _frame value => value)
      observable := by

  intro frame monad

  exact
    hinvariant frame monad

/--
Equivariance is preserved by a map that intertwines the two codomain
actions.
-/
theorem EquivariantObservable.comp
    {Value : Type v}
    {Output : Type w}
    {actValue :
      Frame → Value → Value}
    {actOutput :
      Frame → Output → Output}
    {observable :
      KTMonad.Monad → Value}
    (hequivariant :
      EquivariantObservable A
        actValue
        observable)
    (transform :
      Value → Output)
    (hintertwines :
      ∀
        (frame : Frame)
        (value : Value),
          transform (actValue frame value) =
            actOutput frame (transform value)) :

    EquivariantObservable A
      actOutput
      (fun monad =>
        transform (observable monad)) := by

  intro frame monad

  calc
    transform
        (observable (A.act frame monad)) =
      transform
        (actValue frame
          (observable monad)) := by
            exact
              congrArg transform
                (hequivariant frame monad)

    _ =
      actOutput frame
        (transform (observable monad)) := by
          exact
            hintertwines
              frame
              (observable monad)

/--
The identity map from monads to monads is equivariant under the given
frame action.
-/
theorem equivariantObservable_identity :

    EquivariantObservable A
      A.act
      (fun monad : KTMonad.Monad =>
        monad) := by

  intro frame monad

  rfl

/-!
## Physical admissibility
-/

/--
A scalar monad observable is physically admissible at the substrate
level precisely when it is invariant under every lawful frame
transformation.

This name records the zero-preferred-frame build principle.
-/
abbrev PhysicallyAdmissible
    {Value : Type v}
    (observable :
      KTMonad.Monad → Value) :
    Prop :=

  InvariantObservable A observable

/--
Physical admissibility is preserved under deterministic
postprocessing.
-/
theorem PhysicallyAdmissible.comp
    {Value : Type v}
    {Output : Type w}
    {observable :
      KTMonad.Monad → Value}
    (hadmissible :
      PhysicallyAdmissible A observable)
    (transform :
      Value → Output) :

    PhysicallyAdmissible A
      (fun monad =>
        transform (observable monad)) := by

  exact
    InvariantObservable.comp
      A
      hadmissible
      transform

end MonadInvariant
end KTLean
