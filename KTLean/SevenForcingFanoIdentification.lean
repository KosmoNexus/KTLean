import KTLean.SevenForcingFanoFrameCanonicalTable
import KTLean.Fano
import Mathlib.Tactic.FinCases

/-!
# Identification of the Forced Seven-Point System with the Fano Plane

## Formal status

**Level 2 — Consequence of global triadic closure, nondegeneracy,
minimal seven-point cardinality, and a selected noncollinear frame.**

The forced canonical positions are

    x = first
    y = second
    z = lineThird
    p = external
    a = firstExternalThird
    b = secondExternalThird
    c = lineThirdExternalThird.

We identify them with the explicit Fano coordinates by

    x ↦ 0
    y ↦ 1
    z ↦ 3
    p ↦ 2
    a ↦ 6
    b ↦ 4
    c ↦ 5.

This coordinate assignment sends the seven forced canonical lines

    {x,y,z}
    {x,p,a}
    {y,p,b}
    {z,p,c}
    {x,b,c}
    {y,a,c}
    {z,a,b}

to the seven lines of the explicit `Fano.system`.

The identification is proved to be an equivalence and to preserve the
complete Steiner operation on every ordered pair.
-/

namespace SevenForcingFanoIdentification

noncomputable section

open SevenForcingFanoFrameCanonicalInjective
open SevenForcingFanoFrameCanonicalTable

/--
The forced canonical positions expressed in the explicit coordinates
of `Fano.Point = Fin 7`.
-/
def canonicalPositionToFano :
    CanonicalPosition →
      Fano.Point

  | CanonicalPosition.first =>
      0

  | CanonicalPosition.second =>
      1

  | CanonicalPosition.lineThird =>
      3

  | CanonicalPosition.external =>
      2

  | CanonicalPosition.firstExternalThird =>
      6

  | CanonicalPosition.secondExternalThird =>
      4

  | CanonicalPosition.lineThirdExternalThird =>
      5

/--
The canonical-to-Fano coordinate map is injective.
-/
theorem canonicalPositionToFano_injective :
    Function.Injective
      canonicalPositionToFano := by

  intro firstPosition secondPosition h

  cases firstPosition <;>
    cases secondPosition <;>
    simp_all [canonicalPositionToFano]

/--
The canonical-to-Fano coordinate map is surjective.
-/
theorem canonicalPositionToFano_surjective :
    Function.Surjective
      canonicalPositionToFano := by

  intro point

  fin_cases point

  · exact
      ⟨
        CanonicalPosition.first,
        rfl
      ⟩

  · exact
      ⟨
        CanonicalPosition.second,
        rfl
      ⟩

  · exact
      ⟨
        CanonicalPosition.external,
        rfl
      ⟩

  · exact
      ⟨
        CanonicalPosition.lineThird,
        rfl
      ⟩

  · exact
      ⟨
        CanonicalPosition.secondExternalThird,
        rfl
      ⟩

  · exact
      ⟨
        CanonicalPosition.lineThirdExternalThird,
        rfl
      ⟩

  · exact
      ⟨
        CanonicalPosition.firstExternalThird,
        rfl
      ⟩

/--
The canonical-to-Fano coordinate map is bijective.
-/
theorem canonicalPositionToFano_bijective :
    Function.Bijective
      canonicalPositionToFano :=

  ⟨
    canonicalPositionToFano_injective,
    canonicalPositionToFano_surjective
  ⟩

/--
The seven forced canonical positions are equivalent to the seven
points of the explicit Fano plane.
-/
def canonicalPositionEquivFano :
    CanonicalPosition ≃
      Fano.Point :=

  Equiv.ofBijective
    canonicalPositionToFano
    canonicalPositionToFano_bijective

/--
The forward map of the canonical-to-Fano equivalence is the explicit
coordinate assignment.
-/
@[simp]
theorem canonicalPositionEquivFano_apply
    (position : CanonicalPosition) :
    canonicalPositionEquivFano position =
      canonicalPositionToFano position := by

  rfl

/--
The forced canonical completion table is transported exactly to the
explicit Fano completion operation.
-/
theorem canonicalPositionToFano_preserves_complete
    (firstPosition secondPosition : CanonicalPosition) :
    canonicalPositionToFano
        (
          canonicalCompletionTable
            firstPosition
            secondPosition
        ) =
      Fano.system.complete
        (canonicalPositionToFano firstPosition)
        (canonicalPositionToFano secondPosition) := by

  cases firstPosition <;>
    cases secondPosition <;>
    decide

/--
The canonical-position equivalence preserves completion.
-/
theorem canonicalPositionEquivFano_preserves_complete
    (firstPosition secondPosition : CanonicalPosition) :
    canonicalPositionEquivFano
        (
          forcedCanonicalSystem.complete
            firstPosition
            secondPosition
        ) =
      Fano.system.complete
        (canonicalPositionEquivFano firstPosition)
        (canonicalPositionEquivFano secondPosition) := by

  exact
    canonicalPositionToFano_preserves_complete
      firstPosition
      secondPosition

/--
The inverse Fano coordinate map sends `0` to `first`.
-/
@[simp]
theorem canonicalPositionEquivFano_symm_zero :
    canonicalPositionEquivFano.symm 0 =
      CanonicalPosition.first := by

  apply canonicalPositionEquivFano.injective

  simp [canonicalPositionEquivFano_apply, canonicalPositionToFano]

/--
The inverse Fano coordinate map sends `1` to `second`.
-/
@[simp]
theorem canonicalPositionEquivFano_symm_one :
    canonicalPositionEquivFano.symm 1 =
      CanonicalPosition.second := by

  apply canonicalPositionEquivFano.injective

  simp [canonicalPositionEquivFano_apply, canonicalPositionToFano]

/--
The inverse Fano coordinate map sends `2` to `external`.
-/
@[simp]
theorem canonicalPositionEquivFano_symm_two :
    canonicalPositionEquivFano.symm 2 =
      CanonicalPosition.external := by

  apply canonicalPositionEquivFano.injective

  simp [canonicalPositionEquivFano_apply, canonicalPositionToFano]

/--
The inverse Fano coordinate map sends `3` to `lineThird`.
-/
@[simp]
theorem canonicalPositionEquivFano_symm_three :
    canonicalPositionEquivFano.symm 3 =
      CanonicalPosition.lineThird := by

  apply canonicalPositionEquivFano.injective

  simp [canonicalPositionEquivFano_apply, canonicalPositionToFano]

/--
The inverse Fano coordinate map sends `4` to
`secondExternalThird`.
-/
@[simp]
theorem canonicalPositionEquivFano_symm_four :
    canonicalPositionEquivFano.symm 4 =
      CanonicalPosition.secondExternalThird := by

  apply canonicalPositionEquivFano.injective

  simp [canonicalPositionEquivFano_apply, canonicalPositionToFano]

/--
The inverse Fano coordinate map sends `5` to
`lineThirdExternalThird`.
-/
@[simp]
theorem canonicalPositionEquivFano_symm_five :
    canonicalPositionEquivFano.symm 5 =
      CanonicalPosition.lineThirdExternalThird := by

  apply canonicalPositionEquivFano.injective

  simp [canonicalPositionEquivFano_apply, canonicalPositionToFano]

/--
The inverse Fano coordinate map sends `6` to
`firstExternalThird`.
-/
@[simp]
theorem canonicalPositionEquivFano_symm_six :
    canonicalPositionEquivFano.symm 6 =
      CanonicalPosition.firstExternalThird := by

  apply canonicalPositionEquivFano.injective

  simp [canonicalPositionEquivFano_apply, canonicalPositionToFano]

end

end SevenForcingFanoIdentification

#check SevenForcingFanoIdentification.canonicalPositionToFano
#check SevenForcingFanoIdentification.canonicalPositionToFano_injective
#check SevenForcingFanoIdentification.canonicalPositionToFano_surjective
#check SevenForcingFanoIdentification.canonicalPositionEquivFano
#check SevenForcingFanoIdentification.canonicalPositionToFano_preserves_complete
#check SevenForcingFanoIdentification.canonicalPositionEquivFano_preserves_complete
#check SevenForcingFanoIdentification.canonicalPositionEquivFano_symm_zero
#check SevenForcingFanoIdentification.canonicalPositionEquivFano_symm_six
