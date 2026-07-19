import Mathlib.Data.Complex.Basic

/-!
# Spinor Closure

This module begins the formal study of two-component complex spinors
as candidate state spaces for primitive KT closure paths.

## Formal status

**Level 1 — Encoding, with elementary reconstruction.**

This module defines:

- a two-component complex spinor;
- its squared norm;
- normalized spinors;
- its four real coordinates;
- the unit-three-sphere equation in those coordinates.

It does not yet prove:

- that a primitive KT path is necessarily spinorial;
- that its canonical geometric measure is `2 * π^2`;
- that seven such paths are forced.

Those remain separate obligations.
-/

namespace SpinorClosure

/--
A two-component complex spinor.

No chirality convention is imposed at this level.
-/
structure WeylSpinor where
  upper : ℂ
  lower : ℂ

/--
The squared norm of a two-component complex spinor.
-/
def normSq
    (ψ : WeylSpinor) :
    ℝ :=
  Complex.normSq ψ.upper +
    Complex.normSq ψ.lower

/--
A normalized two-component spinor.
-/
abbrev NormalizedSpinor :=
  { ψ : WeylSpinor // normSq ψ = 1 }

/--
The four real coordinates carried by a two-component complex spinor.
-/
structure RealFour where
  x₀ : ℝ
  x₁ : ℝ
  x₂ : ℝ
  x₃ : ℝ

/--
The real-coordinate representation of a two-component complex spinor.
-/
def toRealFour
    (ψ : WeylSpinor) :
    RealFour where
  x₀ := ψ.upper.re
  x₁ := ψ.upper.im
  x₂ := ψ.lower.re
  x₃ := ψ.lower.im

/--
The squared Euclidean radius in four real coordinates.
-/
def RealFour.radiusSq
    (x : RealFour) :
    ℝ :=
  x.x₀ ^ 2 +
    x.x₁ ^ 2 +
    x.x₂ ^ 2 +
    x.x₃ ^ 2

/--
The unit three-sphere represented as the unit-radius locus in four real
coordinates.
-/
abbrev UnitThreeSphere :=
  { x : RealFour // x.radiusSq = 1 }

/--
The spinor squared norm agrees with the squared Euclidean radius of its
four real coordinates.
-/
theorem radiusSq_toRealFour
    (ψ : WeylSpinor) :
    (toRealFour ψ).radiusSq =
      normSq ψ := by

  simp [
    RealFour.radiusSq,
    toRealFour,
    normSq,
    Complex.normSq,
    pow_two,
    add_assoc
  ]

/--
Every normalized spinor determines a point on the unit three-sphere.
-/
def normalizedToSphere
    (ψ : NormalizedSpinor) :
    UnitThreeSphere :=

  ⟨
    toRealFour ψ.1,
    by
      rw [radiusSq_toRealFour]
      exact ψ.2
  ⟩

@[simp]
theorem normalizedToSphere_coordinates
    (ψ : NormalizedSpinor) :
    (normalizedToSphere ψ).1 =
      toRealFour ψ.1 := by
  rfl

/--
Normalization of a two-component complex spinor is exactly the
unit-three-sphere equation in its four real coordinates.
-/
theorem normalized_iff_on_unitThreeSphere
    (ψ : WeylSpinor) :
    normSq ψ = 1
      ↔
    (toRealFour ψ).radiusSq = 1 := by

  rw [radiusSq_toRealFour]

end SpinorClosure

#check SpinorClosure.WeylSpinor
#check SpinorClosure.NormalizedSpinor
#check SpinorClosure.UnitThreeSphere
#check SpinorClosure.normalizedToSphere
#check SpinorClosure.normalized_iff_on_unitThreeSphere
