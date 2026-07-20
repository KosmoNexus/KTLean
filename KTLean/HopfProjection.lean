import KTLean.SpinorClosure
import Mathlib.Tactic.Linarith

/-!
# Hopf Projection of Normalized Spinors

This module formalizes the visible spin-direction projection from a
normalized two-component complex spinor.

## Formal status

**Level 2 — Geometric reconstruction.**

For a spinor

    ψ = (α, β),

the Hopf coordinates are

    x = 2 Re(α * conj β),
    y = 2 Im(α * conj β),
    z = |α|² - |β|².

In real component coordinates

    α = a + b i,
    β = c + d i,

this becomes

    x = 2(ac + bd),
    y = 2(bc - ad),
    z = a² + b² - c² - d².

The central identity proved here is

    x² + y² + z² = (|α|² + |β|²)².

Consequently, a normalized spinor on S³ projects to a point on S².

This file proves:

- the algebraic Hopf identity;
- projection of normalized spinors from S³ to S²;
- preservation of normalization under common unit phase;
- invariance of the Hopf projection under common U(1) phase.

It does not yet prove:

- characterization of each fiber by phase equivalence;
- noninjectivity of the visible projection;
- identification of the phase fiber with memory escrow.
-/

namespace HopfProjection

/--
Three real coordinates carrying the visible spin direction.
-/

structure RealThree where
  x : ℝ
  y : ℝ
  z : ℝ

theorem RealThree.ext
    {p q : RealThree}
    (hx : p.x = q.x)
    (hy : p.y = q.y)
    (hz : p.z = q.z) :
    p = q := by

  cases p
  cases q
  cases hx
  cases hy
  cases hz
  rfl


/--
Squared Euclidean radius in three real coordinates.
-/
def RealThree.radiusSq
    (p : RealThree) :
    ℝ :=
  p.x ^ 2 +
    p.y ^ 2 +
    p.z ^ 2

/--
The unit two-sphere as the unit-radius locus in real
three-dimensional coordinates.
-/
abbrev UnitTwoSphere :=
  { p : RealThree // p.radiusSq = 1 }

/--
The Hopf coordinates of an arbitrary two-component complex spinor.

The coordinate convention agrees with `SpinorClosure.toRealFour`:

    α = a + b i,
    β = c + d i.
-/
def hopfCoordinates
    (ψ : SpinorClosure.WeylSpinor) :
    RealThree where

  x :=
    2 *
      (
        ψ.upper.re * ψ.lower.re +
          ψ.upper.im * ψ.lower.im
      )

  y :=
    2 *
      (
        ψ.upper.im * ψ.lower.re -
          ψ.upper.re * ψ.lower.im
      )

  z :=
    Complex.normSq ψ.upper -
      Complex.normSq ψ.lower

@[simp]
theorem hopfCoordinates_x
    (ψ : SpinorClosure.WeylSpinor) :
    (hopfCoordinates ψ).x =
      2 *
        (
          ψ.upper.re * ψ.lower.re +
            ψ.upper.im * ψ.lower.im
        ) := by
  rfl

@[simp]
theorem hopfCoordinates_y
    (ψ : SpinorClosure.WeylSpinor) :
    (hopfCoordinates ψ).y =
      2 *
        (
          ψ.upper.im * ψ.lower.re -
            ψ.upper.re * ψ.lower.im
        ) := by
  rfl

@[simp]
theorem hopfCoordinates_z
    (ψ : SpinorClosure.WeylSpinor) :
    (hopfCoordinates ψ).z =
      Complex.normSq ψ.upper -
        Complex.normSq ψ.lower := by
  rfl

/--
The algebraic Hopf identity:

    |Hopf(ψ)|² = |ψ|⁴.

This is a polynomial identity in the four real spinor coordinates.
-/
theorem radiusSq_hopfCoordinates
    (ψ : SpinorClosure.WeylSpinor) :
    (hopfCoordinates ψ).radiusSq =
      SpinorClosure.normSq ψ ^ 2 := by

  simp [
    RealThree.radiusSq,
    hopfCoordinates,
    SpinorClosure.normSq,
    Complex.normSq,
    pow_two
  ]

  ring

/--
The Hopf visible projection from normalized spinors to the unit
two-sphere.
-/
def hopfVisible
    (ψ : SpinorClosure.NormalizedSpinor) :
    UnitTwoSphere :=

  ⟨
    hopfCoordinates ψ.1,
    by
      rw [radiusSq_hopfCoordinates]
      rw [ψ.2]
      norm_num
  ⟩

@[simp]
theorem hopfVisible_coordinates
    (ψ : SpinorClosure.NormalizedSpinor) :
    (hopfVisible ψ).1 =
      hopfCoordinates ψ.1 := by
  rfl

/--
Every normalized spinor has a visible Hopf image on the unit
two-sphere.
-/
theorem hopfVisible_radiusSq
    (ψ : SpinorClosure.NormalizedSpinor) :
    (hopfVisible ψ).1.radiusSq = 1 := by
  exact (hopfVisible ψ).2

end HopfProjection

#check HopfProjection.RealThree
#check HopfProjection.UnitTwoSphere
#check HopfProjection.hopfCoordinates
#check HopfProjection.radiusSq_hopfCoordinates
#check HopfProjection.hopfVisible

namespace HopfProjection

/-!
## HP1: Common phase action
-/

/--
A unit complex phase.

The condition `Complex.normSq u = 1` is the algebraic form of
membership in `U(1)`.
-/
abbrev UnitPhase :=
  { u : ℂ // Complex.normSq u = 1 }

/--
Apply the same complex phase to both components of a spinor.
-/
def phaseAct
    (u : UnitPhase)
    (ψ : SpinorClosure.WeylSpinor) :
    SpinorClosure.WeylSpinor where

  upper :=
    u.1 * ψ.upper

  lower :=
    u.1 * ψ.lower

/--
A common unit phase preserves the spinor norm-square.
-/
theorem normSq_phaseAct
    (u : UnitPhase)
    (ψ : SpinorClosure.WeylSpinor) :
    SpinorClosure.normSq (phaseAct u ψ) =
      SpinorClosure.normSq ψ := by

  simp [
    phaseAct,
    SpinorClosure.normSq,
    Complex.normSq_mul,
    u.2
  ]

/--
A common unit phase therefore acts on normalized spinors.
-/
def phaseActNormalized
    (u : UnitPhase)
    (ψ : SpinorClosure.NormalizedSpinor) :
    SpinorClosure.NormalizedSpinor :=

  ⟨
    phaseAct u ψ.1,
    by
      rw [normSq_phaseAct]
      exact ψ.2
  ⟩

/--
The Hopf coordinates are invariant under a common unit complex phase.

This is the algebraic statement that overall phase is invisible under
the Hopf projection.
-/
theorem hopfCoordinates_phaseAct
    (u : UnitPhase)
    (ψ : SpinorClosure.WeylSpinor) :
    hopfCoordinates (phaseAct u ψ) =
      hopfCoordinates ψ := by

  have hu :
      u.1.re ^ 2 + u.1.im ^ 2 = 1 := by
    simpa [
      Complex.normSq_apply,
      pow_two
    ] using u.2

  have hx :
      u.1.re ^ 2 * ψ.upper.re * ψ.lower.re +
          u.1.re ^ 2 * ψ.upper.im * ψ.lower.im +
          ψ.upper.re * u.1.im ^ 2 * ψ.lower.re +
          u.1.im ^ 2 * ψ.upper.im * ψ.lower.im
        =
      ψ.upper.re * ψ.lower.re +
        ψ.upper.im * ψ.lower.im := by

    calc
      u.1.re ^ 2 * ψ.upper.re * ψ.lower.re +
            u.1.re ^ 2 * ψ.upper.im * ψ.lower.im +
            ψ.upper.re * u.1.im ^ 2 * ψ.lower.re +
            u.1.im ^ 2 * ψ.upper.im * ψ.lower.im
          =
        (u.1.re ^ 2 + u.1.im ^ 2) *
          (
            ψ.upper.re * ψ.lower.re +
              ψ.upper.im * ψ.lower.im
          ) := by
            ring

      _ =
        1 *
          (
            ψ.upper.re * ψ.lower.re +
              ψ.upper.im * ψ.lower.im
          ) := by
            rw [hu]

      _ =
        ψ.upper.re * ψ.lower.re +
          ψ.upper.im * ψ.lower.im := by
            ring

  have hy :
      u.1.re ^ 2 * ψ.upper.im * ψ.lower.re -
          u.1.re ^ 2 * ψ.upper.re * ψ.lower.im +
          ψ.upper.im * u.1.im ^ 2 * ψ.lower.re -
          u.1.im ^ 2 * ψ.upper.re * ψ.lower.im
        =
      ψ.upper.im * ψ.lower.re -
        ψ.upper.re * ψ.lower.im := by

    calc
      u.1.re ^ 2 * ψ.upper.im * ψ.lower.re -
            u.1.re ^ 2 * ψ.upper.re * ψ.lower.im +
            ψ.upper.im * u.1.im ^ 2 * ψ.lower.re -
            u.1.im ^ 2 * ψ.upper.re * ψ.lower.im
          =
        (u.1.re ^ 2 + u.1.im ^ 2) *
          (
            ψ.upper.im * ψ.lower.re -
              ψ.upper.re * ψ.lower.im
          ) := by
            ring

      _ =
        1 *
          (
            ψ.upper.im * ψ.lower.re -
              ψ.upper.re * ψ.lower.im
          ) := by
            rw [hu]

      _ =
        ψ.upper.im * ψ.lower.re -
          ψ.upper.re * ψ.lower.im := by
            ring

  apply RealThree.ext

  · simp [
      hopfCoordinates,
      phaseAct,
      Complex.mul_re,
      Complex.mul_im
    ]
    nlinarith [hu, hx]

  · simp [
      hopfCoordinates,
      phaseAct,
      Complex.mul_re,
      Complex.mul_im
    ]
    nlinarith [hu, hy]

  · simp [
      hopfCoordinates,
      phaseAct,
      Complex.normSq_mul,
      u.2
    ]

/--
The visible spin direction is unchanged by a common unit phase.
-/
theorem hopfVisible_phaseAct
    (u : UnitPhase)
    (ψ : SpinorClosure.NormalizedSpinor) :
    hopfVisible (phaseActNormalized u ψ) =
      hopfVisible ψ := by

  apply Subtype.ext

  exact
    hopfCoordinates_phaseAct
      u
      ψ.1

end HopfProjection

#check HopfProjection.UnitPhase
#check HopfProjection.phaseAct
#check HopfProjection.normSq_phaseAct
#check HopfProjection.phaseActNormalized
#check HopfProjection.hopfCoordinates_phaseAct
#check HopfProjection.hopfVisible_phaseAct
