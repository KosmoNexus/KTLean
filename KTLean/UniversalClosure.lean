import Mathlib

/-!
# Universal Closure

This module begins the formal study of global closure depth in KT.

## Formal status

**Level 1 — Encoding, with generic algebraic consequences.**

The core definitions in this module deliberately contain no reference
to:

- seven paths;
- forty-two glyphs;
- the Fano plane;
- octonions;
- the measured age of the universe;
- the observed value of the fine-structure constant.

Those quantities may enter only through later forcing theorems.

The foundational principle is that independent multiplicative
multiplicities become additive in logarithmic closure depth.
-/

namespace UniversalClosure

open scoped BigOperators

universe u

/--
Abstract data needed to assign a global closure depth.

`Path` is an arbitrary finite family of primitive closure paths.

Each path contributes a real-valued logarithmic closure measure.
The substrate may additionally contain a finite positive number of
disjoint but equivalent sectors.
-/
structure ClosureDatum
    (Path : Type u)
    [Fintype Path] where

  /--
  Logarithmic closure contribution associated with each primitive path.
  -/
  pathMeasure :
    Path → ℝ

  /--
  Number of equivalent substrate sectors contributing disjoint copies
  of the pathwise closure history.
  -/
  sectorMultiplicity :
    ℕ

  /--
  At least one substrate sector exists.
  -/
  sectorMultiplicity_pos :
    0 < sectorMultiplicity

/--
The total logarithmic contribution from all primitive paths.
-/
def totalPathMeasure
    {Path : Type u}
    [Fintype Path]
    (C : ClosureDatum Path) :
    ℝ :=
  ∑ p : Path, C.pathMeasure p

/--
The complete logarithmic closure depth.

The finite sector multiplicity contributes additively through its
natural logarithm.
-/
def logClosureDepth
    {Path : Type u}
    [Fintype Path]
    (C : ClosureDatum Path) :
    ℝ :=
  C.totalPathMeasure +
    Real.log (C.sectorMultiplicity : ℝ)

/--
The multiplicative closure depth obtained by exponentiating the
logarithmic closure measure.
-/
def closureDepth
    {Path : Type u}
    [Fintype Path]
    (C : ClosureDatum Path) :
    ℝ :=
  Real.exp C.logClosureDepth

/--
Every abstract closure depth is strictly positive.
-/
theorem closureDepth_pos
    {Path : Type u}
    [Fintype Path]
    (C : ClosureDatum Path) :
    0 < C.closureDepth := by

  exact Real.exp_pos _

/--
The exponential definition factors into:

- the discrete sector multiplicity;
- the exponential of the total pathwise closure measure.

This is the generic algebraic form underlying any later KT stability
formula.
-/
theorem closureDepth_factorization
    {Path : Type u}
    [Fintype Path]
    (C : ClosureDatum Path) :
    C.closureDepth =
      (C.sectorMultiplicity : ℝ) *
        Real.exp C.totalPathMeasure := by

  have hm :
      (0 : ℝ) < (C.sectorMultiplicity : ℝ) := by
    exact_mod_cast C.sectorMultiplicity_pos

  change
    Real.exp
        (C.totalPathMeasure +
          Real.log (C.sectorMultiplicity : ℝ)) =
      (C.sectorMultiplicity : ℝ) *
        Real.exp C.totalPathMeasure

  rw [
    Real.exp_add,
    Real.exp_log hm
  ]

  exact mul_comm _ _

/--
If every primitive path has the same logarithmic measure `w`, then the
total path measure is the cardinality of the path family multiplied by
`w`.
-/
theorem totalPathMeasure_of_constant
    {Path : Type u}
    [Fintype Path]
    (C : ClosureDatum Path)
    (w : ℝ)
    (huniform :
      ∀ p : Path, C.pathMeasure p = w) :
    C.totalPathMeasure =
      (Fintype.card Path : ℝ) * w := by

  simp [
    totalPathMeasure,
    huniform
  ]

/--
For a uniform path family, logarithmic closure depth depends only on:

- the number of primitive paths;
- their common local measure;
- the discrete sector multiplicity.
-/
theorem logClosureDepth_of_constant
    {Path : Type u}
    [Fintype Path]
    (C : ClosureDatum Path)
    (w : ℝ)
    (huniform :
      ∀ p : Path, C.pathMeasure p = w) :
    C.logClosureDepth =
      (Fintype.card Path : ℝ) * w +
        Real.log (C.sectorMultiplicity : ℝ) := by

  rw [
    logClosureDepth,
    totalPathMeasure_of_constant C w huniform
  ]

end UniversalClosure

#check UniversalClosure.ClosureDatum
#check UniversalClosure.closureDepth_factorization
#check UniversalClosure.logClosureDepth_of_constant
