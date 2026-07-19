import KTLean.ClosedTriflux
import KTLean.UniversalClosure

/-!
# Dynamical Closure

This module connects literal closed-triflux dynamics to the abstract
closure-depth framework.

## Formal status

**Level 2 — Structural integration.**

A `ClosedPath` is not an arbitrary path label. It carries:

- an actual complete-state anchor;
- a strictly positive period;
- proof that reversible evolution returns the anchor after that period.

A finite measured family of such paths canonically determines a
`UniversalClosure.ClosureDatum`.

This module does not assume or derive:

- seven primitive paths;
- forty-two glyphs;
- Fano incidence;
- a path measure of `2 * π^2`;
- eight substrate sectors.

Those remain explicit forcing obligations.
-/

namespace DynamicalClosure

universe u v

noncomputable section

/--
A witnessed closed path in a finite closed-triflux system.

The period need not yet be minimal. It is a certified positive return
time for the selected anchor state.
-/
structure ClosedPath
    {State : Type u}
    [Fintype State]
    (S : ClosedTriflux.System State) where

  /--
  Complete state at which the path is rooted.
  -/
  anchor :
    State

  /--
  Positive number of reversible steps required by this closure witness.
  -/
  period :
    ℕ

  /--
  A closed path cannot have zero length.
  -/
  period_pos :
    0 < period

  /--
  The complete state literally returns after the specified period.
  -/
  returns :
    (S.stepEquiv ^ period) anchor =
      anchor

/--
Every complete state canonically determines a witnessed closed path by
using the global period of the reversible state permutation.

This proves existence of closed paths. It does not claim that the
resulting state-indexed family is primitive or minimal.
-/
def canonicalClosedPath
    {State : Type u}
    [Fintype State]
    (S : ClosedTriflux.System State)
    (state : State) :
    ClosedPath S where

  anchor :=
    state

  period :=
    S.globalPeriod

  period_pos :=
    S.globalPeriod_pos

  returns :=
    S.state_returns_after_globalPeriod state

@[simp]
theorem canonicalClosedPath_anchor
    {State : Type u}
    [Fintype State]
    (S : ClosedTriflux.System State)
    (state : State) :
    (canonicalClosedPath S state).anchor =
      state := by
  rfl

@[simp]
theorem canonicalClosedPath_period
    {State : Type u}
    [Fintype State]
    (S : ClosedTriflux.System State)
    (state : State) :
    (canonicalClosedPath S state).period =
      S.globalPeriod := by
  rfl

/--
A finite family of actual closed dynamical paths equipped with the
additional numerical data required for universal closure.

The distinction is deliberate:

- `closedPath` certifies dynamical closure;
- `pathMeasure` assigns a logarithmic measure whose eventual value
  must be independently derived;
- `sectorMultiplicity` records a finite multiplicity whose eventual
  value must also be independently derived.
-/
structure MeasuredPathFamily
    {State : Type u}
    [Fintype State]
    (S : ClosedTriflux.System State)
    (Path : Type v)
    [Fintype Path] where

  /--
  Dynamical closure witness associated with each path label.
  -/
  closedPath :
    Path → ClosedPath S

  /--
  Logarithmic closure measure assigned to each certified path.
  -/
  pathMeasure :
    Path → ℝ

  /--
  Number of equivalent disjoint substrate sectors.
  -/
  sectorMultiplicity :
    ℕ

  /--
  At least one substrate sector exists.
  -/
  sectorMultiplicity_pos :
    0 < sectorMultiplicity

/--
A measured family of actual closed dynamical paths canonically
determines abstract universal-closure data.
-/
def MeasuredPathFamily.closureDatum
    {State : Type u}
    [Fintype State]
    {S : ClosedTriflux.System State}
    {Path : Type v}
    [Fintype Path]
    (F : MeasuredPathFamily S Path) :
    UniversalClosure.ClosureDatum Path where

  pathMeasure :=
    F.pathMeasure

  sectorMultiplicity :=
    F.sectorMultiplicity

  sectorMultiplicity_pos :=
    F.sectorMultiplicity_pos

@[simp]
theorem MeasuredPathFamily.closureDatum_pathMeasure
    {State : Type u}
    [Fintype State]
    {S : ClosedTriflux.System State}
    {Path : Type v}
    [Fintype Path]
    (F : MeasuredPathFamily S Path)
    (path : Path) :
    F.closureDatum.pathMeasure path =
      F.pathMeasure path := by
  rfl

@[simp]
theorem MeasuredPathFamily.closureDatum_sectorMultiplicity
    {State : Type u}
    [Fintype State]
    {S : ClosedTriflux.System State}
    {Path : Type v}
    [Fintype Path]
    (F : MeasuredPathFamily S Path) :
    F.closureDatum.sectorMultiplicity =
      F.sectorMultiplicity := by
  rfl

/--
The abstract universal-closure factorization applies to every measured
family of certified dynamical paths.
-/
theorem MeasuredPathFamily.closureDepth_factorization
    {State : Type u}
    [Fintype State]
    {S : ClosedTriflux.System State}
    {Path : Type v}
    [Fintype Path]
    (F : MeasuredPathFamily S Path) :
    UniversalClosure.closureDepth F.closureDatum =
      (F.sectorMultiplicity : ℝ) *
        Real.exp (UniversalClosure.totalPathMeasure F.closureDatum) := by

  exact
    UniversalClosure.closureDepth_factorization
      F.closureDatum

/--
When every certified path has one common logarithmic measure `w`, the
closure depth depends only on:

- the number of path labels;
- their common measure;
- the sector multiplicity.
-/
theorem MeasuredPathFamily.logClosureDepth_of_uniform
    {State : Type u}
    [Fintype State]
    {S : ClosedTriflux.System State}
    {Path : Type v}
    [Fintype Path]
    (F : MeasuredPathFamily S Path)
    (w : ℝ)
    (huniform :
      ∀ path : Path,
        F.pathMeasure path = w) :
    UniversalClosure.logClosureDepth F.closureDatum =
      (Fintype.card Path : ℝ) * w +
        Real.log (F.sectorMultiplicity : ℝ) := by

  apply
    UniversalClosure.logClosureDepth_of_constant
      F.closureDatum
      w

  intro path

  exact huniform path

/--
Every finite closed-triflux system admits a nonminimal rooted measured
path family indexed by its complete states.

This is an existence construction only. It must not be interpreted as
a claim that complete states are the primitive KT closure paths.
-/
def rootedGlobalFamily
    {State : Type u}
    [Fintype State]
    (S : ClosedTriflux.System State)
    (pathMeasure : State → ℝ)
    (sectorMultiplicity : ℕ)
    (hsector :
      0 < sectorMultiplicity) :
    MeasuredPathFamily S State where

  closedPath :=
    canonicalClosedPath S

  pathMeasure :=
    pathMeasure

  sectorMultiplicity :=
    sectorMultiplicity

  sectorMultiplicity_pos :=
    hsector

@[simp]
theorem rootedGlobalFamily_period
    {State : Type u}
    [Fintype State]
    (S : ClosedTriflux.System State)
    (pathMeasure : State → ℝ)
    (sectorMultiplicity : ℕ)
    (hsector :
      0 < sectorMultiplicity)
    (state : State) :
    ((rootedGlobalFamily
      S
      pathMeasure
      sectorMultiplicity
      hsector).closedPath state).period =
        S.globalPeriod := by
  rfl

end

end DynamicalClosure

#check DynamicalClosure.ClosedPath
#check DynamicalClosure.canonicalClosedPath
#check DynamicalClosure.MeasuredPathFamily
#check DynamicalClosure.MeasuredPathFamily.closureDatum
#check DynamicalClosure.MeasuredPathFamily.logClosureDepth_of_uniform
