import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Universal Closure

A count-independent framework for global closure depth.

The definitions in this module contain no reference to seven paths,
forty-two glyphs, the Fano plane, octonions, cosmic age, or alpha.
Those values may enter only through later forcing theorems.
-/

namespace UniversalClosure

open scoped BigOperators

universe u

noncomputable section

structure ClosureDatum
    (Path : Type u)
    [Fintype Path] where

  pathMeasure :
    Path → ℝ

  sectorMultiplicity :
    ℕ

  sectorMultiplicity_pos :
    0 < sectorMultiplicity

def totalPathMeasure
    {Path : Type u}
    [Fintype Path]
    (C : ClosureDatum Path) :
    ℝ :=
  ∑ path : Path, C.pathMeasure path

def logClosureDepth
    {Path : Type u}
    [Fintype Path]
    (C : ClosureDatum Path) :
    ℝ :=
  totalPathMeasure C +
    Real.log (C.sectorMultiplicity : ℝ)

def closureDepth
    {Path : Type u}
    [Fintype Path]
    (C : ClosureDatum Path) :
    ℝ :=
  Real.exp (logClosureDepth C)

theorem closureDepth_pos
    {Path : Type u}
    [Fintype Path]
    (C : ClosureDatum Path) :
    0 < closureDepth C := by

  exact Real.exp_pos _

theorem sectorMultiplicity_cast_pos
    {Path : Type u}
    [Fintype Path]
    (C : ClosureDatum Path) :
    (0 : ℝ) <
      (C.sectorMultiplicity : ℝ) := by

  exact
    Nat.cast_pos.mpr
      C.sectorMultiplicity_pos

theorem closureDepth_factorization
    {Path : Type u}
    [Fintype Path]
    (C : ClosureDatum Path) :
    closureDepth C =
      (C.sectorMultiplicity : ℝ) *
        Real.exp (totalPathMeasure C) := by

  have hm :
      (0 : ℝ) <
        (C.sectorMultiplicity : ℝ) :=
    sectorMultiplicity_cast_pos C

  unfold closureDepth
  unfold logClosureDepth

  rw [
    Real.exp_add,
    Real.exp_log hm
  ]

  exact mul_comm _ _

theorem totalPathMeasure_of_constant
    {Path : Type u}
    [Fintype Path]
    (C : ClosureDatum Path)
    (w : ℝ)
    (huniform :
      ∀ path : Path,
        C.pathMeasure path = w) :
    totalPathMeasure C =
      (Fintype.card Path : ℝ) * w := by

  unfold totalPathMeasure

  simp [huniform]

theorem logClosureDepth_of_constant
    {Path : Type u}
    [Fintype Path]
    (C : ClosureDatum Path)
    (w : ℝ)
    (huniform :
      ∀ path : Path,
        C.pathMeasure path = w) :
    logClosureDepth C =
      (Fintype.card Path : ℝ) * w +
        Real.log (C.sectorMultiplicity : ℝ) := by

  unfold logClosureDepth

  rw [
    totalPathMeasure_of_constant
      C
      w
      huniform
  ]

end

end UniversalClosure

#check UniversalClosure.ClosureDatum
#check UniversalClosure.totalPathMeasure
#check UniversalClosure.logClosureDepth
#check UniversalClosure.closureDepth
#check UniversalClosure.closureDepth_factorization
#check UniversalClosure.logClosureDepth_of_constant
