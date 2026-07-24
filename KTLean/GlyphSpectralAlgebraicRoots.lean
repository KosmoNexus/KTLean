import KTLean.GlyphSpectralFibonacci
import KTLean.GlyphFamily
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Multiplicative Triadic Closure Forces the Algebraic Root Pairs

## Formal status

**Level 2 — Exact root derivation conditional on the canonical
Frobenius-to-radicand rule.**

The native KT motif remains:

    two inputs force one unique third state.

For the algebraic-root family, the closure law is multiplication:

    x, y ↦ x * y.

At the diagonal input `(x,x)`, requiring completion to a positive
radicand `n` gives

    x² = n.

For each positive `n`, there is exactly one positive solution:

    x = √n.

Orientation reversal supplies the reciprocal member:

    (√n)⁻¹.

The three forced Frobenius roles are assigned the canonical first
three prime radicands:

    role 0 / Frobenius 1 ↦ 2
    role 1 / Frobenius 2 ↦ 3
    role 2 / Frobenius 4 ↦ 5.

This module proves the six-value block

    (√2)⁻¹, √2,
    (√3)⁻¹, √3,
    (√5)⁻¹, √5.

The root values themselves are derived from multiplicative closure.
The role-to-radicand assignment is explicit and remains a separate
structural convention to be justified or strengthened later.
-/

namespace GlyphSpectralAlgebraicRoots

open GlyphSpectralTriadicEngine
open GlyphForcingTriadicRole
open GlyphForcingOrientation
open GlyphForcingFrobeniusIdentification

/--
The multiplicative two-parent closure law.
-/
def multiplicativeClosure :
    ClosureLaw ℝ :=
  fun x y =>
    x * y

/--
Multiplicative closure has one unique completion for every ordered
pair.
-/
theorem multiplicativeClosure_unique
    (x y : ℝ) :
    ∃! z : ℝ,
      Completes
        multiplicativeClosure
        x
        y
        z := by

  exact
    existsUnique_completion
      multiplicativeClosure
      x
      y

/--
The canonical positive radicand attached to each forced role.
-/
def radicandOfRole :
    ForcedRole →
      Nat

  | 0 =>
      2

  | 1 =>
      3

  | 2 =>
      5

/--
The radicands attached to the three forced roles are exactly
`2, 3, 5`.
-/
theorem radicand_values :
    [
      radicandOfRole 0,
      radicandOfRole 1,
      radicandOfRole 2
    ] =
      [2, 3, 5] := by

  rfl

/--
The radicand assignment agrees with the Frobenius ordering
`1, 2, 4`.
-/
theorem frobenius_radicand_table :
    [
      (
        stepOfForcedRole 0,
        radicandOfRole 0
      ),
      (
        stepOfForcedRole 1,
        radicandOfRole 1
      ),
      (
        stepOfForcedRole 2,
        radicandOfRole 2
      )
    ] =
      [
        (FrobeniusOrbit.Step.one, 2),
        (FrobeniusOrbit.Step.two, 3),
        (FrobeniusOrbit.Step.four, 5)
      ] := by

  rfl

/--
Every canonical radicand is strictly positive.
-/
theorem radicand_positive
    (role : ForcedRole) :
    0 <
      radicandOfRole role := by

  fin_cases role <;>
    simp [
      radicandOfRole
    ]

/--
The positive algebraic root attached to one forced role.
-/
noncomputable def rootOfRole
    (role : ForcedRole) :
    ℝ :=

  Real.sqrt
    (
      radicandOfRole role
    )


 /--
Every canonical algebraic root is positive.
-/
theorem rootOfRole_positive
    (role : ForcedRole) :
    0 <
      rootOfRole role := by

  unfold rootOfRole

  apply Real.sqrt_pos.2

  exact_mod_cast
    radicand_positive role

/--
Every canonical algebraic root is nonzero.
-/
theorem rootOfRole_ne_zero
    (role : ForcedRole) :
    rootOfRole role ≠
      0 := by

  exact
    ne_of_gt
      (
        rootOfRole_positive
          role
      )

/--
The square of the canonical root is its assigned radicand.
-/
theorem rootOfRole_squared
    (role : ForcedRole) :
    (
      rootOfRole role
    ) ^ 2 =
      radicandOfRole role := by

  unfold rootOfRole

  exact
    Real.sq_sqrt
      (
        by
          positivity
      )

/--
The diagonal multiplicative closure of a canonical root completes to
its assigned radicand.
-/
theorem root_completes_radicand
    (role : ForcedRole) :
    Completes
        multiplicativeClosure
        (rootOfRole role)
        (rootOfRole role)
        (radicandOfRole role) := by

  unfold Completes
  unfold multiplicativeClosure

  have hSquare :=
    rootOfRole_squared
      role

  nlinarith

/--
A positive square root of a fixed positive radicand is unique.
-/
theorem positive_square_root_unique
    {n left right : ℝ}
    (hLeftPositive :
      0 < left)
    (hRightPositive :
      0 < right)
    (hLeft :
      left ^ 2 =
        n)
    (hRight :
      right ^ 2 =
        n) :
    left =
      right := by

  nlinarith

/--
The canonical root is the unique positive value whose diagonal
multiplicative completion is the assigned radicand.
-/
theorem existsUnique_positive_root
    (role : ForcedRole) :
    ∃! x : ℝ,
      0 < x
        ∧
      Completes
        multiplicativeClosure
        x
        x
        (radicandOfRole role) := by

  refine
    ⟨
      rootOfRole role,
      ?_,
      ?_
    ⟩

  · exact
      ⟨
        rootOfRole_positive role,
        root_completes_radicand role
      ⟩

  · intro other hOther

    apply
      positive_square_root_unique
        hOther.1
        (rootOfRole_positive role)

    · unfold Completes at hOther

      unfold multiplicativeClosure at hOther

      nlinarith

    · exact
        rootOfRole_squared
          role

/--
The reciprocal root associated with one forced role.
-/
noncomputable def inverseRootOfRole
    (role : ForcedRole) :
    ℝ :=

  (
    rootOfRole role
  )⁻¹

/--
Each root and reciprocal root multiply to one.
-/
theorem inverseRoot_mul_root
    (role : ForcedRole) :
    inverseRootOfRole role
        *
      rootOfRole role =
      1 := by

  unfold inverseRootOfRole

  exact
    inv_mul_cancel₀
      (
        rootOfRole_ne_zero
          role
      )

/--
Orientation selects the root or reciprocal-root member.
-/
noncomputable def orientedRootValue
    (role : ForcedRole) :
    ForcedOrientation →
      ℝ

  | .forward =>
      inverseRootOfRole role

  | .reverse =>
      rootOfRole role

/--
The two oriented root values are reciprocal.
-/
theorem orientedRootValues_reciprocal
    (role : ForcedRole) :
    orientedRootValue
        role
        ForcedOrientation.forward
      *
    orientedRootValue
        role
        ForcedOrientation.reverse =
      1 := by

  exact
    inverseRoot_mul_root
      role

/--
The role-zero root is `√2`.
-/
@[simp]
theorem root_role_zero :
    rootOfRole 0 =
      Real.sqrt 2 := by

  rfl

/--
The role-one root is `√3`.
-/
@[simp]
theorem root_role_one :
    rootOfRole 1 =
      Real.sqrt 3 := by

  rfl

/--
The role-two root is `√5`.
-/
@[simp]
theorem root_role_two :
    rootOfRole 2 =
      Real.sqrt 5 := by

  rfl

/--
The registered six-entry algebraic-root block.
-/
def registeredAlgebraicRootBlock :
    List GlyphSpectrum.SpectralValue :=

  (
    GlyphSpectrum.values.drop 12
  ).take 6

/--
The registered algebraic-root block is exactly the three reciprocal
root pairs.
-/
theorem registeredAlgebraicRootBlock_eq :
    registeredAlgebraicRootBlock =
      [
        .inverse (.squareRoot 2),
        .squareRoot 2,
        .inverse (.squareRoot 3),
        .squareRoot 3,
        .inverse (.squareRoot 5),
        .squareRoot 5
      ] := by

  native_decide

/--
The algebraic-root family occupies glyphs 13 through 18.
-/
def algebraicRootGlyphNumbers :
    List Nat :=

  GlyphTable.coordinates.zipIdx.filterMap
    (
      fun entry =>
        if
          GlyphFamily.familyOfLine
              entry.1.address =
            GlyphFamily.Family.algebraicRoot
        then
          some (entry.2 + 1)
        else
          none
    )

/--
The algebraic-root family selects exactly glyphs 13 through 18.
-/
theorem algebraicRoot_glyph_numbers :
    algebraicRootGlyphNumbers =
      [13, 14, 15, 16, 17, 18] := by

  native_decide

/--
Capstone theorem.

Multiplicative two-parent closure at equal inputs forces one unique
positive square root for each canonical radicand. Orientation produces
the reciprocal member, yielding exactly the registered six-entry
algebraic-root block.
-/
theorem multiplicative_closure_forces_root_pairs :
    (∀ role : ForcedRole,
      ∃! x : ℝ,
        0 < x
          ∧
        Completes
          multiplicativeClosure
          x
          x
          (radicandOfRole role))
      ∧
    (∀ role : ForcedRole,
      inverseRootOfRole role
          *
        rootOfRole role =
        1)
      ∧
    algebraicRootGlyphNumbers =
        [13, 14, 15, 16, 17, 18]
      ∧
    registeredAlgebraicRootBlock =
      [
        .inverse (.squareRoot 2),
        .squareRoot 2,
        .inverse (.squareRoot 3),
        .squareRoot 3,
        .inverse (.squareRoot 5),
        .squareRoot 5
      ] := by

  exact
    ⟨
      existsUnique_positive_root,
      inverseRoot_mul_root,
      algebraicRoot_glyph_numbers,
      registeredAlgebraicRootBlock_eq
    ⟩

end GlyphSpectralAlgebraicRoots

#check GlyphSpectralAlgebraicRoots.multiplicativeClosure
#check GlyphSpectralAlgebraicRoots.radicandOfRole
#check GlyphSpectralAlgebraicRoots.radicand_values
#check GlyphSpectralAlgebraicRoots.frobenius_radicand_table
#check GlyphSpectralAlgebraicRoots.rootOfRole
#check GlyphSpectralAlgebraicRoots.rootOfRole_positive
#check GlyphSpectralAlgebraicRoots.rootOfRole_squared
#check GlyphSpectralAlgebraicRoots.root_completes_radicand
#check GlyphSpectralAlgebraicRoots.positive_square_root_unique
#check GlyphSpectralAlgebraicRoots.existsUnique_positive_root
#check GlyphSpectralAlgebraicRoots.inverseRootOfRole
#check GlyphSpectralAlgebraicRoots.inverseRoot_mul_root
#check GlyphSpectralAlgebraicRoots.orientedRootValue
#check GlyphSpectralAlgebraicRoots.registeredAlgebraicRootBlock_eq
#check GlyphSpectralAlgebraicRoots.algebraicRoot_glyph_numbers
#check GlyphSpectralAlgebraicRoots.multiplicative_closure_forces_root_pairs
