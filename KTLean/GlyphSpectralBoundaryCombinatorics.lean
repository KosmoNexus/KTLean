import KTLean.GlyphSpectralAlgebraicRoots
import KTLean.GlyphAttractorTableBridge
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Combinatorial Boundary Values from the Forced Seven-Point Carrier

## Formal status

**Level 2 — Exact derivation of the structural boundary values
21, 42, and 147.**

The forced Fano carrier has seven points.

From that carrier:

* `21` is the number of unordered pairs:
      C(7,2) = 21;

* `42` is the oriented double cover:
      2 × 21 = 42;

* `147` is the sevenfold closure depth:
      7 × 21 = 147.

These are exact finite consequences of the already established
seven-point and binary-orientation structures.

This module also verifies their positions in the registered boundary
block.

It does not yet derive `23`, `46`, or `137`.
-/

namespace GlyphSpectralBoundaryCombinatorics

/--
The cardinality of the forced Fano carrier.
-/
def fanoCardinality :
    Nat :=
  7

/--
The number of unordered pairs of distinct Fano points.
-/
def visiblePairCount :
    Nat :=
  Nat.choose fanoCardinality 2

/--
The forced seven-point carrier has twenty-one unordered pairs.
-/
theorem visiblePairCount_eq_twentyOne :
    visiblePairCount =
      21 := by

  native_decide

/--
The binary orientation cover doubles the visible pair carrier.
-/
def orientedPairCount :
    Nat :=
  2 * visiblePairCount

/--
The oriented pair carrier has forty-two elements.
-/
theorem orientedPairCount_eq_fortyTwo :
    orientedPairCount =
      42 := by

  unfold orientedPairCount

  rw [
    visiblePairCount_eq_twentyOne
  ]

/--
A sevenfold traversal of the twenty-one visible pairs.
-/
def sevenfoldClosureDepth :
    Nat :=
  fanoCardinality * visiblePairCount

/--
The sevenfold closure depth is one hundred forty-seven.
-/
theorem sevenfoldClosureDepth_eq_oneFortySeven :
    sevenfoldClosureDepth =
      147 := by

  unfold sevenfoldClosureDepth
  unfold fanoCardinality

  rw [
    visiblePairCount_eq_twentyOne
  ]

/--
The three structural values form a multiplicative chain.
-/
theorem structural_boundary_chain :
    visiblePairCount = 21
      ∧
    orientedPairCount = 2 * visiblePairCount
      ∧
    sevenfoldClosureDepth =
      fanoCardinality * visiblePairCount := by

  exact
    ⟨
      visiblePairCount_eq_twentyOne,
      rfl,
      rfl
    ⟩

/--
The registered six-entry boundary block.
-/
def registeredBoundaryBlock :
    List GlyphSpectrum.SpectralValue :=

  (
    GlyphSpectrum.values.drop 36
  ).take 6

/--
The canonical boundary block is exactly
`21, 42, 23, 46, 147, 137`.
-/
theorem registeredBoundaryBlock_eq :
    registeredBoundaryBlock =
      [
        .natural 21,
        .natural 42,
        .natural 23,
        .natural 46,
        .natural 147,
        .natural 137
      ] := by

  native_decide

/--
The three values derived here occupy boundary positions
37, 38, and 41.
-/
theorem derived_boundary_positions :
    GlyphSpectrum.values[36]? =
        some (.natural 21)
      ∧
    GlyphSpectrum.values[37]? =
        some (.natural 42)
      ∧
    GlyphSpectrum.values[40]? =
        some (.natural 147) := by

  native_decide

/--
The 42-value is exactly the binary lift of the 21-value.
-/
theorem fortyTwo_is_oriented_double :
    42 =
      2 * 21 := by

  norm_num

/--
The 147-value is exactly the sevenfold lift of the 21-value.
-/
theorem oneFortySeven_is_sevenfold_twentyOne :
    147 =
      7 * 21 := by

  norm_num

/--
Capstone theorem.

The forced seven-point carrier determines 21 unordered pairs.
Binary orientation doubles this to 42, and sevenfold closure lifts
21 to 147. These values occur at their canonical boundary positions.
-/
theorem forced_seven_structure_derives_boundary_triple :
    visiblePairCount =
        21
      ∧
    orientedPairCount =
        42
      ∧
    sevenfoldClosureDepth =
        147
      ∧
    GlyphSpectrum.values[36]? =
        some (.natural 21)
      ∧
    GlyphSpectrum.values[37]? =
        some (.natural 42)
      ∧
    GlyphSpectrum.values[40]? =
        some (.natural 147) := by

  exact
    ⟨
      visiblePairCount_eq_twentyOne,
      orientedPairCount_eq_fortyTwo,
      sevenfoldClosureDepth_eq_oneFortySeven,
      derived_boundary_positions.1,
      derived_boundary_positions.2.1,
      derived_boundary_positions.2.2
    ⟩

end GlyphSpectralBoundaryCombinatorics

#check GlyphSpectralBoundaryCombinatorics.fanoCardinality
#check GlyphSpectralBoundaryCombinatorics.visiblePairCount
#check GlyphSpectralBoundaryCombinatorics.visiblePairCount_eq_twentyOne
#check GlyphSpectralBoundaryCombinatorics.orientedPairCount
#check GlyphSpectralBoundaryCombinatorics.orientedPairCount_eq_fortyTwo
#check GlyphSpectralBoundaryCombinatorics.sevenfoldClosureDepth
#check GlyphSpectralBoundaryCombinatorics.sevenfoldClosureDepth_eq_oneFortySeven
#check GlyphSpectralBoundaryCombinatorics.registeredBoundaryBlock_eq
#check GlyphSpectralBoundaryCombinatorics.derived_boundary_positions
#check GlyphSpectralBoundaryCombinatorics.forced_seven_structure_derives_boundary_triple
