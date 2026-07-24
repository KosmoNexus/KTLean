import KTLean.GlyphSpectralBoundaryCombinatorics
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# The 137-Channel Projection Boundary

## Formal status

**Level 2 — Exact finite channel-count derivation conditional on the
eight-to-four reversible projection interface.**

For an operational carrier of eight channels projected through
four-channel selections:

    C(8,4) = 70.

Reversibility supplies two transport orientations:

    2 * C(8,4) = 140.

The primordial triad is reserved as closure overhead:

    140 - 3 = 137.

Thus the usable reversible channel count is

    2 * C(8,4) - 3 = 137.

This module proves the finite derivation and identifies the result with
the final glyph of the canonical boundary block.

It does not derive the existence of the eight-to-four interface itself.
That obligation belongs to the later projection/tokenization chain.
-/

namespace GlyphSpectralAlphaBoundary

/--
The operational source-carrier count.
-/
def sourceChannelCount :
    Nat :=
  8

/--
The operational projection-selection count.
-/
def projectedChannelCount :
    Nat :=
  4

/--
The number of four-channel selections from an eight-channel carrier.
-/
def unorientedProjectionChannels :
    Nat :=
  Nat.choose
    sourceChannelCount
    projectedChannelCount

/--
There are exactly seventy four-channel selections from eight channels.
-/
theorem unorientedProjectionChannels_eq_seventy :
    unorientedProjectionChannels =
      70 := by

  native_decide

/--
Forward and reverse transport double the channel carrier.
-/
def reversibleProjectionChannels :
    Nat :=
  2 * unorientedProjectionChannels

/--
The reversible projection carrier contains 140 channels before closure
overhead is reserved.
-/
theorem reversibleProjectionChannels_eq_oneForty :
    reversibleProjectionChannels =
      140 := by

  unfold reversibleProjectionChannels

  rw [
    unorientedProjectionChannels_eq_seventy
  ]

/--
The primordial triad requires three reserved closure channels.
-/
def triadicClosureOverhead :
    Nat :=
  3

/--
Usable reversible channels after reserving the primordial triad.
-/
def usableProjectionChannels :
    Nat :=
  reversibleProjectionChannels -
    triadicClosureOverhead

/--
The usable reversible projection capacity is exactly 137.
-/
theorem usableProjectionChannels_eq_oneThirtySeven :
    usableProjectionChannels =
      137 := by

  native_decide

/--
The channel formula in its compact combinatorial form.
-/
theorem alphaBoundary_formula :
    2 *
        Nat.choose 8 4
      -
        3 =
      137 := by

  native_decide

/--
The three removed channels are exactly one closure triad.
-/
theorem removed_capacity_is_primordial_triad :
    reversibleProjectionChannels =
      usableProjectionChannels +
        triadicClosureOverhead := by

  native_decide

/--
The final canonical glyph carries the symbolic boundary value 137.
-/
theorem alphaBoundary_registered_at_glyph_fortyTwo :
    GlyphSpectrum.values[41]? =
      some
        (.natural 137) := by

  native_decide

/--
The structurally isolated alpha basin contains exactly the final glyph.
-/
theorem alpha_basin_is_final_glyph :
    GlyphAttractorTableBridge.glyphNumbersInBasin
        GlyphAttractorSignature.Basin.alpha =
      [42] := by

  exact
    GlyphAttractorTableBridge.alpha_glyph_numbers

/--
The registered alpha-basin value is exactly 137.
-/
theorem alpha_basin_registered_value :
    GlyphAttractorTableBridge.registeredValuesInBasin
        GlyphAttractorSignature.Basin.alpha =
      [
        .natural 137
      ] := by

  exact
    GlyphAttractorTableBridge.alpha_registered_values

/--
The 137 boundary is distinct from the 147 closure-depth boundary.
-/
theorem alphaBoundary_ne_closureDepth :
    usableProjectionChannels ≠
      GlyphSpectralBoundaryCombinatorics.sevenfoldClosureDepth := by

  rw [
    usableProjectionChannels_eq_oneThirtySeven,
    GlyphSpectralBoundaryCombinatorics.sevenfoldClosureDepth_eq_oneFortySeven
  ]

  norm_num

/--
Capstone theorem.

A reversible eight-to-four channel interface has 140 oriented
four-channel selections. Reserving one primordial triad leaves exactly
137 usable channels, located at the unique glyph of the alpha basin.
-/
theorem reversible_projection_minus_triad_forces_137 :
    unorientedProjectionChannels =
        70
      ∧
    reversibleProjectionChannels =
        140
      ∧
    triadicClosureOverhead =
        3
      ∧
    usableProjectionChannels =
        137
      ∧
    GlyphAttractorTableBridge.glyphNumbersInBasin
        GlyphAttractorSignature.Basin.alpha =
      [42]
      ∧
    GlyphAttractorTableBridge.registeredValuesInBasin
        GlyphAttractorSignature.Basin.alpha =
      [
        .natural 137
      ] := by

  exact
    ⟨
      unorientedProjectionChannels_eq_seventy,
      reversibleProjectionChannels_eq_oneForty,
      rfl,
      usableProjectionChannels_eq_oneThirtySeven,
      alpha_basin_is_final_glyph,
      alpha_basin_registered_value
    ⟩

end GlyphSpectralAlphaBoundary

#check GlyphSpectralAlphaBoundary.sourceChannelCount
#check GlyphSpectralAlphaBoundary.projectedChannelCount
#check GlyphSpectralAlphaBoundary.unorientedProjectionChannels
#check GlyphSpectralAlphaBoundary.unorientedProjectionChannels_eq_seventy
#check GlyphSpectralAlphaBoundary.reversibleProjectionChannels
#check GlyphSpectralAlphaBoundary.reversibleProjectionChannels_eq_oneForty
#check GlyphSpectralAlphaBoundary.triadicClosureOverhead
#check GlyphSpectralAlphaBoundary.usableProjectionChannels
#check GlyphSpectralAlphaBoundary.usableProjectionChannels_eq_oneThirtySeven
#check GlyphSpectralAlphaBoundary.alphaBoundary_formula
#check GlyphSpectralAlphaBoundary.removed_capacity_is_primordial_triad
#check GlyphSpectralAlphaBoundary.alphaBoundary_registered_at_glyph_fortyTwo
#check GlyphSpectralAlphaBoundary.alpha_basin_is_final_glyph
#check GlyphSpectralAlphaBoundary.alpha_basin_registered_value
#check GlyphSpectralAlphaBoundary.alphaBoundary_ne_closureDepth
#check GlyphSpectralAlphaBoundary.reversible_projection_minus_triad_forces_137
