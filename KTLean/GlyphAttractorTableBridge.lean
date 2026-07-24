import KTLean.GlyphAttractorSignature
import KTLean.GlyphSpectrum

/-!
# Bridge from the Forced Attractor Signature to the Canonical Glyph Table

## Formal status

**Level 1 — Exact table identification.**

`GlyphAttractorSignature` derives the four-register partition

    Pascal     : 31 states
    Fibonacci  :  2 states
    Wallis     :  8 states
    Alpha      :  1 state

directly from the forced glyph coordinates, without inspecting the
registered spectrum.

This module proves that the resulting structural classifier selects
exactly the intended numbered rows of the canonical Denver table.

It then records the already registered symbolic values carried by
those selected rows.

The direction of dependence remains explicit:

    forced coordinates
        → basin assignment
        → exact canonical row set
        → registered symbolic values on those rows.

The final arrow is an identification with the existing spectral table,
not yet a proof that the analytic constants are forced by the basin
dynamics.
-/

namespace GlyphAttractorTableBridge

open GlyphAttractorSignature

/--
The one-based glyph numbers selected by one structurally derived
basin.
-/
def glyphNumbersInBasin
    (basin : Basin) :
    List Nat :=

  GlyphTable.coordinates.zipIdx.filterMap
    (
      fun entry =>
        if
          basinOfCoordinates entry.1 =
            basin
        then
          some (entry.2 + 1)
        else
          none
    )

/--
The registered symbolic spectral values carried by one structurally
derived basin.
-/
def registeredValuesInBasin
    (basin : Basin) :
    List GlyphSpectrum.SpectralValue :=

  (
    GlyphTable.coordinates.zip
      GlyphSpectrum.values
  ).filterMap
    (
      fun entry =>
        if
          basinOfCoordinates entry.1 =
            basin
        then
          some entry.2
        else
          none
    )

/--
The structurally derived Fibonacci basin selects exactly glyphs 7 and
8.
-/
theorem fibonacci_glyph_numbers :
    glyphNumbersInBasin Basin.fibonacci =
      [7, 8] := by

  native_decide

/--
The structurally derived Wallis basin selects exactly glyphs 11, 12,
and 31 through 36.
-/
theorem wallis_glyph_numbers :
    glyphNumbersInBasin Basin.wallis =
      [11, 12, 31, 32, 33, 34, 35, 36] := by

  native_decide

/--
The structurally derived Alpha basin selects exactly glyph 42.
-/
theorem alpha_glyph_numbers :
    glyphNumbersInBasin Basin.alpha =
      [42] := by

  native_decide

/--
The structurally derived Pascal basin is the exact complementary
31-row set.
-/
theorem pascal_glyph_numbers :
    glyphNumbersInBasin Basin.pascal =
      [
        1, 2, 3, 4, 5, 6,
        9, 10,
        13, 14, 15, 16, 17, 18,
        19, 20, 21, 22, 23, 24,
        25, 26, 27, 28, 29, 30,
        37, 38, 39, 40, 41
      ] := by

  native_decide

/--
The structurally selected Fibonacci rows carry the registered pair

    φ⁻¹, φ.
-/
theorem fibonacci_registered_values :
    registeredValuesInBasin Basin.fibonacci =
      [
        .inverse .goldenRatio,
        .goldenRatio
      ] := by

  native_decide

/--
The structurally selected Wallis rows carry the registered values

    π⁻¹, π,
    γ⁻¹, γ,
    ζ(2)⁻¹, ζ(2),
    ζ(3)⁻¹, ζ(3).
-/
theorem wallis_registered_values :
    registeredValuesInBasin Basin.wallis =
      [
        .inverse .circleConstant,
        .circleConstant,
        .inverse .eulerMascheroni,
        .eulerMascheroni,
        .inverse (.zeta 2),
        .zeta 2,
        .inverse (.zeta 3),
        .zeta 3
      ] := by

  native_decide

/--
The structurally selected Alpha row carries the registered value 137.
-/
theorem alpha_registered_values :
    registeredValuesInBasin Basin.alpha =
      [
        .natural 137
      ] := by

  native_decide

/--
The Pascal basin contains the remaining 31 registered values,
including 147 but excluding the unique Alpha value 137.
-/
theorem pascal_registered_values :
    registeredValuesInBasin Basin.pascal =
      [
        .natural 1,
        .natural 2,
        .natural 3,
        .natural 4,
        .natural 7,
        .natural 8,

        .inverse .eulerNumber,
        .eulerNumber,

        .inverse (.squareRoot 2),
        .squareRoot 2,
        .inverse (.squareRoot 3),
        .squareRoot 3,
        .inverse (.squareRoot 5),
        .squareRoot 5,

        .inverse (.logarithmNatural 2),
        .logarithmNatural 2,
        .inverse (.logarithmNatural 3),
        .logarithmNatural 3,
        .inverse .logarithmGoldenRatio,
        .logarithmGoldenRatio,

        .inverse .sineOne,
        .sineOne,
        .inverse .cosineOne,
        .cosineOne,
        .inverse .hyperbolicTangentOne,
        .hyperbolicTangentOne,

        .natural 21,
        .natural 42,
        .natural 23,
        .natural 46,
        .natural 147
      ] := by

  native_decide

/--
The row lists selected by the four basins have lengths
`31, 2, 8, 1`.
-/
theorem glyph_number_lengths :
    (glyphNumbersInBasin Basin.pascal).length =
        31
      ∧
    (glyphNumbersInBasin Basin.fibonacci).length =
        2
      ∧
    (glyphNumbersInBasin Basin.wallis).length =
        8
      ∧
    (glyphNumbersInBasin Basin.alpha).length =
        1 := by

  native_decide

/--
The registered-value lists selected by the four structural basins have
the same `31, 2, 8, 1` multiplicities.
-/
theorem registered_value_lengths :
    (registeredValuesInBasin Basin.pascal).length =
        31
      ∧
    (registeredValuesInBasin Basin.fibonacci).length =
        2
      ∧
    (registeredValuesInBasin Basin.wallis).length =
        8
      ∧
    (registeredValuesInBasin Basin.alpha).length =
        1 := by

  native_decide

/--
The structural classifier selects glyph 41 as Pascal and glyph 42 as
Alpha.
-/
theorem boundary_pair_split :
    41 ∈ glyphNumbersInBasin Basin.pascal
      ∧
    42 ∈ glyphNumbersInBasin Basin.alpha
      ∧
    42 ∉ glyphNumbersInBasin Basin.pascal
      ∧
    41 ∉ glyphNumbersInBasin Basin.alpha := by

  native_decide

/--
Consequently, the registered boundary values 147 and 137 occupy
different structurally selected basins.
-/
theorem boundary_values_split :
    GlyphSpectrum.SpectralValue.natural 147 ∈
        registeredValuesInBasin Basin.pascal
      ∧
    GlyphSpectrum.SpectralValue.natural 137 ∈
        registeredValuesInBasin Basin.alpha
      ∧
    GlyphSpectrum.SpectralValue.natural 137 ∉
        registeredValuesInBasin Basin.pascal
      ∧
    GlyphSpectrum.SpectralValue.natural 147 ∉
        registeredValuesInBasin Basin.alpha := by

  native_decide

/--
Capstone bridge theorem.

The coordinate-derived sedenion classifier selects exactly the Denver
canonical row partition and therefore reproduces its registered
Fibonacci, Wallis, Alpha, and complementary Pascal spectral blocks.
-/
theorem forced_signature_matches_registered_table :
    glyphNumbersInBasin Basin.fibonacci =
        [7, 8]
      ∧
    glyphNumbersInBasin Basin.wallis =
        [11, 12, 31, 32, 33, 34, 35, 36]
      ∧
    glyphNumbersInBasin Basin.alpha =
        [42]
      ∧
    registeredValuesInBasin Basin.fibonacci =
        [
          .inverse .goldenRatio,
          .goldenRatio
        ]
      ∧
    registeredValuesInBasin Basin.wallis =
        [
          .inverse .circleConstant,
          .circleConstant,
          .inverse .eulerMascheroni,
          .eulerMascheroni,
          .inverse (.zeta 2),
          .zeta 2,
          .inverse (.zeta 3),
          .zeta 3
        ]
      ∧
    registeredValuesInBasin Basin.alpha =
        [
          .natural 137
        ] := by

  exact
    ⟨
      fibonacci_glyph_numbers,
      wallis_glyph_numbers,
      alpha_glyph_numbers,
      fibonacci_registered_values,
      wallis_registered_values,
      alpha_registered_values
    ⟩

end GlyphAttractorTableBridge

#check GlyphAttractorTableBridge.glyphNumbersInBasin
#check GlyphAttractorTableBridge.registeredValuesInBasin
#check GlyphAttractorTableBridge.fibonacci_glyph_numbers
#check GlyphAttractorTableBridge.wallis_glyph_numbers
#check GlyphAttractorTableBridge.alpha_glyph_numbers
#check GlyphAttractorTableBridge.pascal_glyph_numbers
#check GlyphAttractorTableBridge.fibonacci_registered_values
#check GlyphAttractorTableBridge.wallis_registered_values
#check GlyphAttractorTableBridge.alpha_registered_values
#check GlyphAttractorTableBridge.pascal_registered_values
#check GlyphAttractorTableBridge.glyph_number_lengths
#check GlyphAttractorTableBridge.registered_value_lengths
#check GlyphAttractorTableBridge.boundary_pair_split
#check GlyphAttractorTableBridge.boundary_values_split
#check GlyphAttractorTableBridge.forced_signature_matches_registered_table
