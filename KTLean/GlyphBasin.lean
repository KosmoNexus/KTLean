import KTLean.GlyphAddressFrobenius
import KTLean.GlyphSpectrum
import Mathlib.Tactic.FinCases

/-!
# Canonical glyph basins

The 42 canonical glyphs occur in seven blocks of six.

Each block shares one Fano line address and therefore one
canonical spectral basin:

0. fundamental integers
1. transcendental generators
2. algebraic roots
3. logarithmic operations
4. trigonometric operations
5. special functions
6. boundary/channel values

This module attaches that basin structure to the already
verified Frobenius glyph addresses.

It does not yet prove that the numerical spectral value of
each glyph is forced by its basin. It establishes the exact
finite classification on which that later forcing theorem
will operate.
-/

namespace GlyphBasin

/--
The seven canonical spectral basins of the 42-glyph table.
-/
inductive Basin where
  | integer
  | transcendental
  | algebraicRoot
  | logarithmic
  | trigonometric
  | specialFunction
  | boundary
  deriving DecidableEq, Repr

/--
The canonical basin attached to each Fano line.
-/
def basinOfLine : Fano.Point → Basin
  | 0 => .integer
  | 1 => .transcendental
  | 2 => .algebraicRoot
  | 3 => .logarithmic
  | 4 => .trigonometric
  | 5 => .specialFunction
  | 6 => .boundary

@[simp]
theorem basin_line_zero :
    basinOfLine 0 = .integer := by
  rfl

@[simp]
theorem basin_line_one :
    basinOfLine 1 = .transcendental := by
  rfl

@[simp]
theorem basin_line_two :
    basinOfLine 2 = .algebraicRoot := by
  rfl

@[simp]
theorem basin_line_three :
    basinOfLine 3 = .logarithmic := by
  rfl

@[simp]
theorem basin_line_four :
    basinOfLine 4 = .trigonometric := by
  rfl

@[simp]
theorem basin_line_five :
    basinOfLine 5 = .specialFunction := by
  rfl

@[simp]
theorem basin_line_six :
    basinOfLine 6 = .boundary := by
  rfl

/--
The basin of a canonical Frobenius glyph address is
determined entirely by its Fano line.
-/
def basinOfAddress
    (address : GlyphAddressFrobenius.Address) :
    Basin :=
  basinOfLine address.line

/--
Changing Frobenius step while preserving the line does
not change the basin.
-/
theorem basin_independent_of_step
    (line : Fano.Point)
    (leftStep rightStep : FrobeniusOrbit.Step)
    (orientation : Orientation) :
    basinOfAddress
        {
          line := line
          step := leftStep
          orientation := orientation
        } =
      basinOfAddress
        {
          line := line
          step := rightStep
          orientation := orientation
        } := by
  rfl

/--
Changing orientation while preserving the line does not
change the basin.
-/
theorem basin_independent_of_orientation
    (line : Fano.Point)
    (step : FrobeniusOrbit.Step)
    (leftOrientation rightOrientation : Orientation) :
    basinOfAddress
        {
          line := line
          step := step
          orientation := leftOrientation
        } =
      basinOfAddress
        {
          line := line
          step := step
          orientation := rightOrientation
        } := by
  rfl

/--
Each canonical basin contains exactly six glyph addresses:
three Frobenius steps and two orientations on one Fano line.
-/
def addressesInBasin
    (basin : Basin) :
    List GlyphAddressFrobenius.Address :=
  GlyphTable.coordinates
    |>.map GlyphAddressFrobenius.ofCoordinates
    |>.filter fun address =>
        basinOfAddress address = basin

theorem integer_basin_size :
    (addressesInBasin .integer).length = 6 := by
  native_decide

theorem transcendental_basin_size :
    (addressesInBasin .transcendental).length = 6 := by
  native_decide

theorem algebraicRoot_basin_size :
    (addressesInBasin .algebraicRoot).length = 6 := by
  native_decide

theorem logarithmic_basin_size :
    (addressesInBasin .logarithmic).length = 6 := by
  native_decide

theorem trigonometric_basin_size :
    (addressesInBasin .trigonometric).length = 6 := by
  native_decide

theorem specialFunction_basin_size :
    (addressesInBasin .specialFunction).length = 6 := by
  native_decide

theorem boundary_basin_size :
    (addressesInBasin .boundary).length = 6 := by
  native_decide

/--
Every canonical Frobenius glyph address belongs to exactly
one basin.
-/
theorem address_has_unique_basin
    (address : GlyphAddressFrobenius.Address) :
    ∃! basin : Basin,
      basinOfAddress address = basin := by
  refine ⟨basinOfAddress address, rfl, ?_⟩
  intro other h
  exact h.symm

/--
A readable row combining glyph number, Frobenius address,
basin, and symbolic spectral value.
-/
structure Row where
  glyphNumber : Nat
  line : Nat
  frobeniusStep : Nat
  orientation : Orientation
  basin : Basin
  spectralValue : GlyphSpectrum.SpectralValue
  deriving Repr

/--
Construct one displayed row directly from the original
bounded glyph coordinates and its registered spectrum.

The Fano line remains a `Fin 7` until after the basin has
been determined, so no artificial bound proof is needed.
-/
def rowOfIndexedPair
    (entry :
      (KTGlyph.Coordinates ×
        GlyphSpectrum.SpectralValue) × Nat) :
    Row :=
  let coords := entry.1.1
  let spectralValue := entry.1.2
  let index := entry.2
  let address :=
    GlyphAddressFrobenius.ofCoordinates coords

  {
    glyphNumber := index + 1
    line := address.line.val
    frobeniusStep := address.step.value.val
    orientation := address.orientation
    basin := basinOfLine address.line
    spectralValue := spectralValue
  }

/--
The complete canonical table with structural basin and
registered symbolic spectrum shown together.
-/
def table : List Row :=
  (GlyphTable.coordinates.zip GlyphSpectrum.values)
    |>.zipIdx
    |>.map rowOfIndexedPair

theorem table_length :
    table.length = 42 := by
  native_decide

/--
The twelfth canonical table row.
-/
def glyph12 : Row :=
  table.get
    ⟨11, by native_decide⟩

/--
The forty-second canonical table row.
-/
def glyph42 : Row :=
  table.get
    ⟨41, by native_decide⟩

/--
Glyph 12 lies in the transcendental basin.
-/
theorem glyph12_basin :
    glyph12.basin =
      Basin.transcendental := by
  native_decide

/--
Glyph 42 lies in the boundary basin.
-/
theorem glyph42_basin :
    glyph42.basin =
      Basin.boundary := by
  native_decide

/--
Glyph 12 carries the registered symbolic value π.
-/
theorem glyph12_value :
    glyph12.spectralValue =
      GlyphSpectrum.SpectralValue.circleConstant := by
  native_decide

/--
Glyph 42 carries the registered symbolic value 137.
-/
theorem glyph42_value :
    glyph42.spectralValue =
      GlyphSpectrum.SpectralValue.natural 137 := by
  native_decide

#eval table
#eval glyph12
#eval glyph42

end GlyphBasin
