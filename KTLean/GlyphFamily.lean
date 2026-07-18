import KTLean.GlyphAddressFrobenius
import KTLean.GlyphSpectrum
import Mathlib.Tactic.FinCases

/-!
# Canonical glyph families

The 42 canonical glyphs occur in seven blocks of six.

Each block shares one Fano line address and therefore one
canonical spectral family:

0. fundamental integers
1. transcendental generators
2. algebraic roots
3. logarithmic operations
4. trigonometric operations
5. special functions
6. boundary/channel values

This module attaches that family structure to the already
verified Frobenius glyph addresses.

It does not yet prove that the numerical spectral value of
each glyph is forced by its family. It establishes the exact
finite classification on which that later forcing theorem
will operate.
-/

namespace GlyphFamily

/--
The seven canonical spectral families of the 42-glyph table.
-/
inductive Family where
  | integer
  | transcendental
  | algebraicRoot
  | logarithmic
  | trigonometric
  | specialFunction
  | boundary
  deriving DecidableEq, Repr

/--
The canonical family attached to each Fano line.
-/
def familyOfLine : Fano.Point → Family
  | 0 => .integer
  | 1 => .transcendental
  | 2 => .algebraicRoot
  | 3 => .logarithmic
  | 4 => .trigonometric
  | 5 => .specialFunction
  | 6 => .boundary

@[simp]
theorem family_line_zero :
    familyOfLine 0 = .integer := by
  rfl

@[simp]
theorem family_line_one :
    familyOfLine 1 = .transcendental := by
  rfl

@[simp]
theorem family_line_two :
    familyOfLine 2 = .algebraicRoot := by
  rfl

@[simp]
theorem family_line_three :
    familyOfLine 3 = .logarithmic := by
  rfl

@[simp]
theorem family_line_four :
    familyOfLine 4 = .trigonometric := by
  rfl

@[simp]
theorem family_line_five :
    familyOfLine 5 = .specialFunction := by
  rfl

@[simp]
theorem family_line_six :
    familyOfLine 6 = .boundary := by
  rfl

/--
The family of a canonical Frobenius glyph address is
determined entirely by its Fano line.
-/
def familyOfAddress
    (address : GlyphAddressFrobenius.Address) :
    Family :=
  familyOfLine address.line

/--
Changing Frobenius step while preserving the line does
not change the family.
-/
theorem family_independent_of_step
    (line : Fano.Point)
    (leftStep rightStep : FrobeniusOrbit.Step)
    (orientation : Orientation) :
    familyOfAddress
        {
          line := line
          step := leftStep
          orientation := orientation
        } =
      familyOfAddress
        {
          line := line
          step := rightStep
          orientation := orientation
        } := by
  rfl

/--
Changing orientation while preserving the line does not
change the family.
-/
theorem family_independent_of_orientation
    (line : Fano.Point)
    (step : FrobeniusOrbit.Step)
    (leftOrientation rightOrientation : Orientation) :
    familyOfAddress
        {
          line := line
          step := step
          orientation := leftOrientation
        } =
      familyOfAddress
        {
          line := line
          step := step
          orientation := rightOrientation
        } := by
  rfl

/--
Each canonical family contains exactly six glyph addresses:
three Frobenius steps and two orientations on one Fano line.
-/
def addressesInFamily
    (family : Family) :
    List GlyphAddressFrobenius.Address :=
  GlyphTable.coordinates
    |>.map GlyphAddressFrobenius.ofCoordinates
    |>.filter fun address =>
        familyOfAddress address = family

theorem integer_family_size :
    (addressesInFamily .integer).length = 6 := by
  native_decide

theorem transcendental_family_size :
    (addressesInFamily .transcendental).length = 6 := by
  native_decide

theorem algebraicRoot_family_size :
    (addressesInFamily .algebraicRoot).length = 6 := by
  native_decide

theorem logarithmic_family_size :
    (addressesInFamily .logarithmic).length = 6 := by
  native_decide

theorem trigonometric_family_size :
    (addressesInFamily .trigonometric).length = 6 := by
  native_decide

theorem specialFunction_family_size :
    (addressesInFamily .specialFunction).length = 6 := by
  native_decide

theorem boundary_family_size :
    (addressesInFamily .boundary).length = 6 := by
  native_decide

/--
Every canonical Frobenius glyph address belongs to exactly
one family.
-/
theorem address_has_unique_family
    (address : GlyphAddressFrobenius.Address) :
    ∃! family : Family,
      familyOfAddress address = family := by
  refine ⟨familyOfAddress address, rfl, ?_⟩
  intro other h
  exact h.symm

/--
A readable row combining glyph number, Frobenius address,
family, and symbolic spectral value.
-/
structure Row where
  glyphNumber : Nat
  line : Nat
  frobeniusStep : Nat
  orientation : Orientation
  family : Family
  spectralValue : GlyphSpectrum.SpectralValue
  deriving Repr

/--
Construct one displayed row directly from the original
bounded glyph coordinates and its registered spectrum.

The Fano line remains a `Fin 7` until after the family has
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
    family := familyOfLine address.line
    spectralValue := spectralValue
  }

/--
The complete canonical table with structural family and
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
Glyph 12 lies in the transcendental family.
-/
theorem glyph12_family :
    glyph12.family =
      Family.transcendental := by
  native_decide

/--
Glyph 42 lies in the boundary family.
-/
theorem glyph42_family :
    glyph42.family =
      Family.boundary := by
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

end GlyphFamily
