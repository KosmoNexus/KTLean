import KTLean.GlyphTableProvenance

/-!
# Canonical spectrum of the 42 KT glyphs

This module attaches the canonical K-set spectral value to each
of the 42 formally enumerated glyph positions.

The address table and the spectral assignment remain explicitly
separated:

* `GlyphTable` supplies the lawful canonical glyph coordinates;
* `GlyphSpectrum` supplies the proposed canonical eigenvalue assignment.

This distinction is important. The 42-address structure has already
been formally derived and proved complete. The spectral values below
encode the canonical KT spectral correspondence that subsequent
modules must derive from recurrence and projection.
-/

namespace GlyphSpectrum

/--
Exact symbolic forms of the values occurring in the canonical
42-element KT spectrum.
-/
inductive SpectralValue where
  | natural : Nat → SpectralValue
  | inverse : SpectralValue → SpectralValue
  | goldenRatio : SpectralValue
  | eulerNumber : SpectralValue
  | circleConstant : SpectralValue
  | squareRoot : Nat → SpectralValue
  | logarithmNatural : Nat → SpectralValue
  | logarithmGoldenRatio : SpectralValue
  | sineOne : SpectralValue
  | cosineOne : SpectralValue
  | hyperbolicTangentOne : SpectralValue
  | eulerMascheroni : SpectralValue
  | zeta : Nat → SpectralValue
  deriving Repr, DecidableEq

/--
The canonical spectrum in glyph order 1 through 42.
-/
def values : List SpectralValue :=
  [
    -- Glyphs 1–6: fundamental integers
    .natural 1,
    .natural 2,
    .natural 3,
    .natural 4,
    .natural 7,
    .natural 8,

    -- Glyphs 7–12: transcendental generators
    .inverse .goldenRatio,
    .goldenRatio,
    .inverse .eulerNumber,
    .eulerNumber,
    .inverse .circleConstant,
    .circleConstant,

    -- Glyphs 13–18: algebraic roots
    .inverse (.squareRoot 2),
    .squareRoot 2,
    .inverse (.squareRoot 3),
    .squareRoot 3,
    .inverse (.squareRoot 5),
    .squareRoot 5,

    -- Glyphs 19–24: logarithmic operations
    .inverse (.logarithmNatural 2),
    .logarithmNatural 2,
    .inverse (.logarithmNatural 3),
    .logarithmNatural 3,
    .inverse .logarithmGoldenRatio,
    .logarithmGoldenRatio,

    -- Glyphs 25–30: trigonometric operations
    .inverse .sineOne,
    .sineOne,
    .inverse .cosineOne,
    .cosineOne,
    .inverse .hyperbolicTangentOne,
    .hyperbolicTangentOne,

    -- Glyphs 31–36: special functions
    .inverse .eulerMascheroni,
    .eulerMascheroni,
    .inverse (.zeta 2),
    .zeta 2,
    .inverse (.zeta 3),
    .zeta 3,

    -- Glyphs 37–42: boundary values
    .natural 21,
    .natural 42,
    .natural 23,
    .natural 46,
    .natural 147,
    .natural 137
  ]

/--
The canonical spectrum contains exactly 42 values.
-/
theorem values_length :
    values.length = 42 := by
  native_decide

/--
A numbered spectral entry.
-/
structure Entry where
  glyphNumber : Nat
  value : SpectralValue
  deriving Repr

/--
Convert the zero-based index supplied by `List.zipIdx`
to the conventional one-based glyph number.
-/
def entryOfIndexedValue
    (entry : SpectralValue × Nat) :
    Entry :=
  {
    glyphNumber := entry.2 + 1
    value := entry.1
  }

/--
The complete numbered spectrum.
-/
def spectrum : List Entry :=
  values.zipIdx.map entryOfIndexedValue

/--
The displayed spectrum also contains exactly 42 entries.
-/
theorem spectrum_length :
    spectrum.length = 42 := by
  native_decide

/--
Attach the proposed spectral assignment to the already verified
canonical coordinate table.
-/
def coordinateSpectrum :
    List (GlyphTable.Row × SpectralValue) :=
  GlyphTable.table.zip values

/--
The coordinate-and-value spectrum contains exactly 42 rows.
-/
theorem coordinateSpectrum_length :
    coordinateSpectrum.length = 42 := by
  native_decide

#eval spectrum

end GlyphSpectrum
