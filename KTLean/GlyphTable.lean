import KTLean.Glyph

/-!
# Complete table of the 42 KT glyphs

Each glyph is displayed through its unique canonical coordinates:

* one of seven Fano addresses;
* one of three triadic roles;
* one of two orientations.

The selected Fano point determined by those coordinates is also shown.

This module provides an executable readout of the complete
42-glyph normal-form space.
-/

namespace GlyphTable

/--
A readable row in the complete glyph table.
-/
structure Row where
  index : Nat
  address : Nat
  role : AdmissibleOperation.TriadicRole
  orientation : Orientation
  selectedPoint : Nat
  deriving Repr

/--
The seven Fano addresses in canonical order.
-/
def addresses :
    List Fano.Point :=
  [0, 1, 2, 3, 4, 5, 6]

/--
The three triadic roles in canonical order.
-/
def roles :
    List AdmissibleOperation.TriadicRole :=
  [
    AdmissibleOperation.TriadicRole.anchor,
    AdmissibleOperation.TriadicRole.successor,
    AdmissibleOperation.TriadicRole.completion
  ]

/--
The two orientations in canonical order.
-/
def orientations :
    List Orientation :=
  [
    Orientation.cw,
    Orientation.ccw
  ]

/--
The canonical computable enumeration of all glyph coordinates.

The order is:

    address
      → role
        → orientation.
-/
def coordinates :
    List KTGlyph.Coordinates :=
  addresses.flatMap fun address =>
    roles.flatMap fun role =>
      orientations.map fun orientation =>
        {
          address := address
          role := role
          orientation := orientation
        }

/--
Convert one indexed coordinate triple into a readable row.

`List.zipIdx` returns `(entry, index)`.
-/
def rowOfCoordinate
    (entry : KTGlyph.Coordinates × Nat) :
    Row :=
  let coords := entry.1
  let index := entry.2

  {
    index := index
    address := coords.address.val
    role := coords.role
    orientation := coords.orientation
    selectedPoint :=
      (AdmissibleOperation.selectedPoint coords).val
  }

/--
The complete table of all 42 KT glyphs.
-/
def table :
    List Row :=
  coordinates.zipIdx.map rowOfCoordinate

/--
The coordinate enumeration contains exactly 42 entries.
-/
theorem coordinates_length :
    coordinates.length = 42 := by
  native_decide

/--
The displayed glyph table contains exactly 42 rows.
-/
theorem table_length :
    table.length = 42 := by
  native_decide

#eval table

end GlyphTable
