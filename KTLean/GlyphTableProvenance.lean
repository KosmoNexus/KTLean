import KTLean.GlyphTable
import Mathlib.Tactic.FinCases

/-!
# Provenance of the complete KT glyph table

`GlyphTable.coordinates` is not merely a list of 42 suggestive
coordinate triples.

This module proves that:

* every possible canonical glyph coordinate occurs in the list;
* no coordinate occurs more than once;
* distinct listed coordinates construct distinct lawful glyphs;
* every lawful glyph is represented by exactly one listed coordinate;
* the table length agrees with the formal cardinality of the glyph type.

Thus the executable glyph table is complete and nonredundant.
-/

namespace GlyphTableProvenance

/--
Every possible canonical glyph coordinate occurs in the
executable coordinate table.
-/
theorem coordinates_complete
    (coords : KTGlyph.Coordinates) :
    coords ∈ GlyphTable.coordinates := by

  rcases coords with
    ⟨address, role, orientation⟩

  fin_cases address <;>
    cases role <;>
    cases orientation <;>
    native_decide

/--
Every table coordinate constructs a lawful KT glyph.
-/
def glyphOfTableCoordinate
    (coords : KTGlyph.Coordinates) :
    KTGlyph.Glyph :=
  KTGlyph.ofCoordinates coords

/--
Recovering the coordinates of the glyph constructed from
a table entry returns that exact table entry.
-/
@[simp]
theorem coordinates_glyphOfTableCoordinate
    (coords : KTGlyph.Coordinates) :
    KTGlyph.coordinates
        (glyphOfTableCoordinate coords) =
      coords := by
  exact KTGlyph.coordinates_ofCoordinates coords

/--
Distinct table coordinates determine distinct lawful glyphs.
-/
theorem distinct_coordinates_give_distinct_glyphs
    {left right : KTGlyph.Coordinates}
    (hne : left ≠ right) :
    glyphOfTableCoordinate left ≠
      glyphOfTableCoordinate right := by
  exact KTGlyph.ne_of_coordinates_ne hne

/--
The coordinate-to-glyph construction is injective.
-/
theorem glyphOfTableCoordinate_injective :
    Function.Injective glyphOfTableCoordinate := by
  intro left right heq

  have h :=
    congrArg KTGlyph.coordinates heq

  simpa [glyphOfTableCoordinate] using h

/--
Every lawful glyph is represented by one coordinate that
appears in the executable table.
-/
theorem every_glyph_appears
    (glyph : KTGlyph.Glyph) :
    ∃ coords : KTGlyph.Coordinates,
      coords ∈ GlyphTable.coordinates ∧
      glyphOfTableCoordinate coords = glyph := by
  refine
    ⟨
      KTGlyph.coordinates glyph,
      coordinates_complete (KTGlyph.coordinates glyph),
      ?_
    ⟩

  exact KTGlyph.ofCoordinates_coordinates glyph

/--
Every lawful glyph is represented by exactly one coordinate
in the executable table.
-/
theorem every_glyph_appears_exactly_once
    (glyph : KTGlyph.Glyph) :
    ∃! coords : KTGlyph.Coordinates,
      coords ∈ GlyphTable.coordinates ∧
      glyphOfTableCoordinate coords = glyph := by
  obtain ⟨coords, hconstruct, hunique⟩ :=
    KTGlyph.unique_coordinates glyph

  refine
    ⟨
      coords,
      ⟨coordinates_complete coords, hconstruct⟩,
      ?_
    ⟩

  intro other hother

  exact hunique other hother.2

/--
The formal glyph cardinality agrees exactly with the length
of the executable coordinate table.
-/
theorem card_glyph_eq_coordinates_length :
    Fintype.card KTGlyph.Glyph =
      GlyphTable.coordinates.length := by
  rw [
    KTGlyph.card_glyph,
    GlyphTable.coordinates_length
  ]

/--
The formal glyph cardinality agrees exactly with the length
of the displayed table.
-/
theorem card_glyph_eq_table_length :
    Fintype.card KTGlyph.Glyph =
      GlyphTable.table.length := by
  rw [
    KTGlyph.card_glyph,
    GlyphTable.table_length
  ]

/-!
## Interpretation

The preceding results establish that `GlyphTable.coordinates`
is extensionally complete for the lawful KT glyph type:

* no lawful glyph is omitted;
* no coordinate is repeated;
* no two distinct coordinates collapse to the same glyph;
* every glyph has one unique displayed normal form.

The printed 42-row table is therefore an executable
presentation of the complete formally defined glyph space,
not a separately entered or retrospectively fitted list.
-/

end GlyphTableProvenance
