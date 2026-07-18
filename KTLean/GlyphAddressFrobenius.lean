import KTLean.FrobeniusOrbit
import KTLean.GlyphTableProvenance

/-!
# Frobenius form of the canonical glyph address

The original admissible-operation coordinate type was constructed as

    Fano address × triadic role × orientation.

This module gives that three-element middle factor its canonical
Frobenius interpretation:

    anchor     ↔ 1
    successor  ↔ 2
    completion ↔ 4.

Thus every lawful glyph has an equivalent canonical address

    (a, r, σ)

with

    a ∈ Fin 7,
    r ∈ {1,2,4},
    σ ∈ {cw,ccw}.

This is an exact equivalence of finite coordinate systems, not a
change in the underlying glyph type.
-/

namespace GlyphAddressFrobenius

abbrev Role :=
  AdmissibleOperation.TriadicRole

/--
Interpret the original three triadic roles as the three
canonical Frobenius steps.
-/
def stepOfRole : Role → FrobeniusOrbit.Step
  | .anchor     => .one
  | .successor  => .two
  | .completion => .four

/--
Recover the original triadic role from a Frobenius step.
-/
def roleOfStep : FrobeniusOrbit.Step → Role
  | .one  => .anchor
  | .two  => .successor
  | .four => .completion

@[simp]
theorem roleOfStep_stepOfRole
    (role : Role) :
    roleOfStep (stepOfRole role) = role := by
  cases role <;> rfl

@[simp]
theorem stepOfRole_roleOfStep
    (step : FrobeniusOrbit.Step) :
    stepOfRole (roleOfStep step) = step := by
  cases step <;> rfl

/--
The original role type and the Frobenius-step type are
canonically equivalent.
-/
def roleEquivStep :
    Role ≃ FrobeniusOrbit.Step where
  toFun := stepOfRole
  invFun := roleOfStep
  left_inv := roleOfStep_stepOfRole
  right_inv := stepOfRole_roleOfStep

/--
The canonical Frobenius form of one glyph address.
-/
structure Address where
  line : Fano.Point
  step : FrobeniusOrbit.Step
  orientation : Orientation
  deriving DecidableEq, Repr

/--
Convert an existing lawful glyph coordinate into the
canonical `(line, Frobenius step, orientation)` form.
-/
def ofCoordinates
    (coords : KTGlyph.Coordinates) :
    Address :=
  {
    line := coords.address
    step := stepOfRole coords.role
    orientation := coords.orientation
  }

/--
Convert a canonical Frobenius address back into the
existing lawful glyph-coordinate representation.
-/
def toCoordinates
    (address : Address) :
    KTGlyph.Coordinates :=
  {
    address := address.line
    role := roleOfStep address.step
    orientation := address.orientation
  }

@[simp]
theorem toCoordinates_ofCoordinates
    (coords : KTGlyph.Coordinates) :
    toCoordinates (ofCoordinates coords) = coords := by
  cases coords
  simp [ofCoordinates, toCoordinates]

@[simp]
theorem ofCoordinates_toCoordinates
    (address : Address) :
    ofCoordinates (toCoordinates address) = address := by
  cases address
  simp [ofCoordinates, toCoordinates]

/--
The original coordinate space and the Frobenius-address
space are exactly equivalent.
-/
def coordinateEquivAddress :
    KTGlyph.Coordinates ≃ Address where
  toFun := ofCoordinates
  invFun := toCoordinates
  left_inv := toCoordinates_ofCoordinates
  right_inv := ofCoordinates_toCoordinates

/--
The Frobenius-address space is finite.
-/
instance addressFintype :
    Fintype Address :=
  Fintype.ofEquiv
    KTGlyph.Coordinates
    coordinateEquivAddress

/--
There are exactly 42 canonical Frobenius glyph addresses.
-/
theorem card_address :
    Fintype.card Address = 42 := by
  native_decide
/--
The numerical Frobenius step attached to an address.
-/
def stepValue
    (address : Address) :
    Fano.Point :=
  address.step.value

/--
A readable canonical glyph-address row.
-/
structure Row where
  glyphNumber : Nat
  line : Nat
  frobeniusStep : Nat
  orientation : Orientation
  selectedPoint : Nat
  deriving Repr

/--
Convert an existing verified glyph-table row and coordinate
into the richer Frobenius-address presentation.
-/
def rowOfIndexedCoordinate
    (entry : KTGlyph.Coordinates × Nat) :
    Row :=
  let coords := entry.1
  let address := ofCoordinates coords

  {
    glyphNumber := entry.2 + 1
    line := address.line.val
    frobeniusStep := address.step.value.val
    orientation := address.orientation
    selectedPoint :=
      (AdmissibleOperation.selectedPoint coords).val
  }

/--
The complete canonical table in `(a,r,σ)` notation.
-/
def table : List Row :=
  GlyphTable.coordinates.zipIdx.map rowOfIndexedCoordinate

theorem table_length :
    table.length = 42 := by
  native_decide

/--
Every canonical Frobenius address occurs in the table.
-/
theorem address_complete
    (address : Address) :
    ∃ coords ∈ GlyphTable.coordinates,
      ofCoordinates coords = address := by
  let coords := toCoordinates address

  refine ⟨coords, ?_, ?_⟩

  · exact
      GlyphTableProvenance.coordinates_complete coords

  · exact
      ofCoordinates_toCoordinates address

/--
The Frobenius table is nonredundant because its source
coordinate table is nonredundant and the conversion is
injective.
-/
theorem ofCoordinates_injective :
    Function.Injective ofCoordinates :=
  coordinateEquivAddress.injective

#eval table

end GlyphAddressFrobenius
