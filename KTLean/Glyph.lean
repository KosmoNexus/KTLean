import KTLean.OperationNormalForm

/-!
# KT Glyphs

The previous modules established that every operation
satisfying the oriented Fano frame law possesses one unique
normal form:

    Fano address × triadic role × orientation.

The normal-form space contains exactly

    7 × 3 × 2 = 42

elements.

This module canonically names those lawful local operations
`Glyph`.

No new multiplicity is postulated here. The glyph space is
the previously proved lawful-operation space.
-/

namespace KTGlyph


/--
A KT glyph is a lawful framed local operation.

Its Fano address, active triadic role, and orientation are
recoverable uniquely from its behavior.
-/
abbrev Glyph :=
  OperationNormalForm.LawfulFramedOperation


/--
The finite coordinate representation of a glyph.
-/
abbrev Coordinates :=
  AdmissibleOperation.Operation


/--
Construct a glyph from its structural coordinates.
-/
def ofCoordinates
    (coords : Coordinates) :
    Glyph :=

  OperationNormalForm.operationOf coords


/--
Recover the unique coordinates of a glyph.
-/
noncomputable def coordinates
    (glyph : Glyph) :
    Coordinates :=

  OperationNormalForm.coordinatesOf glyph


/--
Constructing a glyph and then recovering its coordinates
returns the original coordinates.
-/
@[simp]
theorem coordinates_ofCoordinates
    (coords : Coordinates) :

    coordinates
        (ofCoordinates coords) =
      coords := by

  exact
    OperationNormalForm.coordinatesOf_operationOf
      coords


/--
Recovering coordinates and then reconstructing returns the
original glyph.
-/
@[simp]
theorem ofCoordinates_coordinates
    (glyph : Glyph) :

    ofCoordinates
        (coordinates glyph) =
      glyph := by

  exact
    OperationNormalForm.operationOf_coordinatesOf
      glyph


/--
Glyphs are equivalent to their unique prime-structured
coordinate normal forms.
-/
noncomputable def glyphEquivCoordinates :

    Glyph ≃ Coordinates :=

  OperationNormalForm.normalFormEquiv


/-
## Structural components
-/

/--
The Fano address of a glyph.
-/
def address
    (glyph : Glyph) :
    Fano.Point :=

  glyph.address


/--
The active triadic role of a glyph.
-/
def role
    (glyph : Glyph) :
    AdmissibleOperation.TriadicRole :=

  glyph.activeRole


/--
The orientation recovered from the glyph frame.
-/
noncomputable def orientation
    (glyph : Glyph) :
    Orientation :=

  OperationNormalForm.orientationOf glyph


/--
The coordinate address agrees with the glyph address.
-/
@[simp]
theorem coordinates_address
    (glyph : Glyph) :

    (coordinates glyph).address =
      address glyph := by

  rfl


/--
The coordinate role agrees with the glyph active role.
-/
@[simp]
theorem coordinates_role
    (glyph : Glyph) :

    (coordinates glyph).role =
      role glyph := by

  rfl


/--
The coordinate orientation is exactly the orientation
recovered from the lawful glyph frame.
-/
@[simp]
theorem coordinates_orientation
    (glyph : Glyph) :

    (coordinates glyph).orientation =
      orientation glyph := by

  rfl


/-
## Equality and rigidity
-/

/--
Two glyphs with equal coordinates are equal.
-/
theorem eq_of_coordinates_eq
    {left right : Glyph}
    (hcoordinates :
      coordinates left =
        coordinates right) :

    left = right := by

  have h :=
    congrArg ofCoordinates hcoordinates

  simpa using h


/--
Distinct coordinates determine distinct glyphs.
-/
theorem ne_of_coordinates_ne
    {left right : Coordinates}
    (hcoordinates :
      left ≠ right) :

    ofCoordinates left ≠
      ofCoordinates right := by

  intro hglyphs

  have h :=
    congrArg coordinates hglyphs

  have hleft :
      coordinates (ofCoordinates left) =
        left := by

    exact coordinates_ofCoordinates left

  have hright :
      coordinates (ofCoordinates right) =
        right := by

    exact coordinates_ofCoordinates right

  rw [hleft, hright] at h

  exact hcoordinates h

/--
Two glyphs are equal exactly when their structural
coordinates are equal.
-/
theorem coordinates_injective :

    Function.Injective coordinates := by

  intro left right hcoordinates

  exact
    eq_of_coordinates_eq
      hcoordinates


/--
Every structural coordinate triple corresponds to one
glyph.
-/
theorem coordinates_surjective :

    Function.Surjective coordinates := by

  intro coords

  exact
    ⟨
      ofCoordinates coords,
      coordinates_ofCoordinates coords
    ⟩


/--
Every glyph possesses one unique structural coordinate
triple.
-/
theorem unique_coordinates
    (glyph : Glyph) :

    ∃! coords : Coordinates,

      ofCoordinates coords =
        glyph := by

  exact
    OperationNormalForm.unique_normal_form
      glyph


/-
## Enumeration
-/

/--
The glyph space contains exactly 42 elements.
-/
theorem card_glyph :

    Fintype.card Glyph = 42 := by

  exact
    OperationNormalForm.lawful_operation_card


/--
The glyph count factors into the prime structural
components seven, three, and two.
-/
theorem card_glyph_prime_structure :

    Fintype.card Glyph =
      7 * 3 * 2 := by

  exact
    OperationNormalForm.lawful_operation_card_prime_structure


/--
The glyph count is the product of the cardinalities of its
three independently recoverable coordinates.
-/
theorem card_glyph_coordinate_product :

    Fintype.card Glyph =

      Fintype.card Fano.Point
        *
      Fintype.card AdmissibleOperation.TriadicRole
        *
      Fintype.card Orientation := by

  calc

    Fintype.card Glyph =
        42 :=

      card_glyph

    _ =
        7 * 3 * 2 := by

      decide

    _ =
        Fintype.card Fano.Point
          *
        Fintype.card AdmissibleOperation.TriadicRole
          *
        Fintype.card Orientation := by

      rw [
        AdmissibleOperation.fanoPoint_card,
        AdmissibleOperation.triadicRole_card,
        AdmissibleOperation.orientation_card
      ]


/-
## Canonical glyph constructor
-/

/--
Construct one glyph directly from a Fano address, triadic
role, and orientation.
-/
def mk
    (glyphAddress : Fano.Point)
    (glyphRole :
      AdmissibleOperation.TriadicRole)
    (glyphOrientation : Orientation) :
    Glyph :=

  ofCoordinates
    {
      address := glyphAddress
      role := glyphRole
      orientation := glyphOrientation
    }


/--
The coordinates of a directly constructed glyph are
exactly the supplied coordinates.
-/
@[simp]
theorem coordinates_mk
    (glyphAddress : Fano.Point)
    (glyphRole :
      AdmissibleOperation.TriadicRole)
    (glyphOrientation : Orientation) :

    coordinates
        (mk glyphAddress glyphRole glyphOrientation) =

      {
        address := glyphAddress
        role := glyphRole
        orientation := glyphOrientation
      } := by

  exact
    coordinates_ofCoordinates
      {
        address := glyphAddress
        role := glyphRole
        orientation := glyphOrientation
      }


/--
A glyph constructor is injective in all three structural
coordinates.
-/
theorem mk_eq_mk_iff
    {address₁ address₂ : Fano.Point}
    {role₁ role₂ :
      AdmissibleOperation.TriadicRole}
    {orientation₁ orientation₂ :
      Orientation} :

    mk address₁ role₁ orientation₁ =
        mk address₂ role₂ orientation₂
      ↔

    address₁ = address₂
      ∧
    role₁ = role₂
      ∧
    orientation₁ = orientation₂ := by

  constructor

  · intro hglyph

    have hcoordinates :=
      congrArg coordinates hglyph

    simp only [
      coordinates_mk
    ] at hcoordinates

    exact
      ⟨
        congrArg
          AdmissibleOperation.Coordinates.address
          hcoordinates,

        congrArg
          AdmissibleOperation.Coordinates.role
          hcoordinates,

        congrArg
          AdmissibleOperation.Coordinates.orientation
          hcoordinates
      ⟩

  · intro hcoordinates

    rcases hcoordinates with
      ⟨haddress, hrole, horientation⟩

    subst address₂
    subst role₂
    subst orientation₂

    rfl


end KTGlyph
