import Geometry.Basic

namespace Geometry.HilbertAxioms2D
  variable {Point Line: Type}[Membership Point Line][HilbertAxioms2D Point Line]

  structure BrokenLine{Line: Type}[Membership Point Line][HilbertAxioms2D Point Line] where
    vertices: List Point
    hc: vertices.length ≥ 2

  def BrokenLine.edgeAt (poly: BrokenLine (Point := Point) (Line := Line))(i: Fin (poly.vertices.length - 1)): Segment (Point := Point) (Line := Line) :=
    let v1 := poly.vertices.get ⟨i, by omega⟩
    let v2 := poly.vertices.get ⟨(i + 1), by omega⟩
    { p1 := v1, p2 := v2 }

  def BrokenLine.LiesOn (poly: BrokenLine (Point := Point) (Line := Line))(p: Point): Prop :=
    ∃ i : Fin (poly.vertices.length-1),
      let v1 := poly.vertices.get ⟨i, by omega⟩
      let v2 := poly.vertices.get ⟨(i + 1), by omega⟩
      OnSegment Line v1 p v2

  def BrokenLine.head (poly: BrokenLine (Point := Point) (Line := Line)): Point :=
    poly.vertices.head (by sorry)

  def BrokenLine.last (poly: BrokenLine (Point := Point) (Line := Line)): Point :=
    poly.vertices.getLast (by sorry)

  instance : Membership Point (BrokenLine (Point := Point) (Line := Line)) where
    mem := BrokenLine.LiesOn


  structure Polygon{Line: Type}[Membership Point Line][HilbertAxioms2D Point Line] where
    vertices: List Point
    hc: vertices.length ≥ 3

  def Polygon.edgeAt (poly: Polygon (Point := Point) (Line := Line))(i: Fin poly.vertices.length): Segment (Point := Point) (Line := Line) :=
    let v1 := poly.vertices.get i
    let v2 := poly.vertices.get ⟨(i + 1) % poly.vertices.length, by apply Nat.mod_lt; have := poly.hc; omega⟩
    { p1 := v1, p2 := v2 }

  def Polygon.isSimple (poly: Polygon (Point := Point) (Line := Line) ): Prop :=
    ∀ i j : Fin poly.vertices.length,
      i ≠ j →
      let e1 := poly.edgeAt i
      let e2 := poly.edgeAt j
      ∀ p: Point, p ∈ e1 → p ∈ e2 → False

  def Polygon.LiesOn (poly: Polygon (Point := Point) (Line := Line))(p: Point): Prop :=
    ∃ i : Fin poly.vertices.length,
      let v1 := poly.vertices.get i
      let v2 := poly.vertices.get ⟨(i + 1) % poly.vertices.length, by apply Nat.mod_lt; have := poly.hc; omega⟩
      OnSegment Line v1 p v2

  instance : Membership Point (Polygon (Point := Point) (Line := Line)) where
    mem := Polygon.LiesOn

  /--
  A polygonal region divides the plane into three mutually exclusive parts: inside, outside, and boundary.
  The inside and outside are both path-connected, and any path from a point inside to a point outside
  must cross the boundary.
  There is a theorem for this, but it's hard to define the inside and outside parts in a way that makes
  the theorem statement true. So we take the inside and outside as primitive notions, and add
  axioms that they satisfy.
    -/
  class PolygonalRegion(poly: Polygon (Point := Point) (Line := Line))(hSimple: poly.isSimple) where
    inside: Point → Prop
    outside: Point → Prop
    inside_outside_disjoint: ∀ p: Point, ¬(inside p ∧ outside p)
    inside_outside_boundary_exhaustive: ∀ p: Point, inside p ∨ outside p ∨ p ∈ poly
    inside_path_connected: ∀ a b: Point, inside a → inside b →
      ∃ (γ: BrokenLine (Point := Point) (Line := Line)),
        (∀ p: Point, p ∈ γ → inside p) ∧
        γ.head = a ∧
        γ.last = b
    outside_path_connected: ∀ a b: Point, outside a → outside b →
      ∃ (γ: BrokenLine (Point := Point) (Line := Line)),
        (∀ p: Point, p ∈ γ → outside p) ∧
        γ.head = a ∧
        γ.last = b
    crossing_edge: ∀ a b: Point, inside a → outside b →
      (∀ (γ: BrokenLine (Point := Point) (Line := Line)),
        γ.head = a →
        γ.last = b →
        ∃ p: Point, p ∈ γ ∧ p ∈ poly
      )
    not_exists_inside_line: ¬ ∃ l:Line, ∀ p ∈ l, inside p
    exists_outside_line: ∃ l: Line, ∀ p ∈ l, outside p

end Geometry.HilbertAxioms2D
