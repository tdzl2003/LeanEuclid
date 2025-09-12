import Geometry.Basic
import Mathlib.Tactic.Linarith

namespace Geometry
  structure BrokenLine(Point: Type)[G: PointOrder Point][Membership Point (Segment Point)] where
    vertices: List Point
    hc: vertices.length ≥ 2

  variable {Point}[G: PointOrder Point][Membership Point (Segment Point)]

  def BrokenLine.edgeAt
    (poly: BrokenLine Point)(i: Fin (poly.vertices.length - 1)):
      Segment (Point := Point) :=
    let v1 := poly.vertices.get ⟨i, by omega⟩
    let v2 := poly.vertices.get ⟨(i + 1), by omega⟩
    { p1 := v1, p2 := v2 }

  def BrokenLine.vertices_not_empty(poly: BrokenLine Point):
    poly.vertices ≠ [] :=
  by
    intro he
    have h1: poly.vertices.length = 0  := by
      rw [he]
      simp only [List.length_nil]
    have h2:= poly.hc
    linarith

  def BrokenLine.head (poly: BrokenLine Point): Point :=
    poly.vertices.head poly.vertices_not_empty

  def BrokenLine.last (poly: BrokenLine Point): Point :=
    poly.vertices.getLast poly.vertices_not_empty

  instance : Membership Point (BrokenLine Point) where
    mem(bl: BrokenLine Point)(p: Point) := ∃ i, p ∈ bl.edgeAt i

end Geometry

namespace Geometry.HilbertAxioms2D

  structure Polygon(Point: Type) where
    vertices: List Point
    hc: vertices.length ≥ 3

  variable {Point}[G: PointOrder Point][Membership Point (Segment Point)]

  def Polygon.edgeAt (poly: Polygon Point)(i: Fin poly.vertices.length): Segment Point :=
    let v1 := poly.vertices.get i
    let v2 := poly.vertices.get ⟨(i + 1) % poly.vertices.length, by apply Nat.mod_lt; have := poly.hc; omega⟩
    { p1 := v1, p2 := v2 }

  def Polygon.isSimple (poly: Polygon Point): Prop :=
    ∀ i j : Fin poly.vertices.length,
      i ≠ j →
      ∀ p: Point, p ∈ poly.edgeAt i → p ∈ poly.edgeAt j → False


  instance : Membership Point (Polygon Point) where
    mem(poly: Polygon Point)(p: Point) :=
      ∃ i : Fin poly.vertices.length,
        p ∈ poly.edgeAt i

  /--
  A polygonal region divides the plane into three mutually exclusive parts: inside, outside, and boundary.
  The inside and outside are both path-connected, and any path from a point inside to a point outside
  must cross the boundary.
  There is a theorem for this, but it's hard to define the inside and outside parts in a way that makes
  the theorem statement true. So we take the inside and outside as primitive notions, and add
  axioms that they satisfy.
    -/
  class PolygonalRegionConnection(poly: Polygon Point)(hSimple: poly.isSimple) extends LineDef Point where
    inside: Point → Prop
    outside: Point → Prop
    inside_outside_disjoint: ∀ p: Point, ¬(inside p ∧ outside p)
    inside_outside_boundary_exhaustive: ∀ p: Point, inside p ∨ outside p ∨ p ∈ poly
    inside_path_connected: ∀ a b: Point, inside a → inside b →
      ∃ (γ: BrokenLine Point),
        (∀ p: Point, p ∈ γ → inside p) ∧
        γ.head = a ∧
        γ.last = b
    outside_path_connected: ∀ a b: Point, outside a → outside b →
      ∃ (γ: BrokenLine Point),
        (∀ p: Point, p ∈ γ → outside p) ∧
        γ.head = a ∧
        γ.last = b
    crossing_edge: ∀ a b: Point, inside a → outside b →
      (∀ (γ: BrokenLine Point),
        γ.head = a →
        γ.last = b →
        ∃ p: Point, p ∈ γ ∧ p ∈ poly
      )
    not_exists_inside_line: ¬ ∃ l:Line, ∀ p ∈ l, inside p
    exists_outside_line: ∃ l:Line, ∀ p ∈ l, outside p

end Geometry.HilbertAxioms2D
