import Geometry.Basic
import Mathlib.Data.Real.Basic

namespace Geometry.Analytic
  /-- Define a point a (x, y) -/
  structure Point where
    x: ℝ
    y: ℝ

  /-- Define a line by ax + by + c = 0-/
  structure Line where
    a: ℝ
    b: ℝ
    c: ℝ

  instance: HMul Point Real Point where
    hMul(a: Point)(b: Real) := Point.mk (a.x*b) (a.y*b)

  instance: Add Point where
    add(a: Point)(b: Point) :=  Point.mk (a.x+b.x) (a.y+b.y)

  def liesOn(a: Point)(l: Line): Prop :=
    l.a * a.x + l.b * a.y + l.c = 0

  def between(a: Point)(b: Point)(c: Point): Prop :=
    ∃ r: ℝ, r > 0 ∧ r < 1 ∧ a = b * r + c* (r-1)

  def mk_line_from_points(a b: Point): Line :=
    Line.mk (b.y-a.y) (a.x-b.x) (b.x*a.y - a.x*b.y)

  theorem mk_line_liesOn(a b: Point):
    liesOn a (mk_line_from_points a b) ∧ liesOn b (mk_line_from_points a b) := by
      sorry

  theorem unique_line_from_two_points(a b: Point)(l: Line):
    a ≠ b → liesOn a l → liesOn b l → l = mk_line_from_points a b := by
      sorry

  theorem line_exists_two_points(l: Line):
    ∃ a b: Point, a≠b ∧ liesOn a l ∧ liesOn b l := by
      sorry

  theorem exists_three_point_not_on_same_line:
    ∃ a b c: Point, a≠b ∧ b≠c ∧ a≠c ∧ ¬∃ l: Line, liesOn a l ∧ liesOn b l ∧ liesOn c l := by
      sorry

  noncomputable instance: HilbertGeometry2D Point Line where
    liesOn := liesOn
    between := between
    mk_line_from_points := mk_line_from_points
    mk_line_liesOn := mk_line_liesOn
    unique_line_from_two_points := unique_line_from_two_points
    line_exists_two_points := line_exists_two_points
    exists_three_point_not_on_same_line := exists_three_point_not_on_same_line

end Geometry.Analytic
