import Geometry.Basic

namespace Euclid

  axiom Point: Type

  axiom Line: Type

  /-- liesOn: a is on the l -/
  axiom liesOn(a: Point)(l: Line): Prop
  /-- between : a is between b and c -/
  axiom between(a b c: Point): Point → Point → Point → Prop

  /-- axiom I.1: Two distinct points A and B always completely determine a straight line a. --/
  axiom mk_line_from_points(a b: Point):  Line
  /-- axiom I.1: line a determined by points A and B should go throught them. --/
  axiom mk_line_liesOn(a b: Point): liesOn a (mk_line_from_points a b) ∧ liesOn b (mk_line_from_points a b)

  /-- axiom I.2: Any two distinct points of a straight line completely determine that line; that is, if AB = a and AC = a, where B ̸= C, then is also BC = a. -/
  axiom unique_line_from_two_points (a b: Point) (l: Line) : a ≠ b → liesOn a l → liesOn b l → mk_line_from_points a b = l

  /-- axiom I.7.1: Upon every straight line there exist at least two points -/
  axiom line_exists_two_points(l: Line): ∃ a b: Point, a≠b ∧ liesOn a l ∧ liesOn b l

  /-- axiom I.7.2: in every plane at least three points not lying in the same straight line,-/
  axiom exists_three_point_not_on_same_line: ∃ a b c: Point, a≠b ∧ b≠c ∧ a≠c ∧ ¬∃ l: Line, liesOn a l ∧ liesOn b l ∧ liesOn c l

  noncomputable instance: HilbertGeometry2D Point Line where
    liesOn := liesOn
    between := between
    mk_line_from_points := mk_line_from_points
    mk_line_liesOn := mk_line_liesOn
    unique_line_from_two_points := unique_line_from_two_points
    line_exists_two_points := line_exists_two_points
    exists_three_point_not_on_same_line := exists_three_point_not_on_same_line

end Euclid
