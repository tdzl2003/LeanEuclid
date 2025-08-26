

namespace Geometry

/-- Hilbert geometry definition, reference: https://www.gutenberg.org/files/17384/17384-pdf.pdf -/
class HilbertGeometry2D(Point: Type) where
  Line: Type

  /-- LiesOn: a is on the l -/
  LiesOn(a: Point)(l: Line): Prop
  /-- Between : b is Between a and c -/
  Between(a b c: Point): Prop

  /-- a b c is collinear -/
  Collinear (a b c : Point) : Prop := ∃ l : Line, LiesOn a l ∧ LiesOn b l ∧ LiesOn c l

  /-- axiom I.1: Two distinct points A and B always completely determine a straight line a. --/
  mk_line_from_points(a b: Point):  Line
  /-- axiom I.1: line a determined by points A and B should go throught them. --/
  mk_line_liesOn(a b: Point): LiesOn a (mk_line_from_points a b) ∧ LiesOn b (mk_line_from_points a b)

  /-- axiom I.2: Any two distinct points of a straight line completely determine that line; that is, if AB = a and AC = a, where B ̸= C, then is also BC = a. -/
  unique_line_from_two_points (a b: Point) (l: Line) : a ≠ b → LiesOn a l → LiesOn b l → l = mk_line_from_points a b

  /-- axiom I.7.1: Upon every straight line there exist at least two points -/
  line_exists_two_points(l: Line): ∃ a b: Point, a≠b ∧ LiesOn a l ∧ LiesOn b l

  /-- axiom I.7.2: in every plane at least three points not lying in the same straight line,-/
  exists_three_point_not_on_same_line: ∃ a b c: Point, a≠b ∧ b≠c ∧ a≠c ∧ ¬∃ l: Line, LiesOn a l ∧ LiesOn b l ∧ LiesOn c l

  /-- axiom II.1: If A, B, C are points of a straight line and B lies Between A and C, then B lies also Between C and A.-/
  between_symm(a b c: Point): Between a b c → Between c b a

  /-- axiom II.2.2 If A and C are two points of a straight line, at least one point D so situated that C lies Between A and D.-/
  extension_exists(a c: Point): a ≠ c → ∃ d: Point, Between a c d


end Geometry
