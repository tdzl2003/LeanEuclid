import Geometry.Basic

namespace Geometry.Euclid

  axiom Point: Type

  axiom Line: Type

  /-- Between : a is Between b and c -/
  axiom Between(a b c: Point): Prop

  /-- Between relation is exclusive. -/
  axiom between_ne(a b c: Point): Between a b c → a ≠ b ∨ b ≠ c

  /-- axiom II.1: If A, B, C are points of a straight line and B lies Between A and C, then B lies also Between C and A.-/
  axiom between_symm(a b c: Point): Between a b c → Between c b a

  /-- axiom II.2.2 If A and C are two points of a straight line, at least one point D so situated that C lies Between A and D.-/
  axiom extension_exists(a c: Point): a ≠ c → ∃ d: Point, Between a c d

  /-- LiesOn: a is on the l -/
  axiom LiesOn(a: Point)(l: Line): Prop

  /-- axiom I.1: Two distinct points A and B always completely determine a straight line a. --/
  axiom mk_line(a b: Point)(hne: a ≠ b):  Line

  /-- axiom I.1: line a determined by points A and B should go throught them. --/
  axiom mk_line_liesOn(a b: Point)(h: a≠ b): LiesOn a (mk_line a b h) ∧ LiesOn b (mk_line a b h)

  /-- axiom I.2: Any two distinct points of a straight line completely determine that line; that is, if AB = a and AC = a, where B ̸= C, then is also BC = a. -/
  axiom unique_line_from_two_points (a b: Point) (l: Line)(h:  a ≠ b) : LiesOn a l → LiesOn b l → l = mk_line a b h

  /-- axiom I.7.1: Upon every straight line there exist at least two points -/
  axiom line_exists_two_points(l: Line): ∃ a b: Point, a≠b ∧ LiesOn a l ∧ LiesOn b l

  /-- axiom I.7.2: in every plane at least three points not lying in the same straight line,-/
  axiom exists_three_point_not_on_same_line: ∃ a b c: Point, a≠b ∧ b≠c ∧ a≠c ∧ ¬∃ l: Line, LiesOn a l ∧ LiesOn b l ∧ LiesOn c l

  def Collinear (a b c : Point) : Prop := ∃ l : Line, LiesOn a l ∧ LiesOn b l ∧ LiesOn c l

  def OnSegment(a b c: Point): Prop := Between a b c ∨ b = a ∨ b = c

  axiom collinear_of_between(a b c: Point): Between a b c → Collinear a b c

  axiom pasch_axiom {A B C: Point}(h: ¬Collinear A B C)(l: Line):
    (∃ P: Point, OnSegment A P B ∧ LiesOn P l) →
    (∃ Q: Point, OnSegment B Q C ∧ LiesOn Q l) ∨ (∃ R: Point, OnSegment A R C ∧ LiesOn R l)


  noncomputable instance: HilbertAxiomsP Point where
    Between := Between
    between_ne := between_ne
    between_symm := between_symm
    extension_exists := extension_exists

  noncomputable instance: HilbertAxiomsPL Point Line where
    LiesOn := LiesOn
    mk_line := mk_line
    mk_line_liesOn := mk_line_liesOn
    unique_line_from_two_points := unique_line_from_two_points
    line_exists_two_points := line_exists_two_points
    collinear_of_between := collinear_of_between

  axiom exists_three_noncollinear_points: ∃ a b c: Point, ¬Collinear a b c

  noncomputable instance: HilbertAxioms2D Point Line where
    exists_three_noncollinear_points := exists_three_noncollinear_points
    pasch_axiom := pasch_axiom

end Geometry.Euclid
