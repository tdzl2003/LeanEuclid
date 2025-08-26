

namespace Geometry

class HilbertAxiomsP (Point: Type) where
  /-- Between : b is Between a and c (exclusive) -/
  Between(a b c: Point): Prop

  /-- Between relation is exclusive. -/
  between_ne(a b c: Point): Between a b c → a ≠ b ∨ b ≠ c

  /-- axiom II.1: If A, B, C are points of a straight line and B lies Between A and C, then B lies also Between C and A.-/
  between_symm(a b c: Point): Between a b c → Between c b a

  /-- axiom II.2.2 If A and C are two points of a straight line, at least one point D so situated that C lies Between A and D.-/
  extension_exists(a c: Point): a ≠ c → ∃ d: Point, Between a c d

  /-- b is On segment ac: Either between, or is one of the endpoint.-/
  OnSegment(a b c: Point): Prop := Between a b c ∨ b = a ∨ b = c

/-- Hilbert geometry definition, reference: https://www.gutenberg.org/files/17384/17384-pdf.pdf -/
class HilbertAxiomsPL (Point Line: Type) extends HilbertAxiomsP Point where
  /-- LiesOn: a is on the l -/
  LiesOn(a: Point)(l: Line): Prop

  /-- a b c is collinear -/
  Collinear (a b c : Point) : Prop := ∃ l : Line, LiesOn a l ∧ LiesOn b l ∧ LiesOn c l

  /-- axiom I.1: Two distinct points A and B always completely determine a straight line a. --/
  mk_line_from_points(a b: Point): Line
  /-- axiom I.1: line a determined by points A and B should go throught them. --/
  mk_line_liesOn(a b: Point): LiesOn a (mk_line_from_points a b) ∧ LiesOn b (mk_line_from_points a b)

  /-- axiom I.2: Any two distinct points of a straight line completely determine that line; that is, if AB = a and AC = a, where B ̸= C, then is also BC = a. -/
  unique_line_from_two_points (a b: Point) (l: Line) : a ≠ b → LiesOn a l → LiesOn b l → l = mk_line_from_points a b

  /-- axiom I.7.1: Upon every straight line there exist at least two points -/
  line_exists_two_points(l: Line): ∃ a b: Point, a≠b ∧ LiesOn a l ∧ LiesOn b l

  /-- axiom I.7.2: in every plane at least three points not lying in the same straight line,-/
  exists_three_point_not_on_same_line: ∃ a b c: Point, a≠b ∧ b≠c ∧ a≠c ∧ ¬∃ l: Line, LiesOn a l ∧ LiesOn b l ∧ LiesOn c l

  /-- Between implies Collinear -/
  collinear_of_between(a b c: Point): Between a b c → Collinear a b c

  /-- axiom II.5 Let A, B, C be three points not lying in the same straight line and let a be a
  straight line lying in the plane ABC and not passing through any of the points A,
  B, C. Then, if the straight line a passes through a point of the segment AB, it will
  also pass through either a point of the segment BC or a point of the segment AC.-/
  pasch_axiom {A B C: Point}(h: ¬Collinear A B C)(l: Line):
    (∃ P: Point, OnSegment A P B ∧ LiesOn P l) →
    (∃ Q: Point, OnSegment B Q C ∧ LiesOn Q l) ∨ (∃ R: Point, OnSegment A R C ∧ LiesOn R l)

end Geometry

namespace Geometry
  open HilbertAxiomsP HilbertAxiomsPL

  variable {Point Line: Type}[HilbertAxiomsPL Point Line]

  structure Segment where
    p1: Point
    p2: Point
    hne: p1 ≠ p2

  def liesOnSegment (s: Segment (Point := Point))(p: Point): Prop :=
    HilbertAxiomsP.OnSegment s.p1 p s.p2

  def Line.onSameSide (l: Line)(a b: Point): Prop :=
    ¬(∃ c: Point, HilbertAxiomsP.OnSegment a c b ∧ LiesOn c l)

  def Line.onOtherSide (l: Line)(a b: Point): Prop :=
    ∃ c: Point, Between a c b ∧ LiesOn c l

  structure Polygon where
    vertices: List Point
    hc: vertices.length ≥ 3
    hne: ∀ (a b: Point), a ∈ vertices → b ∈ vertices → a ≠ b
    hcol: ∀ (a b c: Point), a ∈ vertices → b ∈ vertices → c ∈ vertices → ¬Collinear Line a b c

  def liesOnPolygon (poly: Polygon (Point := Point) (Line := Line))(p: Point): Prop :=
    ∃ i : Fin poly.vertices.length,
      let v1 := poly.vertices.get i
      let v2 := poly.vertices.get ⟨(i + 1) % poly.vertices.length, by apply Nat.mod_lt; have := poly.hc; omega⟩
      HilbertAxiomsP.OnSegment v1 p v2


end Geometry
