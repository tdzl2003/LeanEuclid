import Geometry.Basic
import Geometry.Polygon

namespace Geometry.Euclid2D

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
  private axiom LiesOn(l: Line)(a: Point): Prop

  instance: Membership Point Line where
    mem := LiesOn

  /-- axiom I.1: Two distinct points A and B always completely determine a straight line a. --/
  axiom mk_line(a b: Point)(hne: a ≠ b):  Line

  /-- axiom I.1: line a determined by points A and B should go throught them. --/
  axiom mk_line_liesOn(a b: Point)(h: a≠ b): a ∈ (mk_line a b h) ∧ b ∈ (mk_line a b h)

  /-- axiom I.2: Any two distinct points of a straight line completely determine that line; that is, if AB = a and AC = a, where B ̸= C, then is also BC = a. -/
  axiom unique_line_from_two_points (a b: Point) (l: Line)(h:  a ≠ b) : a ∈ l → b ∈ l → l = mk_line a b h

  /-- axiom I.7.1: Upon every straight line there exist at least two points -/
  axiom line_exists_two_points(l: Line): ∃ a b: Point, a≠b ∧ a ∈ l ∧ b ∈ l

  def Collinear (a b c : Point) : Prop := ∃ l : Line, a ∈ l ∧ b ∈ l ∧ c ∈ l

  /-- axiom I.7.2: in every plane at least three points not lying in the same straight line,-/
  axiom exists_three_noncollinear_points: ∃ a b c: Point, ¬Collinear a b c

  def OnSegment(a b c: Point): Prop := Between a b c ∨ b = a ∨ b = c

  axiom collinear_of_between(a b c: Point): Between a b c → Collinear a b c

  axiom pasch_axiom {A B C: Point}(h: ¬Collinear A B C)(l: Line):
    (∃ P: Point, OnSegment A P B ∧ P ∈ l) →
    (∃ Q: Point, OnSegment B Q C ∧ Q ∈ l) ∨ (∃ R: Point, OnSegment A R C ∧ R ∈ l)


  noncomputable instance: HilbertAxioms2D Point Line where
    Between := Between
    between_ne := between_ne
    extension_exists := extension_exists

    mk_line := mk_line
    mk_line_liesOn := mk_line_liesOn
    unique_line_from_two_points := unique_line_from_two_points
    line_exists_two_points := line_exists_two_points
    collinear_of_between := collinear_of_between
    exists_three_noncollinear_points := exists_three_noncollinear_points

    pasch_axiom:=pasch_axiom


  section
    abbrev BrokenLine := HilbertAxioms2D.BrokenLine (Point := Point) (Line := Line)
    abbrev Polygon := HilbertAxioms2D.Polygon (Point := Point) (Line := Line)

    axiom inside: Polygon → Point → Prop
    axiom outside: Polygon → Point → Prop
    axiom inside_outside_disjoint: ∀ (poly: Polygon), ∀ (p: Point),  ¬(inside poly p ∧ outside poly p)
    axiom inside_outside_boundary_exhaustive: ∀ (poly: Polygon), ∀ (p: Point), inside poly p ∨ outside poly p ∨ p ∈ poly
    axiom inside_path_connected: ∀ (poly: Polygon), poly.isSimple → ∀ (a b: Point), inside poly a → inside poly b →
      ∃ (γ: BrokenLine),
        (∀ p: Point, p ∈ γ → inside poly p) ∧
        γ.head = a ∧
        γ.last = b
    axiom outside_path_connected: ∀ (poly: Polygon), ∀ (a b: Point), outside poly a → outside poly b →
      ∃ (γ: BrokenLine),
        (∀ p: Point, p ∈ γ → outside poly p) ∧
        γ.head = a ∧
        γ.last = b
    axiom crossing_edge: ∀ (poly: Polygon), ∀ (a b: Point), inside poly a → outside poly b →
      (∀ (γ: BrokenLine),
        γ.head = a →
        γ.last = b →
        ∃ p: Point, p ∈ γ ∧ p ∈ poly
      )
    axiom not_exists_inside_line: ∀ (poly: Polygon), ¬ ∃ l:Line, ∀ p ∈ l, inside poly p

    theorem exists_outside_line: ∀ (poly: Polygon), ∃ l:Line, ∀ p ∈ l, outside poly p := by
      sorry

    noncomputable instance {poly: Polygon}{hSimple: poly.isSimple}: HilbertAxioms2D.PolygonalRegion poly hSimple where
      inside := inside poly
      outside := outside poly
      inside_outside_disjoint := inside_outside_disjoint poly
      inside_outside_boundary_exhaustive := inside_outside_boundary_exhaustive poly
      inside_path_connected := inside_path_connected poly hSimple
      outside_path_connected := outside_path_connected poly
      crossing_edge := crossing_edge poly
      not_exists_inside_line := not_exists_inside_line poly
      exists_outside_line:= exists_outside_line poly
  end

end Geometry.Euclid2D
