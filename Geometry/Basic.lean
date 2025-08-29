

-- Hilbert geometry definition, reference: https://www.gutenberg.org/files/17384/17384-pdf.pdf

namespace Geometry

/-- axioms about point. -/
class HilbertAxiomsP (Point: Type) where
  /-- Between : b is Between a and c (exclusive) -/
  Between(a b c: Point): Prop

  /-- Between relation is exclusive. -/
  between_ne(a b c: Point): Between a b c → a ≠ b ∨ b ≠ c

  /--
    axiom II.1: If A, B, C are points of a straight line and B lies Between A and C, then B lies also Between C and A.
    We don't mension the line here, because we can always create a line from two points.
  -/
  between_symm(a b c: Point): Between a b c → Between c b a

  /--
    axiom II.2.2 If A and C are two points of a straight line, at least one point D so situated that C lies Between A and D.
    We don't mension the line here, because we can always create a line from two points,
    and prove that D is on the line.
  -/
  extension_exists(a c: Point): a ≠ c → ∃ d: Point, Between a c d

  /-- b is On segment ac: Either between, or is one of the endpoint.-/
  OnSegment(a b c: Point): Prop := Between a b c ∨ b = a ∨ b = c

/-- axioms about point and line, at least 1 dimension  -/
class HilbertAxiomsPL (Point Line: Type) extends HilbertAxiomsP Point where
  /-- LiesOn: a is on the l -/
  LiesOn(a: Point)(l: Line): Prop

  /-- a b c is collinear -/
  Collinear (a b c : Point) : Prop := ∃ l : Line, LiesOn a l ∧ LiesOn b l ∧ LiesOn c l

  /-- axiom I.1: Two distinct points A and B always completely determine a straight line a. --/
  mk_line(a b: Point)(h: a ≠ b): Line
  /-- axiom I.1: line a determined by points A and B should go throught them. --/
  mk_line_liesOn(a b: Point)(h: a≠ b): LiesOn a (mk_line a b h) ∧ LiesOn b (mk_line a b h)

  /-- axiom I.2: Any two distinct points of a straight line completely determine that line; that is, if AB = a and AC = a, where B ̸= C, then is also BC = a. -/
  unique_line_from_two_points (a b: Point)(l: Line)(h:  a ≠ b) : LiesOn a l → LiesOn b l → l = mk_line a b h

  /-- axiom I.7.1: Upon every straight line there exist at least two points -/
  line_exists_two_points(l: Line): ∃ a b: Point, a≠b ∧ LiesOn a l ∧ LiesOn b l

  /-- Between implies Collinear -/
  collinear_of_between(a b c: Point): Between a b c → Collinear a b c

/-- axiom about point, line, and plane, at least 2 dimensions -/
class HilbertAxiomsPLP (Point Line Plane: Type) extends HilbertAxiomsPL Point Line where
  LiesOnPlane(a: Point)(pl: Plane): Prop

  LineLiesOnPlane(l: Line)(pl: Plane): Prop := ∀ p: Point, LiesOn p l → LiesOnPlane p pl

  /-- axiom I.3: Three points A, B, C not situated in the same straight line always completely determine a plane α.-/
  mk_plane_fromPoints(a b c: Point)(h: ¬Collinear a b c): Plane

  /-- axiom I.3: plane determined by three points should have them lied on -/
  mk_plane_liesOn{a b c: Point}{h: ¬Collinear a b c}:
    LiesOnPlane a (mk_plane_fromPoints a b c h) ∧
    LiesOnPlane b (mk_plane_fromPoints a b c h) ∧
    LiesOnPlane c (mk_plane_fromPoints a b c h)

  /-- axiom I.4: Any three points A, B, C of a plane α, which do not lie in the same straight line, completely determine that plane. -/
  unique_plane_from_three_points(a b c: Point)(pl: Plane)(h: ¬Collinear a b c):
    LiesOnPlane a pl → LiesOnPlane b pl → LiesOnPlane c pl → pl = mk_plane_fromPoints a b c h

  /-- axiom I.5: If two points A, B of a straight line a lie in a plane α, then every point of a lies in a.-/
  line_in_plane_if_two_points_in_plane(a b: Point)(l: Line)(pl: Plane)(h: a ≠ b):
    LiesOn a l → LiesOn b l → LiesOnPlane a pl → LiesOnPlane b pl → LineLiesOnPlane l pl

  /-- axiom I.6: If two planes α, β have a point A in common, then they have at least a second point B in common.-/
  plane_intersection_exists_two_points(pl1 pl2: Plane)(h: pl1 ≠ pl2)(a: Point):
    LiesOnPlane a pl1 ∧ LiesOnPlane a pl2 →
    ∃ b: Point, b ≠ a ∧ LiesOnPlane b pl1 ∧ LiesOnPlane a pl2

  /-- axiom I.7.2: in every plane at least three points not lying in the same straight line -/
  plane_exists_three_noncollinear_points(pl: Plane): ∃ a b c: Point, ¬Collinear a b c ∧ LiesOnPlane a pl ∧ LiesOnPlane b pl ∧ LiesOnPlane c pl

  /-- axiom II.5: Let A, B, C be three points not lying in the same straight line and let a be a
  straight line lying in the plane ABC and not passing through any of the points A,
  B, C. Then, if the straight line a passes through a point of the segment AB, it will
  also pass through either a point of the segment BC or a point of the segment AC.-/
  pasch_axiom {A B C: Point}(h: ¬Collinear A B C)(l: Line)(h: LineLiesOnPlane l (mk_plane_fromPoints A B C h)):
    (∃ P: Point, OnSegment A P B ∧ LiesOn P l) →
    (∃ Q: Point, OnSegment B Q C ∧ LiesOn Q l) ∨ (∃ R: Point, OnSegment A R C ∧ LiesOn R l)

/-- axioms about space, at least 3 dimensions. -/
class HibertAxiomPLPS (Point Line Plane: Type) extends HilbertAxiomsPLP Point Line Plane where
  /-- axiom I.10: In every space R there exist at least four points not lying in the same plane.-/
  space_exists_four_noncoplanar_points: ∃ a b c d: Point, ¬(∃ pl: Plane, LiesOnPlane a pl ∧ LiesOnPlane b pl ∧ LiesOnPlane c pl ∧ LiesOnPlane d pl)

end Geometry

namespace Geometry
  open HilbertAxiomsP HilbertAxiomsPL

  variable {Point Line: Type}[HilbertAxiomsPL Point Line]

  structure Segment where
    p1: Point
    p2: Point
    hne: p1 ≠ p2

  /-- a point is on the segment -/
  def Segment.LiesOn (s: Segment (Point := Point))(p: Point): Prop :=
    HilbertAxiomsP.OnSegment s.p1 p s.p2

  /-- two point is on same side of a line. -/
  def Line.onSameSide (l: Line)(a b: Point): Prop :=
    ¬(∃ c: Point, HilbertAxiomsP.OnSegment a c b ∧ LiesOn c l)

  /-- two point is on different side of a line. -/
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

namespace Geometry
  open HilbertAxiomsP HilbertAxiomsPL HilbertAxiomsPLP

  class HilbertAxioms2D (Point Line: Type) extends HilbertAxiomsPL Point Line where
    exists_three_noncollinear_points: ∃ a b c: Point, ¬Collinear a b c
    pasch_axiom {A B C: Point}(h: ¬Collinear A B C)(l: Line):
      (∃ P: Point, OnSegment A P B ∧ LiesOn P l) →
      (∃ Q: Point, OnSegment B Q C ∧ LiesOn Q l) ∨ (∃ R: Point, OnSegment A R C ∧ LiesOn R l)

  namespace HilbertAxioms2D.instHilbertAxiomsPLP
    variable {Point Line: Type}[HilbertAxioms2D Point Line]

    private def LiesOnPlane(a: Point)(pl: Unit): Prop := True
    private def LineLiesOnPlane(l: Line)(pl: Unit): Prop := ∀ p: Point, LiesOn p l → LiesOnPlane p pl
    private def mk_plane_fromPoints(a b c: Point)(h: ¬Collinear Line a b c): Unit := ()

    private theorem mk_plane_liesOn{a b c: Point}{h: ¬Collinear Line a b c}:
        LiesOnPlane a (mk_plane_fromPoints a b c h) ∧
        LiesOnPlane b (mk_plane_fromPoints a b c h) ∧
        LiesOnPlane c (mk_plane_fromPoints a b c h):=
    by
      simp only [LiesOnPlane, and_self]

    /-- axiom I.4: Any three points A, B, C of a plane α, which do not lie in the same straight line, completely determine that plane. -/
    private theorem unique_plane_from_three_points(a b c: Point)(pl: Unit)(h: ¬Collinear Line a b c):
        LiesOnPlane a pl → LiesOnPlane b pl → LiesOnPlane c pl → pl = mk_plane_fromPoints a b c h :=
    by
      intro _ _ _
      cases pl
      rfl

    /-- axiom I.5: If two points A, B of a straight line a lie in a plane α, then every point of a lies in a.-/
    private theorem line_in_plane_if_two_points_in_plane(a b: Point)(l: Line)(pl: Unit)(h: a ≠ b):
        LiesOn a l → LiesOn b l → LiesOnPlane a pl → LiesOnPlane b pl →
        ∀ p: Point, LiesOn p l → LiesOnPlane p pl :=
    by
      intro _ _ _ _ p hp
      simp only [LiesOnPlane]

    /-- axiom I.6: If two planes α, β have a point A in common, then they have at least a second point B in common.-/
    private theorem plane_intersection_exists_two_points(pl1 pl2: Unit)(h: pl1 ≠ pl2)(a: Point):
        LiesOnPlane a pl1 ∧ LiesOnPlane a pl2 →
        ∃ b: Point, b ≠ a ∧ LiesOnPlane b pl1 ∧ LiesOnPlane a pl2 :=
    by
      sorry

    private theorem plane_exists_three_noncollinear_points(pl: Unit):
        ∃ a b c: Point, ¬Collinear Line a b c ∧ LiesOnPlane a pl ∧ LiesOnPlane b pl ∧ LiesOnPlane c pl :=
    by
      sorry

    private theorem pasch_axiom {A B C: Point}(h: ¬Collinear Line A B C)(l: Line)
      (_: LineLiesOnPlane (Point:=Point) l (mk_plane_fromPoints (Line:=Line) A B C h)):
        (∃ P: Point, OnSegment A P B ∧ LiesOn P l) →
        (∃ Q: Point, OnSegment B Q C ∧ LiesOn Q l) ∨ (∃ R: Point, OnSegment A R C ∧ LiesOn R l) :=
    by
      apply HilbertAxioms2D.pasch_axiom h l

    /-- axiom about point, line, and plane, in 2 dimensions space -/
    noncomputable instance: HilbertAxiomsPLP Point Line Unit where
      LiesOnPlane := LiesOnPlane
      mk_plane_fromPoints := mk_plane_fromPoints
      mk_plane_liesOn := mk_plane_liesOn
      unique_plane_from_three_points := unique_plane_from_three_points
      line_in_plane_if_two_points_in_plane := line_in_plane_if_two_points_in_plane
      plane_intersection_exists_two_points := plane_intersection_exists_two_points
      plane_exists_three_noncollinear_points := plane_exists_three_noncollinear_points
      pasch_axiom := pasch_axiom

  end HilbertAxioms2D.instHilbertAxiomsPLP

end Geometry
