

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
class HilbertAxiomsPL (Point: outParam Type)(Line: Type)[Membership Point Line] extends HilbertAxiomsP Point where
  /-- a b c is collinear -/
  Collinear (a b c : Point) : Prop := ∃ l : Line, a ∈ l ∧ b ∈ l ∧ c ∈ l

  /-- axiom I.1: Two distinct points A and B always completely determine a straight line a. --/
  mk_line(a b: Point)(h: a ≠ b): Line
  /-- axiom I.1: line a determined by points A and B should go throught them. --/
  mk_line_liesOn(a b: Point)(h: a≠ b): a ∈  (mk_line a b h) ∧ b ∈ (mk_line a b h)

  /-- axiom I.2: Any two distinct points of a straight line completely determine that line; that is, if AB = a and AC = a, where B ̸= C, then is also BC = a. -/
  unique_line_from_two_points (a b: Point)(l: Line)(h:  a ≠ b) : a ∈ l → b ∈ l → l = mk_line a b h

  /-- axiom I.7.1: Upon every straight line there exist at least two points -/
  line_exists_two_points(l: Line): ∃ a b: Point, a≠b ∧ a ∈ l ∧ b ∈ l

  /-- Between implies Collinear -/
  collinear_of_between(a b c: Point): Between a b c → Collinear a b c

/-- axiom about point, line, and plane, at least 2 dimensions -/
class HilbertAxiomsPLP (Point: outParam Type)(Line Plane: Type)[Membership Point Line][Membership Point Plane] extends HilbertAxiomsPL Point Line where
  /-- axiom I.3: Three points A, B, C not situated in the same straight line always completely determine a plane α.-/
  mk_plane_fromPoints(a b c: Point)(h: ¬Collinear a b c): Plane

  /-- axiom I.3: plane determined by three points should have them lied on -/
  mk_plane_liesOn{a b c: Point}{h: ¬Collinear a b c}:
    a ∈ (mk_plane_fromPoints a b c h) ∧
    b ∈ (mk_plane_fromPoints a b c h) ∧
    c ∈ (mk_plane_fromPoints a b c h)

  /-- axiom I.4: Any three points A, B, C of a plane α, which do not lie in the same straight line, completely determine that plane. -/
  unique_plane_from_three_points(a b c: Point)(pl: Plane)(h: ¬Collinear a b c):
    a ∈ pl → b ∈ pl → c ∈ pl → pl = mk_plane_fromPoints a b c h

  /-- axiom I.5: If two points A, B of a straight line a lie in a plane α, then every point of a lies in a.-/
  line_in_plane_if_two_points_in_plane(a b: Point)(l: Line)(pl: Plane)(h: a ≠ b):
    a ∈ l → b ∈ l → a ∈ pl → b ∈ pl → ∀ c ∈ l, c ∈ pl

  /-- axiom I.6: If two planes α, β have a point A in common, then they have at least a second point B in common.-/
  plane_intersection_exists_two_points(pl1 pl2: Plane)(h: pl1 ≠ pl2)(a: Point):
    a ∈ pl1 ∧ a ∈ pl2 →
    ∃ b: Point, b ≠ a ∧ b ∈ pl1 ∧ b ∈ pl2

  /-- axiom I.7.2: in every plane at least three points not lying in the same straight line -/
  plane_exists_three_noncollinear_points(pl: Plane): ∃ a b c: Point, ¬Collinear a b c ∧ a ∈ pl ∧ b ∈ pl ∧ c ∈ pl

  /-- axiom II.5: Let A, B, C be three points not lying in the same straight line and let a be a
  straight line lying in the plane ABC and not passing through any of the points A,
  B, C. Then, if the straight line a passes through a point of the segment AB, it will
  also pass through either a point of the segment BC or a point of the segment AC.-/
  pasch_axiom {A B C: Point}(h: ¬Collinear A B C)(l: Line)
    (h: ∀ c ∈ l, c ∈ (mk_plane_fromPoints A B C h)):
      (∃ P: Point, OnSegment A P B ∧ P ∈ l ) →
      (∃ Q: Point, OnSegment B Q C ∧ Q ∈ l) ∨ (∃ R: Point, OnSegment A R C ∧ R ∈ l)

/-- axioms about space, at least 3 dimensions. -/
class HibertAxiomPLPS (Point Line Plane: Type)[Membership Point Line][Membership Point Plane] extends HilbertAxiomsPLP Point Line Plane where
  /-- axiom I.10: In every space R there exist at least four points not lying in the same plane.-/
  space_exists_four_noncoplanar_points: ∃ a b c d: Point, ¬(∃ pl: Plane, a ∈ pl ∧ b ∈  pl ∧ c ∈ pl ∧ d ∈ pl)

end Geometry

namespace Geometry
  open HilbertAxiomsP HilbertAxiomsPL

  variable {Point: Type}[HilbertAxiomsP Point]

  def IsSubset{α: Type}{β: Type}[Membership Point α][Membership Point β](S: α)(T: β): Prop :=
    ∀ p: Point, p ∈ S → p ∈ T

  scoped infix:99 "⊆" => IsSubset

  variable {Line: Type}[Membership Point Line][HilbertAxiomsPL Point Line]
  variable {Plane: Type}[Membership Point Plane][HilbertAxiomsPLP Point Line Plane]

  structure Segment where
    p1: Point
    p2: Point

  def Segment.isValid (s: Segment (Point := Point)): Prop := s.p1 ≠ s.p2

  def Segment.PointLiesOn(s: Segment (Point := Point))(p: Point): Prop :=
    HilbertAxiomsP.OnSegment s.p1 p s.p2

  instance : Membership Point (Segment (Point := Point)) where
    mem := Segment.PointLiesOn

  /-- two point is on same side of a line. -/
  def SameSideOfLine(pl: Plane)(l: Line)(a b: Point): Prop :=
    a ∈ pl ∧ b ∈ pl ∧ l ⊆ pl ∧ ¬(∃ c: Point, HilbertAxiomsP.OnSegment a c b ∧ c ∈ l)

  /-- two point is on different side of a line. -/
  def OtherSideOfLine(pl: Plane)(l: Line)(a b: Point): Prop :=
    a ∈ pl ∧ b ∈ pl ∧ l ⊆ pl ∧ ∃ c: Point, Between a c b ∧ c ∈ l

  structure Polygon where
    vertices: List Point
    hc: vertices.length ≥ 3

  def Polygon.edgeAt (poly: Polygon (Point := Point) )(i: Fin poly.vertices.length): Segment (Point := Point) :=
    let v1 := poly.vertices.get i
    let v2 := poly.vertices.get ⟨(i + 1) % poly.vertices.length, by apply Nat.mod_lt; have := poly.hc; omega⟩
    { p1 := v1, p2 := v2 }

  def Polygon.isSimple (poly: Polygon (Point := Point) ): Prop :=
    ∀ i j : Fin poly.vertices.length,
      i ≠ j →
      let e1 := poly.edgeAt i
      let e2 := poly.edgeAt j
      ∀ p: Point, p ∈ e1 → p ∈ e2 → False

  def Polygon.LiesOn (poly: Polygon (Point := Point) )(p: Point): Prop :=
    ∃ i : Fin poly.vertices.length,
      let v1 := poly.vertices.get i
      let v2 := poly.vertices.get ⟨(i + 1) % poly.vertices.length, by apply Nat.mod_lt; have := poly.hc; omega⟩
      HilbertAxiomsP.OnSegment v1 p v2
end Geometry

namespace Geometry
  open HilbertAxiomsP HilbertAxiomsPL HilbertAxiomsPLP

  class HilbertAxioms2D (Point: outParam Type)(Line: Type)[Membership Point Line] extends HilbertAxiomsPL Point Line where
    exists_three_noncollinear_points: ∃ a b c: Point, ¬Collinear a b c
    pasch_axiom {A B C: Point}(h: ¬Collinear A B C)(l: Line):
      (∃ P: Point, OnSegment A P B ∧ P ∈ l) →
      (∃ Q: Point, OnSegment B Q C ∧ Q ∈ l) ∨ (∃ R: Point, OnSegment A R C ∧ R ∈ l)

  namespace HilbertAxioms2D.instHilbertAxiomsPLP
    variable {Point Line: Type}[Membership Point Line][HilbertAxioms2D Point Line]

    def Plane{Point Line: Type}[Membership Point Line][HilbertAxioms2D Point Line]: Type := Unit

    instance: Membership Point (Plane (Point:=Point) (Line:=Line)) where
      mem (_ _):= True
    private def LineLiesOnPlane(l: Line)(pl: Plane (Point:=Point) (Line:=Line)): Prop :=
      ∀ p: Point, p ∈ l → p ∈ pl
    private def mk_plane_fromPoints(a b c: Point)(h: ¬Collinear Line a b c): Plane (Line := Line) := ()

    private theorem mk_plane_liesOn{a b c: Point}{h: ¬Collinear Line a b c}:
        a ∈ (mk_plane_fromPoints a b c h) ∧
        b ∈ (mk_plane_fromPoints a b c h) ∧
        c ∈ (mk_plane_fromPoints a b c h):=
    by
      simp only [Membership.mem, true_and]

    /-- axiom I.4: Any three points A, B, C of a plane α, which do not lie in the same straight line, completely determine that plane. -/
    private theorem unique_plane_from_three_points(a b c: Point)(pl: Plane (Line := Line))(h: ¬Collinear Line a b c):
        a ∈ pl → b ∈ pl → c ∈ pl → pl = mk_plane_fromPoints a b c h :=
    by
      intro _ _ _
      cases pl
      rfl

    /-- axiom I.5: If two points A, B of a straight line a lie in a plane α, then every point of a lies in a.-/
    private theorem line_in_plane_if_two_points_in_plane(a b: Point)(l: Line)(pl: Plane (Line := Line))(h: a ≠ b):
        a ∈ l → b ∈ l → a ∈ pl → b ∈ pl→
        ∀ p: Point, p ∈ l → p ∈ pl :=
    by
      intro _ _ _ _ p hp
      simp only [Membership.mem]

    /-- axiom I.6: If two planes α, β have a point A in common, then they have at least a second point B in common.-/
    private theorem plane_intersection_exists_two_points(pl1 pl2: Plane (Line := Line))(h: pl1 ≠ pl2)(a: Point):
        a ∈ pl1 ∧ a ∈ pl2 →
        ∃ b: Point, b ≠ a ∧ b ∈ pl1 ∧ b ∈ pl2 :=
    by
      sorry

    private theorem plane_exists_three_noncollinear_points(pl: Plane (Line := Line)):
        ∃ a b c: Point, ¬Collinear Line a b c ∧ a ∈ pl ∧ b ∈ pl ∧ c ∈ pl :=
    by
      sorry

    private theorem pasch_axiom {A B C: Point}(h: ¬Collinear Line A B C)(l: Line)
      (_: LineLiesOnPlane (Point:=Point) l (mk_plane_fromPoints (Line:=Line) A B C h)):
        (∃ P: Point, OnSegment A P B ∧ P ∈ l) →
        (∃ Q: Point, OnSegment B Q C ∧ Q ∈ l) ∨ (∃ R: Point, OnSegment A R C ∧ R ∈ l) :=
    by
      apply HilbertAxioms2D.pasch_axiom h l

    /-- axiom about point, line, and plane, in 2 dimensions space -/
    noncomputable instance: HilbertAxiomsPLP Point Line (Plane (Line := Line)) where
      mk_plane_fromPoints := mk_plane_fromPoints
      mk_plane_liesOn := mk_plane_liesOn
      unique_plane_from_three_points := unique_plane_from_three_points
      line_in_plane_if_two_points_in_plane := line_in_plane_if_two_points_in_plane
      plane_intersection_exists_two_points := plane_intersection_exists_two_points
      plane_exists_three_noncollinear_points := plane_exists_three_noncollinear_points
      pasch_axiom := pasch_axiom

  end HilbertAxioms2D.instHilbertAxiomsPLP

end Geometry
