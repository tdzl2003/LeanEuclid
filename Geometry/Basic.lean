

-- Hilbert geometry definition, reference: https://www.gutenberg.org/files/17384/17384-pdf.pdf

namespace Geometry

  class HilbertAxioms1D (Point: Type) where
    /-- Between : b is Between a and c (exclusive) -/
    Between(a b c: Point): Prop

    /-- Between relation is exclusive. -/
    between_ne(a b c: Point): Between a b c → a ≠ b ∨ b ≠ c

    /--
      axiom II.1: If A, B, C are points of a straight line and B lies Between A and C, then B lies also Between C and A.
    -/
    between_symm(a b c: Point): Between a b c → Between c b a

    /--
      axiom II.2.1 If A and C are two points of a straight line, there exists at least one point B lying between A and C.
      This can be proved in 2D but is axiom for 1D.
    -/
    between_exists(a c: Point): a ≠ c → ∃ d: Point, Between a c d

    /--
      axiom II.2.2 If A and C are two points of a straight line, there exists at least one point D so situated that C lies Between A and D.
    -/
    extension_exists(a c: Point): a ≠ c → ∃ d: Point, Between a c d

    /-- axiom I.8: There exist at least two points on a line. -/
    line_exists_two_points: ∃ a b: Point, a ≠ b

    OnSegment(a b c: Point): Prop := Between a b c ∨ b = a ∨ b = c

  def IsSubset{Point: Type}{α: Type}{β: Type}[Membership Point α][Membership Point β](S: α)(T: β): Prop :=
      ∀ p: Point, p ∈ S → p ∈ T

  scoped infix:99 "⊆" => IsSubset

  class HilbertAxioms2D (Point: Type) where
    Line: Type
    mem_Line: Membership Point Line

    /-- Between : b is Between a and c (exclusive) -/
    Between(a b c: Point): Prop

    /-- Between relation is exclusive. -/
    between_ne(a b c: Point): Between a b c → a ≠ b ∨ b ≠ c

    /--
      axiom II.2.2 If A and C are two points of a straight line, there exists at least one point D so situated that C lies Between A and D.
    -/
    extension_exists(a c: Point): a ≠ c → ∃ d: Point, Between a c d

    /-- axiom I.1: Two distinct points A and B always completely determine a straight line a. --/
    mk_line(a b: Point)(h: a ≠ b): Line

    /-- axiom I.1: line a determined by points A and B should go throught them. --/
    mk_line_liesOn(a b: Point)(h: a≠ b): a ∈  (mk_line a b h) ∧ b ∈ (mk_line a b h)

    /-- axiom I.2: Any two distinct points of a straight line completely determine that line; that is, if AB = a and AC = a, where B ̸= C, then is also BC = a. -/
    unique_line_from_two_points (a b: Point)(l: Line)(h:  a ≠ b) : a ∈ l → b ∈ l → l = mk_line a b h

    /-- axiom I.8: There exist at least two points on a line. -/
    line_exists_two_points: ∀ l: Line, ∃ a b: Point, a ≠ b ∧ a ∈ l ∧ b ∈ l

    /-- a b c is collinear -/
    Collinear (a b c : Point) : Prop := ∃ l : Line, a ∈ l ∧ b ∈ l ∧ c ∈ l

    /-- If B is between A and C, then A, B, C are collinear. -/
    collinear_of_between(a b c: Point): Between a b c → Collinear a b c

    /-- axiom I.7.2: in every plane at least three points not lying in the same straight line -/
    exists_three_noncollinear_points: ∃ a b c: Point, ¬Collinear a b c

    OnSegment(a b c: Point): Prop := Between a b c ∨ b = a ∨ b = c

    /-- axiom II.5: Let A, B, C be three points not lying in the same straight line and let a be a
    straight line lying in the plane ABC and not passing through any of the points A,
    B, C. Then, if the straight line a passes through a point of the segment AB, it will
    also pass through either a point of the segment BC or a point of the segment AC.-/
    pasch_axiom {A B C: Point}(h: ¬Collinear A B C)(l: Line):
        (∃ P: Point, OnSegment A P B ∧ P ∈ l) →
        (∃ Q: Point, OnSegment B Q C ∧ Q ∈ l) ∨ (∃ R: Point, OnSegment A R C ∧ R ∈ l)

  class HilbertAxioms3D (Point: Type) where
    Line: Type
    mem_Line: Membership Point Line
    Plane: Type
    mem_Plane: Membership Point Plane

    /-- Between : b is Between a and c (exclusive) -/
    Between(a b c: Point): Prop

    /-- Between relation is exclusive. -/
    between_ne(a b c: Point): Between a b c → a ≠ b ∨ b ≠ c

    /--
      axiom II.2.2 If A and C are two points of a straight line, there exists at least one point D so situated that C lies Between A and D.
    -/
    extension_exists(a c: Point): a ≠ c → ∃ d: Point, Between a c d

    /-- axiom I.1: Two distinct points A and B always completely determine a straight line a. --/
    mk_line(a b: Point)(h: a ≠ b): Line

    /-- axiom I.1: line a determined by points A and B should go throught them. --/
    mk_line_liesOn(a b: Point)(h: a≠ b): a ∈  (mk_line a b h) ∧ b ∈ (mk_line a b h)

    /-- axiom I.2: Any two distinct points of a straight line completely determine that line; that is, if AB = a and AC = a, where B ̸= C, then is also BC = a. -/
    unique_line_from_two_points (a b: Point)(l: Line)(h:  a ≠ b) : a ∈ l → b ∈ l → l = mk_line a b h

    /-- axiom I.8: There exist at least two points on a line. -/
    line_exists_two_points: ∀ l: Line, ∃ a b: Point, a ≠ b ∧ a ∈ l ∧ b ∈ l

    /-- a b c is collinear -/
    Collinear (a b c : Point) : Prop := ∃ l : Line, a ∈ l ∧ b ∈ l ∧ c ∈ l

    /-- If B is between A and C, then A, B, C are collinear. -/
    collinear_of_between(a b c: Point): Between a b c → Collinear a b c

    /-- axiom I.7.2: in every plane at least three points not lying in the same straight line -/
    exists_three_noncollinear_points(pl: Plane): ∃ a b c: Point, a∈pl ∧ b∈pl ∧ c∈pl ∧ ¬Collinear a b c

    /-- axiom I.3: Three points A, B, C not situated in the same straight line always completely determine a plane α.-/
    mk_plane(a b c: Point)(h: ¬Collinear a b c): Plane

    OnSegment(a b c: Point): Prop := Between a b c ∨ b = a ∨ b = c

    /-- axiom II.5: Let A, B, C be three points not lying in the same straight line and let a be a
    straight line lying in the plane ABC and not passing through any of the points A,
    B, C. Then, if the straight line a passes through a point of the segment AB, it will
    also pass through either a point of the segment BC or a point of the segment AC.-/
    pasch_axiom {A B C: Point}(h: ¬Collinear A B C)(l: Line)(h: l ⊆ (mk_plane A B C h)):
        (∃ P: Point, OnSegment A P B ∧ P ∈ l) →
        (∃ Q: Point, OnSegment B Q C ∧ Q ∈ l) ∨ (∃ R: Point, OnSegment A R C ∧ R ∈ l)

    /-- axiom I.3: plane determined by three points should have them lied on -/
    mk_plane_liesOn{a b c: Point}{h: ¬Collinear a b c}:
      a ∈ (mk_plane a b c h) ∧
      b ∈ (mk_plane a b c h) ∧
      c ∈ (mk_plane a b c h)

    /-- axiom I.4: Any three points A, B, C of a plane α, which do not lie in the same straight line, completely determine that plane. -/
    unique_plane_from_three_points(a b c: Point)(pl: Plane)(h: ¬Collinear a b c):
      a ∈ pl → b ∈ pl → c ∈ pl → pl = mk_plane a b c h

    /-- axiom I.5: If two points A, B of a straight line a lie in a plane α, then every point of a lies in a.-/
    line_in_plane_if_two_points_in_plane(a b: Point)(l: Line)(pl: Plane)(h: a ≠ b):
      a ∈ l → b ∈ l → a ∈ pl → b ∈ pl → ∀ c ∈ l, c ∈ pl

    /-- axiom I.6: If two planes α, β have a point A in common, then they have at least a second point B in common.-/
    plane_intersection_exists_two_points(pl1 pl2: Plane)(h: pl1 ≠ pl2)(a: Point):
      a ∈ pl1 ∧ a ∈ pl2 →
      ∃ b: Point, b ≠ a ∧ b ∈ pl1 ∧ b ∈ pl2

    /-- axiom I.10: In every space R there exist at least four points not lying in the same plane.-/
    space_exists_four_noncoplanar_points: ∃ a b c d: Point, ¬(∃ pl: Plane, a ∈ pl ∧ b ∈  pl ∧ c ∈ pl ∧ d ∈ pl)

  -- Membership instance for point on line in a plane
  instance {Point Line Plane: Type}[Membership Point Line][Membership Point Plane]{pl: Plane}:
      Membership {p: Point // p ∈ pl} {l: Line // l ⊆ pl} where
    mem (l: {l: Line // l ⊆ pl}) (p: {p: Point // p ∈ pl}) : Prop := p.val ∈ l.val

  section
    structure Segment(Point: Type) where
      p1: Point
      p2: Point

    def Segment.isValid{Point}(s: Segment Point): Prop := s.p1 ≠ s.p2

    instance {Point: Type}[G: HilbertAxioms1D Point]: Membership Point (Segment Point) where
      mem (s: Segment Point) (p: Point) : Prop := G.OnSegment s.p1 p s.p2

    instance {Point: Type}[G: HilbertAxioms2D Point]: Membership Point (Segment Point) where
        mem (s: Segment Point) (p: Point) : Prop := G.Between s.p1 p s.p2 ∨ p = s.p1 ∨ p = s.p2

    instance {Point: Type}[G: HilbertAxioms3D Point]: Membership Point (Segment Point) where
        mem (s: Segment Point) (p: Point) : Prop := G.Between s.p1 p s.p2 ∨ p = s.p1 ∨ p = s.p2
  end

  section
    instance {Point: Type}[G: HilbertAxioms2D Point]: Membership Point (G.Line) := G.mem_Line
    instance {Point: Type}[G: HilbertAxioms3D Point]: Membership Point (G.Line) := G.mem_Line
    instance {Point: Type}[G: HilbertAxioms3D Point]: Membership Point (G.Plane) := G.mem_Plane
  end

end Geometry


namespace Geometry.HilbertAxioms2D
  variable {Point: Type}[G: HilbertAxioms2D Point]

  /-- two point is on same side of a line. -/
  def SameSideOfLine(l: G.Line)(a b: Point): Prop :=
    ¬(∃ c: Point, G.OnSegment a c b ∧ c ∈ l)

  /-- two point is on different side of a line. -/
  def OtherSideOfLine(l: G.Line)(a b: Point): Prop :=
    ∃ c: Point, G.Between a c b ∧ c ∈ l

  /-- Induce a 1D Hilbert axioms structure on points lying on a line in 2D plane. -/
  def onLine(l: G.Line):
    let SubPointType := {p: Point // p ∈ l}
    HilbertAxioms1D SubPointType := {
      Between := fun a b c => G.Between a.val b.val c.val,
      between_ne := by
        simp only [Subtype.forall, Subtype.mk.injEq]
        intro a ha b hb c hc h
        simp only [ne_eq, Subtype.mk.injEq]
        apply between_ne
        exact h
      between_symm := by
        sorry
      between_exists := by
        sorry
      extension_exists := by
        sorry
      line_exists_two_points := by
        sorry
    }
end Geometry.HilbertAxioms2D

namespace Geometry.HilbertAxioms3D
   /-- Induce a 2D Hilbert axioms structure on points lying in 2D plane. -/
  def onPlane{Point: Type}[G:HilbertAxioms3D Point](pl: G.Plane):
    let SubPointType := {p: Point // p ∈ pl}
    HilbertAxioms2D SubPointType := sorry

  def onLine{Point: Type}[G:HilbertAxioms3D Point](l: G.Line):
    let SubPointType := {p: Point // p ∈ l}
    HilbertAxioms1D SubPointType := sorry

end Geometry.HilbertAxioms3D
