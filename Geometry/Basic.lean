
-- Hilbert geometry definition, reference: https://www.gutenberg.org/files/17384/17384-pdf.pdf

namespace Geometry

  class HilbertAxioms1D (Point: Type) where
    /-- Between : b is Between a and c (exclusive) -/
    Between(a b c: Point): Prop

    /-- Between relation is exclusive. -/
    between_ne(a b c: Point): Between a b c → a ≠ b ∧ b ≠ c

    /--
      axiom II.1: If A, B, C are points of a straight line and B lies Between A and C, then B lies also Between C and A.
    -/
    between_symm(a b c: Point): Between a b c → Between c b a

    /--
      axiom II.2.1 If A and C are two points of a straight line, there exists at least one point B lying between A and C.
      This can be proved in 2D but is axiom for 1D.
    -/
    between_exists(a c: Point): a ≠ c → {b: Point // Between a b c}

    /--
      axiom II.2.2 If A and C are two points of a straight line, there exists at least one point D so situated that C lies Between A and D.
    -/
    extension_exists(a c: Point): a ≠ c → {d: Point // Between a c d}

    /-- axiom I.8: There exist at least two points on a line. -/
    line_exists_two_points: {s: Point × Point // s.1 ≠ s.2}

    OnSegment(a b c: Point): Prop := Between a b c ∨ b = a ∨ b = c

    OnSegment_def(a b c: Point): OnSegment a b c ↔ Between a b c ∨ b = a ∨ b = c := by
      simp only [OnSegment]

  def IsSubset{Point: Type}{α: Type}{β: Type}[Membership Point α][Membership Point β](S: α)(T: β): Prop :=
      ∀ p: Point, p ∈ S → p ∈ T

  scoped infix:99 "⊆" => IsSubset

  class HilbertAxioms2D (Point: Type) where
    Line: Type
    mem_Line: Membership Point Line

    /-- Between : b is Between a and c (exclusive) -/
    Between(a b c: Point): Prop

    /-- Between relation is exclusive. -/
    between_ne(a b c: Point): Between a b c → a ≠ b ∧ b ≠ c

    /--
      axiom II.1: If A, B, C are points of a straight line and B lies Between A and C, then B lies also Between C and A.
    -/
    between_symm(a b c: Point): Between a b c → Between c b a

    /--
      axiom II.2.2 If A and C are two points of a straight line, there exists at least one point D so situated that C lies Between A and D.
    -/
    extension_exists(a c: Point): a ≠ c → {d: Point // Between a c d}

    /-- axiom I.1: Two distinct points A and B always completely determine a straight line a. --/
    mk_line(a b: Point)(h: a ≠ b): {l: Line // a ∈ l ∧ b ∈ l}

    /-- axiom I.2: Any two distinct points of a straight line completely determine that line -/
    unique_line_from_two_points (a b: Point)(l: Line)(h:  a ≠ b) : a ∈ l → b ∈ l → l = mk_line a b h

    /-- axiom I.8: There exist at least two points on a line. -/
    line_exists_two_points(l: Line): {s: Point × Point // s.1 ≠ s.2 ∧ s.1 ∈ l ∧ s.2 ∈ l}

    /-- a b c is collinear -/
    Collinear (a b c : Point) : Prop := ∃ l : Line, a ∈ l ∧ b ∈ l ∧ c ∈ l

    collinear_def(a b c :Point) : Collinear a b c ↔ ∃ l : Line, a ∈ l ∧ b ∈ l ∧ c ∈ l := by
      simp only [Collinear]

    /-- If B is between A and C, then A, B, C are collinear. -/
    collinear_of_between(a b c: Point): Between a b c → Collinear a b c

    /--
      axiom I.7.2: in every plane at least three points not lying in the same straight line
      addition: It's important to point out A≠B in axiom. otherwise it's not possible to prove ne_of_not_collinear
    -/
    exists_three_noncollinear_points: {s: Point × Point × Point //
      [s.1, s.2.1, s.2.2].Pairwise (· ≠ ·)
      ∧ ¬Collinear s.1 s.2.1 s.2.2}

    OnSegment(a b c: Point): Prop := Between a b c ∨ b = a ∨ b = c

    OnSegment_def(a b c: Point): OnSegment a b c ↔ Between a b c ∨ b = a ∨ b = c := by
      simp only [OnSegment]

    /-- axiom II.5: Let A, B, C be three points not lying in the same straight line and let a be a
    straight line lying in the plane ABC and not passing through any of the points A,
    B, C. Then, if the straight line a passes through a point of the segment AB, it will
    also pass through either a point of the segment BC or a point of the segment AC.-/
    pasch_axiom {A B C: Point}(h: ¬Collinear A B C)(l: Line)(h2: ∃ P: Point, OnSegment A P B ∧ P ∈ l):
        {Q: Point // (OnSegment B Q C ∨  OnSegment A Q C) ∧ Q ∈ l}

  class HilbertAxioms3D (Point: Type) where
    Line: Type
    mem_Line: Membership Point Line
    Plane: Type
    mem_Plane: Membership Point Plane
    plane_exists: Nonempty Plane

    /-- Between : b is Between a and c (exclusive) -/
    Between(a b c: Point): Prop

    /-- Between relation is exclusive. -/
    between_ne(a b c: Point): Between a b c → a ≠ b ∧  b ≠ c

    /--
      axiom II.1: If A, B, C are points of a straight line and B lies Between A and C, then B lies also Between C and A.
    -/
    between_symm(a b c: Point): Between a b c → Between c b a

    /--
      axiom II.2.2 If A and C are two points of a straight line, there exists at least one point D so situated that C lies Between A and D.
    -/
    extension_exists(a c: Point): a ≠ c → {d: Point // Between a c d}

    /-- axiom I.1: Two distinct points A and B always completely determine a straight line a. --/
    mk_line(a b: Point)(h: a ≠ b): {l: Line // a ∈ l ∧ b ∈ l}

    /-- axiom I.2: Any two distinct points of a straight line completely determine that line; that is, if AB = a and AC = a, where B ̸= C, then is also BC = a. -/
    unique_line_from_two_points (a b: Point)(l: Line)(h:  a ≠ b) : a ∈ l → b ∈ l → l = mk_line a b h

    /-- axiom I.8: There exist at least two points on a line. -/
    line_exists_two_points(l: Line): {s: Point × Point // s.1 ≠ s.2 ∧ s.1 ∈ l ∧ s.2 ∈ l}

    /-- a b c is collinear -/
    Collinear (a b c : Point) : Prop := ∃ l : Line, a ∈ l ∧ b ∈ l ∧ c ∈ l

    collinear_def(a b c :Point) : Collinear a b c ↔ ∃ l : Line, a ∈ l ∧ b ∈ l ∧ c ∈ l := by
      simp only [Collinear]

    /-- If B is between A and C, then A, B, C are collinear. -/
    collinear_of_between(a b c: Point): Between a b c → Collinear a b c

    /-- axiom I.7.2: in every plane at least three points not lying in the same straight line -/
    exists_three_noncollinear_points(pl: Plane):
      {s: Point × Point × Point //
        s.1∈pl ∧ s.2.1∈pl ∧ s.2.2∈pl ∧
        [s.1, s.2.1, s.2.2].Pairwise (· ≠ ·) ∧
        ¬Collinear s.1 s.2.1 s.2.2
      }

    /-- axiom I.3: Three points A, B, C not situated in the same straight line always completely determine a plane α.-/
    mk_plane(a b c: Point)(h: ¬Collinear a b c): {l: Plane // a ∈ l ∧ b ∈ l ∧ c ∈ l}

    OnSegment(a b c: Point): Prop := Between a b c ∨ b = a ∨ b = c

    OnSegment_def(a b c: Point): OnSegment a b c ↔ Between a b c ∨ b = a ∨ b = c := by
      simp only [OnSegment]

    /-- axiom II.5: Let A, B, C be three points not lying in the same straight line and let a be a
    straight line lying in the plane ABC and not passing through any of the points A,
    B, C. Then, if the straight line a passes through a point of the segment AB, it will
    also pass through either a point of the segment BC or a point of the segment AC.-/
    pasch_axiom {A B C: Point}(h1: ¬Collinear A B C)(l: Line)(h2: l ⊆ (mk_plane A B C h1).val)(h3: ∃ P: Point, OnSegment A P B ∧ P ∈ l) :
        {Q: Point // (OnSegment B Q C ∨  OnSegment A Q C) ∧ Q ∈ l}

    /-- axiom I.4: Any three points A, B, C of a plane α, which do not lie in the same straight line, completely determine that plane. -/
    unique_plane_from_three_points(a b c: Point)(pl: Plane)(h: ¬Collinear a b c):
      a ∈ pl → b ∈ pl → c ∈ pl → pl = mk_plane a b c h

    /-- axiom I.5: If two points A, B of a straight line a lie in a plane α, then every point of a lies in a.-/
    line_in_plane_if_two_points_in_plane(a b: Point)(l: Line)(pl: Plane)(h: a ≠ b):
      a ∈ l → b ∈ l → a ∈ pl → b ∈ pl → ∀ c ∈ l, c ∈ pl

    /-- axiom I.6: If two planes α, β have a point A in common, then they have at least a second point B in common.-/
    plane_intersection_exists_two_points(pl1 pl2: Plane)(h: pl1 ≠ pl2)(a: Point):
      a ∈ pl1 ∧ a ∈ pl2 →
      {b: Point // b ≠ a ∧ b ∈ pl1 ∧ b ∈ pl2}

    /--
      axiom I.10: In every space R there exist at least four points not lying in the same plane.
      addition: It's important to point out A≠B in axiom. otherwise it's not possible to prove ne_of_noncoplanar
    -/
    space_exists_four_noncoplanar_points:
      {s: Point × Point × Point × Point //  [s.1, s.2.1, s.2.2.1, s.2.2.2].Pairwise (· ≠ ·) ∧ ¬(∃ pl: Plane, s.1 ∈ pl ∧ s.2.1 ∈ pl ∧ s.2.2.1 ∈ pl ∧ s.2.2.2 ∈ pl)}

  -- Membership instance for point on line in a plane
  instance {Point Line Plane: Type}[Membership Point Line][Membership Point Plane]{pl: Plane}:
      Membership {p: Point // p ∈ pl} {l: Line // l ⊆ pl} where
    mem (l: {l: Line // l ⊆ pl}) (p: {p: Point // p ∈ pl}) : Prop := p.val ∈ l.val

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
end Geometry.HilbertAxioms2D
