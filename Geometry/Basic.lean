
-- Hilbert geometry definition, reference: https://www.gutenberg.org/files/17384/17384-pdf.pdf

namespace List
  def Distinct{α}(l: List α):Prop :=
    l.Pairwise (· ≠ ·)

  theorem Distinct.select{l: List α}(h: l.Distinct)(i j: Fin l.length)(hne: i ≠ j):
    l[i] ≠ l[j] :=
  by
    unfold Distinct at h
    rw [List.pairwise_iff_getElem] at h
    by_cases hle: i < j
    . specialize h i j i.2 j.2 hle
      exact h
    . have : j < i := by
        apply Nat.lt_of_le_of_ne;
        . rw [Fin.mk_lt_mk, Nat.not_lt] at hle; exact hle;
        . apply Ne.symm
          rw [ne_eq, Fin.eq_mk_iff_val_eq] at hne
          exact hne
      specialize h j i j.2 i.2 this
      apply Ne.symm
      exact h

  theorem Distinct.select' {l: List α}(h: l.Distinct)(i j: Nat)(hi: i < l.length)(hj: j<l.length)(hne: i ≠ j):
    l[i]'hi ≠ l[j]'hj :=
  by
    apply h.select ⟨i, hi⟩ ⟨j, hj⟩
    rw [ne_eq, Fin.eq_mk_iff_val_eq]
    exact hne

end List

namespace Geometry
  structure Segment(Point: Type) where
    p1: Point
    p2: Point

  def Segment.valid {Point: Type}(s: Segment Point): Prop :=
    s.p1 ≠ s.p2


  def IsSubset{Point: Type}{α: Type}{β: Type}[Membership Point α][Membership Point β](S: α)(T: β): Prop :=
      ∀ p: Point, p ∈ S → p ∈ T

  scoped infix:99 "⊆" => IsSubset

end Geometry

namespace Geometry

  namespace HilbertAxioms1D
    -- 1D definition
    class Defs (Point: Type) where
      instDecidableEq: DecidableEq Point

    attribute [instance] Defs.instDecidableEq

    class Connections (Point: Type)  where
      /-- axiom I.8: There exist at least two points on a line. -/
      line_exists_two_points: {s: Point × Point // s.1 ≠ s.2}

    class Orders (Point: Type) where
      /-- Between : b is Between a and c (exclusive) -/
      Between(a b c: Point): Prop

      /-- Between relation is exclusive. -/
      between_ne{a b c: Point}: Between a b c → [a,b,c].Distinct

      /--
        axiom II.1: If A, B, C are points of a straight line and B lies Between A and C, then B lies also Between C and A.
      -/
      between_symm{a b c: Point}: Between a b c → Between c b a

      /--
        This can be proved in 2D but is axiom for 1D.
      -/
      between_not_symm_right{a b c : Point}: Between a b c → ¬ Between a c b

      /--
        axiom II.2.1 If A and C are two points of a straight line, there exists at least one point B lying between A and C.
        This can be proved in 2D but is axiom for 1D.
      -/
      between_exists{a c: Point}: a ≠ c → {b: Point // Between a b c}

      /--
        axiom II.2.2 If A and C are two points of a straight line, there exists at least one point D so situated that C lies Between A and D.
        Additional constraints: D ≠ A
      -/
      extension_exists{a c: Point}: a ≠ c → {d: Point // Between a c d}


    instance {Point: Type}[G: Orders Point]: Membership Point (Segment Point) where
      mem (s: Segment Point) (p: Point) : Prop := G.Between s.p1 p s.p2

  end HilbertAxioms1D

  class HilbertAxioms1D (Point: Type) extends
    HilbertAxioms1D.Defs Point,
    HilbertAxioms1D.Connections Point,
    HilbertAxioms1D.Orders Point


  namespace HilbertAxioms2D
    class Defs(Point: Type) where
      instDecidableEq: DecidableEq Point

      Line: Type
      instMemLine: Membership Point Line
      instDecidableMemLine: (l: Line)→(p: Point) → Decidable (p ∈ l)

    attribute [instance] Defs.instDecidableEq
    attribute [instance] Defs.instMemLine
    attribute [instance] Defs.instDecidableMemLine

    def Collinear{Point}[G:Defs Point](a b c: Point):Prop :=
      ∃ l:G.Line, a ∈ l ∧ b ∈ l ∧ c ∈ l

    class Connections(Point: Type) extends Defs Point where
      /-- axiom I.1: Two distinct points A and B always completely determine a straight line a. --/
      mk_line{a b: Point}(h: a ≠ b): {l: Line // a ∈ l ∧ b ∈ l}

      /-- construction axiom: If there's two line with common point, we can construct it. -/
      mk_line_intersection{l1 l2: Line}(hne: l1 ≠ l2)(he: ∃ p, p∈l1 ∧ p ∈ l2) : {p: Point // p ∈ l1 ∧ p ∈ l2}

      /-- axiom I.2: Any two distinct points of a straight line completely determine that line -/
      unique_line_from_two_points{a b: Point}{l: Line}(h:  a ≠ b) : a ∈ l → b ∈ l → l = mk_line h

      /-- axiom I.8: There exist at least two points on a line. -/
      line_exists_two_points(l: Line): {s: Point × Point // s.1 ≠ s.2 ∧ s.1 ∈ l ∧ s.2 ∈ l}

      /--
        axiom I.7.2: in every plane at least three points not lying in the same straight line
        addition: It's important to point out A≠B in axiom. otherwise it's not possible to prove ne_of_not_collinear
      -/
      exists_three_noncollinear_points: {s: Point × Point × Point //
        [s.1, s.2.1, s.2.2].Distinct
        ∧ ¬ Collinear s.1 s.2.1 s.2.2}

    class Orders(Point: Type) extends Connections Point where
      /-- Between : b is Between a and c (exclusive) -/
      Between(a b c: Point): Prop

      /-- Between relation is exclusive. -/
      between_ne{a b c: Point}: Between a b c → [a, b, c].Distinct

      /--
        axiom II.1: If A, B, C are points of a straight line and B lies Between A and C, then B lies also Between C and A.
      -/
      between_symm{a b c: Point}: Between a b c → Between c b a

      /--
        axiom II.2.2 If A and C are two points of a straight line, there exists at least one point D so situated that C lies Between A and D.
        Additional constraints: D ≠ A, which is required to prove between_exists
        TODO: can we remove this constraint and prove one D' ≠ A exists? Maybe it's a circular argument
      -/
      extension_exists{a c: Point}: a ≠ c → {d: Point // Between a c d}

      /-- If B is between A and C, then A, B, C are collinear. -/
      collinear_of_between{a b c: Point}: Between a b c → Collinear a b c

      /-- axiom II.5: Let A, B, C be three points not lying in the same straight line and let a be a
      straight line lying in the plane ABC and not passing through any of the points A,
      B, C. Then, if the straight line a passes through a point of the segment AB, it will
      also pass through either a point of the segment BC or a point of the segment AC.-/
      pasch_axiom {A B C: Point}{l: Line}(h1: ¬Collinear A B C)
        (hA: ¬A ∈ l)(hB: ¬B ∈ l )(hc: ¬C ∈ l)
        (h2: ∃ P: Point, Between A P B ∧ P ∈ l):
          {Q: Point // (Between B Q C ∨ Between A Q C) ∧ Q ∈ l}

    instance {Point: Type}[G: Orders Point]: Membership Point (Segment Point) where
        mem (s: Segment Point) (p: Point) : Prop := G.Between s.p1 p s.p2

  end HilbertAxioms2D


  class HilbertAxioms2D (Point: Type) extends
    HilbertAxioms2D.Defs Point,
    HilbertAxioms2D.Connections Point,
    HilbertAxioms2D.Orders Point



  namespace HilbertAxioms3D
    class Defs(Point: Type) where
      instDecidableEq: DecidableEq Point

      Line: Type
      instMemLine: Membership Point Line
      instDecidableMemLine: (l: Line)→(p: Point) → Decidable (p ∈ l)

      Plane: Type
      instMemPlane: Membership Point Plane
      instPlaneNonEmpty: Nonempty Plane

    attribute [instance] Defs.instDecidableEq
    attribute [instance] Defs.instMemLine
    attribute [instance] Defs.instDecidableMemLine
    attribute [instance] Defs.instMemPlane

    def Collinear{Point}[G:Defs Point](a b c: Point):Prop :=
      ∃ l:G.Line, a ∈ l ∧ b ∈ l ∧ c ∈ l

    class Connections(Point: Type) extends Defs Point where
      /-- axiom I.1: Two distinct points A and B always completely determine a straight line a. --/
      mk_line{a b: Point}(h: a ≠ b): {l: Line // a ∈ l ∧ b ∈ l}

      /-- axiom I.2: Any two distinct points of a straight line completely determine that line; that is, if AB = a and AC = a, where B ̸= C, then is also BC = a. -/
      unique_line_from_two_points{a b: Point}{l: Line}(h:  a ≠ b) : a ∈ l → b ∈ l → l = mk_line h

      /-- construction axiom: If there's two line with common point, we can construct it. -/
      mk_line_intersection{l1 l2: Line}(hne: l1 ≠ l2)(e: ∃ p, p∈l1 ∧ p ∈ l2) : {p: Point // p ∈ l1 ∧ p ∈ l2}

      /-- axiom I.8: There exist at least two points on a line. -/
      line_exists_two_points(l: Line): {s: Point × Point // s.1 ≠ s.2 ∧ s.1 ∈ l ∧ s.2 ∈ l}

      /-- axiom I.7.2: in every plane at least three points not lying in the same straight line -/
      exists_three_noncollinear_points(pl: Plane):
        {s: Point × Point × Point //
          s.1∈pl ∧ s.2.1∈pl ∧ s.2.2∈pl ∧
          [s.1, s.2.1, s.2.2].Distinct ∧
          ¬Collinear s.1 s.2.1 s.2.2
        }

      /-- axiom I.3: Three points A, B, C not situated in the same straight line always completely determine a plane α.-/
      mk_plane{a b c: Point}(h: ¬Collinear a b c): {l: Plane // a ∈ l ∧ b ∈ l ∧ c ∈ l}

      /-- axiom I.4: Any three points A, B, C of a plane α, which do not lie in the same straight line, completely determine that plane. -/
      unique_plane_from_three_points{a b c: Point}{pl: Plane}(h: ¬Collinear a b c):
        a ∈ pl → b ∈ pl → c ∈ pl → pl = mk_plane h

      /-- axiom I.5: If two points A, B of a straight line a lie in a plane α, then every point of a lies in a.-/
      line_in_plane_if_two_points_in_plane{a b: Point}{l: Line}{pl: Plane}(h: a ≠ b):
        a ∈ l → b ∈ l → a ∈ pl → b ∈ pl → ∀ c ∈ l, c ∈ pl

      /-- axiom I.6: If two planes α, β have a point A in common, then they have at least a second point B in common.-/
      plane_intersection_exists_two_points{pl1 pl2: Plane}(h: pl1 ≠ pl2){a: Point}:
        a ∈ pl1 ∧ a ∈ pl2 →
        {b: Point // b ≠ a ∧ b ∈ pl1 ∧ b ∈ pl2}

      /--
        axiom I.10: In every space R there exist at least four points not lying in the same plane.
        addition: It's important to point out A≠B in axiom. otherwise it's not possible to prove ne_of_noncoplanar
      -/
      space_exists_four_noncoplanar_points:
        {s: Point × Point × Point × Point //  [s.1, s.2.1, s.2.2.1, s.2.2.2].Distinct ∧ ¬(∃ pl: Plane, s.1 ∈ pl ∧ s.2.1 ∈ pl ∧ s.2.2.1 ∈ pl ∧ s.2.2.2 ∈ pl)}

    class Orders(Point: Type) extends Connections Point where
      /-- Between : b is Between a and c (exclusive) -/
      Between(a b c: Point): Prop

      /-- Between relation is exclusive. -/
      between_ne{a b c: Point}: Between a b c → [a,b,c].Distinct

      /--
        axiom II.1: If A, B, C are points of a straight line and B lies Between A and C, then B lies also Between C and A.
      -/
      between_symm{a b c: Point}: Between a b c → Between c b a

      /--
        axiom II.2.2 If A and C are two points of a straight line, there exists at least one point D so situated that C lies Between A and D.
        Additional constraints: D ≠ A,
      -/
      extension_exists{a c: Point}: a ≠ c → {d: Point // Between a c d}

      /-- If B is between A and C, then A, B, C are collinear. -/
      collinear_of_between{a b c: Point}: Between a b c → Collinear a b c


      /-- axiom II.5: Let A, B, C be three points not lying in the same straight line and let a be a
      straight line lying in the plane ABC and not passing through any of the points A,
      B, C. Then, if the straight line a passes through a point of the segment AB, it will
      also pass through either a point of the segment BC or a point of the segment AC.-/
      pasch_axiom {A B C: Point}{l: Line}
        (h1: ¬Collinear A B C)(h2: l ⊆ (mk_plane h1).val)
        (hA: ¬A ∈ l)(hB: ¬B ∈ l )(hC: ¬C ∈ l)
        (h3: ∃ P: Point, Between A P B ∧ P ∈ l) :
          {Q: Point // (Between B Q C ∨ Between A Q C) ∧ Q ∈ l}

    instance {Point: Type}[G: Orders Point]: Membership Point (Segment Point) where
        mem (s: Segment Point) (p: Point) : Prop := G.Between s.p1 p s.p2
  end HilbertAxioms3D


  class HilbertAxioms3D (Point: Type) extends
    HilbertAxioms3D.Defs Point,
    HilbertAxioms3D.Connections Point,
    HilbertAxioms3D.Orders Point



end Geometry
