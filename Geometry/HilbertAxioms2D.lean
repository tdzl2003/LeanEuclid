import Geometry.Basic.Point
import Geometry.Basic.Line

namespace Geometry

  class HilbertAxioms2D (Point: Type) extends
    LineConnection Point,
    PointOrder Point where
    /-- axiom II.5: Let A, B, C be three points not lying in the same straight line and let a be a
      straight line lying in the plane ABC and not passing through any of the points A,
      B, C. Then, if the straight line a passes through a point of the segment AB, it will
      also pass through either a point of the segment BC or a point of the segment AC.-/
    pasch_axiom {A B C: Point}{l: Line}(h1: ¬Collinear A B C)
      (hA: ¬A ∈ l)(hB: ¬B ∈ l )(hc: ¬C ∈ l)
      (h2: ∃ P: Point, Between A P B ∧ P ∈ l):
        {Q: Point // (Between B Q C ∨ Between A Q C) ∧ Q ∈ l}

    /--
      axiom I.7.2: in every plane at least three points not lying in the same straight line
    -/
    exists_three_noncollinear_points: {s: Point × Point × Point //
      [s.1, s.2.1, s.2.2].Distinct
      ∧ ¬ Collinear s.1 s.2.1 s.2.2}

end Geometry
