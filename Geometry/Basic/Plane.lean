import Geometry.Basic.Point
import Geometry.Basic.Line
import Geometry.Basic.Subset


namespace Geometry
  class PlaneDef(Point: Type) where
    Plane: Type
    instMemPlane: Membership Point Plane
    instPlaneNonEmpty: Nonempty Plane

  attribute [instance] PlaneDef.instMemPlane

  class PlaneConnection(Point: Type) extends
    LineDef Point,
    PlaneDef Point,
    PointOrder Point
  where
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

    /-- axiom II.5: Let A, B, C be three points not lying in the same straight line and let a be a
      straight line lying in the plane ABC and not passing through any of the points A,
      B, C. Then, if the straight line a passes through a point of the segment AB, it will
      also pass through either a point of the segment BC or a point of the segment AC.-/
    pasch_axiom {A B C: Point}{l: Line}
      (h1: ¬Collinear A B C)(h2: l ⊆ (mk_plane h1).val)
      (hA: ¬A ∈ l)(hB: ¬B ∈ l )(hC: ¬C ∈ l)
      (h3: ∃ P: Point, Between A P B ∧ P ∈ l) :
        {Q: Point // (Between B Q C ∨ Between A Q C) ∧ Q ∈ l}

end Geometry
