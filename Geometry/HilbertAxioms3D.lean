import Geometry.Basic

namespace Geometry

  class HilbertAxioms3D (Point: Type)
  extends
    PointOrder Point,
    LineConnection Point,
    PlaneConnection Point
  where
    /--
      axiom I.10: In every space R there exist at least four points not lying in the same plane.
    -/
    space_exists_four_noncoplanar_points:
      {s: Point × Point × Point × Point //  [s.1, s.2.1, s.2.2.1, s.2.2.2].Distinct ∧ ¬(∃ pl: Plane, s.1 ∈ pl ∧ s.2.1 ∈ pl ∧ s.2.2.1 ∈ pl ∧ s.2.2.2 ∈ pl)}


end Geometry
