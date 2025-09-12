import Geometry.Basic.Order
import Geometry.Basic.Connection

namespace Geometry


  class HilbertAxioms1D (Point: Type) extends
    Order Point where
    /-- axiom I.8: There exist at least two points on a line. -/
    line_exists_two_points: {s: Point × Point // s.1 ≠ s.2}


end Geometry
