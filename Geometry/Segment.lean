import Geometry.Basic

namespace Geometry
  structure Segment(Point: Type) where
    p1: Point
    p2: Point

  def Segment.valid {Point: Type}(s: Segment Point): Prop :=
    s.p1 ≠ s.p2

  instance {Point: Type}[G: HilbertAxioms1D Point]: Membership Point (Segment Point) where
    mem (s: Segment Point) (p: Point) : Prop := G.OnSegment s.p1 p s.p2

  instance {Point: Type}[G: HilbertAxioms2D Point]: Membership Point (Segment Point) where
      mem (s: Segment Point) (p: Point) : Prop := G.OnSegment s.p1 p s.p2

  instance {Point: Type}[G: HilbertAxioms3D Point]: Membership Point (Segment Point) where
      mem (s: Segment Point) (p: Point) : Prop := G.OnSegment s.p1 p s.p2

end Geometry
