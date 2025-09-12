import Geometry.Basic.Point

namespace Geometry
  structure Segment(Point: Type)[G: PointOrder Point] where
    p1: Point
    p2: Point

  def Segment.valid {Point: Type}[G: PointOrder Point](s: Segment Point): Prop :=
    s.p1 ≠ s.p2

  instance {Point: Type}[G: PointOrder Point]: Membership Point (Segment Point) where
      mem (s: Segment Point) (p: Point) : Prop := G.Between s.p1 p s.p2

end Geometry
