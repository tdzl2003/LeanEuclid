import Euclid.Sorts.Triangle
import Euclid.Relations.Point


namespace Euclid

  namespace Triangle
    /--
      正三角形：三边相等
    -/
    def IsRegular(t: Triangle) : Prop :=
      t.a.distance t.b = t.b.distance t.c ∧ t.b.distance t.c = t.c.distance t.a

  end Triangle

  /--
    某点是三角形的顶点之一
  -/
  def Point.is_triangle_vertex(p: Point)(t: Triangle): Prop :=
    p = t.a ∨ p = t.b ∨ p = t.c

end Euclid
