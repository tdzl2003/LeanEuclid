import Euclid.Sorts.Primitives
import Euclid.Relations.Line

namespace Euclid

  /--
    三角形
  -/
  structure Triangle where
    a: Point
    b: Point
    c: Point
    h: ¬ Point.on_same_line a b c

  notation:max "△" a ":" b ":" c:max => Triangle.mk a b c

  namespace Triangle
    namespace Detail
      variable {a b c : Point}
      /--
        交换顶点顺序仍表示同一三角形
      -/
      axiom eq_reorder_bc: △a:b:c h1 = △a:c:b h2

      /--
        交换顶点顺序仍表示同一三角形
      -/
      axiom eq_reorder_ab: △a:b:c h1 = △b:a:c h2

      /--
        交换顶点顺序仍表示同一三角形
      -/
      theorem eq_reorder_ac: △a:b:c h1 = △c:b:a h2 := by
        rw [eq_reorder_ab, eq_reorder_bc, eq_reorder_ab]
        . rw [Point.on_same_line.comm_left]
          exact h2
        . rw [Point.on_same_line.comm_left]
          exact h1
    end Detail

    @[simp]
    def reorder_bc(t: Triangle) : Triangle :=
      △t.a:t.c:t.b (by rw[Point.on_same_line.comm_right]; exact t.h)

    @[simp]
    def reorder_ab(t: Triangle) : Triangle :=
      △t.b:t.a:t.c (by rw[Point.on_same_line.comm_left]; exact t.h)

    @[simp]
    def reorder_ac(t: Triangle) : Triangle :=
      △t.c:t.b:t.a (by rw[Point.on_same_line.comm_left, Point.on_same_line.comm_right, Point.on_same_line.comm_left]; exact t.h)

    theorem reorder_bc.eq(t: Triangle): t.reorder_bc = t := by
      apply Detail.eq_reorder_bc

    theorem reorder_ab.eq(t: Triangle): t.reorder_ab = t := by
      apply Detail.eq_reorder_ab

    theorem reorder_ac.eq(t: Triangle): t.reorder_ac = t := by
      apply Detail.eq_reorder_ac

  end Triangle

end Euclid
