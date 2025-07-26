import Euclid.Sorts.Primitives
import Euclid.Relations.Line

namespace Euclid

  /--
    三角形
    TODO: 需要证明三点不共线
  -/
  structure Triangle where
    a: Point
    b: Point
    c: Point
    h: ¬ Point.on_same_line a b c

  notation:max "△" a ":" b ":" c:max => Triangle.mk a b c

  namespace Triangle
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

  end Triangle

end Euclid
