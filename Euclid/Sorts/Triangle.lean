import Euclid.Sorts.Primitives

namespace Euclid

  /--
    三角形
    TODO: 需要证明三点不共线
  -/
  structure Triangle where
    a: Point
    b: Point
    c: Point
    h: a≠b ∧ b≠c ∧ c≠a

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
    axiom eq_reorder_ac: △a:b:c h1 = △c:b:a h2

    /--
      交换顶点顺序仍表示同一三角形
    -/
    axiom eq_reorder_ab: △a:b:c h1 = △b:a:c h2

  end Triangle

end Euclid
