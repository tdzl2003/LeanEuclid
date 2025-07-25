import Mathlib.Data.Real.Basic


namespace Euclid
  /--
    点
  -/
  axiom Point : Type

  namespace Point

    /--
      两点间的距离
    -/
    axiom distance(p1 p2: Point) : Real

    namespace distance
      /--
        不同的点之间的距离大于0
      -/
      axiom gt_zero {p1 p2: Point} (h: p1≠p2) : distance p1 p2 > 0

      /--
        两点之间的距离 与 两点的顺序无关
      -/
      axiom symm(p1 p2: Point): distance p1 p2 = distance p2 p1

      /--
        点和自己的距离为0
      -/
      axiom self(p: Point): distance p p = 0

      /--
        任意两点的距离 大于等于0
      -/
      theorem ge_zero (p1 p2: Point) : distance p1 p2 ≥ 0 := by
        by_cases h: p1=p2
        . rw [h, self]
        . apply le_of_lt
          exact gt_zero h

    end distance

  end Point

end Euclid
