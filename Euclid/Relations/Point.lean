import Euclid.Sorts.Primitives
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

namespace Euclid
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


    /--
      两点间距离=0 当且仅当两点相等
    -/
    theorem distance_eq_zero_iff(p1 p2: Point): p1 = p2 ↔ distance p1 p2 = 0 := by
      constructor
      . intro h
        rw [h, distance.self]
      . contrapose
        intro h
        have := distance.gt_zero h
        linarith

    /--
      两点间距离>0 当且仅当两点不等
    -/
    theorem distance_gt_zero_iff(p1 p2: Point): p1 ≠ p2 ↔ distance p1 p2 > 0 := by
      constructor
      . intro h
        exact distance.gt_zero h
      . contrapose
        intro h
        rw [ne_eq, not_not] at h
        rw [h]
        have := distance.self p2
        linarith

  end Point
end Euclid
