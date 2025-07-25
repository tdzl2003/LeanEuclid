import Euclid.Sorts.Point
import Mathlib.Tactic.Linarith

namespace Euclid
  namespace Point

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
