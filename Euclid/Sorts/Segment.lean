import Mathlib.Data.Real.Basic
import Euclid.Sorts.Primitives
import Euclid.Relations.Point

namespace Euclid
  /--
    线段，由其两个端点唯一确定。
  -/
  structure Segment where
    p1: Point
    p2: Point
    distinct_endpoints: p1 ≠ p2

  open Lean

  namespace Segment

    /--
    线段的长度，等同于两端点之间的距离
    -/
    noncomputable def length (s: Segment): ℝ := s.p1.distance s.p2

    variable {a b : Point}

  end Segment

end Euclid
