import Mathlib.Data.Real.Basic
import Euclid.Sorts.Point

namespace Euclid

  /--
  圆的定义：到圆心距离相等的所有点的集合。
  在这里采用圆心 和 对应的距离来构造定义。
  -/
  structure Circle : Type where
    center: Point
    radius: ℝ
    radius_pos: radius > 0

  namespace Circle

  end Circle

end Euclid
