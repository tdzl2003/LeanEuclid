import Euclid.Sorts.Primitives
import Euclid.Sorts.Circle
import Euclid.Relations.Point

namespace Euclid

  namespace Circle

    /--
      使用圆心和圆上一点构造圆
    -/
    @[simp]
    noncomputable def mk_from_points(center p: Point)(distinct: center ≠ p): Circle :=
      Circle.mk center (center.distance p) (by
          apply Point.distance.gt_zero
          exact distinct
      )

  end Circle


end Euclid
