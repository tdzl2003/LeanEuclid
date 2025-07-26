import Euclid.Sorts.Primitives
import Euclid.Sorts.Circle
import Euclid.Relations.Point
import Euclid.Relations.Circle

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

  theorem point_on_mk_circle(center p: Point)(distinct: center ≠ p): p.on_circle <| Circle.mk_from_points center p distinct := by
    unfold Circle.mk_from_points Point.on_circle
    simp only

end Euclid
