import Euclid

open Euclid

namespace EuclideaGame.Alpha.TEquilateral

  -- 题目给定一条线段，要求做出以其为一条边的正三角形

  -- 题目给定的任意线段
  axiom s: Segment

  -- 线段的两个端点
  noncomputable def A:= s.p1
  noncomputable def B:= s.p2

  -- 以A为圆心，过B作圆c1
  noncomputable def c1 := Circle.mk_from_points A B (s.distinct_endpoints)

  -- 以B为圆心，过A做圆c2
  noncomputable def c2 := Circle.mk_from_points B A (Ne.symm s.distinct_endpoints)

  -- 证明：c1和c2相交
  theorem c1_intersect_c2 : c1.intersect_circle c2 := by
    -- 通过圆心距离小于半径之和来证明
    apply Circle.intersect_circle_iff.mpr
    unfold c1 c2 Circle.mk_from_points
    simp [Point.distance.symm]
    apply Point.distance.gt_zero s.distinct_endpoints

  -- 取其两个交点p1, p2
  noncomputable def p1 := c1_intersect_c2.p1
  noncomputable def p2 := c1_intersect_c2.p2

  -- TODO: 证明 △A:B:p1 和 △A:B:p2 是正三角形
  noncomputable def t1 := △A:B:p1 (⟨s.distinct_endpoints, sorry⟩)

  -- TODO：证明不存在其他的 以A-B为一条边的正三角形


end EuclideaGame.Alpha.TEquilateral
