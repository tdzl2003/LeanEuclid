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

  -- 构建三角形的必要条件：三点不共线
  theorem hp{p: Point}(hp: p.on_circle c1 ∧ p.on_circle c2):
      ¬Point.on_same_line A B p := by
    intro h
    have eq1: A.distance p = A.distance B := by
      rw [show A = c1.center by unfold c1 Circle.mk_from_points;simp only]
      apply distance_eq_iff_on_same_circle
      exact hp.1
      apply point_on_mk_circle

    have eq2: B.distance p = A.distance B := by
      rw [Point.distance.symm A]
      rw [show B = c2.center by unfold c2 Circle.mk_from_points;simp only]
      apply distance_eq_iff_on_same_circle
      exact hp.2
      apply point_on_mk_circle

    have h2: A.distance B > 0 := by
      apply (Point.distance_gt_zero_iff A B).mp
      exact s.distinct_endpoints

    rcases h.between_cases with h1|h1|h1
    all_goals {
      have h1':= h1.distance
      repeat rw [Point.distance.symm p] at h1'
      try rw [eq1] at h1'
      try rw [eq2] at h1'
      try rw [Point.distance.symm B] at h1'
      have : A.distance B + A.distance B > A.distance B := by
        apply lt_add_of_pos_right
        exact h2
      apply ne_of_lt this
      apply Eq.symm
      exact h1'
    }

  theorem hp1: ¬Point.on_same_line A B p1 := hp c1_intersect_c2.p1_on_circle

  theorem hp2: ¬Point.on_same_line A B p2 := hp c1_intersect_c2.p2_on_circle

  -- 构建两个三角形
  noncomputable def t1 := △A:B:p1 hp1
  noncomputable def t2 := △A:B:p2 hp2

  -- TODO: 证明 △A:B:p1 和 △A:B:p2 是正三角形
  -- TODO：证明不存在其他的 以A-B为一条边的正三角形


end EuclideaGame.Alpha.TEquilateral
