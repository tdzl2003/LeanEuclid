import Euclid
import Mathlib

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

  -- 两圆交点和A、B等距离
  theorem p_distance_eq{p: Point}(hp: p.on_circle c1 ∧ p.on_circle c2):
    A.distance p = A.distance B ∧ B.distance p = A.distance B := by
    constructor
    . rw [show A = c1.center by unfold c1 Circle.mk_from_points;simp only]
      apply distance_eq_iff_on_same_circle
      exact hp.1
      apply point_on_mk_circle
    . rw [Point.distance.symm A]
      rw [show B = c2.center by unfold c2 Circle.mk_from_points;simp only]
      apply distance_eq_iff_on_same_circle
      exact hp.2
      apply point_on_mk_circle

  -- 构建三角形的必要条件：三点不共线
  theorem hp{p: Point}(hp: p.on_circle c1 ∧ p.on_circle c2):
      ¬Point.on_same_line A B p := by
    intro h
    have ⟨eq1, eq2⟩ := p_distance_eq hp

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
  noncomputable def t1 := Triangle.mk A B p1 hp1
  noncomputable def t2 := Triangle.mk A B p2 hp2

  -- 证明 △A:B:p1 和 △A:B:p2 是正三角形
  theorem ht1: t1.IsRegular := by
    unfold t1 Triangle.IsRegular
    simp only
    have ⟨eq1, eq2⟩ := p_distance_eq c1_intersect_c2.p1_on_circle
    rw [show c1_intersect_c2.p1 = p1 by unfold p1; rfl] at eq1 eq2
    constructor
    . apply Eq.symm
      exact eq2
    . rw [Point.distance.symm p1]
      rw [eq1]
      exact eq2

  theorem ht2: t2.IsRegular := by
    unfold t2 Triangle.IsRegular
    simp only
    have ⟨eq1, eq2⟩ := p_distance_eq c1_intersect_c2.p2_on_circle
    rw [show c1_intersect_c2.p2 = p2 by unfold p2; rfl] at eq1 eq2
    constructor
    . apply Eq.symm
      exact eq2
    . rw [Point.distance.symm p2]
      rw [eq1]
      exact eq2

  -- 证明不存在其他的 以A-B为一条边的正三角形
  theorem is_t1_or_t2{t: Triangle}
    (h1: t.IsRegular)
    (h2: t.a = A ∧ t.b = B) :
    t = t1 ∨ t = t2 := by

    -- 证明：最后一个顶点一定是p1或p2
    have hc: t.c = p1 ∨ t.c = p2 := by
      apply Circle.intersect_circle.is_p1_or_p2
      unfold Point.on_circle c1 c2
      simp only [Circle.mk_from_points]
      unfold Triangle.IsRegular at h1
      rw [← h2.1, ← h2.2]
      constructor
      . rw [h1.1, Point.distance.symm t.a]
        rw [h1.2]
      . rw [← h1.1]
        rw [Point.distance.symm t.a]

    rcases hc with hc|hc
    . apply Or.inl
      unfold t1
      rw [Triangle.mk.injEq]
      simp only [h2, hc, and_self]
    . apply Or.inr
      unfold t2
      rw [Triangle.mk.injEq]
      simp only [h2, hc, and_self]


  -- 最终结果：{t1,t2} 即为本问题的解集
  theorem final_answer:
    {t: Triangle | t.IsRegular ∧ t.a=A ∧ t.b=B} = {t1,t2} := by
    apply Set.ext
    intro x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    . intro h
      apply is_t1_or_t2 h.1 h.2
    . intro h
      rcases h with h1|h1
      . rw [h1]
        constructor
        . exact ht1
        . simp only [t1, and_self]
      . rw [h1]
        constructor
        . exact ht2
        . simp only [t2, and_self]

end EuclideaGame.Alpha.TEquilateral
