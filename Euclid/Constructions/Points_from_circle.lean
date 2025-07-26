import Euclid.Sorts.Circle
import Euclid.Sorts.Primitives
import Euclid.Relations.Circle
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card

namespace Euclid

  -- TODO: 可以依据连续性公理证明并构造两个交点，减少axiom的使用
  namespace Detail
    /--
      两个相交的圆 可以构造两个交点
    -/
    axiom Point.mk_from_circle_should_intersect{c1 c2: Circle}
      (h: |c1.radius - c2.radius| < c1.center.distance c2.center ∧  c1.center.distance c2.center < c1.radius + c2.radius)
      : Point × Point

    /--
      构造的交点互不相等，且应该在圆上
    -/
    axiom Point.circle_intersect_on_circle{c1 c2: Circle}
      (h: |c1.radius - c2.radius| < c1.center.distance c2.center ∧  c1.center.distance c2.center < c1.radius + c2.radius):
      let ⟨p1, p2⟩ := Point.mk_from_circle_should_intersect h
      p1≠p2 ∧ p1.on_circle c1 ∧ p1.on_circle c2 ∧ p2.on_circle c1 ∧ p2.on_circle c2

    /--
      两圆相交，有且仅有两个交点，不存在第三个交点
    -/
    axiom Point.circle_intersect_no_third_point {c1 c2: Circle}
      (h: |c1.radius - c2.radius| < c1.center.distance c2.center ∧  c1.center.distance c2.center < c1.radius + c2.radius):
      let ⟨p1, p2⟩ := Point.mk_from_circle_should_intersect h
      ¬ ∃ p3, p3 ≠ p1 ∧ p3 ≠ p2 ∧ p3.on_circle c1 ∧ p3.on_circle c2
  end Detail

  namespace Circle

    /--
      两圆相交，当且仅当圆心距大于半径差 且 小于半径和
    -/
    theorem intersect_circle_iff{c1 c2: Circle}:
      c1.intersect_circle c2 ↔ |c1.radius - c2.radius| < c1.center.distance c2.center ∧  c1.center.distance c2.center < c1.radius + c2.radius := by
      constructor
      . sorry
      . intro h
        let ins := Detail.Point.mk_from_circle_should_intersect h
        unfold Circle.intersect_circle
        have :  {p | p.on_circle c1 ∧ p.on_circle c2} = {ins.1, ins.2} := by
          apply Set.ext
          intro x
          constructor
          . let h1 := Detail.Point.circle_intersect_no_third_point h
            simp only [ne_eq, not_exists, not_and] at h1
            intro hx1
            simp only [Set.mem_setOf_eq] at hx1
            by_contra hx2
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx2
            exact h1 x hx2.1 hx2.2 hx1.1 hx1.2
          . simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
            intro hx1
            have hx2 := Detail.Point.circle_intersect_on_circle h
            simp only [] at hx2
            rcases hx1 with h1 | h1
            . rw [h1]
              constructor
              . exact hx2.2.1
              . exact hx2.2.2.1
            . rw [h1]
              constructor
              . exact hx2.2.2.2.1
              . exact hx2.2.2.2.2
        rw [this]
        rw [Set.encard_insert_of_notMem, Set.encard_singleton]
        norm_cast
        apply Set.notMem_singleton_iff.mpr
        apply (Detail.Point.circle_intersect_on_circle _).1

    namespace intersect_circle
      variable {c1 c2: Circle} (h: c1.intersect_circle c2)

      noncomputable def mk_points :=
        Detail.Point.mk_from_circle_should_intersect <| Circle.intersect_circle_iff.mp h

      /--
        交点1
      -/
      noncomputable def p1 :=
        h.mk_points.1

      /--
        交点2
      -/
      noncomputable def p2 :=
        h.mk_points.2

      /--
        取到的两个点满足 互不相同 且都在两个圆上
      -/
      theorem mk_points_on_circle:
        let ⟨p1, p2⟩ := h.mk_points
        p1≠p2 ∧ p1.on_circle c1 ∧ p1.on_circle c2 ∧ p2.on_circle c1 ∧ p2.on_circle c2
        := by
        apply Detail.Point.circle_intersect_on_circle

      /--
        两个交点互不相同
      -/
      theorem p1_ne_p2:
        h.p1 ≠ h.p2 := by
        have h':=  h.mk_points_on_circle
        simp only [] at h'
        exact h'.1

      /--
        交点1同时在两个圆上
      -/
      theorem p1_on_circle: h.p1.on_circle c1 ∧ h.p1.on_circle c2 := by
        have h' := h.mk_points_on_circle
        constructor
        . exact h'.2.1
        . exact h'.2.2.1

      /--
        交点2同时在两个圆上
      -/
      theorem p2_on_circle: h.p2.on_circle c1 ∧ h.p2.on_circle c2 := by
        have h' := h.mk_points_on_circle
        constructor
        . exact h'.2.2.2.1
        . exact h'.2.2.2.2

      /--
        交点必是p1、p2之一
      -/
      theorem is_p1_or_p2(p:Point)(hp: p.on_circle c1 ∧ p.on_circle c2):
        p = h.p1 ∨ p = h.p2 := by
        have h' := Detail.Point.circle_intersect_no_third_point <| Circle.intersect_circle_iff.mp h
        simp only [not_exists, not_and] at h'
        by_contra h1
        rw [not_or] at h1
        exact h' _ h1.1 h1.2 hp.1 hp.2

    end intersect_circle

    -- 两圆相切，当且仅当圆心距等于半径差（且两圆不相等），或 圆心距等于半径和
    theorem tangency_circle_iff{c1 c2 : Circle}:
      c1.tangency_circle c2 ↔ c1.center.distance c2.center = c1.radius + c2.radius ∨ c1.center.distance c2.center = |c1.radius - c2.radius| ∧ c1≠c2 := by
      sorry

  end Circle

end Euclid
