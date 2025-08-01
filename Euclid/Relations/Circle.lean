import Euclid.Sorts.Primitives
import Euclid.Sorts.Circle
import Euclid.Relations.Point
import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card

namespace Euclid

  namespace Point

    /--
      命题：点在圆的内部
    -/
    def in_circle (p: Point)(c: Circle): Prop :=
      c.center.distance p < c.radius

    /--
      命题：点在圆上
    -/
    def on_circle (p: Point)(c: Circle): Prop :=
      c.center.distance p = c.radius

    namespace on_circle
      variable {p: Point}{c: Circle}

      /--
        圆上的任意一点都不是圆心
      -/
      theorem ne_center(h: on_circle p c) : p ≠ c.center := by
        apply (distance_gt_zero_iff p c.center).mpr
        rw [distance.symm]
        rw [h]
        exact c.radius_pos

    end on_circle

  end Point

  namespace Circle
    /--
      两圆处于相交关系，有且仅有两个不同的交点
    -/
    def intersect_circle(c1 c2: Circle): Prop :=
      {p: Point | p.on_circle c1 ∧ p.on_circle c2}.encard = 2

    /--
      两圆处于相切关系，有且仅有一个公共点
    -/
    def tangency_circle(c1 c2: Circle): Prop :=
      ∃! p: Point, p.on_circle c1 ∧ p.on_circle c2

    /--
      两圆既不相交也不相切，没有公共点
    -/
    def nonintersect_circle(c1 c2: Circle): Prop :=
      ¬ ∃ p: Point, p.on_circle c1 ∧ p.on_circle c2
  end Circle

  def distance_eq_iff_on_same_circle(c: Circle)(p1 p2: Point)(hp1: p1.on_circle c)(hp2: p2.on_circle c):
    c.center.distance p1 = c.center.distance p2 := by
    unfold Point.on_circle at hp1 hp2
    rw [hp1, hp2]

end Euclid
