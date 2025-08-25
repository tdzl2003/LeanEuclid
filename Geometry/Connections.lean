import Geometry.Basic
import Mathlib.Tactic.ByContra

namespace HilbertGeometry2D
  variable {Point Line: Type} [HilbertGeometry2D Point Line]

  /-- Another way to express Axiom I.2: that is, if AB = a and AC = a, where B ̸= C, then is also BC = a.  -/
  theorem line_bc_eq_of_ab_and_ac_eq (a b c: Point)(l: Line): b ≠ c →
     mk_line_from_points a b = l → mk_line_from_points a c = l → mk_line_from_points b c = l
    := by
      intro hne hab hac
      have ha : liesOn a l := by rw [←hab]; exact (mk_line_liesOn a b).left
      have hb : liesOn b l := by rw [←hab]; exact (mk_line_liesOn a b).right
      have hc : liesOn c l := by rw [←hac]; exact (mk_line_liesOn a c).right
      exact unique_line_from_two_points b c l hne hb hc

  /-- Theorem 1.1. Two straight lines of a plane have either one point or no point in
    common -/
  theorem common_point_of_lines(l1 l2: Line)(h: l1 ≠ l2):
    ∀ p1 p2: Point, liesOn p1 l1 → liesOn p1 l2 → liesOn p2 l1 → liesOn p2 l2 → p1 = p2 := by
      intro p1 p2 hp1l1 hp1l2 hp2l1 hp2l2
      by_contra hne
      have t1:= unique_line_from_two_points p1 p2 l1 hne hp1l1 hp2l1
      have t2:= unique_line_from_two_points p1 p2 l2 hne hp1l2 hp2l2
      have : l1 = l2 := by
        rw [← t1, ← t2]
      exact absurd this h

end HilbertGeometry2D
