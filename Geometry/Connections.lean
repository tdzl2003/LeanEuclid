import Geometry.Basic
import Mathlib.Tactic.ByContra

namespace Geometry.HilbertAxioms2D
  variable {Point: Type} [G:HilbertAxioms2D Point]

  /-- Another way to express Axiom I.2: that is, if AB = a and AC = a, where B ̸= C, then is also BC = a.  -/
  theorem line_bc_eq_of_ab_and_ac_eq{a b c: Point}{l: G.Line}(hab: a≠b)(hac: a≠c)(hbc:b≠c):
      mk_line hab = l → mk_line hac = l → mk_line hbc = l
      :=
  by
    intro hab' hac'
    have hb : b ∈ l := by rw [←hab']; exact (mk_line _).property.right
    have hc : c ∈ l := by rw [←hac']; exact (mk_line _).property.right
    apply Eq.symm
    exact unique_line_from_two_points hbc hb hc

  /-- Theorem 1.1. Two straight lines of a plane have either one point or no point in
    common -/
  theorem common_point_of_lines(l1 l2: G.Line)(h: l1 ≠ l2):
      ∀ p1 p2: Point, p1 ∈ l1 → p1 ∈ l2 → p2 ∈ l1 → p2 ∈ l2 → p1 = p2 :=
  by
    intro p1 p2 hp1l1 hp1l2 hp2l1 hp2l2
    by_contra hne
    have t1:= unique_line_from_two_points hne hp1l1 hp2l1
    have t2:= unique_line_from_two_points hne hp1l2 hp2l2
    have : l1 = l2 := by
      rw [t1, t2]
    exact absurd this h

end Geometry.HilbertAxioms2D
