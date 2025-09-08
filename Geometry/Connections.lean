import Geometry.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use

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

  /-- 根据公理I.7.2，直线外恒有一点 -/
  def point_outside_line(l: G.Line)[(p: Point) → Decidable (p ∈ l)]: {p: Point // p ∉ l} :=
    let ⟨⟨A, B, C⟩, hne, hnc⟩ := G.exists_three_noncollinear_points
    if hA: A ∈ l then
      if hB: B ∈ l then
        have hne: A≠B := by
          simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, false_implies, implies_true, List.Pairwise.nil, and_self,
            and_true] at hne
          exact hne.1.1
        have hC: C ∉ l := by
          intro h
          apply hnc
          have : l = G.mk_line hne := by
            apply G.unique_line_from_two_points hne hA hB
          rw [collinear_def]
          use l
        ⟨C, hC⟩
      else
        ⟨B, hB⟩
    else
      ⟨A, hA⟩

  theorem ne_of_not_collinear{a b c: Point}:
    ¬Collinear a b c → a ≠ b := by
    sorry

end Geometry.HilbertAxioms2D


namespace Geometry.HilbertAxioms3D
  variable {Point: Type} [G:HilbertAxioms3D Point]

  theorem ne_of_not_collinear{a b c: Point}:
    ¬Collinear a b c → a ≠ b := by
    sorry

end Geometry.HilbertAxioms3D
