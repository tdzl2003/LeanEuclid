import Geometry.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use
import Mathlib.Tactic.NormNum

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

  theorem line_eq_of_two_points{a b : Point}{l1 l2: G.Line}:
    a≠b → a∈ l1 → a ∈ l2 → b ∈ l1 → b ∈ l2 → l1=l2 :=
  by
    intro hne ha1 ha2 hb1 hb2
    -- 用公理得出 l1 = mk_line hne 和 l2 = mk_line hne
    let e1 := G.unique_line_from_two_points (l := l1) hne ha1 hb1
    let e2 := G.unique_line_from_two_points (l := l2) hne ha2 hb2
    -- 由 l1 = mk_line hne 和 l2 = mk_line hne 得出 l1 = l2
    exact Eq.trans e1 (Eq.symm e2)

  /-- Theorem 1.1. Two straight lines of a plane have either one point or no point in
    common -/
  theorem common_point_of_lines{l1 l2: G.Line}(h: l1 ≠ l2):
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
    ¬Collinear a b c → a ≠ b :=
  by
    intro h h_eq
    subst h_eq
    -- 如果 a = b，则 a, b, c 共线（因为 a,b 在同一条线上且 b=c 时平凡）
    have hcol : Collinear a a c := by
      -- 构造出 a,c 两点确定的直线
      by_cases hac : a = c
      · -- 如果 a = c，那三个点相同，更是共线
        obtain ⟨⟨p,q,r⟩, hpair, _⟩ := G.exists_three_noncollinear_points
        have t1:∀ d, d≠a → Collinear a a c := by
          intro d hda
          let l := G.mk_line hda
          rw [collinear_def, ← hac]
          refine ⟨l, ?_, ?_, ?_⟩
          · exact (G.mk_line hda).property.right   -- a ∈ l
          · exact (G.mk_line hda).property.right   -- b = a ∈ l
          · exact (G.mk_line hda).property.right -- c ∈ l

        by_cases h: p = a
        . have : q ≠ a  := by
            rw [← h]
            rw [List.pairwise_iff_getElem] at hpair
            specialize hpair 0 1 (by norm_num) (by norm_num) (by decide)
            simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hpair
            apply Ne.symm hpair
          apply t1 q this
        . apply t1 p h
      ·
        let l := G.mk_line hac
        rw [collinear_def]
        refine ⟨l, ?_, ?_, ?_⟩
        · exact (G.mk_line hac).property.left   -- a ∈ l
        · exact (G.mk_line hac).property.left   -- b = a ∈ l
        · exact (G.mk_line hac).property.right -- c ∈ l
    exact h hcol

  theorem collinear_comm_cross{a b c: Point}: Collinear a b c → Collinear c b a := by
    rw [collinear_def, collinear_def]
    intro ⟨l, hl⟩
    use l
    simp only [hl, and_self]

  theorem collinear_comm_left{a b c: Point}: Collinear a b c → Collinear b a c := by
    rw [collinear_def, collinear_def]
    intro ⟨l, hl⟩
    use l
    simp only [hl, and_self]

  theorem collinear_comm_right{a b c: Point}: Collinear a b c → Collinear a c b := by
    rw [collinear_def, collinear_def]
    intro ⟨l, hl⟩
    use l
    simp only [hl, and_self]

  theorem collinear_comm_rotate{a b c: Point}: Collinear a b c → Collinear b c a := by
    rw [collinear_def, collinear_def]
    intro ⟨l, hl⟩
    use l
    simp only [hl, and_self]

  theorem collinear_comp{a b c d: Point}(hne: a≠b): Collinear a b c → Collinear a b d → Collinear a c d := by
    sorry

end Geometry.HilbertAxioms2D


namespace Geometry.HilbertAxioms3D
  variable {Point: Type} [G:HilbertAxioms3D Point]

  theorem ne_of_not_collinear{a b c: Point}:
    ¬Collinear a b c → a ≠ b := by
    sorry

end Geometry.HilbertAxioms3D
