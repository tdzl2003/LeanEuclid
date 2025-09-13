import Geometry.Basic.Point

namespace Geometry

  class LineDef(Point: Type) where
    Line: Type
    instMemLine: Membership Point Line
    instDecidableMemLine: (l: Line)→(p: Point) → Decidable (p ∈ l)

  attribute [instance] LineDef.instMemLine
  attribute [instance] LineDef.instMemLine
  attribute [instance] LineDef.instDecidableMemLine

  def Collinear{Point}[G:LineDef Point](a b c: Point):Prop :=
      ∃ l:G.Line, a ∈ l ∧ b ∈ l ∧ c ∈ l

  class LineConnection(Point: Type) extends PointOrder Point, LineDef Point where
    /-- axiom I.1: Two distinct points A and B always completely determine a straight line a. --/
    mk_line{a b: Point}(h: a ≠ b): {l: Line // a ∈ l ∧ b ∈ l}

    /-- axiom I.2: Any two distinct points of a straight line completely determine that line; that is, if AB = a and AC = a, where B ̸= C, then is also BC = a. -/
    unique_line_from_two_points{a b: Point}{l: Line}(h:  a ≠ b) : a ∈ l → b ∈ l → l = mk_line h

    /-- construction axiom: If there's two line with common point, we can construct it. -/
    mk_line_intersection{l1 l2: Line}(hne: l1 ≠ l2)(e: ∃ p, p∈l1 ∧ p ∈ l2) : {p: Point // p ∈ l1 ∧ p ∈ l2}

    /-- axiom I.8: There exist at least two points on a line. -/
    line_exists_two_points(l: Line): {s: Point × Point // s.1 ≠ s.2 ∧ s.1 ∈ l ∧ s.2 ∈ l}

    /-- If B is between A and C, then A, B, C are collinear. -/
    collinear_of_between{a b c: Point}: Between a b c → Collinear a b c


  /-- collection of some theorem/constructor implemented in different way for 2D/3D. -/
  class LineConnectionHelper(Point: Type) extends LineConnection Point where
    mk_any_line: Line

    mk_point_not_on_line(l: Line): {p: Point // p ∉ l}

  section
    open LineConnection

    variable {Point: Type}[G:LineConnection Point]

    theorem in_mk_line_iff_collinear{a b c : Point}(hne: a ≠ c):
      Collinear a b c ↔ b ∈ (mk_line hne).val :=
    by
      constructor
      . intro h
        let ⟨l, ha, hb, hc⟩ := h
        have : l = (mk_line hne).val := by
          apply unique_line_from_two_points
          exact ha
          exact hc
        rw [← this]
        exact hb
      . intro h
        let l' := mk_line hne
        rw [show (mk_line hne).val = l'.val by rfl] at h
        use l'.val
        simp only [l'.property, h, and_self]

    /-- Theorem 1.1. Two straight lines of a plane have either one point or no point in
      common -/
    theorem common_point_of_lines{l1 l2: G.Line}(h: l1 ≠ l2):
        ∀ p1 p2: Point, p1 ∈ l1 → p1 ∈ l2 → p2 ∈ l1 → p2 ∈ l2 → p1 = p2 :=
    by
      intro p1 p2 hp1l1 hp1l2 hp2l1 hp2l2
      by_contra hne
      have t1:= G.unique_line_from_two_points hne hp1l1 hp2l1
      have t2:= G.unique_line_from_two_points hne hp1l2 hp2l2
      have : l1 = l2 := by
        rw [t1, t2]
      exact absurd this h

    /-- Another way to express Axiom I.2: that is, if AB = a and AC = a, where B ̸= C, then is also BC = a.  -/
    theorem line_bc_eq_of_ab_and_ac_eq{a b c: Point}{l: G.Line}(hab: a≠b)(hac: a≠c)(hbc:b≠c):
        G.mk_line hab = l → G.mk_line hac = l → G.mk_line hbc = l
        :=
    by
      intro hab' hac'
      have hb : b ∈ l := by rw [←hab']; exact (G.mk_line _).property.right
      have hc : c ∈ l := by rw [←hac']; exact (G.mk_line _).property.right
      apply Eq.symm
      exact G.unique_line_from_two_points hbc hb hc

    theorem line_eq_of_two_points{a b : Point}{l1 l2: G.Line}:
      a≠b → a∈ l1 → a ∈ l2 → b ∈ l1 → b ∈ l2 → l1=l2 :=
    by
      intro hne ha1 ha2 hb1 hb2
      -- 用公理得出 l1 = mk_line hne 和 l2 = mk_line hne
      let e1 := G.unique_line_from_two_points (l := l1) hne ha1 hb1
      let e2 := G.unique_line_from_two_points (l := l2) hne ha2 hb2
      -- 由 l1 = mk_line hne 和 l2 = mk_line hne 得出 l1 = l2
      exact Eq.trans e1 (Eq.symm e2)

    def mk_second_point[H: LineConnectionHelper Point](a: Point)
      : {p: Point // p ≠ a}
    :=
      let l := H.mk_any_line
      let ⟨⟨b, c⟩, ⟨hbc, _⟩⟩ := H.line_exists_two_points l
      if hac: c = a then
        ⟨b, by rw [hac] at hbc; exact hbc⟩
      else
        ⟨c, hac⟩

    theorem collinear_of_eq[H: LineConnectionHelper Point](a b: Point): Collinear a a b :=
    by
      by_cases h: a = b
      . have ⟨p, hp⟩ := mk_second_point a
        have l := mk_line hp
        use l
        rw [← h]
        simp only [l.property, true_and]
      . have l := mk_line h
        use l
        simp only [l.property, true_and]

    theorem ne_of_not_collinear[H: LineConnectionHelper Point]{a b c: Point}:
      ¬Collinear a b c → a ≠ b :=
    by
      intro h1 h2
      rw [h2] at h1
      apply h1
      apply collinear_of_eq

    theorem collinear_comm_cross{a b c: Point}: Collinear a b c → Collinear c b a := by
      intro ⟨l, hl⟩
      use l
      simp only [hl, and_self]

    theorem collinear_comm_left{a b c: Point}: Collinear a b c → Collinear b a c := by
      intro ⟨l, hl⟩
      use l
      simp only [hl, and_self]

    theorem collinear_comm_right{a b c: Point}: Collinear a b c → Collinear a c b := by
      intro ⟨l, hl⟩
      use l
      simp only [hl, and_self]

    theorem collinear_comm_right_iff{a b c: Point}: Collinear a b c ↔ Collinear a c b := by
      constructor
      . apply collinear_comm_right
      . apply collinear_comm_right

    theorem collinear_comm_rotate{a b c: Point}: Collinear a b c → Collinear b c a := by
      intro ⟨l, hl⟩
      use l
      simp only [hl, and_self]

    theorem collinear_comm_rotate'{a b c: Point}: Collinear a b c → Collinear c a b := by
      intro ⟨l, hl⟩
      use l
      simp only [hl, and_self]

    theorem collinear_comp{a b c d: Point}(hne: a≠b): Collinear a b c → Collinear a b d → Collinear a c d := by
      intro h1 h2
      rcases h1 with ⟨l1, ha1, hb1, hc1⟩
      rcases h2 with ⟨l2, ha2, hb2, hd2⟩
      -- l1 和 l2 都是包含 a,b 的直线，因此唯一性保证它们相等
      have heq : l1 = l2 :=
        G.unique_line_from_two_points (l := l1) hne ha1 hb1 ▸
        (G.unique_line_from_two_points (l := l2) hne ha2 hb2).symm
      subst heq
      -- 于是 a,c,d 都在同一条直线上
      exact ⟨l1, ha2, hc1, hd2⟩

    theorem collinear_trans{a b c d : Point}: a ≠ b →  Collinear a b c → Collinear a b d → Collinear a c d := by
      intro hab ⟨l1, ⟨ha1, hb1, hc1⟩ ⟩ ⟨l2, ⟨ha2, hb2, hd2⟩⟩
      have : l1 = l2 := by
        apply line_eq_of_two_points hab ha1 ha2 hb1 hb2
      rw [← this] at hd2
      use l1

    theorem not_collinear_of_nin{a b c: Point}{l: G.Line}:
      a≠b → Collinear a b c → a∈l → b∈l → c∈l :=
    by
      intro hne hcol ha hb
      have ⟨l', ⟨ha', hb', hc'⟩⟩ := hcol
      have : l=l' := by
        apply line_eq_of_two_points hne ha ha' hb hb'
      subst this
      exact hc'
  end

  class LineConnWithPointOrderExt(Point: Type) extends LineConnection Point, PointOrderExt Point
  where
    /--
      axiom II.3.1 Of any three points situated on a straight line, there is always one
      which lies between the other two.
      This can be proven in 2D.
    --/
    between_trichotomy{a b c: Point}: Collinear a b c → a ≠ b → b ≠ c → a ≠ c →
      (Between a b c ∨ Between b a c ∨ Between a c b)

  section
    variable {Point: Type}[G:LineConnWithPointOrderExt Point]

    theorem between_trans_m{A B C D: Point}:
      G.Between A B D → G.Between A C D →
        B = C ∨ G.Between A B C ∨ G.Between A C B :=
    by
      intro h1 h2
      by_cases hbc: B = C
      . exact Or.inl hbc
      apply Or.inr
      have hab: A ≠ B := by
        apply (G.between_ne h1).select' 0 1
        all_goals norm_num
      have hac: A ≠ C := by
        apply (G.between_ne h2).select' 0 1
        all_goals norm_num

      have had: A ≠ D := by
        apply (G.between_ne h1).select' 0 2
        all_goals norm_num

      have hcol: Collinear A B C := by
        have h1:= G.collinear_of_between h1
        have h2:= G.collinear_of_between h2
        rw [collinear_comm_right_iff] at h1 h2
        apply collinear_trans had h1 h2

      have h := G.between_trichotomy hcol hab hbc hac
      rcases h with h|h|h
      . exact Or.inl h
      . by_contra
        have h:= G.between_symm h
        have h:= (G.between_trans h h1).1
        have h:= G.between_not_symm_right (G.between_symm h)
        apply h
        apply G.between_symm
        exact h2
      . exact Or.inr h

    theorem between_trans_m'{A B C D: Point}:
      G.Between A B C → G.Between A B D →
        C = D ∨ G.Between A C D ∨ G.Between A D C :=
    by
      intro h1 h2
      by_cases hcd: C = D
      . exact Or.inl hcd
      apply Or.inr
      have hab : A ≠ B := by
        apply (G.between_ne h1).select' 0 1
        all_goals norm_num
      have hac : A ≠ C := by
        apply (G.between_ne h1).select' 0 2
        all_goals norm_num
      have had : A ≠ D := by
        apply (G.between_ne h2).select' 0 2
        all_goals norm_num

      have hcol: Collinear A C D := by
        have h1:= G.collinear_of_between h1
        have h2:= G.collinear_of_between h2
        apply collinear_trans hab h1 h2

      have h := G.between_trichotomy hcol hac hcd had
      rcases h with h|h|h
      . exact Or.inl h
      . by_contra
        have h:= G.between_symm h
        have h2 := G.between_symm h2
        have h:= G.between_trans' h2 h
        have h1:= G.between_not_symm_right (G.between_symm h1)
        apply h1
        exact G.between_symm h.2
      . exact Or.inr h
  end
end Geometry
