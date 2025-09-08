import Geometry.Basic
import Geometry.Connections
import Mathlib.Tactic.ByContra
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic


namespace Geometry.HilbertAxioms1D
  variable {Point: Type}[G: HilbertAxioms1D Point]


  /-- 根据公理I.7.2，直线外恒有一点 -/
  def point_outside_line(l: G.Line)[(p: Point) → Decidable (p ∈ l)]: {p: Point // p ∉ l} :=
    let ⟨⟨A, B, C⟩, hne, hnc⟩ := G.exists_three_noncollinear_points
    if hA: A ∈ l then
      if hB: B ∈ l then
        have hne: A≠B := by
          simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil,
            and_self, and_true] at hne
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

  theorem lies_on_mk_line_of_between{a b c: Point}(hne: a≠c)(h: Between a b c):
    b ∈ (mk_line hne).val :=
  by
    have h := G.collinear_of_between h
    rw [collinear_def] at h
    let ⟨l, ha, hb, hc⟩ := h
    have : l = mk_line hne := by
      apply G.unique_line_from_two_points
      exact ha
      exact hc
    rw [← this]
    exact hb

  def between_exists{a c: Point}(hne: a ≠ c): {b: Point // G.Between a b c} :=
    -- 直线AC
    let ⟨l1, ha1, hc1⟩ := G.mk_line hne

    -- 根据公理I.7.2，直线外恒有一点E
    let ⟨e, he1⟩ := point_outside_line l1

    -- A必不等于E，否则E处在直线AC上
    have hae: a ≠ e := by
      intro h
      apply he1
      rw [← h]
      exact ha1

    -- 根据公理II.2.2，直线AE上有一点F，使E在线段AF内
    let ⟨f, hf1⟩ := G.extension_exists hae


    -- F必不等于C，否则F和E都将处在直线AC上
    have hfc: f ≠ c := by
      intro h
      apply he1
      have : l1 = G.mk_line hne := by
        apply G.unique_line_from_two_points
        exact ha1
        exact hc1
      rw [this]
      subst h
      apply lies_on_mk_line_of_between
      exact hf1

    let ⟨g, hg1⟩ := G.extension_exists hfc

    have hg2: f ≠ g := by
      have h := G.between_ne hg1
      rw [List.pairwise_iff_getElem] at h
      specialize h 0 2 (by norm_num) (by norm_num) (by decide)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
      exact h

    have hg2: e ≠ g := by
      have t1 := G.collinear_of_between hf1
      have t2 := G.collinear_of_between hg1
      rw [collinear_def] at t1 t2
      -- 直线AEF
      let ⟨l3, ha, he, hf1⟩ := t1
      -- 直线FCG
      let ⟨l4, hf2, hc, hg⟩ := t2

      intro hc2
      apply hg2
      apply common_point_of_lines l3 l4
      . -- l3 ≠ l4
        have : c ∉ l3 := by
          intro h
          have: l1 = l3 := by
            have : l1 = mk_line hne := by
              apply G.unique_line_from_two_points
              exact ha1
              exact hc1
            rw [this]
            have : l3 = mk_line hne := by
              apply G.unique_line_from_two_points
              exact ha
              exact h
            rw [this]
          apply he1
          rw [this]
          exact he
        intro h
        apply this
        rw [h]
        exact hc
      . exact hf1
      . exact hf2
      . rw [← hc2]
        exact he
      . exact hg

    -- 直线EG
    let ⟨l2, hl2⟩ := G.mk_line hg2

    -- TODO: 和上述证明有少许重复，看看如何精简
    have t1 : ¬ Collinear a f c := by
      intro h
      have t1 := G.collinear_of_between hf1
      rw [collinear_def] at t1 h
      -- 直线AEF
      let ⟨l3, ha, he, hf2⟩ := t1
      -- 虚构的矛盾直线ACF
      let ⟨l4, ha', hf', hc'⟩ := h

      have hf3 : f ≠ a := by
        have hf1 := G.between_ne hf1
        rw [List.pairwise_iff_getElem] at hf1
        specialize hf1 0 2 (by norm_num) (by norm_num) (by decide)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hf1
        apply Ne.symm hf1

      apply he1
      -- l3、l4共点a、f，所以相等
      have t2: l3 = l4 := by
        have: l3 = mk_line hf3 := by
          apply G.unique_line_from_two_points
          exact hf2
          exact ha
        rw [this]
        have: l4 = mk_line hf3 := by
          apply G.unique_line_from_two_points
          exact hf'
          exact ha'
        rw [this]
      -- l1、l3共点a、c，所以相等
      have t3: l1 = l3 := by
        have : l1 = mk_line hne := by
          apply G.unique_line_from_two_points
          exact ha1
          exact hc1
        rw [this]
        have : l3 = mk_line hne := by
          apply G.unique_line_from_two_points
          exact ha
          rw [t2]
          exact hc'
        rw [this]
      rw [t3]
      exact he

    have t2 : ∃ P: Point, OnSegment a P f ∧ P ∈ l2 := by
      use e
      and_intros
      . rw [OnSegment_def]
        apply Or.inl
        exact hf1
      . exact hl2.1

    have ⟨b, hb1, hb2⟩  := G.pasch_axiom t1 t2

    have hFinal: Between a b c  := by
      have t1: ¬ OnSegment f b c := by
        -- 如果b在fc之间，那么b=g，但g又不在fc之间
        sorry
      have t2: b ≠ a := by
        -- 如果b=a，那么e=a，矛盾
        sorry

      have t3: b ≠ c := by
        -- 可以直接从t1推出
        simp only [OnSegment_def, not_or] at t1
        exact t1.2.2
      simp only [t1, t2, t3, OnSegment_def, false_or, or_false] at hb1
      exact hb1

    ⟨b, hFinal⟩


  /-- theorem II.3 Of any three points situated on a straight line, there is always one and only one which lies Between the other two. -/
  theorem between_trichotomy(a b c: Point): a ≠ b → b ≠ c → a ≠ c →
      (G.Between a b c ∨ G.Between b a c ∨ G.Between a c b) ∧
      ¬(G.Between a b c ∧ G.Between b a c) ∧
      ¬(G.Between a b c ∧ G.Between a c b) ∧
      ¬(G.Between b a c ∧ G.Between a c b) := by
    sorry

  /--
    If B is between A and C, and C is between B and D, then B is also between A and D, and C is also between A and D.
  -/
  theorem between_transitivity {A B C D : Point} :
      G.Between A B C → G.Between B C D → G.Between A B D ∧ G.Between A C D := by
    sorry

  /--
    If B is between A and C, and C is between A and D, then B is also between A and D, and C is also between B and D.
  -/
  theorem between_transitivity' {A B C D : Point} :
      G.Between A B C → G.Between A C D → G.Between A B D ∧ G.Between B C D := by
    sorry

  /--
    theorem II.4: Any four points A, B, C, D of a straight line can always be so arranged that B
    shall lie between A and C and also between A and D, and, furthermore, that C shall
    lie between A and D and also between B and D.
  -/
  theorem four_points_ordering{a b c d : Point} :
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ∃ (a' b' c' d' : Point),
        ({a', b', c', d'}: Set Point) =  {a,b,c,d} ∧
        (G.Between a' b' c' ∧ G.Between a' b' d' ∧ G.Between a' c' d' ∧ G.Between b' c' d') :=
  by
    sorry

  /--
    Theorem 3. Between any two points of a straight line, there always exists an
    unlimited number of points.
  -/
  theorem infinite_points_between (A B : Point) (hNe : A ≠ B) :
      ∀ (F : Finset Point), ∃ (P : Point), Between A P B ∧ P ∉ F :=
  by
    sorry

  /-- Definition of a linearly ordered list where for any three indices i < j < k,
    the point at j is between the points at i and k. -/
  def LinearOrderedPointList (L : List Point) : Prop :=
    ∀ (i j k : Fin L.length), i.val < j.val → j.val < k.val → Between (L.get i) (L.get j) (L.get k)

  /-- Theorem 4.1 : For any finite set of points on a straight line, there exists a linearly ordered list
      of these points, and only two such lists exist (the forward and reverse order). -/
  theorem linear_ordering_of_collinear_points[G: HilbertAxioms1D Point](S : Finset Point) :
      ∃ (L : List Point),
        L.toFinset = S ∧
        List.Nodup L ∧
        LinearOrderedPointList L :=
  by
    admit

  /-- Theorem 4.2 reverse order is also LinearOrderedPointList -/
  theorem linear_ordering_reverse(L: List Point):
      LinearOrderedPointList L →
      LinearOrderedPointList (L.reverse) :=
  by
    sorry

end Geometry.HilbertAxioms1D

namespace Geometry.HilbertAxioms2D
  variable {Point: Type}[G: HilbertAxioms2D Point]

  theorem onSameSide.not_liesOn(l: G.Line)(a b: Point):
      G.SameSideOfLine l a b → ¬ a ∈ l ∧ ¬ b ∈ l :=
  by
    sorry

  theorem onOtherSide.not_liesOn(l: G.Line)(a b: Point):
      OtherSideOfLine l a b → ¬ a ∈ l ∧ ¬ b ∈  l :=
  by
    sorry

  theorem onSameSide.not_onOtherSide(l: G.Line)(a b: Point):
      SameSideOfLine l a b → ¬ OtherSideOfLine l a b :=
  by
    sorry

  theorem onOtherSide.not_onSameSide(l: G.Line)(a b: Point):
      OtherSideOfLine l a b → ¬ SameSideOfLine l a b :=
  by
    sorry

  theorem onSameSide.not (l: G.Line)(a b: Point):
      ¬ SameSideOfLine l a b → a ∈ l ∨ b ∈ l ∨ OtherSideOfLine l a b:=
  by
    sorry

  theorem onOtherSide.not (l: G.Line)(a b: Point):
      ¬ OtherSideOfLine l a b → a ∈ l ∨ b ∈ l ∨ SameSideOfLine l a b :=
  by
    sorry

  theorem onSameSide.reflex (l: G.Line)(a: Point):
      SameSideOfLine l a a :=
  by
    sorry

  theorem onOtherSide.not_reflex(l: G.Line)(a: Point):
      ¬ OtherSideOfLine l a a :=
  by
    sorry

  theorem onSameSide.symm(l: G.Line)(a b: Point):
      SameSideOfLine l a b → SameSideOfLine l b a :=
  by
    sorry

  theorem onOtherSide.symm(l: G.Line)(a b: Point):
      OtherSideOfLine l a b → OtherSideOfLine l b a :=
  by
    sorry

  theorem onSameSide.trans(l: G.Line)(a b c: Point):
      SameSideOfLine l a b → SameSideOfLine l b c → SameSideOfLine l a c :=
  by
    sorry

  theorem onOtherSide.trans(a b c: Point)(h: a ≠ b)(l: G.Line):
      OtherSideOfLine l a b → OtherSideOfLine l b c → SameSideOfLine l a c :=
  by
    sorry

end Geometry.HilbertAxioms2D
