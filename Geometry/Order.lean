import Geometry.Basic
import Geometry.Connections
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic


namespace Geometry.HilbertAxioms1D
  variable {Point: Type}[G: HilbertAxioms1D Point]

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

  theorem between_ne'{a b c : Point}(h: Between a b c) : a≠ b ∧ b ≠ c ∧ a ≠ c := by
    have h := between_ne h
    simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self,
      and_true] at h
    simp [h]

  theorem collinear_of_onsegment{a b c:Point}:
    OnSegment a b c → Collinear a b c := by
    intro h
    rw [OnSegment_def] at h
    rcases h with h | h | h
    . apply collinear_of_between h
    . subst h
      apply collinear_of_eq
    . subst h
      apply collinear_comm_cross
      apply collinear_of_eq

  theorem between_not_symm_right{a b c : Point}: Between a b c → ¬ Between a c b := by
    sorry

  theorem not_between_of_onsegment_symm{a b c : Point}: OnSegment a b c → ¬ Between a c b := by
    intro h
    rw [OnSegment_def] at h
    rcases h with h | h | h
    . apply between_not_symm_right h
    . subst h
      intro h
      have h:= (between_ne' h).2.2
      contradiction
    . subst h
      intro h
      have h := (between_ne' h).2.1
      contradiction

  theorem in_mk_line_iff_collinear{a b c : Point}(hne: a ≠ c):
    Collinear a b c ↔ b ∈ (mk_line hne).val :=
  by
    constructor
    . intro h
      rw [collinear_def] at h
      let ⟨l, ha, hb, hc⟩ := h
      have : l = (mk_line hne).val := by
        apply G.unique_line_from_two_points
        exact ha
        exact hc
      rw [← this]
      exact hb
    . intro h
      let l' := mk_line hne
      rw [show (mk_line hne).val = l'.val by rfl] at h
      rw [collinear_def]
      use l'.val
      simp only [l'.property, h, and_self]

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

    have hfe: f ≠ e := by
      apply Ne.symm
      have h := G.between_ne hf1
      rw [List.pairwise_iff_getElem] at h
      specialize h 1 2 (by norm_num) (by norm_num) (by decide)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
      exact h

    have haf: a ≠ f := by
      have h := G.between_ne hf1
      rw [List.pairwise_iff_getElem] at h
      specialize h 0 2 (by norm_num) (by norm_num) (by decide)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
      exact h

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
      rw [← in_mk_line_iff_collinear]
      apply collinear_of_between
      exact hf1

    let ⟨g, hg1⟩ := G.extension_exists hfc

    have hg2: f ≠ g := by
      have h := G.between_ne hg1
      rw [List.pairwise_iff_getElem] at h
      specialize h 0 2 (by norm_num) (by norm_num) (by decide)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
      exact h

    have hg3: e ≠ g := by
      have t1 := G.collinear_of_between hf1
      have t2 := G.collinear_of_between hg1
      rw [collinear_def] at t1 t2
      -- 直线AEF
      let ⟨l3, ha, he, hf1⟩ := t1
      -- 直线FCG
      let ⟨l4, hf2, hc, hg⟩ := t2

      intro hc2
      apply hg2
      apply common_point_of_lines (l1:=l3) (l2:=l4)
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
    let ⟨l2, hl2⟩ := G.mk_line hg3

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
      have t3: ¬ OnSegment f b c := by
        intro H_onseg
        have hb_col : Collinear f b c := collinear_of_onsegment H_onseg
        have hg_col : Collinear f c g := collinear_of_between hg1
        have hb_in_lfc : b ∈ (mk_line hfc).val := by
          rw [← in_mk_line_iff_collinear]
          exact hb_col
        have hg_in_lfc : g ∈ (mk_line hfc).val := by
          rw [← in_mk_line_iff_collinear]
          apply collinear_comm_right
          exact hg_col

        have hbg: b ≠ g := by
          intro eq
          have := not_between_of_onsegment_symm H_onseg
          rw [eq] at this
          exact this hg1

        have : l2 = (mk_line hfc).val := by
          apply line_eq_of_two_points hbg
          exact hb2
          exact hb_in_lfc
          exact hl2.2
          exact hg_in_lfc

        have he_in_lfc : e ∈ (mk_line hfc).val := this ▸ hl2.left
        rw [← in_mk_line_iff_collinear] at he_in_lfc

        have he_in_laf : Collinear f e a := by
          apply collinear_comm_cross
          apply collinear_of_between hf1

        have : Collinear a f c := by
          rw [collinear_def]
          let l:= mk_line hfe
          use l.val
          and_intros
          . unfold l
            rw [← in_mk_line_iff_collinear]
            apply collinear_comm_right
            exact he_in_laf
          . exact l.property.1
          . unfold l
            rw [← in_mk_line_iff_collinear]
            apply collinear_comm_right
            exact he_in_lfc

        exact t1 this

      have t4: b ≠ a := by
        intro he
        -- 如果b=a，那么e=a，矛盾
        have : e = a := by
          let l3 := mk_line hae
          have: l2 ≠ l3 := by
            have hl3: a ∈ l3.val := l3.property.1
            have hg_l2: g ∈ l2 := hl2.2

            intro h_eq
            have hg_l3: g ∈ l3.val := by rw [h_eq] at hg_l2; exact hg_l2

            have h_col : Collinear a e g := by
              apply collinear_comm_right
              rw [in_mk_line_iff_collinear hae]
              exact hg_l3

            -- 目标推导afc共线
            -- aeg、aef共线推出afg共线
            have h_afg : Collinear a f g := by
              apply collinear_comp hae
              . apply collinear_of_between
                exact hf1
              . exact h_col

            -- fga、fgc共线推出afc共线
            have h_afc : Collinear f a c := by
              apply collinear_comp hg2
              . apply collinear_comm_rotate
                exact h_afg
              . apply collinear_comm_right
                apply collinear_of_between
                exact hg1

            apply t1
            apply collinear_comm_left
            exact h_afc

          apply common_point_of_lines this
          . exact hl2.1
          . exact l3.property.2
          . rw [← he]
            exact hb2
          . exact l3.property.1

        apply hae
        rw [this]

      have t5: b ≠ c := by
        -- 可以直接从t1推出
        simp only [OnSegment_def, not_or] at t3
        exact t3.2.2
      simp only [t3, t4, t5, OnSegment_def, false_or, or_false] at hb1
      exact hb1

    ⟨b, hFinal⟩


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
