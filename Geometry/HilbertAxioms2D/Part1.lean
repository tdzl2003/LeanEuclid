import Geometry.Basic.Point
import Geometry.Basic.Line

namespace Geometry

  class HilbertAxioms2D.Part1 (Point: Type) extends
    LineConnection Point,
    PointOrder Point
  where
    /-- axiom II.5: Let A, B, C be three points not lying in the same straight line and let a be a
      straight line lying in the plane ABC and not passing through any of the points A,
      B, C. Then, if the straight line a passes through a point of the segment AB, it will
      also pass through either a point of the segment BC or a point of the segment AC.-/
    pasch_axiom {A B C: Point}{l: Line}(h1: ¬Collinear A B C)
      (hA: ¬A ∈ l)(hB: ¬B ∈ l )(hc: ¬C ∈ l)
      (h2: ∃ P: Point, Between A P B ∧ P ∈ l):
        {Q: Point // (Between B Q C ∨ Between A Q C) ∧ Q ∈ l}

    /--
      axiom I.7.2: in every plane at least three points not lying in the same straight line
    -/
    exists_three_noncollinear_points: {s: Point × Point × Point //
      [s.1, s.2.1, s.2.2].Distinct
      ∧ ¬ Collinear s.1 s.2.1 s.2.2}

  -- prove PointOrderExt with axioms part 1
  namespace HilbertAxioms2D
    open PointOrder LineConnection

    variable {Point: Type}[G: HilbertAxioms2D.Part1 Point]

    def mk_any_line: G.Line :=
      let ⟨⟨A, B, C⟩, hne, hnc⟩ := G.exists_three_noncollinear_points
      G.mk_line (show A ≠ B by
          apply hne.select' 0 1
          all_goals norm_num
        )

    def mk_point_not_on_line(l: G.Line): {p: Point // p ∉ l} :=
      let ⟨⟨A, B, C⟩, hne, hnc⟩ := G.exists_three_noncollinear_points
      if hA: A ∈ l then
        if hB: B ∈ l then
          have hne: A≠B := by
            apply hne.select' 0 1
            all_goals norm_num
          have hC: C ∉ l := by
            intro h
            apply hnc
            have : l = mk_line hne := by
              apply unique_line_from_two_points hne hA hB
            use l
          ⟨C, hC⟩
        else
          ⟨B, hB⟩
      else
        ⟨A, hA⟩

    instance : LineConnectionHelper Point where
      mk_any_line := mk_any_line
      mk_point_not_on_line := mk_point_not_on_line

    def between_exists{a c: Point}(hne: a ≠ c): {b: Point // Between a b c} :=
      -- 直线AC
      let ⟨l1, ha1, hc1⟩ := mk_line hne

      -- 根据公理I.7.2，直线外恒有一点E
      let ⟨e, he1⟩ := mk_point_not_on_line l1

      -- A必不等于E，否则E处在直线AC上
      have hae: a ≠ e := by
        intro h
        apply he1
        rw [← h]
        exact ha1

      -- 根据公理II.2.2，直线AE上有一点F，使E在线段AF内
      let ⟨f, hf1⟩ := extension_exists hae

      have hfe: f ≠ e := by
        apply Ne.symm
        have h := between_ne hf1
        apply h.select' 1 2
        all_goals norm_num

      have haf: a ≠ f := by
        have h := between_ne hf1
        apply h.select' 0 2
        all_goals norm_num

      -- F必不等于C，否则F和E都将处在直线AC上
      have hfc: f ≠ c := by
        intro h
        apply he1
        have : l1 = mk_line hne := by
          apply unique_line_from_two_points
          exact ha1
          exact hc1
        rw [this]
        subst h
        rw [← in_mk_line_iff_collinear]
        apply collinear_of_between
        exact hf1

      let ⟨g, hg1⟩ := extension_exists hfc

      have hg2: f ≠ g := by
        have h := between_ne hg1
        apply h.select' 0 2
        all_goals norm_num

      have hg3: e ≠ g := by
        have t1 := collinear_of_between hf1
        have t2 := collinear_of_between hg1
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
                apply unique_line_from_two_points
                exact ha1
                exact hc1
              rw [this]
              have : l3 = mk_line hne := by
                apply unique_line_from_two_points
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
      let ⟨l2, hl2⟩ := mk_line hg3

      -- TODO: 和上述证明有少许重复，看看如何精简
      have t1 : ¬ Collinear a f c := by
        intro h
        have t1 := collinear_of_between hf1
        -- 直线AEF
        let ⟨l3, ha, he, hf2⟩ := t1
        -- 虚构的矛盾直线ACF
        let ⟨l4, ha', hf', hc'⟩ := h

        have hf3 : f ≠ a := by
          have hf1 := between_ne hf1
          apply Ne.symm
          apply hf1.select' 0 2
          all_goals norm_num

        apply he1
        -- l3、l4共点a、f，所以相等
        have t2: l3 = l4 := by
          have: l3 = mk_line hf3 := by
            apply unique_line_from_two_points
            exact hf2
            exact ha
          rw [this]
          have: l4 = mk_line hf3 := by
            apply unique_line_from_two_points
            exact hf'
            exact ha'
          rw [this]
        -- l1、l3共点a、c，所以相等
        have t3: l1 = l3 := by
          have : l1 = mk_line hne := by
            apply unique_line_from_two_points
            exact ha1
            exact hc1
          rw [this]
          have : l3 = mk_line hne := by
            apply unique_line_from_two_points
            exact ha
            rw [t2]
            exact hc'
          rw [this]
        rw [t3]
        exact he

      have t2 : ∃ P: Point, Between a P f ∧ P ∈ l2 := by
        use e
        and_intros
        . exact hf1
        . exact hl2.1

      have hal2: a ∉ l2 := by
        intro hal2
        have h_col : Collinear a e g := by
          use l2

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

      have hfl2: f ∉ l2 := by
        intro hfl2
        have h_feg : Collinear f e g := by
          use l2

        have h_fec : Collinear f e c := by
          apply collinear_comp hg2
          . apply collinear_comm_right
            exact h_feg
          . apply collinear_comm_right
            apply collinear_of_between
            exact hg1

        have h_fac : Collinear f c a := by
          apply collinear_comp hfe
          . exact h_fec
          . apply collinear_comm_cross
            apply collinear_of_between
            exact hf1

        apply t1
        apply collinear_comm_rotate
        apply collinear_comm_rotate
        exact h_fac

      have hcl2: c ∉ l2 := by
        intro hcl2

        have h_ecg : Collinear e c g := by
          use l2
          simp only [hl2, hcl2, and_self]

        have h_cfe : Collinear c f e := by
          have: c≠g := by
            have := between_ne hg1
            apply this.select' 1 2
            all_goals norm_num
          apply collinear_comp this
          . apply collinear_comm_rotate
            apply collinear_of_between
            exact hg1
          . apply collinear_comm_rotate
            exact h_ecg

        have h_fac : Collinear f c a := by
          apply collinear_comp hfe
          . apply collinear_comm_rotate
            exact h_cfe
          . apply collinear_comm_cross
            apply collinear_of_between
            exact hf1

        apply t1
        apply collinear_comm_rotate
        apply collinear_comm_rotate
        exact h_fac

      have ⟨b, hb1, hb2⟩  := G.pasch_axiom t1 hal2 hfl2 hcl2 t2

      have hFinal: Between a b c  := by
        have t3: ¬ Between f b c := by
          intro H_fbc
          have hb_col : Collinear f b c := collinear_of_between H_fbc
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
            have := between_not_symm_right H_fbc
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

        simp only [t3, false_or, or_false] at hb1
        exact hb1

      ⟨b, hFinal⟩

    instance: PointOrderExt Point where
      between_exists := between_exists
      between_trans := sorry
      between_trans' := sorry

    instance: LineConnWithPointOrderExt Point where
      between_trichotomy := sorry

  end HilbertAxioms2D


end Geometry
