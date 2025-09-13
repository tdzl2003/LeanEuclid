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

    /--
      axiom II.3.1 Of any three points situated on a straight line, there is always one
      which lies between the other two.
      This can be proven in 2D.
    --/
    theorem between_trichotomy{a b c: Point}: Collinear a b c → a ≠ b → b ≠ c → a ≠ c →
      (Between a b c ∨ Between b a c ∨ Between a c b) :=
    by
      intro hcol hab hbc hac
      by_contra h
      rw [not_or, not_or] at h
      have ⟨h1, h2, h3⟩ := h
      apply h1 ; clear h1
      let ⟨l, ⟨hal, hbl, hcl⟩⟩ := hcol
      let ⟨d, hd⟩ := mk_point_not_on_line l
      have hbd: b ≠ d := by
        intro h
        apply hd
        rw [← h]
        exact hbl
      let ⟨g, hg⟩ := G.extension_exists hbd

      have had: a ≠ d := by
        intro h
        apply hd
        rw [← h]
        exact hal

      -- l1 = line AD
      let ⟨l1, ⟨hal1,hdl1⟩ ⟩ := mk_line had

      have hacd : ¬ Collinear a c d := by
        intro h
        apply hd
        apply not_collinear_of_nin hac h hal hcl

      have hbg: b ≠ g := by
        have h := G.between_ne hg
        apply h.select' 0 2
        all_goals norm_num

      have hbcg : ¬ Collinear b g c := by
        intro hbgc
        apply hacd
        have hg := collinear_comm_right $ collinear_of_between hg
        have hbcd := collinear_trans hbg hbgc hg
        have hbcd := collinear_comm_left hbcd
        have hcol := collinear_comm_cross hcol
        apply collinear_comm_rotate'
        apply collinear_trans _ hbcd hcol
        apply Ne.symm hbc

      have hbl1: b ∉ l1 := by
        intro hbl1
        have : l1 = l := by
          apply line_eq_of_two_points hab hal1 hal hbl1 hbl
        subst this
        exact hd hdl1

      have hcl1: c ∉ l1 := by
        intro hcl1
        have : l1 = l := by
          apply line_eq_of_two_points hac hal1 hal hcl1 hcl
        subst this
        exact hd hdl1

      have hdg: d ≠ g := by
        apply (between_ne hg).select' 1 2
        all_goals norm_num

      have hgl1: g ∉ l1 := by
        intro hgl1
        have hadg : Collinear a d g := by
          use l1
        have hg := collinear_of_between hg
        have hdab: Collinear d a b := by
          apply collinear_trans hdg
          exact collinear_comm_rotate hadg
          exact collinear_comm_rotate hg
        apply hacd
        apply collinear_trans hab
        exact hcol
        exact collinear_comm_rotate hdab

      let ⟨e, ⟨he1, he2⟩⟩  := G.pasch_axiom hbcg hbl1 hgl1 hcl1 (by use d)

      have hae: a ≠ e := by
        intro hae
        subst hae
        simp only [h2, or_false] at he1
        have ⟨l', hgl', hal', hcl'⟩:= collinear_of_between he1
        have : l = l' := by
          apply line_eq_of_two_points hac hal hal' hcl hcl'
        subst this
        have ⟨l'', hbl'', hdl'', hgl''⟩ := collinear_of_between hg
        have : l = l'' := by
          apply line_eq_of_two_points hbg hbl hbl'' hgl' hgl''
        subst this
        contradiction

      have : ¬ Between b e c := by
        intro hbec
        have ⟨l', hbl', hel', hcl'⟩  := collinear_of_between hbec
        have : l = l' := by
          apply line_eq_of_two_points hbc hbl hbl' hcl hcl'
        subst this
        have : l = l1 := by
          apply line_eq_of_two_points hae hal hal1 hel' he2
        subst this
        contradiction

      simp only [this, or_false] at he1

      -- l2 = line CD
      have hcd: c ≠ d := by
        intro h
        apply hd
        rw [← h]
        exact hcl

      let ⟨l2, ⟨hcl2,hdl2⟩ ⟩ := mk_line hcd

      have hagb : ¬ Collinear b g a := by
        intro h
        apply hbcg
        apply collinear_trans (Ne.symm hab)
        apply collinear_comm_right h
        apply collinear_comm_left hcol

      have hal2: a ∉ l2 := by
        intro hal2
        have: l = l2 := by
          apply line_eq_of_two_points hac hal hal2 hcl hcl2
        subst this
        contradiction

      have hcg: c ≠ g := by
        intro hcg
        subst hcg
        apply hagb
        apply collinear_comm_rotate
        exact hcol

      have hde: d ≠ e := by
        intro hde
        subst hde
        have ⟨l', ⟨hgl', hdl', hcl'⟩ ⟩ := collinear_of_between he1
        have : l2 = l' := by
          apply line_eq_of_two_points hcd hcl2 hcl' hdl2 hdl'
        subst this
        have ⟨l'', ⟨hbl'', hdl'', hgl''⟩⟩ := collinear_of_between hg
        have : l2 = l'' := by
          apply line_eq_of_two_points hdg hdl' hdl'' hgl' hgl''
        subst this
        apply hbcg
        use l2

      have hgl2: g ∉ l2 := by
        intro hgl2
        have ⟨l', ⟨hgl', hel', hcl'⟩ ⟩ := collinear_of_between he1
        have : l2 = l' := by
          apply line_eq_of_two_points hcg hcl2 hcl' hgl2 hgl'
        subst this
        have : l2 = l1 := by
          apply line_eq_of_two_points hde hdl2 hdl1 hel' he2
        subst this
        contradiction

      have hbl2: b ∉ l2 := by
        intro hbl2
        have ⟨l', ⟨hal', hbl', hcl'⟩ ⟩ := hcol
        have: l2 = l' := by
          apply line_eq_of_two_points hbc hbl2 hbl' hcl2 hcl'
        subst this
        apply hacd
        use l2

      let ⟨f, ⟨hf1, hf2⟩⟩  := G.pasch_axiom hagb hbl2 hgl2 hal2 (by use d)

      have hcf: c ≠ f := by
        intro he
        subst he
        rw [between_symm_iff] at h3
        simp only [h3, or_false] at hf1
        have ⟨l', ⟨hgl', hcl', hal' ⟩⟩ := collinear_of_between hf1
        have ⟨l'', ⟨hal'', hbl'', hcl''⟩ ⟩ := hcol
        have : l' = l'' := by
          apply line_eq_of_two_points hac hal' hal'' hcl' hcl''
        subst this

        have ⟨l''', ⟨hbl''', hdl''', hgl'''⟩⟩ := collinear_of_between hg
        have: l' = l''' := by
          apply line_eq_of_two_points hbg hbl'' hbl''' hgl' hgl'''
        subst this
        apply hacd
        use l'

      have : ¬ Between b f a:= by
        intro hbfa
        have ⟨l', ⟨hbl', hfl', hal'⟩ ⟩ := collinear_of_between hbfa
        have ⟨l'', ⟨hal'', hbl'', hcl''⟩ ⟩ := hcol
        have : l' = l'' := by
          apply line_eq_of_two_points hab hal' hal'' hbl' hbl''
        subst this
        have: l2 = l' := by
          apply line_eq_of_two_points hcf hcl2 hcl'' hf2 hfl'
        subst this
        apply hacd
        use l2

      simp only [this, or_false] at hf1

      have hel2: e ∉ l2 := by
        intro hel2
        sorry

      have hage: ¬ Collinear a g e := by
        sorry

      rw [between_symm_iff] at hf1

      let ⟨d', ⟨hd'1, hd'2⟩⟩ := G.pasch_axiom hage hal2 hgl2 hel2 (by use f)


      have : d = d' := by
        sorry

      subst this

      have: ¬ Between g d e := by
        sorry
      simp only [this, false_or] at hd'1

      have haec: ¬ Collinear a e c := by
        sorry

      -- l3 = line BD
      let ⟨l3, ⟨hbl3,hdl3⟩ ⟩ := mk_line hbd

      have hal3: a ∉ l3 := by
        sorry

      have hel3: e ∉ l3 := by
        sorry

      have hcl3: c ∉ l3 := by
        sorry

      let ⟨b', ⟨hb'1, hb'2⟩⟩ := G.pasch_axiom haec hal3 hel3 hcl3 (by use d)

      have : b = b' := by
        sorry
      subst this

      have : ¬ Between e b c := by
        sorry
      simp only [this, false_or] at hb'1
      exact hb'1


    instance: PointOrderExt Point where
      between_exists := between_exists
      between_trans := sorry
      between_trans' := sorry

    instance: LineConnWithPointOrderExt Point where
      between_trichotomy := between_trichotomy

  end HilbertAxioms2D


end Geometry
