import Geometry.Basic
import Mathlib.Tactic.Use
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.DefEqTransformations
import Mathlib.Tactic.Contrapose

namespace Geometry.HilbertAxioms1D
  def transfer {Point1 Point2 : Type} (e : Point2 ≃ Point1) (h1 : HilbertAxioms1D Point1) : HilbertAxioms1D Point2 :=
  {
    Between := fun a b c => h1.Between (e a) (e b) (e c)
    between_ne := by
      intro a b c h
      have h' := h1.between_ne (e a) (e b) (e c) h
      simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq] at h'
      exact h'
    between_symm := by
      intro a b c h
      apply h1.between_symm
      exact h
    between_exists := by
      intro a b hne
      let a1 := e a
      let b1 := e b
      have : a1 ≠ b1 := by
        simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, a1, b1]
        exact hne
      let ⟨c, hc⟩ := h1.between_exists a1 b1 this
      exact ⟨e.symm c, by simp only [Equiv.apply_symm_apply]; exact hc⟩
    extension_exists := by
      intro a c hne
      let a1 := e a
      let c1 := e c
      have hne1 : a1 ≠ c1 := by
        intro heq
        apply hne
        apply e.injective
        exact heq
      let ⟨b, hb⟩ := h1.extension_exists a1 c1 hne1
      exact ⟨e.symm b, by simp only [Equiv.apply_symm_apply]; exact hb⟩
    line_exists_two_points := by
      let ⟨⟨a1, b1⟩, h⟩ := h1.line_exists_two_points
      let a' := e.symm a1
      let b' := e.symm b1
      have hne : a' ≠ b' := by
        simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, a', b']
        exact h
      exact ⟨⟨a', b'⟩, hne⟩
    OnSegment_def := by
      intro a b c
      simp only [OnSegment, h1.OnSegment_def]
  }

end Geometry.HilbertAxioms1D


namespace Geometry.HilbertAxioms2D
  variable {Point: Type}[G: HilbertAxioms2D Point]

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
          have : l = G.mk_line A B hne := by
            apply G.unique_line_from_two_points A B l hne hA hB
          rw [collinear_def]
          use l
        ⟨C, hC⟩
      else
        ⟨B, hB⟩
    else
      ⟨A, hA⟩

  -- TODO: Can we prove this? or it should be added to axiom system?
  theorem a_ne_c_of_between{a b c: Point}(h: Between a b c): a ≠ c := by
    sorry

  theorem lies_on_mk_line_of_between{a b c: Point}{p}(h: Between a b c): b ∈ (mk_line a c p).val :=
  by
    sorry

  def between_exists[(l: G.Line)→(p: Point) → Decidable (p ∈ l)](a c: Point)(hne: a ≠ c): {b: Point // G.Between a b c} :=
    let ⟨l1, ha1, hc1⟩ := G.mk_line a c hne
    -- 根据公理I.7.2，直线外恒有一点E
    let ⟨e, he1⟩ := point_outside_line l1

    -- A必不等于E，否则E处在直线AC上
    have hae: a ≠ e := by
      intro h
      apply he1
      rw [← h]
      exact ha1

    -- 根据公理II.2.2，直线AE上有一点F，使E在线段AF内
    let ⟨f, hf1⟩ := G.extension_exists a e hae

    -- F必不等于C，否则F和E都将处在直线AC上
    have hfc: f ≠ c := by
      intro h
      apply he1
      have : l1 = G.mk_line a c hne := by
        apply G.unique_line_from_two_points
        exact ha1
        exact hc1
      rw [this]
      have haf: a ≠ f := by
        apply a_ne_c_of_between hf1
      subst h
      -- TODO: between a e f → e ∈ mk_line a f _ 可以作为一个单独的定理
      apply lies_on_mk_line_of_between
      exact hf1

    let ⟨c, hc1⟩ := G.extension_exists f c hfc
    sorry

  /-- Induce a 1D Hilbert axioms structure on points lying on a line in 2D plane. -/
  def onLine(l: G.Line):
    HilbertAxioms1D {p: Point // p ∈ l} := {
      Between := fun a b c => G.Between a.val b.val c.val,
      between_ne := by
        simp only [Subtype.forall, Subtype.mk.injEq]
        intro a ha b hb c hc h
        simp only [ne_eq, Subtype.mk.injEq]
        apply G.between_ne
        exact h
      between_symm := by
        simp only [Subtype.forall, Subtype.mk.injEq]
        intro a ha b hb c hc h
        apply G.between_symm
        exact h
      between_exists(a c h) :=
        let ⟨b, hb⟩ := between_exists a.val c.val (by rw [ne_eq, Subtype.mk.injEq] at h; exact h)
        have hb1 : b ∈ l := by
          have h:= G.collinear_of_between a.val b c.val hb
          rw [G.collinear_def] at h
          obtain ⟨l', h1, h2, h3⟩ := h
          rw [G.unique_line_from_two_points a.val c.val l]
          rw [← G.unique_line_from_two_points a.val c.val l']
          exact h2
          rw [ne_eq, Subtype.mk.injEq] at h; exact h
          exact h1
          exact h3
          exact a.property
          exact c.property
        ⟨⟨b, hb1⟩, hb⟩
      extension_exists(a' c')(hne: a' ≠ c') :=
        let ⟨a, ha⟩ := a'
        let ⟨c, hc⟩ := c'
        let ⟨d, hd⟩ := G.extension_exists a c (by simp only [ne_eq, Subtype.mk.injEq] at hne; exact hne)
        have hd1 : d ∈ l := by
          have h:= G.collinear_of_between a c d hd
          rw [G.collinear_def] at h
          simp only [ne_eq, Subtype.mk.injEq] at hne
          obtain ⟨l', h1, h2, h3⟩ := h
          have {h}: l = mk_line a c h := by
            apply G.unique_line_from_two_points a c l hne ha hc
          rw [this]
          have {h}: l' = mk_line a c h := by
            apply G.unique_line_from_two_points a c l' hne h1 h2
          rw [← this]
          exact h3
          exact hne
        ⟨⟨d, hd1⟩, hd⟩

      line_exists_two_points :=
        let ⟨⟨a, b⟩, ⟨h1, h2, h3⟩⟩ := G.line_exists_two_points l
        ⟨⟨⟨a, h2⟩, ⟨b, h3⟩⟩, by simp only [ne_eq, Subtype.mk.injEq]; exact h1⟩

      OnSegment_def := by
        intro a b c
        simp only [Subtype.eq_iff]
    }
end Geometry.HilbertAxioms2D

namespace Geometry.HilbertAxioms3D
  def not_collinear{Point: Type}[G:HilbertAxioms3D Point]{A B C: Point}(hne: A≠B):
    ¬ G.Collinear A B C ↔ ∃ l: G.Line, A ∈ l ∧ B ∈ l ∧ C ∉ l :=
  by
    rw [G.collinear_def]
    constructor
    . rw [not_exists]
      intro h
      let l := mk_line A B hne
      use l
      have h:=h l
      simp only [l.property, true_and] at h ⊢
      exact h
    . intro ⟨l, hA, hB, hC⟩
      intro ⟨l',hA',hB',hC'⟩
      have : l' = mk_line A B hne := by
        apply G.unique_line_from_two_points A B l' hne hA' hB'
      rw [this] at hC'
      have : l = mk_line A B hne := by
        apply G.unique_line_from_two_points A B l hne hA hB
      rw [← this] at hC'
      apply hC hC'

  theorem exists_point_not_on_line{Point: Type}[G:HilbertAxioms3D Point]
    (l: G.Line): ∃ p: Point, p ∉ l :=
  by
    let pl' := G.plane_exists.some
    let ⟨⟨A,B,C⟩, _,_,_,hne, hnc⟩ := G.exists_three_noncollinear_points pl'
    by_cases hA': A∈ l
    . by_cases hB': B ∈ l
      . have hne: A≠B := by
          simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil,
            and_self, and_true] at hne
          exact hne.1.1
        have hC': C ∉ l := by
          intro h
          apply hnc
          have : l = G.mk_line A B hne := by
            apply G.unique_line_from_two_points A B l hne hA' hB'
          rw [collinear_def]
          use l
        use C
      . use B
    . use A

  theorem coplannar_of_collinear{Point: Type}[G:HilbertAxioms3D Point]
    (l: G.Line)(D: Point): ∃ pl: G.Plane, l ⊆ pl ∧ D ∈ pl :=
  by
    let ⟨⟨P, Q⟩, hne, hP, hQ⟩  := G.line_exists_two_points l
    by_cases h2: D ∈ l
    . have ⟨R, hR⟩ := exists_point_not_on_line l
      have hPQR := (not_collinear hne).mpr (by use l)
      have ⟨pl, hPl⟩ := G.mk_plane P Q R hPQR
      use pl
      have : l ⊆ pl := by
        apply G.line_in_plane_if_two_points_in_plane
        exact hne
        exact hP
        exact hQ
        exact hPl.1
        exact hPl.2.1
      and_intros
      . exact this
      . apply this
        exact h2
    . let ⟨pl, hpl⟩ := G.mk_plane P Q D (by rw [not_collinear]; use l; apply hne)
      use pl
      simp only [hpl, and_true]
      apply G.line_in_plane_if_two_points_in_plane P Q l pl hne hP hQ hpl.1 hpl.2.1

  theorem noncollinear_of_noncoplanar{Point: Type}[G:HilbertAxioms3D Point]{A B C D: Point}:
     ¬(∃ pl: G.Plane, A ∈ pl ∧ B ∈ pl ∧ C ∈ pl ∧ D ∈ pl) →  ¬ Collinear A B C:=
  by
    contrapose
    rw [not_not, not_not]
    intro h
    rw [G.collinear_def] at h
    let ⟨l, h⟩ := h
    have ⟨pl, hl, hD⟩ := coplannar_of_collinear l D
    use pl
    simp only [hD, and_true]
    and_intros
    all_goals apply hl; simp only [h]


  def mk_plane_through_line{Point: Type}[G:HilbertAxioms3D Point](l: G.Line)[(p: Point) → Decidable (p ∈ l)]:
    {pl: G.Plane // l ⊆ pl} :=
      let ⟨⟨P,Q⟩, hne, hP, hQ⟩ := G.line_exists_two_points l
      let f1(A:Point)(hA: ¬A∈l):{pl: G.Plane // l ⊆ pl} :=
        have hPQA: ¬ Collinear P Q A := by
          apply (not_collinear hne).mpr
          use l
        let pl := G.mk_plane P Q A hPQA
        ⟨pl, by
          apply G.line_in_plane_if_two_points_in_plane P Q l pl hne hP hQ
          exact pl.property.1
          exact pl.property.2.1
        ⟩

      let ⟨⟨A, B, C, D⟩ , h1, h2⟩ := G.space_exists_four_noncoplanar_points
      if hA: A ∈ l then
        have hAB: A ≠ B := by
          simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil,
            and_self, and_true] at h1
          exact h1.1.1
        if hB: B ∈ l then
          have hl: l = mk_line A B hAB := by
            apply G.unique_line_from_two_points A B l hAB hA hB
          have hABC:= noncollinear_of_noncoplanar h2
          let pl := G.mk_plane A B C hABC
          ⟨pl, by
            apply G.line_in_plane_if_two_points_in_plane A B l pl hAB hA hB
            exact pl.property.1
            exact pl.property.2.1
          ⟩
        else
          f1 B hB
      else
        f1 A hA


  def mk_line_through_point_on_plane{Point: Type}[DecidableEq Point][G:HilbertAxioms3D Point]
      {pl: G.Plane}(p: Point)(h: p ∈ pl):
      {l: G.Line // l ⊆ pl ∧ p ∈ l} :=
    let ⟨⟨A, B, C⟩, h1, h2, h3, h4, h5⟩  := G.exists_three_noncollinear_points pl
    if hA : A = p then
      have hB: p ≠ B := by
        rw [← hA]
        simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil,
          and_self, and_true] at h4
        exact h4.1.1

      let ⟨l, hl⟩ := G.mk_line p B hB
      ⟨l, by
          and_intros
          . apply G.line_in_plane_if_two_points_in_plane p B l
            exact hB
            exact hl.1
            exact hl.2
            exact h
            simp only at h2; exact h2
          . exact hl.1
        ⟩
    else
      let ⟨l, hl⟩ := G.mk_line A p hA
      ⟨l, by
          and_intros
          . apply G.line_in_plane_if_two_points_in_plane A p l
            exact hA
            exact hl.1
            exact hl.2
            simp only at h1; exact h1
            exact h
          . exact hl.2
        ⟩

   /-- Induce a 2D Hilbert axioms structure on points lying on a plane in 3D space. -/
  def onPlane{Point: Type}[DecidableEq Point][G:HilbertAxioms3D Point](pl: G.Plane):
    HilbertAxioms2D {p: Point // p ∈ pl} := {
      Line: Type := {l: G.Line // l ⊆ pl},
      mem_Line := {
        mem(h1 h2) := h2.val ∈ h1.val
      },
      Between(a b c) := Between a.val b.val c.val,
      between_ne(a b c)(h) := by
        have h := G.between_ne a.val b.val c.val h
        rw [ne_eq, ←Subtype.eq_iff, ne_eq, ←Subtype.eq_iff, ← ne_eq, ← ne_eq] at h
        exact h
      between_symm(a b c h) := by
        apply G.between_symm
        exact h
      extension_exists(a c)(h) :=
        have ⟨d, hd⟩:= G.extension_exists a c (by rw [Subtype.coe_ne_coe]; exact h)

        have hd1 : d ∈ pl := by
          have h:= G.collinear_of_between a c d hd
          rw [G.collinear_def] at h
          obtain ⟨l, h1, h2, h3⟩ := h
          have hl: l ⊆ pl := by
            intro p hp
            apply G.line_in_plane_if_two_points_in_plane a c
            rw [Subtype.coe_ne_coe]; exact h
            exact h1
            exact h2
            exact a.property
            exact c.property
            exact hp
          apply hl
          exact h3
        ⟨⟨d, hd1⟩, hd⟩

      mk_line(a c h) :=
        let ⟨l, hl1, hl2⟩ := G.mk_line a.val c.val (by rw [Subtype.coe_ne_coe]; exact h)
        have : l ⊆ pl := by
          intro p hp
          apply G.line_in_plane_if_two_points_in_plane a.val c.val l
          rw [Subtype.coe_ne_coe]; exact h
          exact hl1
          exact hl2
          exact a.property
          exact c.property
          exact hp
        ⟨⟨l, this⟩, hl1, hl2⟩

      unique_line_from_two_points := by
        intros a b l hne ha hb
        have hne': a.val ≠ b.val := by rw [Subtype.coe_ne_coe]; exact hne
        rw [Subtype.eq_iff]
        rw [G.unique_line_from_two_points a.val b.val l.val hne' ha hb]
        let ⟨l', hl'⟩ := G.mk_line a.val b.val hne'
        split
        rename_i l'
        simp only
        simp [Subtype.eq_iff] at l'
        exact l'

      line_exists_two_points(l) :=
        let ⟨⟨a, b⟩, h1, h2, h3⟩ := G.line_exists_two_points l.val
        have ha: a ∈ pl := by
          apply l.property
          exact h2
        have hb: b ∈ pl := by
          apply l.property
          exact h3
        ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, by
          simp only [ne_eq, Subtype.mk.injEq, h1, not_false_eq_true, h2, h3, and_self]
        ⟩

      collinear_of_between := by
        intro a b c h
        have h1 := G.collinear_of_between a.val b.val c.val h
        rw [G.collinear_def] at h1
        rw [collinear_def]
        exact h1

      exists_three_noncollinear_points :=
        let ⟨⟨a, b, c⟩, h1, h2, h3, h4, h5⟩ := G.exists_three_noncollinear_points pl
        ⟨⟨⟨a, h1⟩, ⟨b, h2⟩, ⟨c, h3⟩⟩, by
            simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
              forall_eq_or_imp, Subtype.mk.injEq, forall_eq, IsEmpty.forall_iff, implies_true,
              List.Pairwise.nil, and_self, and_true] at h4 ⊢
            exact h4
        , h5⟩

      pasch_axiom{A B C}(h1 l h2) :=
        have t1: pl = G.mk_plane A B C h1 := by
          apply G.unique_plane_from_three_points A B C pl h1
          exact A.property
          exact B.property
          exact C.property
        have t2: l.val ⊆ (G.mk_plane A B C h1).val := by
          rw [← t1]
          exact l.property
        have t3: (∃ P, G.OnSegment A P B ∧ P ∈ l.val) := by
          let ⟨P, hP1, hP2⟩ := h2
          use P
          and_intros
          . simp only at hP1
            rw [G.OnSegment_def]
            rw [Subtype.eq_iff, Subtype.eq_iff] at hP1
            exact hP1
          . exact hP2

        let ⟨Q, hQ⟩ := G.pasch_axiom h1 l.val t2 t3
        have hQ1: Q∈ pl := by
          apply l.property
          exact hQ.2

        ⟨⟨Q, hQ1⟩, by
            repeat rw [G.OnSegment_def] at hQ
            simp only [Subtype.eq_iff];
            exact hQ
        ⟩

      collinear_def := by
        intro a b c
        simp only [G.collinear_def, Subtype.exists, exists_and_left, exists_prop]
        constructor
        . intro ⟨l, h1, h2, h3⟩

          by_cases h: a = c
          . by_cases h': a = b
            . -- case: a=b=c, choose any line through a on plane pl
              let ⟨l, h1, h2⟩ := mk_line_through_point_on_plane a.val a.property
              use l
              simp only [h2, ← h', ← h, and_true, true_and]
              exact h1
            . use l
              simp only [h1, h2, h3, and_true, true_and]
              apply G.line_in_plane_if_two_points_in_plane a.val b.val l
              rw [Subtype.coe_ne_coe]; exact h'
              exact h1
              exact h2
              exact a.property
              exact b.property
          .
            use l
            simp only [h1, h2, h3, and_true, true_and]
            apply G.line_in_plane_if_two_points_in_plane a.val c.val l
            rw [Subtype.coe_ne_coe]; exact h
            exact h1
            exact h3
            exact a.property
            exact c.property

        . intro ⟨l, h1, h2, h3, h4⟩
          use l

      OnSegment_def(a b c) := by
        simp only [OnSegment]
    }

  /-- Induce a 1D Hilbert axioms structure on points lying on a line in 3D space. -/
  def onLine{Point: Type}[DecidableEq Point][G:HilbertAxioms3D Point](l: G.Line)[(p: Point) → Decidable (p ∈ l)]:
    HilbertAxioms1D {p: Point // p ∈ l} :=
      let SubPointType := {p: Point // p ∈ l}
      let pl := mk_plane_through_line l
      let l': {l': G.Line // l' ⊆ pl.val} := ⟨l, pl.property⟩
      let G' := (onPlane pl.val).onLine l'
      let e1 : {p // p ∈ l} ≃ {p: {p // p ∈ pl.val} // p ∈ l'} :=
        { toFun := fun x =>
            have h1: x.val ∈ pl.val := by
              have h:= pl.property
              exact h x.val x.property
            have h2 {p}: ⟨x, p⟩ ∈ l' := by
              simp only [Membership.mem, l']
              exact x.property
            ⟨⟨x.val, h1⟩, h2⟩
          invFun := fun x =>
            have h: x.val.val ∈ l := by
              exact x.property
            ⟨x.val, h⟩
          left_inv := by intro x; ext; rfl
          right_inv := by intro x; ext; rfl }
      HilbertAxioms1D.transfer e1 G'

end Geometry.HilbertAxioms3D
