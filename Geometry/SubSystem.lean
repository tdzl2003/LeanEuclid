import Geometry.Basic
import Geometry.Connections
import Geometry.Order
import Mathlib.Tactic.Use
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.DefEqTransformations
import Mathlib.Tactic.Contrapose

namespace Geometry.HilbertAxioms1D
  def transfer {Point1 Point2 : Type} (e : Point2 ≃ Point1) (h1 : HilbertAxioms1D Point1) : HilbertAxioms1D Point2 :=
  {
    instDecidableEq(a b) :=
      let v := h1.instDecidableEq (e a) (e b)
      match v with
      | isFalse h => Decidable.isFalse (by rw [Equiv.apply_eq_iff_eq] at h;exact h)
      | isTrue h => Decidable.isTrue (by rw [Equiv.apply_eq_iff_eq] at h;exact h)
    Between := fun a b c => h1.Between (e a) (e b) (e c)
    between_ne := by
      intro a b c h
      have h' := h1.between_ne h
      rw [show [e a, e b, e c] = ([a, b, c].map (fun v ↦ e v)) by simp only [List.map_cons,
        List.map_nil]] at h'
      rw [List.pairwise_map] at h'
      apply List.Pairwise.imp _ h'
      intro a b
      simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, imp_self]
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
      let ⟨c, hc⟩ := h1.between_exists this
      exact ⟨e.symm c, by simp only [Equiv.apply_symm_apply]; exact hc⟩
    extension_exists{a c}(hne) :=
      let a1 := e a
      let c1 := e c
      have hne1 : a1 ≠ c1 := by
        intro heq
        apply hne
        apply e.injective
        exact heq
      let ⟨b1, hb2⟩ := h1.extension_exists hne1
      let b := e.symm b1

      ⟨b, by
        rw [show e b = b1 by simp only [Equiv.apply_symm_apply, b]]
        exact hb2
      ⟩
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

  /-- Induce a 1D Hilbert axioms structure on points lying on a line in 2D plane. -/
  def onLine(l: G.Line):
    HilbertAxioms1D {p: Point // p ∈ l} := {
      instDecidableEq(a b) :=
        let v := G.instDecidableEq (a.val) (b.val)
        match v with
        | isFalse h => Decidable.isFalse (by rw [Subtype.mk_eq_mk];exact h)
        | isTrue h => Decidable.isTrue (by rw [Subtype.mk_eq_mk];exact h)

      Between := fun a b c => G.Between a.val b.val c.val,
      between_ne := by
        intro ⟨a,ha⟩ ⟨b,hb⟩  ⟨c,hc⟩ h
        simp only at h
        have h := G.between_ne h
        apply List.Pairwise.of_map (fun (a: {p: Point // p ∈ l})  ↦ a.val) _ h
        intro a b
        simp only [ne_eq]
        rw [Subtype.mk_eq_mk]
        simp only [imp_self]

      between_symm := by
        simp only [Subtype.forall, Subtype.mk.injEq]
        intro a ha b hb c hc h
        apply G.between_symm
        exact h
      between_exists{a' c'}(hne') :=
        let ⟨a, ha⟩ := a'
        let ⟨c, hc⟩ := c'
        have hne : a ≠ c := by simp only [ne_eq, Subtype.mk.injEq] at hne'; exact hne'

        let ⟨b, hb⟩ := between_exists hne
        have hb1 : b ∈ l := by
          have h:= G.collinear_of_between hb
          rw [G.collinear_def] at h
          obtain ⟨l', h1, h2, h3⟩ := h
          rw [G.unique_line_from_two_points hne ha hc]
          rw [← G.unique_line_from_two_points hne h1 h3]
          exact h2
        ⟨⟨b, hb1⟩, hb⟩
      extension_exists{a' c'}(hne': a' ≠ c') :=
        let ⟨a, ha⟩ := a'
        let ⟨c, hc⟩ := c'
        have hne : a ≠ c := by simp only [ne_eq, Subtype.mk.injEq] at hne'; exact hne'

        let ⟨d, hd⟩ := G.extension_exists hne
        have hd1 : d ∈ l := by
          have h:= G.collinear_of_between hd
          rw [G.collinear_def] at h
          obtain ⟨l', h1, h2, h3⟩ := h
          rw [G.unique_line_from_two_points hne ha hc]
          rw [← G.unique_line_from_two_points hne h1 h2]
          exact h3
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
      let l := mk_line hne
      use l
      have h:=h l
      simp only [l.property, true_and] at h ⊢
      exact h
    . intro ⟨l, hA, hB, hC⟩
      intro ⟨l',hA',hB',hC'⟩
      rw [G.unique_line_from_two_points hne hA' hB'] at hC'
      rw [← G.unique_line_from_two_points hne hA hB] at hC'
      apply hC hC'

  theorem exists_point_not_on_line{Point: Type}[G:HilbertAxioms3D Point]
    (l: G.Line): ∃ p: Point, p ∉ l :=
  by
    let pl' := G.instPlaneNonEmpty.some
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
          have : l = G.mk_line hne := by
            apply G.unique_line_from_two_points hne hA' hB'
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
      have ⟨pl, hPl⟩ := G.mk_plane hPQR
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
    . have hnc: ¬ Collinear P Q D := by rw [not_collinear]; use l; apply hne
      let ⟨pl, hpl⟩ := G.mk_plane hnc
      use pl
      simp only [hpl, and_true]
      apply G.line_in_plane_if_two_points_in_plane hne hP hQ hpl.1 hpl.2.1

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
        let pl := G.mk_plane hPQA
        ⟨pl, by
          apply G.line_in_plane_if_two_points_in_plane hne hP hQ
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
          have hl: l = mk_line hAB := by
            apply G.unique_line_from_two_points hAB hA hB
          have hABC:= noncollinear_of_noncoplanar h2
          let pl := G.mk_plane hABC
          ⟨pl, by
            apply G.line_in_plane_if_two_points_in_plane hAB hA hB
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

      let ⟨l, hl⟩ := G.mk_line hB
      ⟨l, by
          and_intros
          . apply G.line_in_plane_if_two_points_in_plane hB
            exact hl.1
            exact hl.2
            exact h
            exact h2
          . exact hl.1
        ⟩
    else
      let ⟨l, hl⟩ := G.mk_line hA
      ⟨l, by
          and_intros
          . apply G.line_in_plane_if_two_points_in_plane hA
            exact hl.1
            exact hl.2
            exact h1
            exact h
          . exact hl.2
        ⟩

   /-- Induce a 2D Hilbert axioms structure on points lying on a plane in 3D space. -/
  def onPlane{Point: Type}[DecidableEq Point][G:HilbertAxioms3D Point](pl: G.Plane):
    HilbertAxioms2D {p: Point // p ∈ pl} :=
    let SubPoint := {p: Point // p ∈ pl}
    let SubLine := {l: G.Line // l ⊆ pl}

    {
      instDecidableEq(a b) :=
        let v := G.instDecidableEq (a.val) (b.val)
        match v with
        | isFalse h => Decidable.isFalse (by rw [Subtype.mk_eq_mk];exact h)
        | isTrue h => Decidable.isTrue (by rw [Subtype.mk_eq_mk];exact h)

      Line: Type := SubLine,
      instMemLine := {
        mem(h1 h2) := h2.val ∈ h1.val
      },
      instDecidableMemLine(l p) :=
        let v := G.instDecidableMemLine (l.val) (p.val)
        match v with
        | isFalse h => Decidable.isFalse h
        | isTrue h => Decidable.isTrue h


      Between(a b c) := Between a.val b.val c.val,
      between_ne{a b c}(h) := by
        have h := G.between_ne h
        apply List.Pairwise.of_map (fun (a: SubPoint)  ↦ a.val) _ h
        intro a b
        simp only [ne_eq]
        rw [Subtype.mk_eq_mk]
        simp only [imp_self]
      between_symm{a b c}(h) := by
        apply G.between_symm
        exact h
      extension_exists{a c}(h) :=
        have ⟨d, hd⟩:= G.extension_exists (by rw [Subtype.coe_ne_coe]; exact h)

        have hd1 : d ∈ pl := by
          have h:= G.collinear_of_between hd
          rw [G.collinear_def] at h
          obtain ⟨l, h1, h2, h3⟩ := h
          have hl: l ⊆ pl := by
            intro p hp
            apply G.line_in_plane_if_two_points_in_plane
            rw [Subtype.coe_ne_coe]; exact h
            exact h1
            exact h2
            exact a.property
            exact c.property
            exact hp
          apply hl
          exact h3
        ⟨⟨d, hd1⟩, hd⟩

      Collinear(a b c) := ∃ l : SubLine, a ∈ l ∧ b ∈ l ∧ c ∈ l

      collinear_def{a b c} := by
        rfl

      OnSegment_def{a b c} := by
        simp only [OnSegment]

      mk_line{a c}(h) :=
        let ⟨l, hl1, hl2⟩ := G.mk_line (by rw [Subtype.coe_ne_coe]; exact h)
        have : l ⊆ pl := by
          intro p hp
          apply G.line_in_plane_if_two_points_in_plane
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
        rw [G.unique_line_from_two_points hne' ha hb]
        let ⟨l', hl'⟩ := G.mk_line hne'
        split
        rename_i l'
        simp only
        rw [Subtype.eq_iff] at l'
        exact l'

      mk_line_intersection{l1' l2'}(hne' h') :=
        let ⟨l1, hl1⟩ := l1'
        let ⟨l2, hl2⟩ := l2'
        have hne: l1 ≠ l2 := by rw [ne_eq, Subtype.mk_eq_mk] at hne'; exact hne'
        let ⟨p, hp⟩:= G.mk_line_intersection hne (by let ⟨p, hp⟩:= h'; use p; simp only at hp; exact hp)
        ⟨⟨p, by apply hl1; exact hp.1⟩, hp⟩

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
        have h1 := G.collinear_of_between h
        rw [G.collinear_def] at h1
        let ⟨l, ha, hb, hc⟩ := h1
        have hne : a.val ≠ b.val := by
          have hne := G.between_ne h
          rw [List.pairwise_iff_getElem] at hne
          specialize hne 0 1 (by norm_num) (by norm_num) (by decide)
          exact hne

        have : l ⊆ pl := by
          apply G.line_in_plane_if_two_points_in_plane hne
          exact ha
          exact hb
          exact a.property
          exact b.property

        use ⟨l, this⟩
        simp only [Membership.mem]
        simp only [ha, hb, hc, and_self]

      exists_three_noncollinear_points :=
        let ⟨⟨a, b, c⟩, h1, h2, h3, h4, h5⟩ := G.exists_three_noncollinear_points pl
        ⟨⟨⟨a, h1⟩, ⟨b, h2⟩, ⟨c, h3⟩⟩, by
            apply List.Pairwise.of_map (fun (a: {p: Point // p ∈ pl})  ↦ a.val) _ h4
            intro a b
            simp only [ne_eq]
            rw [Subtype.mk_eq_mk]
            simp only [imp_self]
        , by
            simp only [G.collinear_def, not_exists] at h5
            simp only [Subtype.exists, not_exists]
            intro x
            apply h5
        ⟩

      pasch_axiom{A' B' C'}{l'}(h1 h2) :=
        let ⟨A, hA⟩ := A'
        let ⟨B, hB⟩ := B'
        let ⟨C, hC⟩ := C'
        let ⟨l, hl⟩ := l'

        have hne: A ≠ B := by
          intro hE

          by_cases t1: A = C
          . have t2: ∀ D, A ≠ D → D ∈ pl → False := by
              intro D had hD
              let ⟨l, hAl, hDl⟩  := G.mk_line had
              have : l ⊆ pl := by
                apply G.line_in_plane_if_two_points_in_plane had
                exact hAl
                exact hDl
                exact hA
                exact hD
              apply h1
              use ⟨l, this⟩
              simp only [Membership.mem]
              and_intros
              . exact hAl
              . rw [← hE]; exact hAl
              . rw [← t1]; exact hAl

            let ⟨⟨D, E, F⟩ , ⟨hD, hE, hF, hne, hnc⟩⟩  := G.exists_three_noncollinear_points pl
            by_cases t3: A = D
            . have : D ≠ E := by
                rw [List.pairwise_iff_getElem] at hne
                specialize hne 0 1 (by norm_num) (by norm_num) (by decide)
                exact hne
              apply t2 E
              . rw [t3]
                exact this
              . exact hE
            . apply t2 D
              . exact t3
              . exact hD
          .
            let ⟨l, hAl, hCl⟩  := G.mk_line t1
            have : l ⊆ pl := by
              apply G.line_in_plane_if_two_points_in_plane t1
              exact hAl
              exact hCl
              exact hA
              exact hC
            apply h1
            use ⟨l, this⟩
            simp only [Membership.mem]
            and_intros
            . exact hAl
            . rw [← hE]; exact hAl
            . exact hCl

        have t4: ¬G.Collinear A B C := by
          rw [G.collinear_def, not_exists]
          simp only [Membership.mem, not_exists]  at h1
          intro l ⟨hA1, hB1, hC1⟩
          have : l ⊆ pl := by
            apply G.line_in_plane_if_two_points_in_plane hne
            exact hA1
            exact hB1
            exact hA
            exact hB
          apply h1 ⟨l, this⟩
          and_intros
          exact hA1
          exact hB1
          exact hC1

        have t1: pl = G.mk_plane t4 := by
          apply G.unique_plane_from_three_points t4
          exact hA
          exact hB
          exact hC
        have t2: l ⊆ (G.mk_plane t4).val := by
          rw [← t1]
          exact hl
        have t3: (∃ P, G.OnSegment A P B ∧ P ∈ l) := by
          let ⟨P, hP1, hP2⟩ := h2
          use P
          and_intros
          . simp only at hP1
            rw [G.OnSegment_def]
            rw [Subtype.eq_iff, Subtype.eq_iff] at hP1
            exact hP1
          . exact hP2

        let ⟨Q, hQ⟩ := G.pasch_axiom t4 t2 t3

        have hQ1: Q ∈ pl := by
          apply hl
          exact hQ.2

        ⟨⟨Q, hQ1⟩, by
            repeat rw [G.OnSegment_def] at hQ
            simp only [Subtype.eq_iff]
            exact hQ
        ⟩

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
