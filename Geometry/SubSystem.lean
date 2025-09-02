import Geometry.Basic
import Mathlib.Tactic.Use
import Mathlib.Logic.Equiv.Defs

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
  }

end Geometry.HilbertAxioms1D


namespace Geometry.HilbertAxioms2D
  variable {Point: Type}[G: HilbertAxioms2D Point]

  def between_exists(a b c: Point)(h: a ≠ c): {d: Point // G.Between a d c} :=
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
      between_exists := by
        sorry
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
    }
end Geometry.HilbertAxioms2D

namespace Geometry.HilbertAxioms3D
   /-- Induce a 2D Hilbert axioms structure on points lying on a plane in 3D space. -/
  def onPlane{Point: Type}[G:HilbertAxioms3D Point](pl: G.Plane):
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

        sorry

      line_exists_two_points := by
        sorry,
      collinear_of_between := by
        sorry,
      exists_three_noncollinear_points :=
        sorry,
      pasch_axiom := by
        sorry,
      collinear_def := by
        sorry
    }

  def mk_plane_through_line{Point: Type}[G:HilbertAxioms3D Point](l: G.Line):{pl: G.Plane // l ⊆ pl} :=
    sorry

  /-- Induce a 1D Hilbert axioms structure on points lying on a line in 3D space. -/
  def onLine{Point: Type}[G:HilbertAxioms3D Point](l: G.Line):
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
