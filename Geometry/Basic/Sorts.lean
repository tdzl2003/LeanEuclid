import Geometry.Basic.Point

namespace Geometry
  structure Segment(Point: Type)[G: PointOrder Point] where
    p1: Point
    p2: Point

  def Segment.valid {Point: Type}[G: PointOrder Point](s: Segment Point): Prop :=
    s.p1 ≠ s.p2

  instance {Point: Type}[G: PointOrder Point]: Membership Point (Segment Point) where
      mem (s: Segment Point) (p: Point) : Prop := G.Between s.p1 p s.p2

  structure RayRaw(Point: Type)[G: PointOrderExt Point] where
    start: Point
    p: Point

  namespace RayRaw
    def Equiv {Point}[G: PointOrderExt Point](l₁ l₂: RayRaw Point): Prop
      := l₁.start = l₂.start ∧ (
        l₁.p = l₂.p ∨
        G.Between l₁.start l₁.p l₂.p ∨
        G.Between l₁.start l₂.p l₁.p
      )

    theorem equiv_refl{Point}[G: PointOrderExt Point](l: RayRaw Point): Equiv l l :=
    by
      unfold Equiv
      simp only [or_self, true_or, and_self]

    theorem equiv_symm{Point}[G: PointOrderExt Point]{l₁ l₂: RayRaw Point}:
      Equiv l₁ l₂ →  Equiv l₂ l₁ :=
    by
      intro ⟨h1, h2⟩
      and_intros ; apply Eq.symm h1
      rcases h2 with h2|h2|h2
      . apply Or.inl
        apply Eq.symm
        exact h2
      . apply Or.inr
        apply Or.inr
        rw [← h1]
        exact h2
      . apply Or.inr
        apply Or.inl
        rw [← h1]
        exact h2

    theorem equiv_trans{Point}[G: PointOrderExt Point]{l₁ l₂ l₃: RayRaw Point} :
      Equiv l₁ l₂ →  Equiv l₂ l₃ → Equiv l₁ l₃ :=
    by
      intro ⟨h1, h2⟩ ⟨h3, h4⟩
      and_intros
      . rw [h1]
        exact h3

      rcases h2 with h2|h2|h2
      . rw [h2, h1]
        exact h4
      . rcases h4 with h4|h4|h4
        . rw [← h4]
          apply Or.inr
          apply Or.inl
          exact h2
        . apply Or.inr
          apply Or.inl
          rw [← h1] at h4
          have h:= G.between_trans' h2 h4
          exact h.1
        . rw [← h1] at h4
          apply between_trans_m
          . exact h2
          . exact h4
      . rcases h4 with h4|h4|h4
        . rw [← h4]
          apply Or.inr
          apply Or.inr
          exact h2
        . rw [← h1] at h4
          apply between_trans_m'
          . exact h2
          . exact h4
        . rw [← h1] at h4
          have h:= G.between_trans' h4 h2
          apply Or.inr
          apply Or.inr
          exact h.1

    instance setoid(Point)[G: PointOrderExt Point] : Setoid (RayRaw Point) where
      r := Equiv
      iseqv := ⟨equiv_refl, equiv_symm, equiv_trans⟩
  end RayRaw

  def Ray{Point}[G: PointOrderExt Point] := Quotient (RayRaw.setoid Point)


end Geometry
