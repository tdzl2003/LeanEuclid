import Geometry.Basic.Point

namespace Geometry


  class HilbertAxioms1D (Point: Type) extends
    PointOrderExt Point where

    /-- axiom I.8: There exist at least two points on a line. -/
    line_exists_two_points: {s: Point × Point // s.1 ≠ s.2}

    /--
      axiom II.3.1 Of any three points situated on a straight line, there is always one
      which lies between the other two.
    --/
    between_trichotomy{a b c: Point}: a ≠ b → b ≠ c → a ≠ c →
      (Between a b c ∨ Between b a c ∨ Between a c b)


  namespace HilbertAxioms1D
    theorem between_trans_m{Point}[G: HilbertAxioms1D Point] {A B C D: Point}:
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

      have h := G.between_trichotomy hab hbc hac
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

    theorem between_trans_m'{Point}[G: HilbertAxioms1D Point] {A B C D: Point}:
      G.Between A B C → G.Between A B D →
        C = D ∨ G.Between A C D ∨ G.Between A D C :=
    by
      intro h1 h2
      by_cases hcd: C = D
      . exact Or.inl hcd
      apply Or.inr
      have hac : A ≠ C := by
        apply (G.between_ne h1).select' 0 2
        all_goals norm_num
      have had : A ≠ D := by
        apply (G.between_ne h2).select' 0 2
        all_goals norm_num

      have h := G.between_trichotomy hac hcd had
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
  end HilbertAxioms1D
end Geometry
