import Geometry.Basic.Distinct
import Mathlib.Tactic.NormNum

namespace Geometry
  class PointDef(Point: Type) where
    instDecidableEq: DecidableEq Point

  attribute [instance] PointDef.instDecidableEq

  /-- collection of axioms about point orders -/
  class PointOrder (Point: Type) extends PointDef Point where
    /-- Between : b is Between a and c (exclusive) -/
    Between(a b c: Point): Prop

    /-- Between relation is exclusive. -/
    between_ne{a b c: Point}: Between a b c → [a,b,c].Distinct

    /--
      axiom II.1: If A, B, C are points of a straight line and B lies Between A and C, then B lies also Between C and A.
    -/
    between_symm{a b c: Point}: Between a b c → Between c b a

    /--
      axiom II.2.2 If A and C are two points of a straight line, there exists at least one point D so situated that C lies Between A and D.
      Additional constraints: D ≠ A
    -/
    extension_exists{a c: Point}: a ≠ c → {d: Point // Between a c d}

  /-- collection of axioms which can be proved in 2D or above but cannot in 1D. --/
  class PointOrderExt (Point: Type) extends PointOrder Point where
    between_not_symm_right{a b c : Point}: Between a b c → ¬ Between a c b

    between_trichotomy(a b c: Point): a ≠ b → b ≠ c → a ≠ c →
      (Between a b c ∨ Between b a c ∨ Between a c b)

    /--
      axiom II.2.1 If A and C are two points of a straight line, there exists at least one point B lying between A and C.
      This can be proved in 2D but is axiom for 1D.
    -/
    between_exists{a c: Point}: a ≠ c → {b: Point // Between a b c}

    /--
      If B is between A and C, and C is between B and D, then B is also between A and C, and C is also between A and D.
    -/
    between_trans {A B C D : Point} :
      Between A B C → Between B C D → Between A B D ∧ Between A C D

    /--
      If B is between A and C, and C is between A and D, then B is also between A and D, and C is also between B and D.
    -/
    between_trans' {A B C D : Point} :
      Between A B C → Between A C D → Between A B D ∧ Between B C D

  theorem between_trans_m{Point}[G: PointOrderExt Point] {A B C D: Point}:
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

    have h := G.between_trichotomy A B C hab hbc hac
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

  theorem between_trans_m'{Point}[G: PointOrderExt Point] {A B C D: Point}:
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

    have h := G.between_trichotomy A C D hac hcd had
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

end Geometry
