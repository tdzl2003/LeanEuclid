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

    /--
      axiom II.3.2 Of any three points situated on a straight line, there is at most one
      which lies between the other two.
      我们通过右交换为否来表达此公理，通过between_symm可以得到需要的其它结论
    -/
    between_not_symm_right{a b c : Point}: Between a b c → ¬ Between a c b

  /-- collection of axioms which can be proved in 2D or above but cannot in 1D. --/
  class PointOrderExt (Point: Type) extends PointOrder Point where
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

  section
    variable {Point: Type}[G:PointOrder Point]
    theorem between_symm_iff{a b c: Point}:
      G.Between a b c ↔ G.Between c b a :=
    by
      constructor
      all_goals apply G.between_symm

  end
end Geometry
