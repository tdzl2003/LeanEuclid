import Geometry.Basic
import Mathlib.Tactic.ByContra



namespace Geometry.HilbertGeometry2D

  section
    variable {Point: Type}[HilbertGeometry2D Point]

    /-- axiom II.2.1 If A and C are two points of a straight line, then there exists at least one point B lying Between A and C-/
    theorem HilbertGeometry2D.between_exists(a c: Point): a ≠ c → ∃ b: Point, Between a b c := by
      sorry

    /-- axiom II.3 Of any three points situated on a straight line, there is always one and only one which lies Between the other two. -/
    theorem HilbertGeometry2D.between_trichotomy(a b c: Point): Collinear a b c → a ≠ b → b ≠ c → a ≠ c →
      (Between a b c ∨ Between b a c ∨ Between a c b) ∧
      ¬(Between a b c ∧ Between b a c) ∧
      ¬(Between a b c ∧ Between a c b) ∧
      ¬(Between b a c ∧ Between a c b) := by
        sorry

  end

end Geometry.HilbertGeometry2D
