import Geometry.Basic
import Mathlib.Tactic.ByContra

namespace HilbertGeometry2D
  variable {Point Line: Type}[HilbertGeometry2D Point Line]

  /-- axiom II.2.1 If A and C are two points of a straight line, then there exists at least one point B lying Between A and C-/
  theorem between_exists(a c: Point): a ≠ c → ∃ b: Point, Between a b c := by
    sorry

  /-- axiom II.3 Of any three points situated on a straight line, there is always one and only one which lies Between the other two. -/
  theorem between_trichotomy(a b c: Point): Collinear Line a b c → a ≠ b → b ≠ c → a ≠ c →
    (Between a b c ∨ Between b a c ∨ Between a c b) ∧
    ¬(Between a b c ∧ Between b a c) ∧
    ¬(Between a b c ∧ Between a c b) ∧
    ¬(Between b a c ∧ Between a c b) := by
      sorry

end HilbertGeometry2D
