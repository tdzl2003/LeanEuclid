import Geometry.Basic.Point

namespace Geometry

  class LineDef(Point: Type) where
    Line: Type
    instMemLine: Membership Point Line
    instDecidableMemLine: (l: Line)→(p: Point) → Decidable (p ∈ l)

  attribute [instance] LineDef.instMemLine
  attribute [instance] LineDef.instMemLine
  attribute [instance] LineDef.instDecidableMemLine

  def Collinear{Point}[G:LineDef Point](a b c: Point):Prop :=
      ∃ l:G.Line, a ∈ l ∧ b ∈ l ∧ c ∈ l

  class LineConnection(Point: Type) extends PointOrder Point, LineDef Point where
    /-- axiom I.1: Two distinct points A and B always completely determine a straight line a. --/
    mk_line{a b: Point}(h: a ≠ b): {l: Line // a ∈ l ∧ b ∈ l}

    /-- axiom I.2: Any two distinct points of a straight line completely determine that line; that is, if AB = a and AC = a, where B ̸= C, then is also BC = a. -/
    unique_line_from_two_points{a b: Point}{l: Line}(h:  a ≠ b) : a ∈ l → b ∈ l → l = mk_line h

    /-- construction axiom: If there's two line with common point, we can construct it. -/
    mk_line_intersection{l1 l2: Line}(hne: l1 ≠ l2)(e: ∃ p, p∈l1 ∧ p ∈ l2) : {p: Point // p ∈ l1 ∧ p ∈ l2}

    /-- axiom I.8: There exist at least two points on a line. -/
    line_exists_two_points(l: Line): {s: Point × Point // s.1 ≠ s.2 ∧ s.1 ∈ l ∧ s.2 ∈ l}

    /-- If B is between A and C, then A, B, C are collinear. -/
    collinear_of_between{a b c: Point}: Between a b c → Collinear a b c


end Geometry
