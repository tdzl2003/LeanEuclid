import Geometry.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

namespace Geometry
  variable {Point: Type}[G: LineConnection Point]
  /--
    theorem II.4: Any four points A, B, C, D of a straight line can always be so arranged that B
    shall lie between A and C and also between A and D, and, furthermore, that C shall
    lie between A and D and also between B and D.
  -/
  theorem four_points_ordering{a b c d : Point}:
      [a, b, c, d].Distinct → ∃ l: G.Line, a∈l ∧ b∈l ∧ c∈l ∧ d∈l →
      ∃ (a' b' c' d' : Point),
        ({a', b', c', d'}: Set Point) =  {a,b,c,d} ∧
        (G.Between a' b' c' ∧ G.Between a' b' d' ∧ G.Between a' c' d' ∧ G.Between b' c' d') :=
  by
    sorry

  /--
    Theorem 3. Between any two points of a straight line, there always exists an
    unlimited number of points.
  -/
  theorem infinite_points_between (A B : Point) (hNe : A ≠ B) :
      ∀ (F : Finset Point), ∃ (P : Point), G.Between A P B ∧ P ∉ F :=
  by
    sorry

  /-- Definition of a linearly ordered list where for any three indices i < j < k,
    the point at j is between the points at i and k. -/
  def LinearOrderedPointList (L : List Point) : Prop :=
    ∀ (i j k : Fin L.length), i.val < j.val → j.val < k.val → G.Between (L.get i) (L.get j) (L.get k)

  /-- Theorem 4.1 : For any finite set of points on a straight line, there exists a linearly ordered list
      of these points, and only two such lists exist (the forward and reverse order). -/
  theorem linear_ordering_of_collinear_points(S : Finset Point) :
      ∃ (L : List Point),
        L.toFinset = S ∧
        List.Nodup L ∧
        LinearOrderedPointList L :=
  by
    admit

  /-- Theorem 4.2 reverse order is also LinearOrderedPointList -/
  theorem linear_ordering_reverse(L: List Point):
      LinearOrderedPointList L →
      LinearOrderedPointList (L.reverse) :=
  by
    sorry

end Geometry

namespace Geometry

  section
    variable {Point: Type}[G: LineConnection Point]

    /-- two point is on same side of a line. -/
    def SameSideOfLine(l: G.Line)(a b: Point): Prop :=
      ¬ a ∈ l ∧ ¬ b ∈ l ∧ ¬(∃ c: Point, G.Between a c b ∧ c ∈ l)

    /-- two point is on different side of a line. -/
    def OtherSideOfLine(l: G.Line)(a b: Point): Prop :=
      ¬ a ∈ l ∧ ¬ b ∈ l ∧ ∃ c: Point, G.Between a c b ∧ c ∈ l

    theorem onSameSide.not_liesOn(l: G.Line)(a b: Point):
        SameSideOfLine l a b → ¬ a ∈ l ∧ ¬ b ∈ l :=
    by
      sorry

    theorem onOtherSide.not_liesOn(l: G.Line)(a b: Point):
        OtherSideOfLine l a b → ¬ a ∈ l ∧ ¬ b ∈  l :=
    by
      sorry

    theorem onSameSide.not_onOtherSide(l: G.Line)(a b: Point):
        SameSideOfLine l a b → ¬ OtherSideOfLine l a b :=
    by
      sorry

    theorem onOtherSide.not_onSameSide(l: G.Line)(a b: Point):
        OtherSideOfLine l a b → ¬ SameSideOfLine l a b :=
    by
      sorry

    theorem onSameSide.not (l: G.Line)(a b: Point):
        ¬ SameSideOfLine l a b → a ∈ l ∨ b ∈ l ∨ OtherSideOfLine l a b:=
    by
      sorry

    theorem onOtherSide.not (l: G.Line)(a b: Point):
        ¬ OtherSideOfLine l a b → a ∈ l ∨ b ∈ l ∨ SameSideOfLine l a b :=
    by
      sorry

    theorem onSameSide.reflex (l: G.Line)(a: Point):
        SameSideOfLine l a a :=
    by
      sorry

    theorem onOtherSide.not_reflex(l: G.Line)(a: Point):
        ¬ OtherSideOfLine l a a :=
    by
      sorry

    theorem onSameSide.symm(l: G.Line)(a b: Point):
        SameSideOfLine l a b → SameSideOfLine l b a :=
    by
      sorry

    theorem onOtherSide.symm(l: G.Line)(a b: Point):
        OtherSideOfLine l a b → OtherSideOfLine l b a :=
    by
      sorry

    theorem onSameSide.trans(l: G.Line)(a b c: Point):
        SameSideOfLine l a b → SameSideOfLine l b c → SameSideOfLine l a c :=
    by
      sorry

    theorem onOtherSide.trans(a b c: Point)(h: a ≠ b)(l: G.Line):
        OtherSideOfLine l a b → OtherSideOfLine l b c → SameSideOfLine l a c :=
    by
      sorry

  end
end Geometry
