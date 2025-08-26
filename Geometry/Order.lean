import Geometry.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

namespace Geometry
  open HilbertAxiomsP HilbertAxiomsPL

  variable {Point: Type}[HilbertAxiomsP Point]

  /-- theorem II.2.1 If A and C are two points of a straight line, then there exists at least one point B lying Between A and C-/
  theorem between_exists(a c: Point): a ≠ c → ∃ b: Point, Between a b c := by
    sorry

  /-- theorem II.3 Of any three points situated on a straight line, there is always one and only one which lies Between the other two. -/
  theorem between_trichotomy(Line: Type)[HilbertAxiomsPL Point Line](a b c: Point): Collinear Line a b c → a ≠ b → b ≠ c → a ≠ c →
      (Between a b c ∨ Between b a c ∨ Between a c b) ∧
      ¬(Between a b c ∧ Between b a c) ∧
      ¬(Between a b c ∧ Between a c b) ∧
      ¬(Between b a c ∧ Between a c b) := by
    sorry

  /--
    If B is between A and C, and C is between B and D, then B is also between A and D, and C is also between A and D.
  -/
  theorem between_transitivity {A B C D : Point} :
      Between A B C → Between B C D → Between A B D ∧ Between A C D := by
    sorry

  /--
    If B is between A and C, and C is between A and D, then B is also between A and D, and C is also between B and D.
  -/
  theorem between_transitivity' {A B C D : Point} :
      Between A B C → Between A C D → Between A B D ∧ Between B C D := by
    sorry

  /--
    theorem II.4: Any four points A, B, C, D of a straight line can always be so arranged that B
    shall lie between A and C and also between A and D, and, furthermore, that C shall
    lie between A and D and also between B and D.
  -/
  theorem four_points_ordering(Line: Type)[HilbertAxiomsPL Point Line] {a b c d : Point} :
      ∃ l : Line, LiesOn a l → LiesOn b l → LiesOn c l → LiesOn d l →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ∃ (a' b' c' d' : Point),
        ({a', b', c', d'}: Set Point) =  {a,b,c,d} ∧
        (Between a' b' c' ∧ Between a' b' d' ∧ Between a' c' d' ∧ Between b' c' d') :=
  by
    sorry

  /--
    Theorem 3. Between any two points of a straight line, there always exists an
    unlimited number of points.
  -/
  theorem infinite_points_between (A B : Point) (hNe : A ≠ B) :
      ∀ (F : Finset Point), ∃ (P : Point), Between A P B ∧ P ∉ F :=
  by
    sorry

  /-- Definition of a linearly ordered list where for any three indices i < j < k,
    the point at j is between the points at i and k. -/
  def LinearOrderedPointList (L : List Point) : Prop :=
    ∀ (i j k : Fin L.length), i.val < j.val → j.val < k.val → Between (L.get i) (L.get j) (L.get k)

  /-- Theorem 4.1 : For any finite set of points on a straight line, there exists a linearly ordered list
      of these points, and only two such lists exist (the forward and reverse order). -/
  theorem linear_ordering_of_collinear_points{Line: Type}[HilbertAxiomsPL Point Line][DecidableEq Point] (l : Line) (S : Finset Point)
      (h : ∀ p ∈ S, LiesOn p l) :
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

  namespace Line
    variable {Line: Type}[HilbertAxiomsPL Point Line]

    theorem onSameSide.not_liesOn(l: Line)(a b: Point):
        onSameSide l a b → ¬ LiesOn a l ∧ ¬ LiesOn b l :=
    by
      sorry

    theorem onOtherSide.not_liesOn(l: Line)(a b: Point):
        onOtherSide l a b → ¬ LiesOn a l ∧ ¬ LiesOn b l :=
    by
      sorry

    theorem onSameSide.not_onOtherSide(l: Line)(a b: Point):
        onSameSide l a b → ¬ onOtherSide l a b :=
    by
      sorry

    theorem onOtherSide.not_onSameSide(l: Line)(a b: Point):
        onOtherSide l a b → ¬ onSameSide l a b :=
    by
      sorry

    theorem onSameSide.not (l: Line)(a b: Point):
        ¬ onSameSide l a b → LiesOn a l ∨ LiesOn b l ∨ onOtherSide l a b:=
    by
      sorry

    theorem onOtherSide.not (l: Line)(a b: Point):
        ¬ onOtherSide l a b → LiesOn a l ∨ LiesOn b l ∨ onSameSide l a b :=
    by
      sorry

    theorem onSameSide.reflex(l: Line)(a: Point):
        onSameSide l a a :=
    by
      sorry

    theorem onOtherSide.not_reflex(l: Line)(a: Point):
        ¬ onOtherSide l a a :=
    by
      sorry

    theorem onSameSide.symm(l: Line)(a b: Point):
        onSameSide l a b → onSameSide l b a :=
    by
      sorry

    theorem onOtherSide.symm(l: Line)(a b: Point):
        onOtherSide l a b → onOtherSide l b a :=
    by
      sorry

    theorem onSameSide.trans(l: Line)(a b c: Point):
        onSameSide l a b → onSameSide l b c → onSameSide l a c :=
    by
      sorry

    theorem onOtherSide.trans(a b c: Point)(h: a ≠ b)(l: Line):
        onOtherSide l a b → onOtherSide l b c → onSameSide l a c :=
    by
      sorry

  end Line

end Geometry
