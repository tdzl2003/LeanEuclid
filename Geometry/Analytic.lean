import Geometry.Basic
import Mathlib.Data.Real.Basic

namespace Geometry.Analytic
  /-- Define a point a (x, y) -/
  structure Point where
    x: ℝ
    y: ℝ

  /-- Define a raw line by ax + by + c = 0-/
  structure LineRaw where
    a : ℝ
    b : ℝ
    c : ℝ
    h : a ≠ 0 ∨ b ≠ 0

  instance : DecidableEq Point := by
    intro a b
    have hx : Decidable (a.x = b.x) := by infer_instance
    have hy : Decidable (a.y = b.y) := by infer_instance
    sorry

  namespace LineRaw

    def Equiv (l₁ l₂ : LineRaw) : Prop :=
      ∃ k : ℝ, k ≠ 0 ∧ l₂.a = k * l₁.a ∧ l₂.b = k * l₁.b ∧ l₂.c = k * l₁.c

    theorem equiv_refl (l: LineRaw): Equiv l l := by
      refine ⟨1, zero_ne_one.symm, ?_, ?_, ?_⟩ <;> simp only [one_mul]

    theorem equiv_symm (h : Equiv l₁ l₂) : Equiv l₂ l₁ := by
      sorry

    theorem equiv_trans (h₁ : Equiv l₁ l₂) (h₂ : Equiv l₂ l₃) : Equiv l₁ l₃ := by
      sorry

    instance setoid : Setoid LineRaw where
      r := Equiv
      iseqv := ⟨equiv_refl, equiv_symm, equiv_trans⟩

    def liesOn (p : Point) (l : LineRaw) : Prop :=
      l.a * p.x + l.b * p.y + l.c = 0

    theorem liesOn_equiv (p : Point) (l₁ l₂ : LineRaw) (h : LineRaw.Equiv l₁ l₂) :
      liesOn p l₁ ↔ liesOn p l₂ := by
        sorry

    def mk_line_from_points(a b: Point): LineRaw :=
      if a = b then
        LineRaw.mk 0 1 (-a.y) (by sorry)
      else
        LineRaw.mk (b.y-a.y) (a.x-b.x) (b.x*a.y - a.x*b.y) (by sorry)

  end LineRaw

  def Line := Quotient LineRaw.setoid

  instance: HMul Point Real Point where
    hMul(a: Point)(b: Real) := Point.mk (a.x*b) (a.y*b)

  instance: Add Point where
    add(a: Point)(b: Point) :=  Point.mk (a.x+b.x) (a.y+b.y)

  def liesOn(a: Point)(l: Line): Prop :=
    Quotient.lift (LineRaw.liesOn a) (fun l₁ l₂ h => propext (LineRaw.liesOn_equiv a l₁ l₂ h)) l

  def between(a: Point)(b: Point)(c: Point): Prop :=
    ∃ r: ℝ, r > 0 ∧ r < 1 ∧ a = b * r + c* (r-1)

  def mk_line_from_points(a b: Point): Line :=
    Quotient.mk'' <| LineRaw.mk_line_from_points a b

  theorem mk_line_liesOn(a b: Point):
    liesOn a (mk_line_from_points a b) ∧ liesOn b (mk_line_from_points a b) := by
      sorry

  theorem unique_line_from_two_points(a b: Point)(l: Line):
    a ≠ b → liesOn a l → liesOn b l → l = mk_line_from_points a b := by
      sorry

  theorem line_exists_two_points(l: Line):
    ∃ a b: Point, a≠b ∧ liesOn a l ∧ liesOn b l := by
      sorry

  theorem exists_three_point_not_on_same_line:
    ∃ a b c: Point, a≠b ∧ b≠c ∧ a≠c ∧ ¬∃ l: Line, liesOn a l ∧ liesOn b l ∧ liesOn c l := by
      sorry

  noncomputable instance: HilbertGeometry2D Point Line where
    liesOn := liesOn
    between := between
    mk_line_from_points := mk_line_from_points
    mk_line_liesOn := mk_line_liesOn
    unique_line_from_two_points := unique_line_from_two_points
    line_exists_two_points := line_exists_two_points
    exists_three_point_not_on_same_line := exists_three_point_not_on_same_line

end Geometry.Analytic
