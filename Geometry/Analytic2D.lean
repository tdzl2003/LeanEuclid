import Geometry.Basic
import Geometry.Polygon
import Mathlib.Data.Real.Basic

namespace Geometry.Analytic2D
  /-- Define a point a (x, y) -/
  structure Point where
    x: ℝ
    y: ℝ

  instance: HMul Point Real Point where
    hMul(a: Point)(b: Real) := Point.mk (a.x*b) (a.y*b)

  instance: Add Point where
    add(a: Point)(b: Point) :=  Point.mk (a.x+b.x) (a.y+b.y)

  def Between(a: Point)(b: Point)(c: Point): Prop :=
    ∃ r: ℝ, r > 0 ∧ r < 1 ∧ a = b * r + c* (r-1)

  /-- Between relation is exclusive. -/
  theorem between_ne(a b c: Point):
    Between a b c → a ≠ b ∨ b ≠ c :=
  by
    sorry

  /-- axiom II.1: If A, B, C are points of a straight line and B lies Between A and C, then B lies also Between C and A.-/
  theorem between_symm(a b c: Point):
    Between a b c → Between c b a :=
  by
    sorry

  /-- axiom II.2.2 If A and C are two points of a straight line, at least one point D so situated that C lies Between A and D.-/
  theorem extension_exists(a c: Point):
    a ≠ c → ∃ d: Point, Between a c d :=
  by
    sorry

  /-- Define a raw line by ax + by + c = 0-/
  structure LineRaw where
    a : ℝ
    b : ℝ
    c : ℝ
    h : a ≠ 0 ∨ b ≠ 0

  noncomputable instance : DecidableEq Point := by
    intro a b
    have hx : Decidable (a.x = b.x) := by infer_instance
    have hy : Decidable (a.y = b.y) := by infer_instance
    rw [Point.mk.injEq]
    exact instDecidableAnd

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

    def LiesOn (p : Point) (l : LineRaw) : Prop :=
      l.a * p.x + l.b * p.y + l.c = 0

    theorem liesOn_equiv (p : Point) (l₁ l₂ : LineRaw) (h : LineRaw.Equiv l₁ l₂) :
      LiesOn p l₁ ↔ LiesOn p l₂ := by
        sorry

    noncomputable def mk_line(a b: Point)(h: a≠b): LineRaw :=
      LineRaw.mk (b.y-a.y) (a.x-b.x) (b.x*a.y - a.x*b.y) (by sorry)

  end LineRaw

  def Line := Quotient LineRaw.setoid

  private def LiesOn(l: Line)(a: Point): Prop :=
    Quotient.lift (LineRaw.LiesOn a) (fun l₁ l₂ h => propext (LineRaw.liesOn_equiv a l₁ l₂ h)) l

  instance: Membership Point Line where
    mem := LiesOn

  noncomputable def mk_line(a b: Point)(h: a≠b): Line :=
    Quotient.mk'' <| LineRaw.mk_line a b h

  theorem mk_line_liesOn(a b: Point)(h: a≠ b):
      a ∈ (mk_line a b h) ∧ b ∈ (mk_line a b h) :=
  by
    sorry

  theorem unique_line_from_two_points(a b: Point)(l: Line)(h:  a ≠ b):
      a ∈ l → b ∈ l → l = mk_line a b h :=
  by
    sorry

  theorem line_exists_two_points(l: Line):
      ∃ a b: Point, a≠b ∧ a ∈ l ∧ b ∈ l :=
  by
    sorry

  def Collinear (a b c : Point) : Prop := ∃ l : Line, a ∈ l ∧ b ∈ l ∧ c ∈ l

  def OnSegment(a b c: Point): Prop := Between a b c ∨ b = a ∨ b = c

  theorem collinear_of_between(a b c: Point): Between a b c → Collinear a b c :=
  by
    sorry

  theorem pasch_axiom {A B C: Point}(h: ¬Collinear A B C)(l: Line):
      (∃ P: Point, OnSegment A P B ∧ P ∈ l) →
      (∃ Q: Point, OnSegment B Q C ∧ Q ∈ l) ∨ (∃ R: Point, OnSegment A R C ∧ R ∈ l) :=
  by
    sorry

  theorem exists_three_noncollinear_points:
      ∃ a b c: Point, ¬Collinear a b c :=
  by
    sorry

  noncomputable instance: HilbertAxioms2D Point where
    Line := Line
    mem_Line := by infer_instance
    Between := Between
    between_ne := between_ne
    extension_exists := extension_exists
    mk_line := mk_line
    mk_line_liesOn := mk_line_liesOn
    unique_line_from_two_points := unique_line_from_two_points
    line_exists_two_points := line_exists_two_points
    collinear_of_between := collinear_of_between

    exists_three_noncollinear_points := exists_three_noncollinear_points
    pasch_axiom := pasch_axiom

  section
    abbrev Segment := Geometry.Segment Point
    abbrev BrokenLine := Geometry.BrokenLine Point
    abbrev Polygon := HilbertAxioms2D.Polygon Point

    def someOutsidePoint(poly: Polygon): Point :=
      let x:= (poly.vertices.map (fun p => p.x)).min?
      let y:= (poly.vertices.map (fun p => p.y)).min?
      have hx: x.isSome := by
        sorry
      have hy: y.isSome := by
        sorry
      Point.mk ((x.get hx) -1) ((y.get hy)-1)

    def outside(poly: Polygon)(p: Point): Prop :=
      ∃ l:Line, ∀ q ∈ l, q ≠ p ∧ ¬(q ∈ poly)

    def inside(poly: Polygon)(p: Point): Prop:=
      ¬ (outside poly p ∨ p ∈ poly)

    theorem inside_outside_disjoint:
      ∀ (poly: Polygon) (p: Point), ¬(inside poly p ∧ outside poly p) :=
    by
      sorry

    theorem inside_outside_boundary_exhaustive:
      ∀ (poly: Polygon) (p: Point), inside poly p ∨ outside poly p ∨ p ∈ poly :=
    by
      sorry

    theorem inside_path_connected: ∀ (poly: Polygon), poly.isSimple → ∀ (a b: Point), inside poly a → inside poly b →
      ∃ (γ: BrokenLine),
        (∀ p: Point, p ∈ γ → inside poly p) ∧
        γ.head = a ∧
        γ.last = b :=
    by
      sorry

    theorem outside_path_connected: ∀ (poly: Polygon) (a b: Point), outside poly a → outside poly b →
      ∃ (γ: BrokenLine),
        (∀ p: Point, p ∈ γ → outside poly p) ∧
        γ.head = a ∧
        γ.last = b :=
    by
      sorry

    theorem crossing_edge:
      ∀ (poly: Polygon) (a b: Point), inside poly a → outside poly b →
        (∀ (γ: BrokenLine),
          γ.head = a →
          γ.last = b →
          ∃ p: Point, p ∈ γ ∧ p ∈ poly
        ) :=
    by
      sorry

    theorem not_exists_inside_line:
      ∀ (poly: Polygon), ¬ ∃ l:Line, ∀ p ∈ l, inside poly p :=
    by
      sorry

    theorem exists_outside_line:
      ∀ (poly: Polygon), ∃ l:Line, ∀ p ∈ l, outside poly p :=
    by
      sorry

    noncomputable instance {poly: Polygon}{hSimple: poly.isSimple}: HilbertAxioms2D.PolygonalRegion poly hSimple where
      inside := inside poly
      outside := outside poly
      inside_outside_disjoint := inside_outside_disjoint poly
      inside_outside_boundary_exhaustive := inside_outside_boundary_exhaustive poly
      inside_path_connected := inside_path_connected poly hSimple
      outside_path_connected := outside_path_connected poly
      crossing_edge := crossing_edge poly
      not_exists_inside_line := not_exists_inside_line poly
      exists_outside_line:= exists_outside_line poly
  end

end Geometry.Analytic2D
