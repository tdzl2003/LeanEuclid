import Geometry.Basic
import Geometry.Polygon
import Geometry.HilbertAxioms2D
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Geometry.Analytic2D
  /-- Define a point a (x, y) -/
  structure Point where
    x: ℝ
    y: ℝ

  @[simp]
  instance: HMul Point Real Point where
    hMul(a: Point)(b: Real) := Point.mk (a.x*b) (a.y*b)

  @[simp]
  instance: HAdd Point Point Point where
    hAdd(a: Point)(b: Point) :=  Point.mk (a.x+b.x) (a.y+b.y)

  def Between(a: Point)(b: Point)(c: Point): Prop :=
    a ≠ c ∧ ∃ r: ℝ, r > 0 ∧ r < 1 ∧ b = a * r + c* (1-r)

  /-- Between relation is exclusive. -/
  theorem between_ne{a b c: Point}:
    Between a b c → [a, b, c].Distinct :=
  by
    unfold Between
    intro ⟨hne, r, hr⟩
    simp only [List.Distinct, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self,
      and_true]
    and_intros
    . intro he
      rw [he] at hr
      subst he
      rcases hr with ⟨r_pos, r_lt1, h_eq⟩
      apply hne
      rw [Point.mk.injEq] at h_eq ⊢
      simp only [instHAddPoint, instHMulPointReal] at h_eq
      have hr1: 1-r ≠ 0 := by linarith
      and_intros
      . have : a.x * (1 - r) = c.x * (1 - r) := by linarith
        apply mul_right_cancel₀ hr1
        exact this
      . have : a.y * (1 - r) = c.y * (1 - r) := by linarith
        apply mul_right_cancel₀ hr1
        exact this
    . exact hne
    . intro he
      rw [he] at hr
      subst he
      rcases hr with ⟨r_pos, r_lt1, h_eq⟩
      apply hne
      rw [Point.mk.injEq] at h_eq ⊢
      have hr0: r ≠ 0 := by linarith
      simp only [instHAddPoint, instHMulPointReal] at h_eq
      and_intros
      . have : a.x * r = b.x * r := by linarith
        apply mul_right_cancel₀ hr0
        exact this
      . have : a.y * r = b.y * r := by linarith
        apply mul_right_cancel₀ hr0
        exact this

  /-- axiom II.1: If A, B, C are points of a straight line and B lies Between A and C, then B lies also Between C and A.-/
  theorem between_symm{a b c: Point}:
    Between a b c → Between c b a :=
  by
    unfold Between
    intro ⟨hne, r, hr0, hr1, h1⟩
    and_intros ; apply Ne.symm hne
    use 1-r
    and_intros
    . linarith
    . linarith
    rw [h1]
    field_simp
    and_intros
    . linarith
    . linarith

  /-- axiom II.2.2 If A and C are two points of a straight line, at least one point D so situated that C lies Between A and D.-/
  def extension_exists{a c: Point}(hne: a ≠ c ):
    {d: Point // Between a c d} :=
    let d := a * (-1: ℝ) + c * (2: ℝ)
    ⟨d, by
        and_intros
        . intro had
          unfold d at had
          apply hne
          rw [Point.mk.injEq] at had ⊢
          simp only [instHAddPoint, instHMulPointReal] at had
          and_intros
          . linarith
          . linarith
        . use (0.5: ℝ)
          unfold d
          and_intros
          . linarith
          . linarith
          . rw [Point.mk.injEq]
            simp only [instHAddPoint, instHMulPointReal]
            and_intros
            . linarith
            . linarith
    ⟩

  theorem between_not_symm_left{a b c : Point}:
    Between a b c → ¬ Between b a c :=
  by
    unfold Between
    intro ⟨hac, r, hr0, hr1, hr⟩
    rw [not_and_or]
    apply Or.inr
    rw [not_exists]
    intro x ⟨hx0, hx1, hx⟩
    apply hac
    rw [hr] at hx
    rw [Point.mk.injEq] at hx ⊢
    simp only [instHAddPoint, instHMulPointReal] at hx
    have hnz: 1-r*x ≠ 0 := by
      have : r * x < 1 := by
        calc r * x < 1 * x := by
              apply mul_lt_mul_of_pos_right hr1 hx0
        _ < 1 := by linarith
      linarith
    and_intros
    . replace hx := hx.1
      have : a.x * (1-r*x) = c.x*(1-r*x) := by
        linarith
      apply mul_right_cancel₀ hnz this
    . have : a.y * (1-r*x) = c.y*(1-r*x) := by
        linarith
      apply mul_right_cancel₀ hnz this

  theorem between_not_symm_right{a b c : Point}:
    Between a b c → ¬ Between a c b :=
  by
    intro h
    replace h := between_symm h
    replace h := between_not_symm_left h
    intro h'
    apply h
    apply between_symm h'

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
      let ⟨k, hk0, ha, hb, hc⟩ := h
      use 1/k
      rw [ha, hb, hc]
      field_simp

    theorem equiv_trans (h₁ : Equiv l₁ l₂) (h₂ : Equiv l₂ l₃) : Equiv l₁ l₃
      :=
    by
      let ⟨k1, hk1, ha1, hb1, hc1⟩ := h₁
      let ⟨k2, hk2, ha2, hb2, hc2⟩ := h₂
      use k2 * k1
      rw [ha2, hb2, hc2, ha1, hb1, hc1]
      constructor; positivity
      simp only [mul_assoc, and_self]

    instance setoid : Setoid LineRaw where
      r := Equiv
      iseqv := ⟨equiv_refl, equiv_symm, equiv_trans⟩

    def LiesOn (p : Point) (l : LineRaw) : Prop :=
      l.a * p.x + l.b * p.y + l.c = 0

    theorem liesOn_equiv {p : Point} {l₁ l₂ : LineRaw} (h : LineRaw.Equiv l₁ l₂) :
      LiesOn p l₁ →  LiesOn p l₂ :=
    by
      replace ⟨k, hk0, hka, hkb, hkc⟩ := h
      intro hpl
      unfold LiesOn at hpl ⊢
      rw [hka, hkb, hkc]
      rw [mul_assoc, mul_assoc, ← mul_add, ← mul_add, hpl]
      apply mul_zero

    theorem liesOn_equiv_iff {p : Point} {l₁ l₂ : LineRaw} (h : LineRaw.Equiv l₁ l₂) :
      LiesOn p l₁ ↔ LiesOn p l₂ :=
    by
      constructor
      . apply liesOn_equiv h
      . replace h:= equiv_symm h
        apply liesOn_equiv h

    noncomputable def mk_line{a b: Point}(h: a≠b): LineRaw :=
      have h': b.y - a.y ≠ 0 ∨ a.x - b.x ≠ 0 := by
        by_contra h'
        rw [not_or, not_ne_iff, not_ne_iff] at h'
        apply h
        rw [Point.mk.injEq]
        and_intros
        . linarith
        . linarith
      LineRaw.mk (b.y-a.y) (a.x-b.x) (b.x*a.y - a.x*b.y) h'

    theorem mem_mk_line{a b : Point}(h: a≠b):
      LiesOn a (mk_line h) ∧ LiesOn b (mk_line h) :=
    by
      unfold LiesOn mk_line
      simp only
      and_intros
      . linarith
      . linarith

    noncomputable instance (p: Point)(l: LineRaw): Decidable (LiesOn p l) := by
      unfold LiesOn
      exact inferInstance

  end LineRaw

  def Line := Quotient LineRaw.setoid

  private def LiesOn(l: Line)(a: Point): Prop :=
    Quotient.lift (LineRaw.LiesOn a) (fun _ _ h => propext (LineRaw.liesOn_equiv_iff h)) l

  instance: Membership Point Line where
    mem := LiesOn

  noncomputable instance(l: Line)(a: Point): Decidable (a ∈ l) :=
    let lraw := Quotient.out l
    have h : LineRaw.LiesOn a lraw ↔ a∈l := by
      have : l = ⟦lraw⟧ := by
        rw [Quotient.eq_mk_iff_out]
      rw [this]
      simp only [Membership.mem, LiesOn, Quotient.lift_mk]

    decidable_of_iff (LineRaw.LiesOn a lraw) h

  noncomputable def mk_line{a b: Point}(h: a≠b): {l: Line // a ∈ l ∧ b ∈ l} :=
    ⟨Quotient.mk'' <| LineRaw.mk_line h,
      by
        simp only [instMembershipPointLine, LiesOn, Quotient.lift_mk]
        apply LineRaw.mem_mk_line
    ⟩

  theorem unique_line_from_two_points{a b: Point}{l: Line}(h:  a ≠ b):
      a ∈ l → b ∈ l → l = mk_line h :=
  by
    sorry

  def line_exists_two_points(l: Line):
      {s: Point × Point // s.1 ≠ s.2 ∧ s.1 ∈ l ∧ s.2 ∈ l} :=
    sorry

  def Collinear (a b c : Point) : Prop := ∃ l : Line, a ∈ l ∧ b ∈ l ∧ c ∈ l

  theorem collinear_of_between{a b c: Point}: Between a b c → Collinear a b c :=
  by
    sorry

  def pasch_axiom {A B C: Point}{l: Line}(h: ¬Collinear A B C)(hA: ¬A ∈ l)(hB: ¬B ∈ l )(hc: ¬C ∈ l):
      (∃ P: Point, Between A P B ∧ P ∈ l) →
      {Q: Point // (Between B Q C ∨  Between A Q C) ∧ Q ∈ l} :=
  by
    sorry

  def exists_three_noncollinear_points:
      {s: Point × Point × Point // [s.1, s.2.1, s.2.2].Distinct ∧ ¬Collinear s.1 s.2.1 s.2.2} :=
    sorry

  def mk_line_intersection{l1 l2: Line}(hne: l1 ≠ l2)(he: ∃ p, p∈l1 ∧ p ∈ l2) : {p: Point // p ∈ l1 ∧ p ∈ l2} :=
    sorry

  noncomputable instance: PointDef Point where
    instDecidableEq := by infer_instance

  noncomputable instance: PointOrder Point where
    Between := Between
    between_ne := between_ne
    between_symm := between_symm
    extension_exists := extension_exists
    between_not_symm_right := between_not_symm_right

  noncomputable instance : LineDef Point where
    Line := Line
    instMemLine := by infer_instance
    instDecidableMemLine := by infer_instance

  noncomputable instance: LineConnection Point where
    mk_line := mk_line
    mk_line_intersection := mk_line_intersection
    unique_line_from_two_points := unique_line_from_two_points
    line_exists_two_points := line_exists_two_points
    collinear_of_between := collinear_of_between

  noncomputable instance: HilbertAxioms2D Point where
    exists_three_noncollinear_points := exists_three_noncollinear_points
    pasch_axiom:=pasch_axiom


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

    noncomputable instance {poly: Polygon}(hSimple: poly.isSimple): HilbertAxioms2D.PolygonalRegionConnection poly hSimple where
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
