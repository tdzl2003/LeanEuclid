import Euclid.Sorts.Primitives
import Euclid.Relations.Point

namespace Euclid

  namespace Point
    /--
      命题：点p在直线l上
    -/
    opaque on_line(p: Point)(l:Line): Prop

    /--
      命题：点p1 p2 p3共线
      注意这包含了其中存在两点相等的情况
    -/
    def on_same_line(p1 p2 p3: Point): Prop :=
      ∃ l: Line, p1.on_line l ∧ p2.on_line l ∧ p3.on_line l

    namespace on_same_line
      theorem comm_left{p1 p2 p3: Point}:
        on_same_line p1 p2 p3 ↔ on_same_line p2 p1 p3 := by
        constructor
        all_goals {
          intro ⟨l, hl⟩
          use l
          exact ⟨hl.2.1, hl.1, hl.2.2⟩
        }

      theorem comm_right{p1 p2 p3: Point}:
        on_same_line p1 p2 p3 ↔ on_same_line p1 p3 p2 := by
        constructor
        all_goals {
          intro ⟨l, hl⟩
          use l
          exact ⟨hl.1, hl.2.2, hl.2.1⟩
        }

    end on_same_line

    /--
      命题：点p在ab之间
    -/
    opaque between(p: Point)(a b: Point): Prop

    namespace between

      /--
        点p在ab之间蕴含它们三点共线
      -/
      axiom one_same_line{p a b: Point}(h: between p a b):
        on_same_line p a b

      /--
        点p在ab之间蕴含它们的距离关系
      -/
      axiom distance{p a b: Point}(h: between p a b):
        p.distance a + p.distance b = a.distance b

    end between

    namespace on_same_line
      /--
        共线的三点至少有一个点在另外两点之间
      -/
      axiom between_cases{a b c: Point}(h: on_same_line a b c):
        between a b c ∨ between b c a ∨ between c b a

    end on_same_line


  end Point

end Euclid
