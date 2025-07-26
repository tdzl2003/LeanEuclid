import Euclid.Sorts.Triangle
import Euclid.Relations.Triangle

namespace Euclid.Triangle

  theorem choose_two_vertices{t: Triangle}
    {A B: Point}
    (hne: A≠B)
    (h: A.is_triangle_vertex t ∧ B.is_triangle_vertex t) :
    ∃ t', t'= t ∧ t'.a = A ∧ t'.b = B := by
    let ⟨hA, hB⟩ := h
    unfold Point.is_triangle_vertex at hA hB
    -- 枚举A和B的位置
    rcases hA with hA|hA|hA
    all_goals rcases hB with hB|hB|hB
    -- 删除掉不可能的三个分支（A、B不是同一个顶点）
    all_goals try {
      rw [← hB] at hA
      by_contra
      apply hne
      exact hA
    }
    . use t
      exact ⟨rfl, Eq.symm hA, Eq.symm hB⟩
    . let t' := t.reorder_bc
      have hA': t'.a = A := by
        unfold t' Triangle.reorder_bc
        rw [hA]
      have hB': t'.b = B := by
        unfold t' Triangle.reorder_bc
        rw [hB]
      use t'
      constructor
      . unfold t'
        apply Triangle.reorder_bc.eq
      exact ⟨hA', hB'⟩
    . let t' := t.reorder_ab
      have hA': t'.a = A := by
        unfold t' Triangle.reorder_ab
        rw [hA]
      have hB': t'.b = B := by
        unfold t' Triangle.reorder_ab
        rw [hB]
      use t'
      constructor
      . unfold t'
        apply Triangle.reorder_ab.eq
      exact ⟨hA', hB'⟩
    . let t' := t.reorder_ab.reorder_bc
      have hA': t'.a = A := by
        unfold t' Triangle.reorder_ab Triangle.reorder_bc
        rw [hA]
      have hB': t'.b = B := by
        unfold t' Triangle.reorder_ab Triangle.reorder_bc
        rw [hB]
      use t'
      constructor
      . unfold t'
        rw [Triangle.reorder_ab.eq, Triangle.reorder_bc.eq]
      exact ⟨hA', hB'⟩
    . let t' := t.reorder_ac.reorder_bc
      have hA': t'.a = A := by
        unfold t' Triangle.reorder_ac Triangle.reorder_bc
        rw [hA]
      have hB': t'.b = B := by
        unfold t' Triangle.reorder_ac Triangle.reorder_bc
        rw [hB]
      use t'
      constructor
      . unfold t'
        rw [Triangle.reorder_ac.eq, Triangle.reorder_bc.eq]
      exact ⟨hA', hB'⟩
    . let t' := t.reorder_ac
      have hA': t'.a = A := by
        unfold t' Triangle.reorder_ac
        rw [hA]
      have hB': t'.b = B := by
        unfold t' Triangle.reorder_ac
        rw [hB]
      use t'
      constructor
      . unfold t'
        apply Triangle.reorder_ac.eq
      exact ⟨hA', hB'⟩

end Euclid.Triangle
