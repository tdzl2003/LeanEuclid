
namespace List
  @[simp]
  def Distinct{α}(l: List α):Prop :=
    l.Pairwise (· ≠ ·)

  theorem Distinct.select{l: List α}(h: l.Distinct)(i j: Fin l.length)(hne: i ≠ j):
    l[i] ≠ l[j] :=
  by
    unfold Distinct at h
    rw [List.pairwise_iff_getElem] at h
    by_cases hle: i < j
    . specialize h i j i.2 j.2 hle
      exact h
    . have : j < i := by
        apply Nat.lt_of_le_of_ne;
        . rw [Fin.mk_lt_mk, Nat.not_lt] at hle; exact hle;
        . apply Ne.symm
          rw [ne_eq, Fin.eq_mk_iff_val_eq] at hne
          exact hne
      specialize h j i j.2 i.2 this
      apply Ne.symm
      exact h

  theorem Distinct.select' {l: List α}(h: l.Distinct)(i j: Nat)(hi: i < l.length)(hj: j<l.length)(hne: i ≠ j):
    l[i]'hi ≠ l[j]'hj :=
  by
    apply h.select ⟨i, hi⟩ ⟨j, hj⟩
    rw [ne_eq, Fin.eq_mk_iff_val_eq]
    exact hne

  theorem Distinct.map {l: List α}
    (f: α → β)(h: ∀ a b: α, a ≠ b → f a ≠ f b):
    l.Distinct → (l.map f).Distinct :=
  by
    unfold List.Distinct
    rw [pairwise_map]
    intro h1
    rw [pairwise_iff_getElem] at h1 ⊢
    intro i j hi hj hij
    apply h
    exact h1 i j hi hj hij

  theorem Distinct.map' {l: List α}
    (f: α → β)(h: ∀ a b: α, f a ≠ f b → a ≠ b):
    (l.map f).Distinct → l.Distinct :=
  by
    unfold List.Distinct
    rw [pairwise_map]
    intro h1
    rw [pairwise_iff_getElem] at h1 ⊢
    intro i j hi hj hij
    apply h
    exact h1 i j hi hj hij

end List
