# 形式化纯欧几何的尝试

实时讨论可加群[776491665](https://qm.qq.com/q/JzD4s222g8)



## TODO:


两两不相等性质比较常用，考虑定义成一个专门的性质，例如：

```lean
def MyAxioms.Constraint.not_coincide {α : Type}(l: List α) : → Prop
    := l.Pairwise (· ≠ ·)
```

并定义一个高效的tactic，例如 `not_coincide_simp` 来抽取其中两个元素不相等的证明（来自 [@D-eval](https://github.com/D-eval) 的建议）。

