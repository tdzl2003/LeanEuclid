namespace Geometry
  def IsSubset{Point: Type}{α: Type}{β: Type}[Membership Point α][Membership Point β](S: α)(T: β): Prop :=
    ∀ p: Point, p ∈ S → p ∈ T

  scoped infix:99 "⊆" => IsSubset
end Geometry
