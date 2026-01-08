import AsymptoticSpectra.Tensor.Tensor

universe u v w

open TensorObj

namespace TensorObj

open PiTensorProduct

variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

/-- X is a restriction of Y (X ≤ Y) if there exists a family of linear maps f_i : Y.V_i → X.V_i
    such that the induced map on the tensor product sends Y.t to X.t. -/
def Restrict (X Y : TensorObj K d) : Prop :=
  ∃ f : ∀ i, Y.V i →ₗ[K] X.V i, liftMap f Y.t = X.t


theorem restrict_refl (X : TensorObj K d) : Restrict X X := by
  use fun i => LinearMap.id
  rw [TensorObj.liftMap_id]

theorem restrict_trans {X Y Z : TensorObj K d} : Restrict X Y → Restrict Y Z → Restrict X Z := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩
  use fun i => (f i).comp (g i)
  rw [← TensorObj.liftMap_comp, hg, hf]

/-- Taking restriction respects isomorphism. -/
theorem restrict_iff_of_iso {X X' Y Y' : TensorObj K d}
    (hX : Isomorphic X X') (hY : Isomorphic Y Y') :
    Restrict X Y ↔ Restrict X' Y' := by
  obtain ⟨iX⟩ := hX
  obtain ⟨iY⟩ := hY
  constructor
  · rintro ⟨f, hf⟩
    use fun i => (iX.equiv i).toLinearMap.comp ((f i).comp (iY.equiv i).symm.toLinearMap)
    rw [← TensorObj.liftMap_comp, ← TensorObj.liftMap_comp]
    have hY_symm : liftMap (fun i => (iY.equiv i).symm.toLinearMap) Y'.t = Y.t := by
      rw [← iY.map_t, TensorObj.liftMap_comp]
      convert TensorObj.liftMap_id Y using 2
      apply PiTensorProduct.ext
      apply MultilinearMap.ext; intro v
      simp [liftMap, lift_tprod]
    rw [hY_symm, hf, iX.map_t]
  · rintro ⟨f, hf⟩
    use fun i => (iX.equiv i).symm.toLinearMap.comp ((f i).comp (iY.equiv i).toLinearMap)
    rw [← TensorObj.liftMap_comp, ← TensorObj.liftMap_comp]
    rw [iY.map_t, hf]
    have hX_symm : liftMap (fun i => (iX.equiv i).symm.toLinearMap) X'.t = X.t := by
      rw [← iX.map_t, TensorObj.liftMap_comp]
      convert TensorObj.liftMap_id X using 2
      apply PiTensorProduct.ext
      apply MultilinearMap.ext; intro v
      simp [liftMap, lift_tprod]
    rw [hX_symm]


end TensorObj

namespace Tensor

open TensorObj

variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

def Restrict (x y : Tensor K d) : Prop :=
  Quotient.liftOn₂ x y TensorObj.Restrict
    (fun _ _ _ _ h1 h2 => propext (restrict_iff_of_iso h1 h2))

instance : Preorder (Tensor K d) where
  le := Restrict
  le_refl x := by
    induction x using Quotient.inductionOn
    exact restrict_refl _
  le_trans x y z := by
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    induction z using Quotient.inductionOn
    exact restrict_trans

end Tensor
