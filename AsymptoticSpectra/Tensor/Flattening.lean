import AsymptoticSpectra.Tensor.Tensor
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

open TensorProduct PiTensorProduct BigOperators Module

namespace AsymptoticSpectra

variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

structure Split (ι : Type*) [Fintype ι] [DecidableEq ι] where
  S : Finset ι
  hS : S.Nonempty
  hSc : Sᶜ.Nonempty

variable {V : Fin d → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

variable (σ : Split (Fin d))

/-- Complement of the first block. -/
abbrev Sc := σ.Sᶜ

def splitEquiv : σ.S ⊕ Sc σ ≃ Fin d where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun x := if h : x ∈ σ.S then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, Finset.mem_compl.mpr h⟩
  left_inv := fun
    | .inl ⟨x, hx⟩ => by simp [hx]
    | .inr ⟨x, hx⟩ => by simp [Finset.mem_compl.mp hx]
  right_inv x := by simp only []; split_ifs <;> rfl

def splitTensorEquiv :
    PiTensorProduct K V ≃ₗ[K] (PiTensorProduct K (fun i : σ.S => V i)) ⊗[K] (PiTensorProduct K (fun i : Sc σ => V i)) :=
  let step1 : PiTensorProduct K V ≃ₗ[K] PiTensorProduct K (fun i : σ.S ⊕ (Sc σ) => V (splitEquiv σ i)) :=
    PiTensorProduct.reindex K V (splitEquiv σ).symm
  let N : σ.S ⊕ (Sc σ) → Type v := fun i => V (splitEquiv σ i)
  let step2 : PiTensorProduct K N ≃ₗ[K]
      (PiTensorProduct K (fun i₁ : σ.S => N (.inl i₁))) ⊗[K]
      (PiTensorProduct K (fun i₂ : Sc σ => N (.inr i₂))) :=
    (PiTensorProduct.tmulEquivDep K N).symm
  step1.trans step2

section Flattening

variable (K)

/-- The canonical linear map from `A ⊗ B` to `(A* →ₗ B)` that sends `a ⊗ b` to `f ↦ f(a) • b`.
This is the "view tensor as matrix" operation. -/
noncomputable def tensorToDualHom (A B : Type*) [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] :
    A ⊗[K] B →ₗ[K] (Dual K A →ₗ[K] B) :=
  TensorProduct.lift {
    toFun := fun a => {
      toFun := fun b => {
        toFun := fun f => f a • b
        map_add' := fun f g => add_smul (f a) (g a) b
        map_smul' := fun r f => by
          simp only [RingHom.id_apply, LinearMap.smul_apply]
          rw [smul_eq_mul, smul_smul]
      }
      map_add' := fun b₁ b₂ => by
        ext f
        exact smul_add (f a) b₁ b₂
      map_smul' := fun r b => by
        ext f
        exact smul_comm (f a) r b
    }
    map_add' := fun a₁ a₂ => by
      ext b f
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
      rw [map_add, add_smul]
    map_smul' := fun r a => by
      ext b f
      simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply,
        LinearMap.map_smul]
      rw [smul_eq_mul, smul_smul]
  }

@[simp]
theorem tensorToDualHom_tmul (A B : Type*) [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (a : A) (b : B) (f : Dual K A) :
    tensorToDualHom K A B (a ⊗ₜ b) f = f a • b := by
  simp [tensorToDualHom]

variable {K}

/-- The flattening linear map for a tensor object, given a split.
This is the canonical map from `A*` to `B` where the tensor is viewed as an element of `A ⊗ B`. -/
noncomputable def flatteningMap (σ : Split (Fin d)) (X : TensorObj K d) :
    Dual K (PiTensorProduct K (fun i : σ.S => X.V i)) →ₗ[K]
    PiTensorProduct K (fun i : Sc σ => X.V i) :=
  let A := PiTensorProduct K (fun i : σ.S => X.V i)
  let B := PiTensorProduct K (fun i : Sc σ => X.V i)
  -- Transport X.t to A ⊗ B using splitTensorEquiv
  let t_AB : A ⊗[K] B := splitTensorEquiv σ X.t
  -- Apply the canonical curry map
  tensorToDualHom K A B t_AB

/-- The flattening rank of a tensor object with respect to a split.
This is the rank of the flattening linear map, i.e., the dimension of its image. -/
noncomputable def flatteningRank (σ : Split (Fin d)) (X : TensorObj K d) : ℕ :=
  Module.finrank K (LinearMap.range (flatteningMap σ X))

end Flattening

end AsymptoticSpectra
