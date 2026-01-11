import AsymptoticSpectra.Tensor.Tensor
import AsymptoticSpectra.Tensor.BaseChange
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
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

section Isomorphism

variable (K)

/-- Lift factorwise linear equivalences to a linear equivalence on PiTensorProduct.
This generalizes `TensorObj.liftMap` to the case of equivalences. -/
noncomputable def liftEquiv {ι : Type*} [Fintype ι] {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (e : ∀ i, V i ≃ₗ[K] W i) :
    PiTensorProduct K V ≃ₗ[K] PiTensorProduct K W :=
  LinearEquiv.ofLinear
    (TensorObj.liftMap (fun i => (e i).toLinearMap))
    (TensorObj.liftMap (fun i => (e i).symm.toLinearMap))
    (by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext; intro v
      simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.compMultilinearMap_apply]
      rw [TensorObj.liftMap_comp]
      have : (fun i => ((e i).toLinearMap).comp ((e i).symm.toLinearMap)) = fun i => LinearMap.id := by
        ext i x
        simp
      rw [this]
      simp [TensorObj.liftMap])
    (by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext; intro v
      simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.compMultilinearMap_apply]
      rw [TensorObj.liftMap_comp]
      have : (fun i => ((e i).symm.toLinearMap).comp ((e i).toLinearMap)) = fun i => LinearMap.id := by
        ext i x
        simp
      rw [this]
      simp [TensorObj.liftMap])

variable {K}

/-- Naturality of `PiTensorProduct.reindex`: it commutes with functorial maps. -/
theorem reindex_liftEquiv_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (φ : ι ≃ ι) (e : ∀ i, V i ≃ₗ[K] W i) (t : PiTensorProduct K V) :
    PiTensorProduct.reindex K W φ (liftEquiv K e t) =
    liftEquiv K (fun i => e (φ.symm i)) (PiTensorProduct.reindex K V φ t) := by
  suffices h : (liftEquiv K e).trans (PiTensorProduct.reindex K W φ) =
      (PiTensorProduct.reindex K V φ).trans (liftEquiv K (fun i => e (φ.symm i))) by
    exact LinearEquiv.congr_fun h t
  ext v : 1
  simp only [LinearEquiv.trans_apply, liftEquiv, LinearEquiv.ofLinear_apply]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul]
    rw [TensorObj.liftMap_tprod]
    rw [PiTensorProduct.reindex_tprod]
    rw [PiTensorProduct.reindex_tprod]
    rw [TensorObj.liftMap_tprod]
  | add x y ihx ihy =>
    simp only [map_add, ihx, ihy]

/-- Naturality of `PiTensorProduct.tmulEquivDep`: it commutes with functorial maps. -/
theorem tmulEquivDep_liftEquiv_comm {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {V W : ι₁ ⊕ ι₂ → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (e : ∀ i, V i ≃ₗ[K] W i) (t : PiTensorProduct K V) :
    (PiTensorProduct.tmulEquivDep K W).symm (liftEquiv K e t) =
    TensorProduct.map
      (liftEquiv K (fun i : ι₁ => e (.inl i))).toLinearMap
      (liftEquiv K (fun i : ι₂ => e (.inr i))).toLinearMap
      ((PiTensorProduct.tmulEquivDep K V).symm t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, liftEquiv, LinearEquiv.ofLinear_apply]
    congr 1
    rw [TensorObj.liftMap_tprod]
    rw [PiTensorProduct.tmulEquivDep_symm_apply]
    conv_rhs => rw [PiTensorProduct.tmulEquivDep_symm_apply]
    rw [TensorProduct.map_tmul]
    congr 1
    · change _ = (LinearEquiv.ofLinear (TensorObj.liftMap _) (TensorObj.liftMap _) _ _) _
      rw [LinearEquiv.ofLinear_apply, TensorObj.liftMap_tprod]
    · change _ = (LinearEquiv.ofLinear (TensorObj.liftMap _) (TensorObj.liftMap _) _ _) _
      rw [LinearEquiv.ofLinear_apply, TensorObj.liftMap_tprod]
  | add x y ihx ihy =>
    simp only [map_add, ihx, ihy]

/-- Naturality of `splitTensorEquiv`: it commutes with `liftEquiv`. -/
theorem splitTensorEquiv_naturality (σ : Split (Fin d)) {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (e : ∀ i, V i ≃ₗ[K] W i) (t : PiTensorProduct K V) :
    splitTensorEquiv σ (liftEquiv K e t) =
    TensorProduct.map
      (liftEquiv K (fun (i : σ.S) => e i.val)).toLinearMap
      (liftEquiv K (fun (i : Sc σ) => e i.val)).toLinearMap
      (splitTensorEquiv σ t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, liftEquiv, LinearEquiv.ofLinear_apply]
    congr 1
    rw [TensorObj.liftMap_tprod]
    simp only [splitTensorEquiv, LinearEquiv.trans_apply]
    show (PiTensorProduct.tmulEquivDep K _).symm
        ((PiTensorProduct.reindex K W (splitEquiv σ).symm) (tprod K (fun i => e i (f i)))) =
      TensorProduct.map _ _ ((PiTensorProduct.tmulEquivDep K _).symm
        ((PiTensorProduct.reindex K V (splitEquiv σ).symm) (tprod K f)))
    rw [PiTensorProduct.reindex_tprod, PiTensorProduct.reindex_tprod]
    rw [PiTensorProduct.tmulEquivDep_symm_apply, PiTensorProduct.tmulEquivDep_symm_apply]
    rw [TensorProduct.map_tmul]
    simp only [Equiv.symm_symm, LinearEquiv.toLinearMap_eq_coe]
    congr 1
    · change _ = (liftEquiv K (fun i : σ.S => e i.val)) (tprod K _)
      simp only [liftEquiv, LinearEquiv.ofLinear_apply, TensorObj.liftMap_tprod]
      rfl
    · change _ = (liftEquiv K (fun i : Sc σ => e i.val)) (tprod K _)
      simp only [liftEquiv, LinearEquiv.ofLinear_apply, TensorObj.liftMap_tprod]
      rfl
  | add x y ihx ihy =>
    simp only [map_add, ihx, ihy]

variable (K)

/-- Naturality of `tensorToDualHom`: it commutes with tensor product maps. -/
theorem tensorToDualHom_naturality {A A' B B' : Type*}
    [AddCommGroup A] [Module K A] [AddCommGroup A'] [Module K A']
    [AddCommGroup B] [Module K B] [AddCommGroup B'] [Module K B']
    (eA : A ≃ₗ[K] A') (eB : B ≃ₗ[K] B') (t : A ⊗[K] B) (f : Dual K A') :
    tensorToDualHom K A' B' (TensorProduct.map eA.toLinearMap eB.toLinearMap t) f =
    eB (tensorToDualHom K A B t (f ∘ₗ eA.toLinearMap)) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    simp [tensorToDualHom]
  | tmul a b =>
    simp only [TensorProduct.map_tmul, tensorToDualHom_tmul, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.map_smul]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy]

variable {K}

/-- Rank is invariant under conjugation by linear equivalences on the codomain. -/
theorem finrank_range_comp_equiv {M N P : Type*}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P]
    (f : M →ₗ[K] N) (g : N ≃ₗ[K] P) :
    Module.finrank K (LinearMap.range (g.toLinearMap.comp f)) =
    Module.finrank K (LinearMap.range f) := by
  have : LinearMap.range (g.toLinearMap.comp f) = Submodule.map g.toLinearMap (LinearMap.range f) := by
    ext x
    simp only [LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply, Submodule.mem_map]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨f y, ⟨y, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩
  rw [this]
  exact LinearEquiv.finrank_map_eq g (LinearMap.range f)

private theorem split_eq_aux (σ : Split (Fin d)) {X Y : TensorObj K d} (iso : TensorIso X Y) :
    splitTensorEquiv σ Y.t =
    TensorProduct.map
      (liftEquiv K (fun (i : σ.S) => iso.equiv i.val)).toLinearMap
      (liftEquiv K (fun (i : Sc σ) => iso.equiv i.val)).toLinearMap
      (splitTensorEquiv σ X.t) := by
  rw [iso.map_t.symm]
  induction X.t using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, liftEquiv, LinearEquiv.ofLinear_apply]
    congr 1
    rw [TensorObj.liftMap_tprod]
    simp only [splitTensorEquiv, LinearEquiv.trans_apply]
    show (PiTensorProduct.tmulEquivDep K _).symm
        ((PiTensorProduct.reindex K Y.V (splitEquiv σ).symm) (tprod K (fun i => iso.equiv i (f i)))) =
      TensorProduct.map _ _ ((PiTensorProduct.tmulEquivDep K _).symm
        ((PiTensorProduct.reindex K X.V (splitEquiv σ).symm) (tprod K f)))
    rw [PiTensorProduct.reindex_tprod, PiTensorProduct.reindex_tprod]
    rw [PiTensorProduct.tmulEquivDep_symm_apply, PiTensorProduct.tmulEquivDep_symm_apply]
    rw [TensorProduct.map_tmul]
    simp only [Equiv.symm_symm, LinearEquiv.toLinearMap_eq_coe]
    congr 1
    · change _ = (liftEquiv K (fun i : σ.S => iso.equiv i.val)) (tprod K _)
      simp only [liftEquiv, LinearEquiv.ofLinear_apply, TensorObj.liftMap_tprod]
      rfl
    · change _ = (liftEquiv K (fun i : Sc σ => iso.equiv i.val)) (tprod K _)
      simp only [liftEquiv, LinearEquiv.ofLinear_apply, TensorObj.liftMap_tprod]
      rfl
  | add x y ihx ihy =>
    simp only [map_add, ihx, ihy]

/-- The main theorem: flattening rank is invariant under tensor isomorphism. -/
theorem flatteningRank_isomorphic (σ : Split (Fin d)) {X Y : TensorObj K d}
    (h : TensorObj.Isomorphic X Y) : flatteningRank σ X = flatteningRank σ Y := by
  obtain ⟨iso⟩ := h
  let eA := liftEquiv K (fun (i : σ.S) => iso.equiv i.val)
  let eB := liftEquiv K (fun (i : Sc σ) => iso.equiv i.val)

  have split_eq : splitTensorEquiv σ Y.t =
      TensorProduct.map eA.toLinearMap eB.toLinearMap (splitTensorEquiv σ X.t) :=
    split_eq_aux σ iso

  have flatteningMap_eq : flatteningMap σ Y =
      eB.toLinearMap.comp ((flatteningMap σ X).comp eA.toLinearMap.dualMap) := by
    ext f
    simp only [flatteningMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [split_eq]
    exact tensorToDualHom_naturality K eA eB (splitTensorEquiv σ X.t) f

  unfold flatteningRank
  rw [flatteningMap_eq, finrank_range_comp_equiv]

  have dualMap_surj : Function.Surjective (eA.toLinearMap.dualMap) := by
    intro g
    use g.comp eA.symm.toLinearMap
    ext a
    simp

  have range_eq : LinearMap.range ((flatteningMap σ X).comp eA.toLinearMap.dualMap) =
      LinearMap.range (flatteningMap σ X) :=
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr dualMap_surj)

  rw [range_eq]

end Isomorphism

end Flattening

namespace Tensor

variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

/-- Flattening rank lifted to the quotient `Tensor K d`.
    This is well-defined since flattening rank is invariant under isomorphism. -/
noncomputable def flatteningRank (σ : Split (Fin d)) : Tensor K d → ℕ :=
  Quotient.lift (fun X => AsymptoticSpectra.flatteningRank σ X)
    (fun _ _ h => flatteningRank_isomorphic σ h)

/-- The real-valued version of flattening rank on `Tensor K d`. -/
noncomputable def flatteningRankReal (σ : Split (Fin d)) : Tensor K d → ℝ :=
  fun x => (flatteningRank σ x : ℝ)

@[simp]
theorem flatteningRank_mk (σ : Split (Fin d)) (X : TensorObj K d) :
    flatteningRank σ (Tensor.toTensor X) = AsymptoticSpectra.flatteningRank σ X := by
  simp only [flatteningRank, Tensor.toTensor, Quotient.lift_mk]

@[simp]
theorem flatteningRankReal_mk (σ : Split (Fin d)) (X : TensorObj K d) :
    flatteningRankReal σ (Tensor.toTensor X) = ↑(AsymptoticSpectra.flatteningRank σ X) := by
  simp only [flatteningRankReal, flatteningRank_mk]

end Tensor

end AsymptoticSpectra
