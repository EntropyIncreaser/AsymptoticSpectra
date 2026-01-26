import AsymptoticSpectra.Tensor.Tensor
import AsymptoticSpectra.Tensor.BaseChange
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import AsymptoticSpectra.Spectrum
import AsymptoticSpectra.Structures

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

/-- The rank of `f ⊗ g` is the product of the ranks of `f` and `g`. -/
theorem finrank_range_map {A B C D : Type*}
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]
    [FiniteDimensional K A] [FiniteDimensional K B]
    (f : A →ₗ[K] C) (g : B →ₗ[K] D) :
    finrank K (LinearMap.range (TensorProduct.map f g)) =
    finrank K (LinearMap.range f) * finrank K (LinearMap.range g) := by
  let f' := f.rangeRestrict
  let g' := g.rangeRestrict
  let i := (LinearMap.range f).subtype
  let j := (LinearMap.range g).subtype
  have h_decomp : TensorProduct.map f g = (TensorProduct.map i j).comp (TensorProduct.map f' g') := by
    apply TensorProduct.ext
    ext a b
    simp [f', g', i, j]
  rw [h_decomp]
  rw [LinearMap.range_comp_of_range_eq_top]
  swap
  · -- Show map f' g' is surjective
    rw [LinearMap.range_eq_top]
    intro z
    induction z using TensorProduct.induction_on with
    | zero => use 0; simp
    | tmul x y =>
      obtain ⟨a, hx⟩ := f.surjective_rangeRestrict x
      obtain ⟨b, hy⟩ := g.surjective_rangeRestrict y
      use a ⊗ₜ b
      rw [← hx, ← hy]
      simp only [TensorProduct.map_tmul]
      rfl
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      use a + b
      rw [← ha, ← hb]
      simp only [map_add]


  -- map i j is injective
  have h_inj : Function.Injective (TensorProduct.map i j) := by
    -- In vector spaces, injective linear maps have left inverses
    obtain ⟨i_inv, hi⟩ := LinearMap.exists_leftInverse_of_injective i (LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _))
    obtain ⟨j_inv, hj⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _))
    let m_inv := TensorProduct.map i_inv j_inv
    have h_inv : Function.LeftInverse m_inv (TensorProduct.map i j) := by
      intro x
      dsimp [m_inv]
      rw [TensorProduct.map_map, hi, hj, TensorProduct.map_id]
      rfl
    exact h_inv.injective

  -- Rank of range of injective map = rank of domain
  rw [← Module.finrank_tensorProduct]
  apply LinearEquiv.finrank_eq
  apply (LinearEquiv.ofInjective (TensorProduct.map i j) h_inj).symm

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
    simp only [map_smul, liftEquiv]
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

namespace AsymptoticSpectra.Tensor

variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

variable (σ : Split (Fin d))

theorem flatteningRank_add
    (x y : Tensor K d) :
    flatteningRank σ (x + y)
      = flatteningRank σ x
      + flatteningRank σ y := by
  -- Lift to TensorObj representatives
  induction x using Quotient.inductionOn with | _ X =>
  induction y using Quotient.inductionOn with | _ Y =>
  -- Tensor.add is defined via Quotient.liftOn₂
  change flatteningRank σ (Tensor.add (Tensor.toTensor X) (Tensor.toTensor Y)) =
         flatteningRank σ (Tensor.toTensor X) + flatteningRank σ (Tensor.toTensor Y)
  simp only [Tensor.add, flatteningRank_mk]
  -- Now the goal is: AsymptoticSpectra.flatteningRank σ (X + Y) =
  --                  AsymptoticSpectra.flatteningRank σ X + AsymptoticSpectra.flatteningRank σ Y
  --
  -- Mathematical outline:
  -- 1. (X + Y).V i = X.V i × Y.V i (direct sum of vector spaces)
  -- 2. (X + Y).t = liftMap inl X.t + liftMap inr Y.t
  --
  -- 3. splitTensorEquiv σ is linear, so:
  --    splitTensorEquiv σ (X + Y).t =
  --      splitTensorEquiv σ (liftMap inl X.t) + splitTensorEquiv σ (liftMap inr Y.t)
  --
  -- 4. The key naturality: splitTensorEquiv σ (liftMap f t) relates to
  --    (map f_S ⊗ map f_Sc) (splitTensorEquiv σ t)
  --    This follows from splitTensorEquiv_naturality.
  --
  -- 5. For the direct sum structure, the flattening maps have orthogonal ranges:
  --    - flatteningMap σ (X + Y) applied to (inl ∘ f) gives output in (inl image)
  --    - flatteningMap σ (X + Y) applied to (inr ∘ g) gives output in (inr image)
  --
  -- 6. The range of the sum is the direct sum of ranges, so:
  --    finrank(range(flatteningMap σ (X + Y))) =
  --      finrank(range(flatteningMap σ X)) + finrank(range(flatteningMap σ Y))
  --
  -- This proof requires establishing the naturality of flatteningMap with respect to
  -- the direct sum structure and showing the ranges are in direct sum position.
  sorry

/-- Auxiliary bilinear map for the distributivity construction.
    For fixed v' and w', the map (v, w) ↦ (tprod (update v' i v)) ⊗ (tprod (update w' i w))
    is bilinear. -/
private noncomputable def piTensorDistribAuxBilin {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (i : ι) (v' : ∀ j, V j) (w' : ∀ j, W j) :
    V i →ₗ[K] W i →ₗ[K] (PiTensorProduct K V) ⊗[K] (PiTensorProduct K W) where
  toFun v := {
    toFun := fun w => tprod K (Function.update v' i v) ⊗ₜ[K] tprod K (Function.update w' i w)
    map_add' := fun w₁ w₂ => by simp only [MultilinearMap.map_update_add, tmul_add]
    map_smul' := fun c w => by simp only [MultilinearMap.map_update_smul, tmul_smul, RingHom.id_apply]
  }
  map_add' v₁ v₂ := by
    ext w; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
      MultilinearMap.map_update_add, add_tmul]
  map_smul' c v := by
    ext w; simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply,
      MultilinearMap.map_update_smul, smul_tmul']

/-- For fixed v' and w', the linear map on V i ⊗ W i induced by the bilinear map. -/
private noncomputable def piTensorDistribAuxLin {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (i : ι) (v' : ∀ j, V j) (w' : ∀ j, W j) :
    V i ⊗[K] W i →ₗ[K] (PiTensorProduct K V) ⊗[K] (PiTensorProduct K W) :=
  TensorProduct.lift (piTensorDistribAuxBilin i v' w')

@[simp]
private theorem piTensorDistribAuxLin_tmul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (i : ι) (v' : ∀ j, V j) (w' : ∀ j, W j) (v : V i) (w : W i) :
    piTensorDistribAuxLin i v' w' (v ⊗ₜ[K] w) =
      tprod K (Function.update v' i v) ⊗ₜ[K] tprod K (Function.update w' i w) := by
  simp only [piTensorDistribAuxLin, TensorProduct.lift.tmul, piTensorDistribAuxBilin,
    LinearMap.coe_mk, AddHom.coe_mk]

/-- The bilinear map (v, w) ↦ (tprod v) ⊗ (tprod w) is multilinear in v and w.
    This is a 2n-linear map when ι has n elements. -/
private noncomputable def tprodTensorBilin {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] :
    MultilinearMap K V (MultilinearMap K W ((PiTensorProduct K V) ⊗[K] (PiTensorProduct K W))) where
  toFun v := {
    toFun := fun w => tprod K v ⊗ₜ[K] tprod K w
    map_update_add' := fun w i x y => by
      simp only [MultilinearMap.map_update_add, tmul_add]
    map_update_smul' := fun w i c x => by
      simp only [MultilinearMap.map_update_smul, tmul_smul]
  }
  map_update_add' v i x y := by
    ext w
    simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply,
      MultilinearMap.map_update_add, add_tmul]
  map_update_smul' v i c x := by
    ext w
    simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply,
      MultilinearMap.map_update_smul, smul_tmul']

/-- Existence of the multilinear map M : (∀ i, V i ⊗ W i) →ₘ (⨂V) ⊗ (⨂W)
    satisfying M (fun i => v i ⊗ₜ w i) = tprod v ⊗ₜ tprod w. -/
private theorem piTensorDistribMultilinear_exists {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] :
    ∃ M : MultilinearMap K (fun i => V i ⊗[K] W i)
            ((PiTensorProduct K V) ⊗[K] (PiTensorProduct K W)),
      ∀ v w, M (fun i => v i ⊗ₜ[K] w i) = tprod K v ⊗ₜ[K] tprod K w := by
  induction h : Fintype.card ι using Nat.strong_induction_on generalizing ι V W with
  | _ n ih =>
    cases isEmpty_or_nonempty ι with
    | inl hι =>
      haveI : IsEmpty ι := hι
      refine ⟨⟨fun _ => (PiTensorProduct.isEmptyEquiv ι).symm 1 ⊗ₜ[K]
                        (PiTensorProduct.isEmptyEquiv ι).symm 1,
               fun _ i => isEmptyElim i, fun _ i => isEmptyElim i⟩, ?_⟩
      intro v w
      have hv : tprod K v = (PiTensorProduct.isEmptyEquiv ι).symm 1 := by
        have : v = isEmptyElim := funext (fun i => isEmptyElim i)
        rw [this, PiTensorProduct.isEmptyEquiv_symm_apply, one_smul]
      have hw : tprod K w = (PiTensorProduct.isEmptyEquiv ι).symm 1 := by
        have : w = isEmptyElim := funext (fun i => isEmptyElim i)
        rw [this, PiTensorProduct.isEmptyEquiv_symm_apply, one_smul]
      simp only [MultilinearMap.coe_mk, hv, hw]
    | inr hι =>
      haveI : Nonempty ι := hι
      haveI : Inhabited ι := Classical.inhabited_of_nonempty hι

      obtain ⟨α, e⟩ := Equiv.sigmaEquivOptionOfInhabited ι
      haveI : Fintype α := fintypeOfOptionEquiv e
      haveI : DecidableEq α := Classical.decEq α

      have hα_lt : Fintype.card α < n := by
        have h1 : Fintype.card ι = Fintype.card (Option α) := Fintype.card_congr e
        rw [Fintype.card_option] at h1
        omega

      let V' : α → Type _ := fun a => V (e.symm (some a))
      let W' : α → Type _ := fun a => W (e.symm (some a))
      obtain ⟨M', hM'⟩ := ih (Fintype.card α) hα_lt (V := V') (W := W') rfl

      let i₀ : ι := e.symm none

      -- Key equivalence: Option α ≃ α ⊕ PUnit (some ↔ inl, none ↔ inr)
      let optSum : Option α ≃ α ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit α

      -- Define the type families over the sum type
      let Vsum : α ⊕ PUnit.{1} → Type _ := fun s => V (e.symm (optSum.symm s))
      let Wsum : α ⊕ PUnit.{1} → Type _ := fun s => W (e.symm (optSum.symm s))

      let eSum : ι ≃ α ⊕ PUnit.{1} := e.trans optSum

      let subsingleV := (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : PUnit.{1} => V i₀) PUnit.unit).symm
      let subsingleW := (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : PUnit.{1} => W i₀) PUnit.unit).symm

      -- Define combineV and combineW as functions (we'll prove they're bilinear via sorry)
      let combineV_fun : V i₀ → PiTensorProduct K V' → PiTensorProduct K V := fun v₀ tV' =>
        (PiTensorProduct.reindex K V eSum).symm
          ((PiTensorProduct.tmulEquivDep K Vsum) (tV' ⊗ₜ[K] subsingleV v₀))

      let combineW_fun : W i₀ → PiTensorProduct K W' → PiTensorProduct K W := fun w₀ tW' =>
        (PiTensorProduct.reindex K W eSum).symm
          ((PiTensorProduct.tmulEquivDep K Wsum) (tW' ⊗ₜ[K] subsingleW w₀))

      have combineW_add : ∀ tW' x y, combineW_fun (x + y) tW' = combineW_fun x tW' + combineW_fun y tW' := by
        intro tW' x y
        unfold combineW_fun
        simp only [map_add, tmul_add]
      have combineW_smul : ∀ tW' (c : K) x, combineW_fun (c • x) tW' = c • combineW_fun x tW' := by
        intro tW' c x
        unfold combineW_fun
        simp only [map_smul, tmul_smul]
      have combineV_add : ∀ tV' x y, combineV_fun (x + y) tV' = combineV_fun x tV' + combineV_fun y tV' := by
        intro tV' x y
        unfold combineV_fun
        simp only [map_add, tmul_add]
      have combineV_smul : ∀ tV' (c : K) x, combineV_fun (c • x) tV' = c • combineV_fun x tV' := by
        intro tV' c x
        unfold combineV_fun
        simp only [map_smul, tmul_smul]

      -- Linearity in the second argument (tW' and tV')
      have combineW_add' : ∀ w₀ x y, combineW_fun w₀ (x + y) = combineW_fun w₀ x + combineW_fun w₀ y := by
        intro w₀ x y
        unfold combineW_fun
        simp only [add_tmul, map_add]
      have combineW_smul' : ∀ w₀ (c : K) x, combineW_fun w₀ (c • x) = c • combineW_fun w₀ x := by
        intro w₀ c x
        unfold combineW_fun
        rw [TensorProduct.smul_tmul, tmul_smul, map_smul, map_smul]
      have combineV_add' : ∀ v₀ x y, combineV_fun v₀ (x + y) = combineV_fun v₀ x + combineV_fun v₀ y := by
        intro v₀ x y
        unfold combineV_fun
        simp only [add_tmul, map_add]
      have combineV_smul' : ∀ v₀ (c : K) x, combineV_fun v₀ (c • x) = c • combineV_fun v₀ x := by
        intro v₀ c x
        unfold combineV_fun
        rw [TensorProduct.smul_tmul, tmul_smul, map_smul, map_smul]

      let innerBilin : (PiTensorProduct K V') →ₗ[K] (PiTensorProduct K W') →ₗ[K]
          (V i₀ →ₗ[K] W i₀ →ₗ[K] (PiTensorProduct K V) ⊗[K] (PiTensorProduct K W)) :=
        { toFun := fun tV' =>
            { toFun := fun tW' =>
                { toFun := fun v₀ =>
                    { toFun := fun w₀ => combineV_fun v₀ tV' ⊗ₜ[K] combineW_fun w₀ tW'
                      map_add' := fun x y => by simp only [combineW_add, tmul_add]
                      map_smul' := fun c x => by simp only [combineW_smul, tmul_smul, RingHom.id_apply] }
                  map_add' := fun x y => by ext w₀; simp only [LinearMap.coe_mk, AddHom.coe_mk, combineV_add, add_tmul, LinearMap.add_apply]
                  map_smul' := fun c x => by ext w₀; simp only [LinearMap.coe_mk, AddHom.coe_mk, combineV_smul, smul_tmul', RingHom.id_apply, LinearMap.smul_apply] }
              map_add' := fun x y => by
                ext v₀ w₀
                simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
                rw [combineW_add', tmul_add]
              map_smul' := fun c x => by
                ext v₀ w₀
                simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply]
                rw [combineW_smul', tmul_smul] }
          map_add' := fun x y => by
            apply PiTensorProduct.ext
            ext tW' v₀ w₀
            simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply, LinearMap.coe_mk,
              AddHom.coe_mk, combineV_add', add_tmul]
          map_smul' := fun c x => by
            apply PiTensorProduct.ext
            ext tW' v₀ w₀
            simp only [LinearMap.compMultilinearMap_apply, LinearMap.smul_apply, LinearMap.coe_mk,
              AddHom.coe_mk, RingHom.id_apply, combineV_smul', smul_tmul'] }

      use {
        toFun := fun f =>
          let f_none : V i₀ ⊗[K] W i₀ := f i₀
          let f_some : ∀ a : α, V' a ⊗[K] W' a := fun a => f (e.symm (some a))
          let ih_result := M' f_some
          let step1 := TensorProduct.lift innerBilin ih_result
          TensorProduct.lift step1 f_none
        map_update_add' := fun f i x y => by
          simp only
          by_cases hi : i = i₀
          · subst hi
            simp only [Function.update_self]
            have hne : ∀ a, e.symm (some a) ≠ i₀ := by
              intro a h
              have : e (e.symm (some a)) = e i₀ := by rw [h]
              simp only [Equiv.apply_symm_apply, i₀] at this
              cases this
            have h_some : ∀ a, Function.update f i₀ (x + y) (e.symm (some a)) = f (e.symm (some a)) :=
              fun a => Function.update_of_ne (hne a) (x + y) f
            have h_some_x : ∀ a, Function.update f i₀ x (e.symm (some a)) = f (e.symm (some a)) :=
              fun a => Function.update_of_ne (hne a) x f
            have h_some_y : ∀ a, Function.update f i₀ y (e.symm (some a)) = f (e.symm (some a)) :=
              fun a => Function.update_of_ne (hne a) y f
            simp only [h_some, h_some_x, h_some_y]
            rw [map_add]
          · have h_none : Function.update f i (x + y) i₀ = f i₀ := Function.update_of_ne (Ne.symm hi) (x + y) f
            have h_none_x : Function.update f i x i₀ = f i₀ := Function.update_of_ne (Ne.symm hi) x f
            have h_none_y : Function.update f i y i₀ = f i₀ := Function.update_of_ne (Ne.symm hi) y f
            simp only [h_none, h_none_x, h_none_y]
            have hi' : ∃ a, i = e.symm (some a) := by
              cases he : e i with
              | none => exfalso; apply hi; simp only [i₀]; rw [← he]; simp
              | some a => exact ⟨a, by simp [← he]⟩
            obtain ⟨a₀, ha₀⟩ := hi'
            subst ha₀
            have hM'_add := M'.map_update_add (fun a => f (e.symm (some a))) a₀ x y
            simp only at hM'_add ⊢
            have h_update : ∀ z : V' a₀ ⊗[K] W' a₀, (fun a => Function.update f (e.symm (some a₀)) z (e.symm (some a))) =
                Function.update (fun a => f (e.symm (some a))) a₀ z := by
              intro z; ext a
              by_cases ha : a = a₀
              · subst ha; simp [Function.update_self]
              · rw [Function.update_of_ne ha, Function.update_of_ne]
                intro h; apply ha; exact Option.some_injective α (e.symm.injective h)
            simp only [h_update]
            rw [hM'_add, map_add]
            have lift_add : ∀ (g₁ g₂ : V i₀ →ₗ[K] W i₀ →ₗ[K] PiTensorProduct K V ⊗[K] PiTensorProduct K W),
                TensorProduct.lift (g₁ + g₂) = TensorProduct.lift g₁ + TensorProduct.lift g₂ := by
              intro g₁ g₂
              change TensorProduct.uncurry _ _ _ _ (g₁ + g₂) = TensorProduct.uncurry _ _ _ _ g₁ + TensorProduct.uncurry _ _ _ _ g₂
              rw [map_add]
            rw [lift_add, LinearMap.add_apply]
        map_update_smul' := fun f i c x => by
          simp only
          by_cases hi : i = i₀
          · subst hi
            simp only [Function.update_self]
            have hne : ∀ a, e.symm (some a) ≠ i₀ := by
              intro a h
              have : e (e.symm (some a)) = e i₀ := by rw [h]
              simp only [Equiv.apply_symm_apply, i₀] at this
              cases this
            have h_some : ∀ a, Function.update f i₀ (c • x) (e.symm (some a)) = f (e.symm (some a)) :=
              fun a => Function.update_of_ne (hne a) (c • x) f
            have h_some_x : ∀ a, Function.update f i₀ x (e.symm (some a)) = f (e.symm (some a)) :=
              fun a => Function.update_of_ne (hne a) x f
            simp only [h_some, h_some_x]
            rw [map_smul]
          · have h_none : Function.update f i (c • x) i₀ = f i₀ := Function.update_of_ne (Ne.symm hi) (c • x) f
            have h_none_x : Function.update f i x i₀ = f i₀ := Function.update_of_ne (Ne.symm hi) x f
            simp only [h_none, h_none_x]
            have hi' : ∃ a, i = e.symm (some a) := by
              cases he : e i with
              | none => exfalso; apply hi; simp only [i₀]; rw [← he]; simp
              | some a => exact ⟨a, by simp [← he]⟩
            obtain ⟨a₀, ha₀⟩ := hi'
            subst ha₀
            have hM'_smul := M'.map_update_smul (fun a => f (e.symm (some a))) a₀ c x
            simp only at hM'_smul ⊢
            have h_update : ∀ z : V' a₀ ⊗[K] W' a₀, (fun a => Function.update f (e.symm (some a₀)) z (e.symm (some a))) =
                Function.update (fun a => f (e.symm (some a))) a₀ z := by
              intro z; ext a
              by_cases ha : a = a₀
              · subst ha; simp [Function.update_self]
              · rw [Function.update_of_ne ha, Function.update_of_ne]
                intro h; apply ha; exact Option.some_injective α (e.symm.injective h)
            simp only [h_update]
            rw [hM'_smul, map_smul]
            have lift_smul : ∀ (c : K) (g : V i₀ →ₗ[K] W i₀ →ₗ[K] PiTensorProduct K V ⊗[K] PiTensorProduct K W),
                TensorProduct.lift (c • g) = c • TensorProduct.lift g := by
              intro c g
              change TensorProduct.uncurry _ _ _ _ (c • g) = c • TensorProduct.uncurry _ _ _ _ g
              rw [map_smul]
            rw [lift_smul, LinearMap.smul_apply]
      }
      intro v w
      simp only [MultilinearMap.coe_mk]
      let v' : ∀ a : α, V' a := fun a => v (e.symm (some a))
      let w' : ∀ a : α, W' a := fun a => w (e.symm (some a))
      have ih_eq : M' (fun a => v' a ⊗ₜ[K] w' a) = (PiTensorProduct.tprod K) v' ⊗ₜ[K] (PiTensorProduct.tprod K) w' := hM' v' w'
      conv_lhs => simp only [TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, ih_eq]
      rw [ih_eq, TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
      show combineV_fun (v i₀) ((PiTensorProduct.tprod K) v') ⊗ₜ[K] combineW_fun (w i₀) ((PiTensorProduct.tprod K) w') =
           (PiTensorProduct.tprod K) v ⊗ₜ[K] (PiTensorProduct.tprod K) w
      have hcombineV : combineV_fun (v i₀) ((PiTensorProduct.tprod K) v') = (PiTensorProduct.tprod K) v := by
        simp only [combineV_fun, subsingleV, PiTensorProduct.subsingletonEquiv_symm_apply']
        rw [show ((PiTensorProduct.tprod K) v' : PiTensorProduct K V') =
            (PiTensorProduct.tprod K (fun a => v' a) : ⨂[K] (a : α), Vsum (Sum.inl a)) from rfl]
        rw [show ((PiTensorProduct.tprod K) (fun _ : PUnit => v i₀) : ⨂[K] (_ : PUnit), V i₀) =
            (PiTensorProduct.tprod K (fun _ : PUnit => v i₀) : ⨂[K] (u : PUnit), Vsum (Sum.inr u)) from rfl]
        rw [PiTensorProduct.tmulEquivDep_apply, LinearEquiv.symm_apply_eq, PiTensorProduct.reindex_tprod]
        congr 1; ext s
        cases s with
        | inl a => simp only [eSum, Equiv.symm_trans_apply, optSum, Equiv.optionEquivSumPUnit_symm_inl, v']
        | inr u => simp only [eSum, Equiv.symm_trans_apply, optSum, Equiv.optionEquivSumPUnit_symm_inr, i₀]
      have hcombineW : combineW_fun (w i₀) ((PiTensorProduct.tprod K) w') = (PiTensorProduct.tprod K) w := by
        simp only [combineW_fun, subsingleW, PiTensorProduct.subsingletonEquiv_symm_apply']
        rw [show ((PiTensorProduct.tprod K) w' : PiTensorProduct K W') =
            (PiTensorProduct.tprod K (fun a => w' a) : ⨂[K] (a : α), Wsum (Sum.inl a)) from rfl]
        rw [show ((PiTensorProduct.tprod K) (fun _ : PUnit => w i₀) : ⨂[K] (_ : PUnit), W i₀) =
            (PiTensorProduct.tprod K (fun _ : PUnit => w i₀) : ⨂[K] (u : PUnit), Wsum (Sum.inr u)) from rfl]
        rw [PiTensorProduct.tmulEquivDep_apply, LinearEquiv.symm_apply_eq, PiTensorProduct.reindex_tprod]
        have heq : (fun (s : α ⊕ PUnit) => Sum.rec w' (fun _ => w i₀) s) =
                   (fun (s : α ⊕ PUnit) => w (eSum.symm s)) := by funext s; cases s <;> rfl
        simp only [heq]; rfl
      rw [hcombineV, hcombineW]

/-- The multilinear map M : (∀ i, V i ⊗ W i) →ₘ (⨂V) ⊗ (⨂W) that is the left inverse
    of the interchange map. Satisfies M (fun i => v i ⊗ₜ w i) = tprod v ⊗ₜ tprod w.

    Defined via Classical.choose from the existence theorem. -/
private noncomputable def piTensorDistribMultilinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] :
    MultilinearMap K (fun i => V i ⊗[K] W i)
      ((PiTensorProduct K V) ⊗[K] (PiTensorProduct K W)) :=
  Classical.choose (piTensorDistribMultilinear_exists (K := K))

/-- The key property of piTensorDistribMultilinear: on pure tensor inputs,
    it produces tprod v ⊗ₜ tprod w. -/
private theorem piTensorDistribMultilinear_pure {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    piTensorDistribMultilinear (fun i => v i ⊗ₜ[K] w i) = tprod K v ⊗ₜ[K] tprod K w :=
  Classical.choose_spec (piTensorDistribMultilinear_exists (K := K)) v w

/-- The interchange map (lifted to tensor product) is injective. -/
private theorem piTensorDistribInvFun_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] :
    Function.Injective (TensorProduct.lift (TensorObj.interchange (K := K) (V := V) (W := W))) := by
  induction h : Fintype.card ι using Nat.strong_induction_on generalizing ι V W with
  | _ n ih =>
    cases isEmpty_or_nonempty ι with
    | inl hι =>
      haveI : IsEmpty ι := hι
      intro x y hxy
      let eV : PiTensorProduct K V ≃ₗ[K] K := PiTensorProduct.isEmptyEquiv ι
      let eW : PiTensorProduct K W ≃ₗ[K] K := PiTensorProduct.isEmptyEquiv ι
      let eVW : PiTensorProduct K (fun i => V i ⊗[K] W i) ≃ₗ[K] K :=
        PiTensorProduct.isEmptyEquiv ι
      let eTensor : (PiTensorProduct K V) ⊗[K] (PiTensorProduct K W) ≃ₗ[K] K :=
        TensorProduct.congr eV eW ≪≫ₗ TensorProduct.lid K K
      have h1 : eTensor x = eTensor y := by
        have hcomm : ∀ t, eVW (TensorProduct.lift TensorObj.interchange t) = eTensor t := by
          intro t
          induction t using TensorProduct.induction_on with
          | zero => simp
          | tmul a b =>
            simp only [TensorProduct.lift.tmul]
            induction a using PiTensorProduct.induction_on with
            | smul_tprod c v =>
              induction b using PiTensorProduct.induction_on with
              | smul_tprod c' w =>
                simp only [map_smul, LinearMap.smul_apply]
                rw [TensorObj.interchange_tprod_K]
                simp only [smul_eq_mul]
                have heVW : eVW (tprod K fun i => v i ⊗ₜ[K] w i) = 1 :=
                  PiTensorProduct.isEmptyEquiv_apply_tprod ι _
                have heV1 : eV (tprod K v) = 1 := PiTensorProduct.isEmptyEquiv_apply_tprod ι _
                have heW1 : eW (tprod K w) = 1 := PiTensorProduct.isEmptyEquiv_apply_tprod ι _
                calc c' * (c * eVW (tprod K fun i => v i ⊗ₜ[K] w i))
                    = c' * (c * 1) := by rw [heVW]
                  _ = c * c' := by ring
                  _ = eV (c • tprod K v) * eW (c' • tprod K w) := by
                      rw [LinearEquiv.map_smul, LinearEquiv.map_smul, heV1, heW1,
                          smul_eq_mul, smul_eq_mul, mul_one, mul_one]
                  _ = eV (c • tprod K v) • eW (c' • tprod K w) := by
                      rw [smul_eq_mul]
                  _ = (TensorProduct.congr eV eW ≪≫ₗ TensorProduct.lid K K)
                        ((c • tprod K v) ⊗ₜ[K] (c' • tprod K w)) := by
                      simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul,
                        TensorProduct.lid_tmul]
              | add x y ihx ihy =>
                simp only [tmul_add, map_add]
                rw [ihx, ihy]
            | add x y ihx ihy =>
              simp only [add_tmul, map_add, LinearMap.add_apply]
              rw [ihx, ihy]
          | add x y ihx ihy => simp only [map_add, ihx, ihy]
        rw [← hcomm x, ← hcomm y, hxy]
      exact eTensor.injective h1
    | inr hι =>
      haveI : Nonempty ι := hι

      let L : PiTensorProduct K (fun i => V i ⊗[K] W i) →ₗ[K]
              (PiTensorProduct K V) ⊗[K] (PiTensorProduct K W) :=
        PiTensorProduct.lift piTensorDistribMultilinear

      apply Function.LeftInverse.injective (g := L)
      intro t

      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul t₁ t₂ =>
        induction t₁ using PiTensorProduct.induction_on with
        | smul_tprod c v =>
          induction t₂ using PiTensorProduct.induction_on with
          | smul_tprod c' w =>
            simp only [TensorProduct.lift.tmul, map_smul, LinearMap.smul_apply]
            rw [TensorObj.interchange_tprod_K, PiTensorProduct.lift.tprod]
            rw [piTensorDistribMultilinear_pure]
            rw [smul_smul, mul_comm, ← smul_smul]
            rw [smul_tmul', smul_tmul]
            rfl
          | add x y ihx ihy =>
            simp only [tmul_add, map_add] at ihx ihy ⊢
            rw [ihx, ihy]
        | add x y ihx ihy =>
          simp only [add_tmul, map_add] at ihx ihy ⊢
          rw [ihx, ihy]
      | add x y ihx ihy =>
        simp only [map_add, ihx, ihy]

/-- Helper lemma: interchange is surjective onto tprod of pure tensors. -/
private theorem interchange_surj_pure {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    ∃ t : (PiTensorProduct K V) ⊗[K] (PiTensorProduct K W),
      TensorProduct.lift TensorObj.interchange t = tprod K (fun i => v i ⊗ₜ[K] w i) :=
  ⟨tprod K v ⊗ₜ[K] tprod K w, by simp [TensorObj.interchange_tprod_K]⟩

/-- For any f : ∀ i, V i ⊗ W i, there exists a unique preimage under the interchange map. -/
private theorem piTensorDistribAux_exists_unique {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i ⊗[K] W i) :
    ∃! t : (PiTensorProduct K V) ⊗[K] (PiTensorProduct K W),
      TensorProduct.lift TensorObj.interchange t = tprod K f := by
  refine ⟨?wit, ?prop, ?unique⟩
  case wit =>
      exact Classical.epsilon (fun t => TensorProduct.lift TensorObj.interchange t = tprod K f)
  case prop =>
    have h_exists : ∃ t, TensorProduct.lift TensorObj.interchange t = tprod K f := by
      have h_surj : Function.Surjective (TensorProduct.lift
          (TensorObj.interchange (K := K) (V := V) (W := W))) := by
        rw [← LinearMap.range_eq_top, eq_top_iff]
        intro x _
        induction x using PiTensorProduct.induction_on with
        | smul_tprod c g =>
          apply Submodule.smul_mem
          have h_pure : ∀ (v : ∀ i, V i) (w : ∀ i, W i),
              tprod K (fun i => v i ⊗ₜ[K] w i) ∈ LinearMap.range (TensorProduct.lift
                (TensorObj.interchange (K := K) (V := V) (W := W))) := by
            intro v w
            exact ⟨tprod K v ⊗ₜ[K] tprod K w, by simp [TensorObj.interchange_tprod_K]⟩
          let R := LinearMap.range (TensorProduct.lift
                (TensorObj.interchange (K := K) (V := V) (W := W)))
          suffices h_main : ∀ g' : ∀ i, V i ⊗[K] W i, tprod K g' ∈ R by exact h_main g
          intro g'
          revert g'
          have h_ind : ∀ S : Finset ι, ∀ g' : ∀ i, V i ⊗[K] W i,
              (∀ i, i ∉ S → ∃ v w, g' i = v ⊗ₜ[K] w) → tprod K g' ∈ R := by
            intro S
            induction S using Finset.induction with
            | empty =>
              intro g' h_all_pure
              have h_pure_all : ∀ i, ∃ v w, g' i = v ⊗ₜ[K] w := fun i =>
                h_all_pure i (by simp)
              choose v w hg using h_pure_all
              have : g' = fun i => v i ⊗ₜ[K] w i := funext hg
              rw [this]
              exact h_pure v w
            | insert i₀ S' hi₀ ih =>
              intro g' h_pure_outside
              have h_submod : ∀ t : V i₀ ⊗[K] W i₀,
                  tprod K (Function.update g' i₀ t) ∈ R := by
                intro t
                induction t using TensorProduct.induction_on with
                | zero =>
                  convert Submodule.zero_mem R
                  have : (Function.update g' i₀ 0) i₀ = 0 := Function.update_self i₀ 0 g'
                  exact MultilinearMap.map_coord_zero (tprod K) i₀ this
                | tmul v w =>
                  apply ih
                  intro i hi_not_in_S'
                  by_cases h : i = i₀
                  · subst h
                    refine ⟨v, w, ?_⟩
                    simp only [Function.update_self]
                  · rw [Function.update_of_ne h]
                    apply h_pure_outside
                    simp only [Finset.mem_insert, not_or]
                    exact ⟨h, hi_not_in_S'⟩
                | add x y ihx ihy =>
                  have h_eq : tprod K (Function.update g' i₀ (x + y)) =
                      tprod K (Function.update g' i₀ x) +
                      tprod K (Function.update g' i₀ y) :=
                    MultilinearMap.map_update_add (tprod K) g' i₀ x y
                  rw [h_eq]
                  exact Submodule.add_mem R ihx ihy
              convert h_submod (g' i₀) using 2
              simp only [Function.update_eq_self]
          intro g'
          apply h_ind Finset.univ g'
          intro i hi
          exact absurd (Finset.mem_univ i) hi
        | add x y ihx ihy =>
          exact Submodule.add_mem _ (ihx trivial) (ihy trivial)
      exact h_surj (tprod K f)
    exact Classical.epsilon_spec h_exists
  case unique =>
    intro y hy
    have h_exists' : ∃ t, TensorProduct.lift TensorObj.interchange t = tprod K f := ⟨y, hy⟩
    have h_wit : TensorProduct.lift TensorObj.interchange
        (Classical.epsilon (fun t => TensorProduct.lift TensorObj.interchange t = tprod K f)) =
        tprod K f := Classical.epsilon_spec h_exists'
    have h_eq : TensorProduct.lift TensorObj.interchange y =
        TensorProduct.lift TensorObj.interchange
          (Classical.epsilon (fun t => TensorProduct.lift TensorObj.interchange t = tprod K f)) :=
      hy.trans h_wit.symm
    exact piTensorDistribInvFun_injective h_eq

/-- Auxiliary multilinear map for the distributivity construction.

Given a family of elements `t : ∀ i, V i ⊗[K] W i`, we want to produce an element of
`(⨂[K] i, V i) ⊗[K] (⨂[K] i, W i)`.

The map is multilinear in the sense that it's linear in each `t i` component.
On pure tensors `t i = v i ⊗ w i`, it gives `(⊗ᵢ v i) ⊗ (⊗ᵢ w i)`.

The key insight is that the map `(v, w) ↦ (tprod v) ⊗ (tprod w)` is multilinear
in both v and w. For each index i, fixing the other components, the map
`(vᵢ, wᵢ) ↦ result` is bilinear, hence factors through `Vᵢ ⊗ Wᵢ`.

The construction uses the universal property of PiTensorProduct combined with
TensorProduct.lift at each index. -/
private noncomputable def piTensorDistribAux {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] :
    MultilinearMap K (fun i => V i ⊗[K] W i)
      ((PiTensorProduct K V) ⊗[K] (PiTensorProduct K W)) where
  toFun f :=
    -- For f : ∀ i, V i ⊗[K] W i, we define the result as the unique preimage
    -- of tprod K f under the interchange map.
    (piTensorDistribAux_exists_unique f).choose
  map_update_add' f i x y := by
    -- We need to show linearity in the i-th slot.
    -- By uniqueness, it suffices to show that the sum of preimages maps to the
    -- sum of the tprod values.
    have h_unique_sum := (piTensorDistribAux_exists_unique (Function.update f i (x + y))).choose_spec
    have h_unique_x := (piTensorDistribAux_exists_unique (Function.update f i x)).choose_spec
    have h_unique_y := (piTensorDistribAux_exists_unique (Function.update f i y)).choose_spec
    have h_add : tprod K (Function.update f i (x + y)) =
        tprod K (Function.update f i x) + tprod K (Function.update f i y) :=
      MultilinearMap.map_update_add (tprod K) f i x y
    -- The sum of preimages maps to the sum of images
    have h_sum_maps : TensorProduct.lift TensorObj.interchange
        ((piTensorDistribAux_exists_unique (Function.update f i x)).choose +
         (piTensorDistribAux_exists_unique (Function.update f i y)).choose) =
        tprod K (Function.update f i (x + y)) := by
      rw [map_add, h_unique_x.1, h_unique_y.1, ← h_add]
    -- By uniqueness, the preimage of the sum equals the sum of preimages
    exact (piTensorDistribAux_exists_unique (Function.update f i (x + y))).unique
      h_unique_sum.1 h_sum_maps
  map_update_smul' f i c x := by
    have h_unique_smul := (piTensorDistribAux_exists_unique (Function.update f i (c • x))).choose_spec
    have h_unique_x := (piTensorDistribAux_exists_unique (Function.update f i x)).choose_spec
    have h_smul : tprod K (Function.update f i (c • x)) =
        c • tprod K (Function.update f i x) :=
      MultilinearMap.map_update_smul (tprod K) f i c x
    have h_smul_maps : TensorProduct.lift TensorObj.interchange
        (c • (piTensorDistribAux_exists_unique (Function.update f i x)).choose) =
        tprod K (Function.update f i (c • x)) := by
      rw [map_smul, h_unique_x.1, ← h_smul]
    exact (piTensorDistribAux_exists_unique (Function.update f i (c • x))).unique
      h_unique_smul.1 h_smul_maps

/-- The auxiliary multilinear map applied to pure tensors gives the expected result.

This is the defining property of `piTensorDistribAux`. The construction ensures
that this holds by definition. -/
private theorem piTensorDistribAux_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    piTensorDistribAux (fun i => v i ⊗ₜ[K] w i) = tprod K v ⊗ₜ[K] tprod K w := by
  -- By uniqueness, it suffices to show that tprod K v ⊗ₜ tprod K w maps to
  -- tprod K (fun i => v i ⊗ₜ w i) under the interchange map
  have h_exists := piTensorDistribAux_exists_unique (fun i => v i ⊗ₜ[K] w i)
  have h_maps : TensorProduct.lift TensorObj.interchange (tprod K v ⊗ₜ[K] tprod K w) =
      tprod K (fun i => v i ⊗ₜ[K] w i) := by
    simp only [TensorProduct.lift.tmul, TensorObj.interchange_tprod_K]
  exact h_exists.unique h_exists.choose_spec.1 h_maps

/-- The interchange map followed by piTensorDistribAux returns to tprod.

This is the key property that piTensorDistribAux is a right-inverse of the
interchange map (lifted to tensor products). -/
private theorem piTensorDistribInvFun_piTensorDistribAux {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i ⊗[K] W i) :
    TensorProduct.lift TensorObj.interchange (piTensorDistribAux f) = tprod K f := by
  -- This follows directly from the construction: piTensorDistribAux f is defined as
  -- the .choose of piTensorDistribAux_exists_unique, which satisfies this property
  exact (piTensorDistribAux_exists_unique f).choose_spec.1

/-- The forward direction of the distributivity map:
    `⨂[K] i, (V i ⊗ W i) → (⨂[K] i, V i) ⊗ (⨂[K] i, W i)`.

This is built using the universal property of PiTensorProduct.

The key insight is that while we can't decompose an arbitrary element of `V i ⊗ W i`,
we can use the fact that the pi-tensor product is generated by pure tensors
`⊗ᵢ (vᵢ ⊗ wᵢ)`, and these map to `(⊗ᵢ vᵢ) ⊗ (⊗ᵢ wᵢ)`.

The construction proceeds by building a multilinear map that, when all inputs
are pure tensors `vᵢ ⊗ wᵢ`, gives `(⊗ᵢ vᵢ) ⊗ (⊗ᵢ wᵢ)`. This extends by
multilinearity to all of `⨂[K] i, (V i ⊗ W i)`. -/
private noncomputable def piTensorDistribToFun {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] :
    PiTensorProduct K (fun i => V i ⊗[K] W i) →ₗ[K]
    (PiTensorProduct K V) ⊗[K] (PiTensorProduct K W) :=
  PiTensorProduct.lift piTensorDistribAux

/-- The backward direction of the distributivity map:
    `(⨂[K] i, V i) ⊗ (⨂[K] i, W i) → ⨂[K] i, (V i ⊗ W i)`.

This is the interchange map. -/
private noncomputable def piTensorDistribInvFun {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] :
    (PiTensorProduct K V) ⊗[K] (PiTensorProduct K W) →ₗ[K]
    PiTensorProduct K (fun i => V i ⊗[K] W i) :=
  TensorProduct.lift (TensorObj.interchange)

/-- The inverse distributivity map on pure tensors. -/
private theorem piTensorDistribInvFun_tprod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    piTensorDistribInvFun ((tprod K v) ⊗ₜ[K] (tprod K w)) = tprod K (fun i => v i ⊗ₜ[K] w i) := by
  simp only [piTensorDistribInvFun, TensorProduct.lift.tmul, TensorObj.interchange_tprod_K]

/-- The distributivity isomorphism: `⨂[K] i, (V i ⊗ W i) ≃ (⨂[K] i, V i) ⊗ (⨂[K] i, W i)`.

This isomorphism is canonical and arises from the universal property of tensor products.
It sends `⊗ᵢ (vᵢ ⊗ wᵢ)` to `(⊗ᵢ vᵢ) ⊗ (⊗ᵢ wᵢ)`.

The inverse is the interchange map. -/
noncomputable def piTensorDistrib {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] :
    PiTensorProduct K (fun i => V i ⊗[K] W i) ≃ₗ[K]
    (PiTensorProduct K V) ⊗[K] (PiTensorProduct K W) := by
  refine LinearEquiv.ofLinear piTensorDistribToFun piTensorDistribInvFun ?_ ?_
  · apply TensorProduct.ext
    apply LinearMap.ext; intro t₁
    apply LinearMap.ext; intro t₂
    change piTensorDistribToFun (piTensorDistribInvFun (t₁ ⊗ₜ[K] t₂)) = t₁ ⊗ₜ[K] t₂
    induction t₁ using PiTensorProduct.induction_on with
    | smul_tprod c v =>
      induction t₂ using PiTensorProduct.induction_on with
      | smul_tprod c' w =>
        simp only [piTensorDistribInvFun, TensorProduct.lift.tmul, map_smul, LinearMap.smul_apply]
        rw [TensorObj.interchange_tprod_K]
        simp only [piTensorDistribToFun, PiTensorProduct.lift.tprod]
        rw [piTensorDistribAux_apply]
        rw [smul_tmul', tmul_smul]
      | add x y ihx ihy =>
        simp only [tmul_add, map_add, ihx, ihy]
    | add x y ihx ihy =>
      simp only [add_tmul, map_add, ihx, ihy]
  · apply PiTensorProduct.ext
    apply MultilinearMap.ext; intro f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.id_apply]
    simp only [piTensorDistribToFun, PiTensorProduct.lift.tprod]
    exact piTensorDistribInvFun_piTensorDistribAux f

/-- The distributivity isomorphism applied to a pure tensor. -/
theorem piTensorDistrib_tprod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    piTensorDistrib (tprod K (fun i => v i ⊗ₜ[K] w i)) = tprod K v ⊗ₜ[K] tprod K w := by
  simp only [piTensorDistrib, LinearEquiv.ofLinear_apply, piTensorDistribToFun,
    PiTensorProduct.lift.tprod, piTensorDistribAux_apply]

/-- The interchange map followed by distributivity equals the tensor of the identity maps.

The proof uses that for pure tensors:
  `piTensorDistrib (interchange (tprod K v) (tprod K w)) = tprod K v ⊗ₜ tprod K w`
and extends by linearity. -/
theorem piTensorDistrib_interchange {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (t₁ : PiTensorProduct K V) (t₂ : PiTensorProduct K W) :
    piTensorDistrib (TensorObj.interchange t₁ t₂) = t₁ ⊗ₜ[K] t₂ := by
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction t₂ using PiTensorProduct.induction_on with
    | smul_tprod c' w =>
      simp only [map_smul, LinearMap.smul_apply]
      rw [TensorObj.interchange_tprod_K, piTensorDistrib_tprod]
      rw [smul_tmul', tmul_smul]
    | add x y ihx ihy =>
      simp only [map_add, ihx, ihy, tmul_add]
  | add x y ihx ihy =>
    rw [map_add, LinearMap.add_apply, map_add, ihx, ihy, add_tmul]

/-- The rearrangement isomorphism for tensor products.

This isomorphism rearranges `(A ⊗ B) ⊗ (C ⊗ D)` to `(A ⊗ C) ⊗ (B ⊗ D)`.
It is built from associativity and commutativity of tensor products. -/
noncomputable def tensorFourRearrange (A B C D : Type*)
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D] :
    (A ⊗[K] B) ⊗[K] (C ⊗[K] D) ≃ₗ[K] (A ⊗[K] C) ⊗[K] (B ⊗[K] D) :=
  -- (A ⊗ B) ⊗ (C ⊗ D) → A ⊗ (B ⊗ (C ⊗ D)) → A ⊗ ((B ⊗ C) ⊗ D)
  -- → A ⊗ ((C ⊗ B) ⊗ D) → A ⊗ (C ⊗ (B ⊗ D)) → (A ⊗ C) ⊗ (B ⊗ D)
  (TensorProduct.assoc K A B (C ⊗[K] D)).trans <|
  (LinearEquiv.lTensor A (TensorProduct.assoc K B C D).symm).trans <|
  (LinearEquiv.lTensor A (LinearEquiv.rTensor D (TensorProduct.comm K B C))).trans <|
  (LinearEquiv.lTensor A (TensorProduct.assoc K C B D)).trans <|
  (TensorProduct.assoc K A C (B ⊗[K] D)).symm

@[simp]
theorem tensorFourRearrange_tmul (A B C D : Type*)
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]
    (a : A) (b : B) (c : C) (d : D) :
    tensorFourRearrange A B C D ((a ⊗ₜ[K] b) ⊗ₜ[K] (c ⊗ₜ[K] d)) = (a ⊗ₜ[K] c) ⊗ₜ[K] (b ⊗ₜ[K] d) := by
  simp only [tensorFourRearrange, LinearEquiv.trans_apply, TensorProduct.assoc_tmul,
    LinearEquiv.lTensor_tmul, TensorProduct.assoc_symm_tmul, LinearEquiv.rTensor_tmul,
    TensorProduct.comm_tmul]
variable {V : Fin d → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- Helper lemma: splitTensorEquiv applied to a pure tensor product. -/
private theorem splitTensorEquiv_tprod (v : (i : Fin d) → V i) :
    splitTensorEquiv σ (tprod K v) =
      tprod K (fun (i : σ.S) => v i) ⊗ₜ[K] tprod K (fun (i : Sc σ) => v i) := by
  dsimp [splitTensorEquiv]
  erw [PiTensorProduct.reindex_tprod]
  simp
  erw [PiTensorProduct.tmulEquivDep_symm_apply]
  congr


/-- Split tensor equiv commutes with interchange via distributivity.

This shows that splitting the product tensor `(X * Y).t = interchange X.t Y.t`
is equivalent to taking the tensor product of the splits after rearranging
via the distributivity isomorphism.

Specifically, for tensors `t₁ : ⨂[K] V` and `t₂ : ⨂[K] W`, we have:
  `splitTensorEquiv σ (interchange t₁ t₂)`
is equivalent (up to associativity and commutativity isomorphisms) to:
  `(splitTensorEquiv σ t₁) ⊗ (splitTensorEquiv σ t₂)`
after applying the distributivity isomorphisms to each factor. -/
theorem splitTensorEquiv_interchange
    {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (t₁ : PiTensorProduct K V) (t₂ : PiTensorProduct K W) :
    splitTensorEquiv σ (TensorObj.interchange t₁ t₂) =
      TensorProduct.map piTensorDistribInvFun piTensorDistribInvFun
        (tensorFourRearrange
          (PiTensorProduct K (fun i : σ.S => V i))
          (PiTensorProduct K (fun i : Sc σ => V i))
          (PiTensorProduct K (fun i : σ.S => W i))
          (PiTensorProduct K (fun i : Sc σ => W i))
          ((splitTensorEquiv σ t₁) ⊗ₜ[K] (splitTensorEquiv σ t₂))) := by
  -- Both sides are bilinear in (t₁, t₂), so it suffices to check on pure tensors
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction t₂ using PiTensorProduct.induction_on with
    | smul_tprod c' w =>
      simp only [map_smul, LinearMap.smul_apply]
      rw [TensorObj.interchange_tprod_K]
      rw [splitTensorEquiv_tprod]
      rw [splitTensorEquiv_tprod, splitTensorEquiv_tprod]
      simp only [smul_tmul']
      rw [tensorFourRearrange_tmul]
      rw [TensorProduct.map_tmul]
      -- LHS: (⨂ i:S, v i ⊗ w i) ⊗ (⨂ j:Sc, v j ⊗ w j)
      -- RHS: piTensorDistribInvFun ((⨂ i:S, v i) ⊗ (⨂ i:S, w i)) ⊗
      --      piTensorDistribInvFun ((⨂ j:Sc, v j) ⊗ (⨂ j:Sc, w j))
      -- Use piTensorDistribInvFun_tprod to simplify the RHS
      congr 1
      · -- Goal: c' • c • tprod ... = piTensorDistribInvFun ((c • tprod ...) ⊗ (c' • tprod ...))
        symm
        rw [TensorProduct.smul_tmul_smul, mul_smul, map_smul, map_smul,
          piTensorDistribInvFun_tprod, smul_comm]
      · -- Goal: tprod ... = piTensorDistribInvFun (tprod ... ⊗ tprod ...)
        rw [piTensorDistribInvFun_tprod]
    | add x y ihx ihy =>
      simp only [map_add, tmul_add, ihx, ihy]
  | add x y ihx ihy =>
    simp only [LinearMap.add_apply, map_add, add_tmul, ihx, ihy]

/-- The finrank of a tensor product of finite-dimensional spaces equals the product of finranks. -/
theorem finrank_tensorProduct
    {A B : Type*}
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [FiniteDimensional K A] [FiniteDimensional K B] :
    finrank K (A ⊗[K] B) = finrank K A * finrank K B :=
  Module.finrank_tensorProduct

/-- `tensorToDualHom` of a rearranged tensor product corresponds to the Kronecker product of
    the `tensorToDualHom`s, precomposed with the dual distribution isomorphism. -/
theorem tensorToDualHom_tensorFourRearrange {A B C D : Type*}
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]
    [FiniteDimensional K A] [FiniteDimensional K C]
    (t1 : A ⊗[K] B) (t2 : C ⊗[K] D) :
    tensorToDualHom K (A ⊗[K] C) (B ⊗[K] D) (tensorFourRearrange A B C D (t1 ⊗ₜ[K] t2)) =
    (TensorProduct.map (tensorToDualHom K A B t1) (tensorToDualHom K C D t2)).comp
      (TensorProduct.dualDistribEquiv K A C).symm.toLinearMap := by
  induction t1 using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, tensorFourRearrange, LinearEquiv.trans_apply]
    rw [TensorProduct.zero_tmul]
    simp
  | tmul a b =>
    induction t2 using TensorProduct.induction_on with
    | zero =>
      simp only [TensorProduct.tmul_zero, map_zero, LinearMap.zero_comp,
        TensorProduct.map_zero_right]
    | tmul c d =>
      ext f
      let e := TensorProduct.dualDistribEquiv K A C
      let g := e.symm f
      have hf : f = e g := (e.apply_symm_apply f).symm
      rw [hf]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      induction g using TensorProduct.induction_on with
      | zero => simp
      | tmul u v =>
        simp only [tensorFourRearrange_tmul, tensorToDualHom_tmul, TensorProduct.dualDistribEquiv]
        have hsymm : (TensorProduct.dualDistribEquivOfBasis (Free.chooseBasis K A)
            (Free.chooseBasis K C)).symm (e (u ⊗ₜ[K] v)) = u ⊗ₜ[K] v := by
          simp only [e, TensorProduct.dualDistribEquiv, LinearEquiv.symm_apply_apply]
        rw [hsymm, TensorProduct.map_tmul, tensorToDualHom_tmul, tensorToDualHom_tmul,
          TensorProduct.smul_tmul_smul]
        -- Goal: (e (u ⊗ₜ v)) (a ⊗ₜ c) • b ⊗ₜ d = (u a * v c) • b ⊗ₜ d
        -- Show (e (u ⊗ₜ v)) (a ⊗ₜ c) = u a * v c
        have he_apply : (e (u ⊗ₜ[K] v)) (a ⊗ₜ[K] c) = u a * v c := by
          simp only [e, TensorProduct.dualDistribEquiv, TensorProduct.dualDistribEquivOfBasis,
            LinearEquiv.ofLinear_apply, TensorProduct.dualDistrib_apply]
        rw [he_apply]
      | add x y ihx ihy =>
        simp only [map_add, ihx, ihy]
    | add x y ihx ihy =>
      simp only [TensorProduct.tmul_add, map_add, ihx, ihy, TensorProduct.map_add_right,
        LinearMap.add_comp]
  | add x y ihx ihy =>
    simp only [TensorProduct.add_tmul, map_add, ihx, ihy, TensorProduct.map_add_left,
      LinearMap.add_comp]


/-- Multiplicativity of flattening rank.

The proof requires establishing:
1. `splitTensorEquiv` commutes with `interchange` via distributivity isomorphisms:
   - There exist canonical isomorphisms `⨂[K] i, (V i ⊗ W i) ≃ (⨂[K] i, V i) ⊗ (⨂[K] i, W i)`
   - These make the split of `X * Y` equivalent to a tensor product of splits

2. The flattening map factors: `flatteningMap σ (X * Y)` corresponds to the Kronecker product
   of `flatteningMap σ X` and `flatteningMap σ Y` (after the distributivity isomorphisms)

3. Rank is multiplicative for Kronecker products: `rank(A ⊗ B) = rank(A) * rank(B)`
   This is the key linear algebra fact: the range of a tensor product of linear maps
   is the tensor product of the ranges, and `finrank(U ⊗ V) = finrank(U) * finrank(V)`. -/
theorem flatteningRank_mul
    (x y : Tensor K d) :
    flatteningRank σ (x * y)
      = flatteningRank σ x
      * flatteningRank σ y := by
  induction x using Quotient.inductionOn with | _ X =>
  induction y using Quotient.inductionOn with | _ Y =>

  haveI := X.finiteDimensional
  haveI := Y.finiteDimensional

  change flatteningRank σ (Tensor.mul (Tensor.toTensor X) (Tensor.toTensor Y)) =
         flatteningRank σ (Tensor.toTensor X) * flatteningRank σ (Tensor.toTensor Y)
  simp only [Tensor.mul, flatteningRank_mk]

  let AS := PiTensorProduct K (fun i : σ.S => X.V i)
  let BS := PiTensorProduct K (fun i : Sc σ => X.V i)
  let AT := PiTensorProduct K (fun i : σ.S => Y.V i)
  let BT := PiTensorProduct K (fun i : Sc σ => Y.V i)

  -- Manually provide FiniteDimensional instances using the basis
  haveI : FiniteDimensional K AS :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun i => Module.Free.chooseBasis K (X.V i)))
  haveI : FiniteDimensional K BS :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun i => Module.Free.chooseBasis K (X.V i)))
  haveI : FiniteDimensional K AT :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun i => Module.Free.chooseBasis K (Y.V i)))
  haveI : FiniteDimensional K BT :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun i => Module.Free.chooseBasis K (Y.V i)))

  let tX := splitTensorEquiv σ X.t
  let tY := splitTensorEquiv σ Y.t

  -- The flattening map of X*Y
  let fXY := flatteningMap σ (X * Y)

  -- tXY is related to tX ⊗ tY via splitTensorEquiv_interchange
  have h_tXY_eq : splitTensorEquiv σ (TensorObj.interchange X.t Y.t) =
      TensorProduct.map
        (piTensorDistrib (K := K) (ι := σ.S)).symm.toLinearMap
        (piTensorDistrib (K := K) (ι := Sc σ)).symm.toLinearMap
        (tensorFourRearrange AS BS AT BT (tX ⊗ₜ[K] tY)) := by
    rw [splitTensorEquiv_interchange]
    rfl

  -- Now express fXY using tensorToDualHom naturality
  have h_fXY : flatteningMap σ (X * Y) =
      (piTensorDistrib (K := K)).symm.toLinearMap.comp
      ((tensorToDualHom K (AS ⊗[K] AT) (BS ⊗[K] BT)
        (tensorFourRearrange AS BS AT BT (tX ⊗ₜ[K] tY))).comp
        (piTensorDistrib (K := K)).symm.toLinearMap.dualMap) := by
      change flatteningMap σ (X * Y) = _
      dsimp [flatteningMap, TensorObj.mul]
      -- Replace splitTensorEquiv with mapped version using h_tXY_eq
      have eq1 : splitTensorEquiv σ (TensorObj.interchange X.t Y.t) =
        TensorProduct.map (piTensorDistrib (K := K) (ι := σ.S)).symm.toLinearMap
                          (piTensorDistrib (K := K) (ι := Sc σ)).symm.toLinearMap
                          (tensorFourRearrange AS BS AT BT (tX ⊗ₜ[K] tY)) := by
         rw [h_tXY_eq]
      erw [eq1]
      -- Now apply naturality
      ext phi
      -- The goal follows from tensorToDualHom_naturality:
      -- tensorToDualHom (map eA eB t) phi = eB (tensorToDualHom t (phi ∘ eA))
      -- where eA = piTensorDistrib.symm (on σ.S), eB = piTensorDistrib.symm (on Sc σ)
      -- and t = tensorFourRearrange AS BS AT BT (tX ⊗ₜ tY)
      -- Note: (X * Y).V i = X.V i ⊗ Y.V i by definition of TensorObj.mul
      simp only [HMul.hMul, Mul.mul, TensorObj.mul, LinearMap.comp_apply]
      convert tensorToDualHom_naturality K piTensorDistrib.symm piTensorDistrib.symm
        (tensorFourRearrange AS BS AT BT (tX ⊗ₜ[K] tY)) phi using 2

  -- The rest of the proof uses h_fXY to factor the flattening map and apply rank multiplicativity
  -- Key steps:
  -- 1. Use h_fXY to rewrite flatteningMap σ (X * Y)
  -- 2. Apply finrank_range_comp_equiv for the outer equivalence
  -- 3. Apply tensorToDualHom_tensorFourRearrange to factor as tensor product of maps
  -- 4. Use finrank_range_map for multiplicativity of rank under tensor products

  -- First simplify the LHS: flatteningRank σ (X * Y) = finrank K (range (flatteningMap σ (X * Y)))
  -- The quotient on the LHS simplifies to the tensor product TensorObj
  change AsymptoticSpectra.flatteningRank σ (X * Y) = _
  unfold AsymptoticSpectra.flatteningRank

  -- Rewrite using h_fXY
  conv_lhs => rw [h_fXY]

  -- Simplify using finrank_range_comp_equiv for the outer piTensorDistrib.symm
  -- The map is: piTensorDistrib.symm ∘ (tensorToDualHom ... ∘ piTensorDistrib.symm.dualMap)
  rw [finrank_range_comp_equiv]

  -- Now apply tensorToDualHom_tensorFourRearrange to factor the tensorToDualHom
  rw [tensorToDualHom_tensorFourRearrange]

  -- The map is now: ((map fX fY) ∘ dualDistribEquiv.symm) ∘ piTensorDistrib.symm.dualMap
  -- where fX = tensorToDualHom K AS BS tX and fY = tensorToDualHom K AT BT tY
  -- Need to show that dualDistribEquiv.symm ∘ piTensorDistrib.symm.dualMap is an equivalence
  -- Build the equivalence explicitly
  -- piTensorDistrib : ⨂[K] (i : σ.S), X.V ↑i ⊗[K] Y.V ↑i ≃ AS ⊗ AT
  -- piTensorDistrib.symm : AS ⊗ AT ≃ ⨂[K] (i : σ.S), X.V ↑i ⊗[K] Y.V ↑i
  -- (piTensorDistrib.symm).dualMap : Dual K (⨂...) → Dual K (AS ⊗ AT)
  -- But we need LinearEquiv, not LinearMap. Use LinearEquiv.dualMap:
  -- LinearEquiv.dualMap piTensorDistrib.symm : Dual K (AS ⊗ AT) ≃ Dual K (⨂...)
  -- So we need the inverse: (LinearEquiv.dualMap piTensorDistrib.symm).symm : Dual K (⨂...) ≃ Dual K (AS ⊗ AT)
  -- Note: LinearEquiv.dualMap e : Dual M₂ ≃ Dual M₁ when e : M₁ ≃ M₂
  let piTD := piTensorDistrib (K := K) (ι := σ.S) (V := fun i => X.V ↑i) (W := fun i => Y.V ↑i)
  -- piTD : ⨂[K] ... ≃ AS ⊗ AT
  -- piTD.symm : AS ⊗ AT ≃ ⨂[K] ...
  -- LinearEquiv.dualMap piTD.symm : Dual K (⨂...) ≃ Dual K (AS ⊗ AT)
  let e1 : Dual K (⨂[K] (i : σ.S), X.V ↑i ⊗[K] Y.V ↑i) ≃ₗ[K] Dual K (AS ⊗[K] AT) :=
    LinearEquiv.dualMap piTD.symm
  let e2 : (Dual K AS ⊗[K] Dual K AT) ≃ₗ[K] Dual K (AS ⊗[K] AT) :=
    TensorProduct.dualDistribEquiv K AS AT
  let e_comp : Dual K (⨂[K] (i : σ.S), X.V ↑i ⊗[K] Y.V ↑i) ≃ₗ[K] (Dual K AS ⊗[K] Dual K AT) :=
    e1.trans e2.symm
  have h_equiv : ((TensorProduct.dualDistribEquiv K AS AT).symm.toLinearMap.comp
                  piTD.symm.toLinearMap.dualMap) = e_comp.toLinearMap := by
    ext phi
    simp only [e_comp, e1, e2, piTD, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
               LinearEquiv.trans_apply]
    rfl
  rw [LinearMap.comp_assoc, h_equiv]

  -- Now we have f ∘ e_comp where e_comp is an equivalence
  -- Composing with equivalence on the right preserves the range
  have h_range_eq : (TensorProduct.map (tensorToDualHom K AS BS tX) (tensorToDualHom K AT BT tY) ∘ₗ
                     e_comp.toLinearMap).range =
                    (TensorProduct.map (tensorToDualHom K AS BS tX) (tensorToDualHom K AT BT tY)).range := by
    ext x
    simp only [LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e_comp y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e_comp.symm y, by simp⟩
  rw [h_range_eq]

  -- Now we have: finrank K (range (map fX fY)) = finrank K (range fX) * finrank K (range fY)
  -- where fX = tensorToDualHom K AS BS tX : Dual K AS →ₗ[K] BS
  --       fY = tensorToDualHom K AT BT tY : Dual K AT →ₗ[K] BT
  -- Use finrank_range_map
  rw [finrank_range_map]

  -- Now we need to relate back to flatteningMap
  -- flatteningMap σ X = tensorToDualHom K AS BS (splitTensorEquiv σ X.t) = tensorToDualHom K AS BS tX
  -- and similarly for Y
  rfl

theorem flatteningRank_zero :
    flatteningRank σ (0 : Tensor K d) = 0 := by
  have : (0 : Tensor K d) = Tensor.toTensor TensorObj.zeroObj := rfl
  rw [this, flatteningRank_mk]
  unfold AsymptoticSpectra.flatteningRank flatteningMap
  have h_zero : (TensorObj.zeroObj : TensorObj K d).t = 0 := rfl
  rw [h_zero]
  rw [map_zero, map_zero]
  rw [LinearMap.range_zero, finrank_bot]



/-- A dual functional on `⨂[K] i, ULift K` that evaluates to the product of the components. -/
private noncomputable def tprodOneDual {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Dual K (PiTensorProduct K (fun _ : ι => ULift K)) :=
  PiTensorProduct.lift
    { toFun := fun v => ∏ i, (v i).down
      map_update_add' := fun v i x y => by
        rw [Fintype.prod_eq_prod_compl_mul (a := i) (f := fun j => (Function.update v i (x + y) j).down),
            Fintype.prod_eq_prod_compl_mul (a := i) (f := fun j => (Function.update v i x j).down),
            Fintype.prod_eq_prod_compl_mul (a := i) (f := fun j => (Function.update v i y j).down)]
        simp only [Function.update_self, ULift.add_down]
        have h : ∀ z : ULift K, ∏ j ∈ {i}ᶜ, (Function.update v i z j).down = ∏ j ∈ {i}ᶜ, (v j).down := by
          intro z
          apply Finset.prod_congr rfl; intro j hj
          simp only [Finset.mem_compl, Finset.mem_singleton] at hj
          rw [Function.update_of_ne hj]
        rw [h (x + y), h x, h y]
        ring
      map_update_smul' := fun v i c x => by
        rw [Fintype.prod_eq_prod_compl_mul (a := i) (f := fun j => (Function.update v i (c • x) j).down),
            Fintype.prod_eq_prod_compl_mul (a := i) (f := fun j => (Function.update v i x j).down)]
        simp only [Function.update_self, ULift.smul_down, smul_eq_mul]
        have h : ∀ z : ULift K, ∏ j ∈ {i}ᶜ, (Function.update v i z j).down = ∏ j ∈ {i}ᶜ, (v j).down := by
          intro z
          apply Finset.prod_congr rfl; intro j hj
          simp only [Finset.mem_compl, Finset.mem_singleton] at hj
          rw [Function.update_of_ne hj]
        rw [h (c • x), h x]
        ring }

private theorem tprodOneDual_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ULift K) :
    tprodOneDual (tprod K v) = ∏ i, (v i).down := by
  simp only [tprodOneDual, PiTensorProduct.lift.tprod]
  rfl

private theorem tprodOneDual_apply_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    tprodOneDual (tprod K (fun (_ : ι) => ULift.up (1 : K))) = (1 : K) := by
  rw [tprodOneDual_apply]
  simp

private theorem tprodOne_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    tprod K (fun (_ : ι) => ULift.up (1 : K)) ≠ (0 : PiTensorProduct K (fun _ : ι => ULift K)) := by
  intro h
  have := congr_arg tprodOneDual h
  simp only [map_zero] at this
  rw [tprodOneDual_apply_one] at this
  exact one_ne_zero this

theorem flatteningRank_one :
    flatteningRank σ (1 : Tensor K d) = 1 := by
  have : (1 : Tensor K d) = Tensor.toTensor TensorObj.oneObj := rfl
  rw [this, flatteningRank_mk]
  unfold AsymptoticSpectra.flatteningRank flatteningMap
  have h_split : splitTensorEquiv σ TensorObj.oneObj.t =
      tprod K (fun (_ : σ.S) => ULift.up (1 : K)) ⊗ₜ[K] tprod K (fun (_ : Sc σ) => ULift.up (1 : K)) := by
    change splitTensorEquiv σ (tprod K (fun _ => ULift.up 1)) = _
    rw [splitTensorEquiv_tprod]
  rw [h_split]
  let vS := tprod K (fun (_ : σ.S) => ULift.up (1 : K))
  let vSc := tprod K (fun (_ : Sc σ) => ULift.up (1 : K))
  change finrank K (LinearMap.range (tensorToDualHom K _ _ (vS ⊗ₜ[K] vSc))) = 1
  haveI : Nonempty σ.S := σ.hS.to_subtype
  haveI : Nonempty (Sc σ) := σ.hSc.to_subtype
  have hS_ne_zero : vS ≠ 0 := tprodOne_ne_zero
  have hSc_ne_zero : vSc ≠ 0 := tprodOne_ne_zero
  have h_range : LinearMap.range (tensorToDualHom K _ _ (vS ⊗ₜ[K] vSc)) = Submodule.span K {vSc} := by
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      rw [tensorToDualHom_tmul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · intro hx
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      use c • tprodOneDual
      rw [tensorToDualHom_tmul, LinearMap.smul_apply, tprodOneDual_apply]
      simp only [Finset.prod_const_one, smul_one_smul]
  rw [h_range, finrank_span_singleton hSc_ne_zero]

noncomputable def FlatteningRankPoint
    (P : SemiringPreorder (Tensor K d))
    (h_mono : ∀ {x y : Tensor K d}, P.le x y → flatteningRankReal σ x ≤ flatteningRankReal σ y) :
    SemiringSpectrumPoint (Tensor K d) P where
  toFun := flatteningRankReal σ
  map_zero' := by
    simp only [flatteningRankReal]
    rw [AsymptoticSpectra.Tensor.flatteningRank_zero σ]
    simp only [Nat.cast_zero]
  map_one' := by
    simp only [flatteningRankReal]
    rw [AsymptoticSpectra.Tensor.flatteningRank_one σ]
    simp only [Nat.cast_one]
  map_add' x y := by
    simp only [flatteningRankReal]
    rw [flatteningRank_add]
    push_cast
    rfl
  map_mul' x y := by
    simp only [flatteningRankReal]
    rw [flatteningRank_mul]
    push_cast
    rfl
  monotone' := h_mono

end AsymptoticSpectra.Tensor
