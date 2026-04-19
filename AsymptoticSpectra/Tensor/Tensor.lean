import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Logic.Basic
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Module.PUnit
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Tower

universe u v w

open BigOperators TensorProduct

-- We open PiTensorProduct, but distinct names prevent clashes with the type
open PiTensorProduct

/-- `TensorObj` represents a single concrete (d)-th order tensor
  t ∈ V₁ ⊗ V₂ ⊗ ⋯ ⊗ V_d over a field K.

  Unlike a coordinate representation, this structure stores the vector spaces
  themselves and an element of their iterated tensor product.

  Arguments:
  * `K`: The base field.
  * `d`: The order of the tensor (must be greater than 1). -/
structure TensorObj (K : Type u) [Field K] (d : ℕ) [Fact (1 < d)] where
  /-- The family of vector spaces involved in the tensor product. -/
  V : Fin d → Type v
  /-- Each space must be an additive commutative group. -/
  [addCommGroup : ∀ i, AddCommGroup (V i)]
  /-- Each space must be a module over K. -/
  [module : ∀ i, Module K (V i)]
  /-- Each space must be finite-dimensional over K. -/
  [finiteDimensional : ∀ i, FiniteDimensional K (V i)]
  /-- The concrete tensor element in the iterated tensor product of the V i. -/
  t : PiTensorProduct K V

attribute [instance] TensorObj.addCommGroup TensorObj.module TensorObj.finiteDimensional

namespace TensorObj


variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

noncomputable section

/-- Helper for product of LinearEquivs. -/
def prodEquiv {M M' N N' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N] [AddCommMonoid N']
    [Module K M] [Module K M'] [Module K N] [Module K N']
    (e1 : M ≃ₗ[K] M') (e2 : N ≃ₗ[K] N') : (M × N) ≃ₗ[K] (M' × N') :=
  { toFun := Prod.map e1 e2
    invFun := Prod.map e1.symm e2.symm
    left_inv := fun ⟨x, y⟩ => by simp
    right_inv := fun ⟨x, y⟩ => by simp
    map_add' := fun x y => by
      cases x; cases y
      dsimp [Prod.map]
      simp only [map_add]
    map_smul' := fun c x => by
      cases x
      dsimp [Prod.map]
      simp only [map_smul] }

/-- Helper for commutativity. -/
def prodComm {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module K M] [Module K N] :
    (M × N) ≃ₗ[K] (N × M) :=
  { toFun := Prod.swap
    invFun := Prod.swap
    left_inv := fun ⟨x, y⟩ => by simp
    right_inv := fun ⟨x, y⟩ => by simp
    map_add' := fun x y => by simp
    map_smul' := fun c x => by simp }

/-- Helper for associativity. -/
def prodAssoc {M N P : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module K M] [Module K N] [Module K P] : ((M × N) × P) ≃ₗ[K] (M × (N × P)) :=
  { toFun := fun ⟨⟨m, n⟩, p⟩ => (m, (n, p))
    invFun := fun ⟨m, ⟨n, p⟩⟩ => ((m, n), p)
    left_inv := fun ⟨⟨m, n⟩, p⟩ => rfl
    right_inv := fun ⟨m, ⟨n, p⟩⟩ => rfl
    map_add' := fun x y => by simp
    map_smul' := fun c x => by simp }

/-- Helper for zero unit. -/
def prodZero {M : Type*} [AddCommMonoid M] [Module K M] : (PUnit × M) ≃ₗ[K] M :=
  { toFun := fun ⟨_, m⟩ => m
    invFun := fun m => (PUnit.unit, m)
    left_inv := fun ⟨u, m⟩ => by simp
    right_inv := fun m => rfl
    map_add' := fun x y => rfl
    map_smul' := fun c x => rfl }

/-- Helper for ULift equivalence. -/
def uliftEquiv : ULift.{v} K ≃ₗ[K] K :=
  { toFun := ULift.down
    invFun := ULift.up
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- Helper for tensor unit. -/
def tensorOne {V : Type*} [AddCommGroup V] [Module K V] : (ULift.{v} K) ⊗[K] V ≃ₗ[K] V :=
  LinearEquiv.trans (TensorProduct.congr (uliftEquiv) (LinearEquiv.refl K V)) (TensorProduct.lid K V)

/-- Helper for tensor zero. -/
def tensorZero {V : Type*} [AddCommGroup V] [Module K V] : PUnit ⊗[K] V ≃ₗ[K] PUnit :=
  { toFun := fun _ => PUnit.unit
    invFun := fun _ => 0
    left_inv := fun x => by
       -- 0 ⊗ v = 0 = PUnit.unit from iso perspective?
       -- x : PUnit ⊗ V. PUnit is zero module. x=0.
       rw [Subsingleton.elim x 0]

    right_inv := fun x => rfl
    map_add' := fun x y => rfl
    map_smul' := fun c x => rfl }

/-- Helper for left distributivity: M ⊗ (N × P) ≃ (M ⊗ N) × (M ⊗ P). -/
def distribLeft {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module K M] [Module K N] [Module K P] : M ⊗[K] (N × P) ≃ₗ[K] (M ⊗[K] N) × (M ⊗[K] P) :=
  TensorProduct.prodRight K K M N P

/-- Helper for right distributivity: (N × P) ⊗ M ≃ (N ⊗ M) × (P ⊗ M). -/
def distribRight {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module K M] [Module K N] [Module K P] : (N × P) ⊗[K] M ≃ₗ[K] (N ⊗[K] M) × (P ⊗[K] M) :=
  TensorProduct.prodLeft K K N P M

/-- Functoriality of PiTensorProduct: a family of linear maps induces a map on the tensor product.
    Renamed to `liftMap` to avoid namespace conflicts. -/
def liftMap {ι : Type*} [Fintype ι] {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) : PiTensorProduct K V →ₗ[K] PiTensorProduct K W :=
  lift <| (tprod K).compLinearMap f

/-- Functoriality of PiTensorProduct: identity map. -/
@[simp]
theorem liftMap_id (X : TensorObj K d) : liftMap (fun _ => LinearMap.id) X.t = X.t := by
  have : liftMap (fun (i : Fin d) => (LinearMap.id : X.V i →ₗ[K] X.V i)) = LinearMap.id := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext; intro v
    simp [liftMap]
  rw [this]; rfl

/-- Functoriality of PiTensorProduct: composition. -/
theorem liftMap_comp {ι : Type*} [Fintype ι] {V₁ V₂ V₃ : ι → Type*}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    (f : ∀ i, V₂ i →ₗ[K] V₃ i) (g : ∀ i, V₁ i →ₗ[K] V₂ i) (t : PiTensorProduct K V₁) :
    liftMap f (liftMap g t) = liftMap (fun i => (f i).comp (g i)) t := by
  have : liftMap f ∘ₗ liftMap g = liftMap (fun i => (f i).comp (g i)) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext; intro v
    simp [liftMap]
  rw [← LinearMap.comp_apply, this]

/-- liftMap on a pure tensor is a pure tensor with each component mapped. -/
theorem liftMap_tprod {ι : Type*} [Fintype ι] {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) (v : ∀ i, V i) :
    liftMap f (tprod K v) = tprod K (fun i => f i (v i)) := by
  simp only [liftMap, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply]

/-- Helper to construct interchange map definition -/
def interchangeAux {ι : Type*} [Fintype ι] [DecidableEq ι] {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) : MultilinearMap K W (PiTensorProduct K (fun i => V i ⊗[K] W i)) where
    toFun w := tprod K fun i => v i ⊗ₜ[K] w i
    map_update_add' w i x y := by
      -- h1: Align LHS to a Function.update that matches (tprod K).map_add input
      have h1 : (fun j => v j ⊗ₜ[K] Function.update w i (x + y) j) =
                Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] (x + y)) := by
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [h]

      -- h2: Break down the updated value
      have h2 : Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] (x + y)) =
                Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] x + v i ⊗ₜ[K] y) := by
        simp [TensorProduct.tmul_add]

      -- h3: Align RHS term 1
      have h3 : Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] x) =
                (fun j => v j ⊗ₜ[K] Function.update w i x j) := by
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [h]

      -- h4: Align RHS term 2
      have h4 : Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] y) =
                (fun j => v j ⊗ₜ[K] Function.update w i y j) := by
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [h]

      calc
        (tprod K) (fun j => v j ⊗ₜ[K] (Function.update w i (x + y)) j)
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] (x + y))) := by rw [h1]
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] x + v i ⊗ₜ[K] y)) := by rw [h2]
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] x)) +
            (tprod K) (Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] y)) := by
            rw [MultilinearMap.map_update_add (tprod K) (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] x) (v i ⊗ₜ[K] y)]
        _ = (tprod K) (fun j => v j ⊗ₜ[K] (Function.update w i x) j) +
            (tprod K) (fun j => v j ⊗ₜ[K] (Function.update w i y) j) := by rw [h3, h4]

    map_update_smul' w i c x := by
      have h1 : (fun j => v j ⊗ₜ[K] Function.update w i (c • x) j) =
                Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] (c • x)) := by
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [h]

      have h2 : Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] (c • x)) =
                Function.update (fun j => v j ⊗ₜ[K] w j) i (c • (v i ⊗ₜ[K] x)) := by
        simp [TensorProduct.tmul_smul]

      calc
        (tprod K) (fun j => v j ⊗ₜ[K] (Function.update w i (c • x)) j)
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] (c • x))) := by rw [h1]
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] w j) i (c • (v i ⊗ₜ[K] x))) := by rw [h2]
        _ = c • (tprod K) (Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] x)) := by
            rw [MultilinearMap.map_update_smul (tprod K) (fun j => v j ⊗ₜ[K] w j) i c (v i ⊗ₜ[K] x)]
        _ = c • (tprod K) (fun j => v j ⊗ₜ[K] (Function.update w i x) j) := by
            -- Explicitly use map_smul effect on function instead of bad lemma h3
            congr 1; congr; ext j; by_cases h : j = i
            · subst h; simp
            · simp [h]

noncomputable def interchangeMap {ι : Type*} [Fintype ι] [DecidableEq ι] {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] :
    MultilinearMap K V (PiTensorProduct K W →ₗ[K] PiTensorProduct K (fun i => V i ⊗[K] W i)) where
    toFun v := lift (interchangeAux v)
    map_update_add' v i x y := by
      apply _root_.PiTensorProduct.ext
      apply MultilinearMap.ext; intro m
      simp only [LinearMap.add_apply, LinearMap.compMultilinearMap_apply]

      simp only [_root_.PiTensorProduct.lift.tprod]
      dsimp [interchangeAux, MultilinearMap.coe_mk]

      have h1 : (fun j => Function.update v i (x + y) j ⊗ₜ[K] m j) =
                Function.update (fun j => v j ⊗ₜ[K] m j) i ((x + y) ⊗ₜ[K] m i) := by
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [h]

      have h2 : Function.update (fun j => v j ⊗ₜ[K] m j) i ((x + y) ⊗ₜ[K] m i) =
                Function.update (fun j => v j ⊗ₜ[K] m j) i (x ⊗ₜ[K] m i + y ⊗ₜ[K] m i) := by
        simp [TensorProduct.add_tmul]

      have h3 : Function.update (fun j => v j ⊗ₜ[K] m j) i (x ⊗ₜ[K] m i) =
                (fun j => Function.update v i x j ⊗ₜ[K] m j) := by
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [h]

      have h4 : Function.update (fun j => v j ⊗ₜ[K] m j) i (y ⊗ₜ[K] m i) =
                (fun j => Function.update v i y j ⊗ₜ[K] m j) := by
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [h]

      calc
        (tprod K) (fun j => (Function.update v i (x + y)) j ⊗ₜ[K] m j)
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] m j) i ((x + y) ⊗ₜ[K] m i)) := by rw [h1]
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] m j) i (x ⊗ₜ[K] m i + y ⊗ₜ[K] m i)) := by rw [h2]
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] m j) i (x ⊗ₜ[K] m i)) +
            (tprod K) (Function.update (fun j => v j ⊗ₜ[K] m j) i (y ⊗ₜ[K] m i)) := by
            rw [MultilinearMap.map_update_add (tprod K) (fun j => v j ⊗ₜ[K] m j) i (x ⊗ₜ[K] m i) (y ⊗ₜ[K] m i)]
        _ = (tprod K) (fun j => (Function.update v i x) j ⊗ₜ[K] m j) +
            (tprod K) (fun j => (Function.update v i y) j ⊗ₜ[K] m j) := by rw [h3, h4]

    map_update_smul' v i c x := by
      apply _root_.PiTensorProduct.ext
      apply MultilinearMap.ext; intro m
      simp only [LinearMap.smul_apply, LinearMap.compMultilinearMap_apply]

      simp only [_root_.PiTensorProduct.lift.tprod]
      dsimp [interchangeAux, MultilinearMap.coe_mk]

      have h1 : (fun j => Function.update v i (c • x) j ⊗ₜ[K] m j) =
                Function.update (fun j => v j ⊗ₜ[K] m j) i ((c • x) ⊗ₜ[K] m i) := by
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [h]

      have h2 : Function.update (fun j => v j ⊗ₜ[K] m j) i ((c • x) ⊗ₜ[K] m i) =
                Function.update (fun j => v j ⊗ₜ[K] m j) i (c • (x ⊗ₜ[K] m i)) := by
         simp [TensorProduct.smul_tmul]

      calc
        (tprod K) (fun j => (Function.update v i (c • x)) j ⊗ₜ[K] m j)
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] m j) i ((c • x) ⊗ₜ[K] m i)) := by rw [h1]
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] m j) i (c • (x ⊗ₜ[K] m i))) := by rw [h2]
        _ = c • (tprod K) (Function.update (fun j => v j ⊗ₜ[K] m j) i (x ⊗ₜ[K] m i)) := by
            rw [MultilinearMap.map_update_smul (tprod K) (fun j => v j ⊗ₜ[K] m j) i c (x ⊗ₜ[K] m i)]
        _ = c • (tprod K) (fun j => (Function.update v i x) j ⊗ₜ[K] m j) := by
            congr 1; congr; ext j; by_cases h : j = i
            · subst h; simp
            · simp [h]


def interchange {ι : Type*} [Fintype ι] [DecidableEq ι] {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] :
    PiTensorProduct K V →ₗ[K] PiTensorProduct K W →ₗ[K] PiTensorProduct K (fun i => V i ⊗[K] W i) :=
  lift interchangeMap

/-- Naturality of the interchange map. -/
@[simp]
theorem liftMap_interchange {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V₁ V₂ V₃ V₄ : ι → Type*}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)]
    (f : ∀ i, V₁ i →ₗ[K] V₃ i) (g : ∀ i, V₂ i →ₗ[K] V₄ i)
    (t₁ : PiTensorProduct K V₁) (t₂ : PiTensorProduct K V₂) :
    liftMap (fun i => TensorProduct.map (f i) (g i)) (interchange t₁ t₂) =
    interchange (liftMap f t₁) (liftMap g t₂) := by
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul]
    induction t₂ using PiTensorProduct.induction_on with
    | smul_tprod c' v' =>
      simp only [map_smul]
      simp only [interchange, interchangeMap, liftMap, interchangeAux]
      simp [TensorProduct.map_tmul]
    | add x y ih1 ih2 =>
      simp only [map_add, ih1, ih2]
  | add x y ih1 ih2 =>
    simp only [map_add, LinearMap.add_apply, ih1, ih2]

/-- interchange on pure tensors gives a pure tensor of tensor products. -/
theorem interchange_tprod_K {ι : Type*} [Fintype ι] [DecidableEq ι] {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) = tprod K (fun i => v i ⊗ₜ[K] w i) := by
  dsimp [interchange]
  rw [PiTensorProduct.lift.tprod]
  dsimp [interchangeMap]
  rw [PiTensorProduct.lift.tprod]
  rfl

/-- Direct sum of two tensor objects. -/
def add (X Y : TensorObj K d) : TensorObj K d where
  V := fun i => X.V i × Y.V i
  t := liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
       liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t

/-- Tensor product of two tensor objects. -/
def mul (X Y : TensorObj K d) : TensorObj K d where
  V := fun i => X.V i ⊗[K] Y.V i
  t := interchange X.t Y.t

instance : Add (TensorObj K d) := ⟨add⟩
instance : Mul (TensorObj K d) := ⟨mul⟩

@[simp] theorem add_t (X Y : TensorObj K d) : (X + Y).t =
    liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
    liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t := rfl

@[simp] theorem mul_t (X Y : TensorObj K d) : (X * Y).t = interchange X.t Y.t := rfl

end

end TensorObj

namespace TensorObj

variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

/-- X is a restriction of Y (X ≤ Y) if there exists a family of linear maps f_i : Y.V_i → X.V_i
    such that the induced map on the tensor product sends Y.t to X.t. -/
def Restrict (X Y : TensorObj K d) : Prop :=
  ∃ f : ∀ i, Y.V i →ₗ[K] X.V i, liftMap f Y.t = X.t

theorem restrict_refl (X : TensorObj K d) : Restrict X X :=
  ⟨fun _ => LinearMap.id, liftMap_id X⟩

theorem restrict_trans {X Y Z : TensorObj K d} : Restrict X Y → Restrict Y Z → Restrict X Z := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩
  exact ⟨fun i => (f i).comp (g i), by rw [← liftMap_comp, hg, hf]⟩

end TensorObj

/-- An isomorphism between two `TensorObj` K d consists of:
    1. A family of linear equivalences `equiv : X.V i ≃ₗ[K] Y.V i` for each `i`.
    2. A compatibility condition `map_t` stating that the induced map on the tensor product
       sends `X.t` to `Y.t`. -/
structure TensorIso {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]
    (X Y : TensorObj K d) where
  equiv : ∀ i : Fin d, X.V i ≃ₗ[K] Y.V i
  /-- The induced map on the tensor product must send X.t to Y.t. -/
  map_t : TensorObj.liftMap (fun i => (equiv i).toLinearMap) X.t = Y.t

namespace TensorObj

variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

/-- The zero tensor object. -/
noncomputable def zeroObj : TensorObj.{u, v} K d where
  V := fun _ => PUnit
  t := 0

/-- The unit tensor object (1 ⊗ ⋯ ⊗ 1). -/
noncomputable def oneObj : TensorObj.{u, max u v} K d where
  V := fun _ => ULift.{v} K
  t := tprod K (fun _ => ULift.up 1)

/-- The equivalence relation: two tensor objects are isomorphic if there exists a `TensorIso`. -/
def Isomorphic (X Y : TensorObj K d) : Prop := Nonempty (TensorIso X Y)

/-- The isomorphism relation is an equivalence relation. -/
private theorem isomorphic_refl (X : TensorObj K d) : Isomorphic X X := by
  refine ⟨{ equiv := fun i => LinearEquiv.refl _ _, map_t := ?_ }⟩
  simp only [LinearEquiv.refl_toLinearMap]
  exact liftMap_id X

private theorem isomorphic_symm {X Y : TensorObj K d} : Isomorphic X Y → Isomorphic Y X := by
  rintro ⟨iso⟩
  refine ⟨{ equiv := fun i => (iso.equiv i).symm, map_t := ?_ }⟩
  rw [← iso.map_t, liftMap_comp]
  convert liftMap_id X using 2
  apply PiTensorProduct.ext
  apply MultilinearMap.ext; intro v
  simp

private theorem isomorphic_trans {X Y Z : TensorObj K d} : Isomorphic X Y → Isomorphic Y Z → Isomorphic X Z := by
  rintro ⟨iXY⟩ ⟨iYZ⟩
  refine ⟨{ equiv := fun i => (iXY.equiv i).trans (iYZ.equiv i), map_t := ?_ }⟩
  simp only [LinearEquiv.coe_trans]
  rw [← liftMap_comp, iXY.map_t, iYZ.map_t]

/-- The setoid structure on `TensorObj` defined by mutual restriction (X ~ Y iff X ≤ Y and Y ≤ X). -/
def tensorSetoid (K : Type u) [Field K] (d : ℕ) [Fact (1 < d)] : Setoid (TensorObj.{u, max u v} K d) where
  r X Y := TensorObj.Restrict X Y ∧ TensorObj.Restrict Y X
  iseqv := {
    refl  := fun X => ⟨restrict_refl X, restrict_refl X⟩
    symm  := fun ⟨h1, h2⟩ => ⟨h2, h1⟩
    trans := fun ⟨h1, h2⟩ ⟨h3, h4⟩ => ⟨restrict_trans h1 h3, restrict_trans h4 h2⟩
  }

/-- Addition respects mutual restriction. -/
theorem add_isomorphic {X Y Z W : TensorObj K d}
    (h1 : Restrict X Y ∧ Restrict Y X) (h2 : Restrict Z W ∧ Restrict W Z) :
    Restrict (X + Z) (Y + W) ∧ Restrict (Y + W) (X + Z) := by
  obtain ⟨⟨f, hf⟩, ⟨f', hf'⟩⟩ := h1
  obtain ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩ := h2
  constructor
  · refine ⟨fun i => LinearMap.prodMap (f i) (g i), ?_⟩
    simp only [add_t]
    have h1 : (fun i => LinearMap.prodMap (f i) (g i) ∘ₗ LinearMap.inl K (Y.V i) (W.V i)) =
              (fun i => LinearMap.inl K (X.V i) (Z.V i) ∘ₗ f i) := by
      funext i; ext x <;> simp [LinearMap.prodMap]
    have h2 : (fun i => LinearMap.prodMap (f i) (g i) ∘ₗ LinearMap.inr K (Y.V i) (W.V i)) =
              (fun i => LinearMap.inr K (X.V i) (Z.V i) ∘ₗ g i) := by
      funext i; ext x <;> simp [LinearMap.prodMap]
    have key : (liftMap (fun i => (f i).prodMap (g i)))
        ((liftMap (fun i => LinearMap.inl K (Y.V i) (W.V i))) Y.t +
         (liftMap (fun i => LinearMap.inr K (Y.V i) (W.V i))) W.t) =
        (liftMap (fun i => LinearMap.inl K (X.V i) (Z.V i))) X.t +
        (liftMap (fun i => LinearMap.inr K (X.V i) (Z.V i))) Z.t := by
      rw [(liftMap _).map_add, liftMap_comp, liftMap_comp, h1, h2, ← liftMap_comp, ← liftMap_comp, hf, hg]
    exact key
  · refine ⟨fun i => LinearMap.prodMap (f' i) (g' i), ?_⟩
    simp only [add_t]
    have h1 : (fun i => LinearMap.prodMap (f' i) (g' i) ∘ₗ LinearMap.inl K (X.V i) (Z.V i)) =
              (fun i => LinearMap.inl K (Y.V i) (W.V i) ∘ₗ f' i) := by
      funext i; ext x <;> simp [LinearMap.prodMap]
    have h2 : (fun i => LinearMap.prodMap (f' i) (g' i) ∘ₗ LinearMap.inr K (X.V i) (Z.V i)) =
              (fun i => LinearMap.inr K (Y.V i) (W.V i) ∘ₗ g' i) := by
      funext i; ext x <;> simp [LinearMap.prodMap]
    have key : (liftMap (fun i => (f' i).prodMap (g' i)))
        ((liftMap (fun i => LinearMap.inl K (X.V i) (Z.V i))) X.t +
         (liftMap (fun i => LinearMap.inr K (X.V i) (Z.V i))) Z.t) =
        (liftMap (fun i => LinearMap.inl K (Y.V i) (W.V i))) Y.t +
        (liftMap (fun i => LinearMap.inr K (Y.V i) (W.V i))) W.t := by
      rw [(liftMap _).map_add, liftMap_comp, liftMap_comp, h1, h2, ← liftMap_comp, ← liftMap_comp, hf', hg']
    exact key

/-- Helper: liftMap with a linear equiv applied to a sum of inl/inr. -/
private theorem add_comm_restrict (X Y : TensorObj K d) :
    Restrict (X + Y) (Y + X) :=
  ⟨fun i => (prodComm : (Y.V i × X.V i) ≃ₗ[K] (X.V i × Y.V i)).toLinearMap, by
    simp only [add_t]
    have h1 : (fun i => (prodComm : (Y.V i × X.V i) ≃ₗ[K] _).toLinearMap ∘ₗ LinearMap.inl K (Y.V i) (X.V i)) =
              fun i => LinearMap.inr K (X.V i) (Y.V i) := by
      funext i; ext x <;> simp [prodComm]
    have h2 : (fun i => (prodComm : (Y.V i × X.V i) ≃ₗ[K] _).toLinearMap ∘ₗ LinearMap.inr K (Y.V i) (X.V i)) =
              fun i => LinearMap.inl K (X.V i) (Y.V i) := by
      funext i; ext x <;> simp [prodComm]
    erw [(liftMap _).map_add, liftMap_comp, liftMap_comp, h1, h2]
    exact add_comm _ _⟩

theorem add_comm_isomorphic {X Y : TensorObj K d} :
    Restrict (X + Y) (Y + X) ∧ Restrict (Y + X) (X + Y) :=
  ⟨add_comm_restrict X Y, add_comm_restrict Y X⟩

private theorem add_assoc_restrict_aux (X Y Z : TensorObj K d)
    (x : PiTensorProduct K X.V) (y : PiTensorProduct K Y.V) (z : PiTensorProduct K Z.V) :
    (liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap))
      (liftMap (fun i => LinearMap.inl K (X.V i) ((Y + Z).V i)) x +
       liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
         (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) y +
          liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) z)) =
    liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
      (liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) x +
       liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) y) +
    liftMap (fun i => LinearMap.inr K ((X + Y).V i) (Z.V i)) z := by
  -- Direct induction: hA/hB/hC without liftMap_comp.
  -- hA: prodAssoc.symm (inl_X_YZ x) = inl_XY_Z (inl_X_Y x)
  -- hB: prodAssoc.symm (inr_X_YZ (inl_Y_Z y)) = inl_XY_Z (inr_X_Y y)
  -- hC: prodAssoc.symm (inr_X_YZ (inr_Y_Z z)) = inr_XY_Z z
  have hA : ∀ t : PiTensorProduct K X.V,
      liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)
        (liftMap (fun i => LinearMap.inl K (X.V i) ((Y + Z).V i)) t) =
      liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
        (liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) t) := by
    suffices h : ∀ t : PiTensorProduct K X.V,
        liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)
          (liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i × Z.V i)) t) =
        liftMap (fun i => LinearMap.inl K (X.V i × Y.V i) (Z.V i))
          (liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) t) from h
    intro t; induction t using PiTensorProduct.induction_on with
    | smul_tprod c v =>
        simp only [liftMap, PiTensorProduct.lift.tprod, LinearEquiv.prodAssoc, map_smul]; rfl
    | add t1 t2 ih1 ih2 => simp only [map_add, ih1, ih2]
  have hB : ∀ t : PiTensorProduct K Y.V,
      liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)
        (liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
          (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) t)) =
      liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
        (liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) t) := by
    suffices h : ∀ t : PiTensorProduct K Y.V,
        liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)
          (liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i × Z.V i))
            (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) t)) =
        liftMap (fun i => LinearMap.inl K (X.V i × Y.V i) (Z.V i))
          (liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) t) from h
    intro t; induction t using PiTensorProduct.induction_on with
    | smul_tprod c v =>
        simp [liftMap, PiTensorProduct.lift.tprod, LinearEquiv.prodAssoc, map_smul,
              MultilinearMap.compLinearMap_apply, LinearMap.inl_apply, LinearMap.inr_apply]
    | add t1 t2 ih1 ih2 => simp only [map_add, ih1, ih2]
  have hC : ∀ t : PiTensorProduct K Z.V,
      liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)
        (liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
          (liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) t)) =
      liftMap (fun i => LinearMap.inr K ((X + Y).V i) (Z.V i)) t := by
    suffices h : ∀ t : PiTensorProduct K Z.V,
        liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)
          (liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i × Z.V i))
            (liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) t)) =
        liftMap (fun i => LinearMap.inr K (X.V i × Y.V i) (Z.V i)) t from h
    intro t; induction t using PiTensorProduct.induction_on with
    | smul_tprod c v =>
        simp [liftMap, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
              LinearMap.inr_apply, LinearEquiv.prodAssoc]; norm_cast
    | add t1 t2 ih1 ih2 => simp only [map_add, ih1, ih2]
  -- apply hA/hB/hC by linearity
  have step1 : (liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap))
      (liftMap (fun i => LinearMap.inl K (X.V i) ((Y + Z).V i)) x +
       liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
         (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) y +
          liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) z)) =
      liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)
        (liftMap (fun i => LinearMap.inl K (X.V i) ((Y + Z).V i)) x) +
      liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)
        (liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
          (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) y +
           liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) z)) :=
    (liftMap _).map_add _ _
  have step2 : liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)
      (liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
        (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) y +
         liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) z)) =
      liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)
        (liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
          (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) y)) +
      liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)
        (liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
          (liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) z)) := by
    have hmid : liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
        (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) y +
         liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) z) =
        liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
          (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) y) +
        liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
          (liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) z) :=
      (liftMap _).map_add _ _
    rw [hmid]
    exact (liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)).map_add _ _
  have step3 : liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
      (liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) x +
       liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) y) =
      liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
        (liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) x) +
      liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
        (liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) y) :=
    (liftMap _).map_add _ _
  rw [step1, step2, hA, hB, hC, step3]
  abel

private theorem add_assoc_restrict (X Y Z : TensorObj K d) :
    Restrict (X + Y + Z) (X + (Y + Z)) :=
  ⟨fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap, by
    simp only [add_t]
    exact add_assoc_restrict_aux X Y Z X.t Y.t Z.t⟩

-- Auxiliary: liftMap prodAssoc on add_t = add_t rearranged (symmetric to add_assoc_restrict_aux)
private theorem add_assoc_bwd_aux (X Y Z : TensorObj K d)
    (x : PiTensorProduct K X.V) (y : PiTensorProduct K Y.V) (z : PiTensorProduct K Z.V) :
    (liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap))
      (liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
        (liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) x +
         liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) y) +
       liftMap (fun i => LinearMap.inr K ((X + Y).V i) (Z.V i)) z) =
    liftMap (fun i => LinearMap.inl K (X.V i) ((Y + Z).V i)) x +
    liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
      (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) y +
       liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) z) := by
  -- Direct induction: hA'/hB'/hC' without liftMap_comp.
  have hA' : ∀ t : PiTensorProduct K X.V,
      liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap)
        (liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
          (liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) t)) =
      liftMap (fun i => LinearMap.inl K (X.V i) ((Y + Z).V i)) t := by
    suffices h : ∀ t : PiTensorProduct K X.V,
        liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap)
          (liftMap (fun i => LinearMap.inl K (X.V i × Y.V i) (Z.V i))
            (liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) t)) =
        liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i × Z.V i)) t from h
    intro t; induction t using PiTensorProduct.induction_on with
    | smul_tprod c v =>
        simp only [liftMap, PiTensorProduct.lift.tprod, LinearEquiv.prodAssoc, map_smul,
                   MultilinearMap.compLinearMap_apply, LinearMap.inl_apply]; rfl
    | add t1 t2 ih1 ih2 => simp only [map_add, ih1, ih2]
  have hB' : ∀ t : PiTensorProduct K Y.V,
      liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap)
        (liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
          (liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) t)) =
      liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
        (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) t) := by
    suffices h : ∀ t : PiTensorProduct K Y.V,
        liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap)
          (liftMap (fun i => LinearMap.inl K (X.V i × Y.V i) (Z.V i))
            (liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) t)) =
        liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i × Z.V i))
          (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) t) from h
    intro t; induction t using PiTensorProduct.induction_on with
    | smul_tprod c v =>
        simp [liftMap, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
              LinearMap.inl_apply, LinearMap.inr_apply, LinearEquiv.prodAssoc]
    | add t1 t2 ih1 ih2 => simp only [map_add, ih1, ih2]
  have hC' : ∀ t : PiTensorProduct K Z.V,
      liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap)
        (liftMap (fun i => LinearMap.inr K ((X + Y).V i) (Z.V i)) t) =
      liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
        (liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) t) := by
    suffices h : ∀ t : PiTensorProduct K Z.V,
        liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap)
          (liftMap (fun i => LinearMap.inr K (X.V i × Y.V i) (Z.V i)) t) =
        liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i × Z.V i))
          (liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) t) from h
    intro t; induction t using PiTensorProduct.induction_on with
    | smul_tprod c v =>
        simp only [liftMap, PiTensorProduct.lift.tprod, LinearEquiv.prodAssoc, map_smul]; rfl
    | add t1 t2 ih1 ih2 => simp only [map_add, ih1, ih2]
  have step1' : (liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap))
      (liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
        (liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) x +
         liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) y) +
       liftMap (fun i => LinearMap.inr K ((X + Y).V i) (Z.V i)) z) =
      liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap)
        (liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
          (liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) x +
           liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) y)) +
      liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap)
        (liftMap (fun i => LinearMap.inr K ((X + Y).V i) (Z.V i)) z) :=
    (liftMap _).map_add _ _
  have step2' : liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap)
      (liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
        (liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) x +
         liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) y)) =
      liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap)
        (liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
          (liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) x)) +
      liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap)
        (liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
          (liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) y)) := by
    have hmid' : liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
        (liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) x +
         liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) y) =
        liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
          (liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) x) +
        liftMap (fun i => LinearMap.inl K ((X + Y).V i) (Z.V i))
          (liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) y) :=
      (liftMap _).map_add _ _
    rw [hmid']
    exact (liftMap (fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap)).map_add _ _
  have step3' : liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
      (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) y +
       liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) z) =
      liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
        (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) y) +
      liftMap (fun i => LinearMap.inr K (X.V i) ((Y + Z).V i))
        (liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) z) :=
    (liftMap _).map_add _ _
  rw [step1', step2', hA', hB', hC', step3']
  abel

theorem add_assoc_isomorphic {X Y Z : TensorObj K d} :
    Restrict (X + Y + Z) (X + (Y + Z)) ∧ Restrict (X + (Y + Z)) (X + Y + Z) :=
  ⟨add_assoc_restrict X Y Z,
   ⟨fun i => (LinearEquiv.prodAssoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap, by
    simp only [add_t]
    exact add_assoc_bwd_aux X Y Z X.t Y.t Z.t⟩⟩

/-- Multiplication respects mutual restriction. -/
theorem mul_isomorphic {X Y Z W : TensorObj K d}
    (h1 : Restrict X Y ∧ Restrict Y X) (h2 : Restrict Z W ∧ Restrict W Z) :
    Restrict (X * Z) (Y * W) ∧ Restrict (Y * W) (X * Z) := by
  obtain ⟨⟨f, hf⟩, ⟨f', hf'⟩⟩ := h1
  obtain ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩ := h2
  constructor
  · exact ⟨fun i => TensorProduct.map (f i) (g i), by
      simp only [mul_t]
      erw [liftMap_interchange, hf, hg]⟩
  · exact ⟨fun i => TensorProduct.map (f' i) (g' i), by
      simp only [mul_t]
      erw [liftMap_interchange, hf', hg']⟩

private theorem mul_comm_restrict_aux (X Y : TensorObj K d)
    (x : PiTensorProduct K X.V) (y : PiTensorProduct K Y.V) :
    (liftMap (fun i => (TensorProduct.comm K (Y.V i) (X.V i)).toLinearMap)) (interchange y x) =
    interchange x y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul]
    induction y using PiTensorProduct.induction_on with
    | smul_tprod c' v' =>
      dsimp only [interchange, interchangeMap, liftMap, interchangeAux]
      simp only [map_smul, LinearMap.smul_apply, smul_smul]
      simp only [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.coe_mk]
      rw [mul_comm c c']; congr 1
    | add y1 y2 ih1 ih2 =>
      simp only [map_add, LinearMap.add_apply, smul_add, ih1, ih2]
  | add x1 x2 ih1 ih2 =>
    simp only [LinearMap.add_apply, map_add, ih1, ih2]

private theorem mul_comm_restrict (X Y : TensorObj K d) : Restrict (X * Y) (Y * X) :=
  ⟨fun i => (TensorProduct.comm K (Y.V i) (X.V i)).toLinearMap, by
    simp only [mul_t]
    exact mul_comm_restrict_aux X Y X.t Y.t⟩

theorem mul_comm_isomorphic {X Y : TensorObj K d} :
    Restrict (X * Y) (Y * X) ∧ Restrict (Y * X) (X * Y) :=
  ⟨mul_comm_restrict X Y, mul_comm_restrict Y X⟩

/-- Associativity of the interchange map. -/
@[simp]
theorem interchange_assoc {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W U : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
    (tV : PiTensorProduct K V) (tW : PiTensorProduct K W) (tU : PiTensorProduct K U) :
    liftMap (fun i => (TensorProduct.assoc K (V i) (W i) (U i)).toLinearMap)
      (interchange (interchange tV tW) tU) =
    interchange tV (interchange tW tU) := by
  induction tV using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul, interchange, liftMap]
    induction tW using PiTensorProduct.induction_on with
    | smul_tprod c' w =>
      simp only [map_smul]
      induction tU using PiTensorProduct.induction_on with
      | smul_tprod c'' u =>
        dsimp [interchange, liftMap, interchangeMap, interchangeAux]
        simp only [map_smul, LinearMap.smul_apply, smul_smul]
        simp only [PiTensorProduct.lift.tprod, MultilinearMap.coe_mk, MultilinearMap.compLinearMap_apply]
        simp only [_root_.mul_comm, _root_.mul_left_comm]
        congr
      | add x y ih1 ih2 =>
        simp only [map_add, ih1, ih2]
    | add x y ih1 ih2 =>
      simp only [map_add, LinearMap.add_apply, ih1, ih2]
  | add x y ih1 ih2 =>
    simp only [map_add, LinearMap.add_apply, ih1, ih2]

-- Restrict (X*Y*Z) (X*(Y*Z)): f : (X*(Y*Z)).V i →ₗ (X*Y*Z).V i = assoc.symm
private theorem mul_assoc_restrict_fwd (X Y Z : TensorObj K d) : Restrict (X * Y * Z) (X * (Y * Z)) :=
  ⟨fun i => (TensorProduct.assoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap, by
    change liftMap (fun i => (TensorProduct.assoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap)
      (interchange X.t (interchange Y.t Z.t)) = interchange (interchange X.t Y.t) Z.t
    rw [← interchange_assoc, liftMap_comp]
    have : (fun i => (TensorProduct.assoc K (X.V i) (Y.V i) (Z.V i)).symm.toLinearMap ∘ₗ
            (TensorProduct.assoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap) =
           fun _ => LinearMap.id := by
      funext i; apply LinearMap.ext; intro v; simp
    rw [this]; exact liftMap_id (X * Y * Z)⟩

-- Restrict (X*(Y*Z)) (X*Y*Z): f : (X*Y*Z).V i →ₗ (X*(Y*Z)).V i = assoc
theorem mul_assoc_isomorphic {X Y Z : TensorObj K d} :
    Restrict (X * Y * Z) (X * (Y * Z)) ∧ Restrict (X * (Y * Z)) (X * Y * Z) :=
  ⟨mul_assoc_restrict_fwd X Y Z,
   ⟨fun i => (TensorProduct.assoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap, by
    change liftMap (fun i => (TensorProduct.assoc K (X.V i) (Y.V i) (Z.V i)).toLinearMap)
      (interchange (interchange X.t Y.t) Z.t) = interchange X.t (interchange Y.t Z.t)
    rw [interchange_assoc]⟩⟩

-- Restrict (X + zeroObj) X: embed X into X+zeroObj via inl
-- f : X.V i →ₗ (X+zeroObj).V i, need liftMap inl X.t = (X+zeroObj).t
private theorem add_zero_restrict_fwd (X : TensorObj K d) : Restrict (X + zeroObj) X :=
  ⟨fun i => LinearMap.inl K (X.V i) PUnit, by
    simp only [add_t, zeroObj, map_zero, add_zero]; rfl⟩

-- Restrict X (X + zeroObj): project X+zeroObj to X via fst
-- f : (X+zeroObj).V i →ₗ X.V i, need liftMap fst (X+zeroObj).t = X.t
theorem add_zero_isomorphic {X : TensorObj K d} :
    Restrict (X + zeroObj) X ∧ Restrict X (X + zeroObj) :=
  ⟨add_zero_restrict_fwd X,
   ⟨fun i => LinearMap.fst K (X.V i) PUnit, by
    have : liftMap (fun i => LinearMap.fst K (X.V i) PUnit) ((X + zeroObj).t) = X.t := by
      simp only [add_t, zeroObj, map_zero, add_zero]
      have heq : (fun i => (LinearMap.fst K (X.V i) PUnit).comp (LinearMap.inl K (X.V i) PUnit)) =
                 fun _ => LinearMap.id := by funext i; ext; rfl
      rw [liftMap_comp, heq, liftMap_id]
    exact this⟩⟩

-- Restrict (zeroObj + X) X: embed X into zeroObj+X via inr
-- f : X.V i →ₗ (zeroObj+X).V i, need liftMap inr X.t = (zeroObj+X).t
private theorem zero_add_restrict_fwd (X : TensorObj K d) : Restrict (zeroObj + X) X :=
  ⟨fun i => LinearMap.inr K PUnit (X.V i), by
    simp only [add_t, zeroObj, map_zero, zero_add]; rfl⟩

-- Restrict X (zeroObj + X): project via snd
-- f : (zeroObj+X).V i →ₗ X.V i, need liftMap snd (zeroObj+X).t = X.t
theorem zero_add_isomorphic {X : TensorObj K d} :
    Restrict (zeroObj + X) X ∧ Restrict X (zeroObj + X) :=
  ⟨zero_add_restrict_fwd X,
   ⟨fun i => LinearMap.snd K PUnit (X.V i), by
    have : liftMap (fun i => LinearMap.snd K PUnit (X.V i)) ((zeroObj + X).t) = X.t := by
      simp only [add_t, zeroObj, map_zero, zero_add]
      have heq : (fun i => (LinearMap.snd K PUnit (X.V i)).comp (LinearMap.inr K PUnit (X.V i))) =
                 fun _ => LinearMap.id := by funext i; ext; rfl
      rw [liftMap_comp, heq, liftMap_id]
    exact this⟩⟩

-- one_mul: oneObj * X ~ X
-- Restrict (oneObj * X) X: f : X.V i →ₗ (oneObj*X).V i = ULift K ⊗ X.V i
-- We prove this by showing liftMap tensorOne.symm X.t = interchange oneObj.t X.t
-- via: liftMap tensorOne (liftMap tensorOne.symm X.t) = X.t = liftMap tensorOne (interchange ...)
private theorem one_mul_restrict_fwd (X : TensorObj K d) : Restrict (oneObj * X) X := by
  refine ⟨fun i => tensorOne.symm.toLinearMap, ?_⟩
  simp only [mul_t]
  have hTO_symm_TO : (fun i => (tensorOne (K := K) (V := X.V i)).symm.toLinearMap ∘ₗ
      (tensorOne (K := K) (V := X.V i)).toLinearMap) = fun _ => LinearMap.id := by
    funext i; apply LinearMap.ext; intro v; simp [tensorOne]
  have hTO_TO_symm : (fun i => (tensorOne (K := K) (V := X.V i)).toLinearMap ∘ₗ
      (tensorOne (K := K) (V := X.V i)).symm.toLinearMap) = fun _ => LinearMap.id := by
    funext i; apply LinearMap.ext; intro v; simp [tensorOne]
  -- suffices: liftMap tensorOne (liftMap tensorOne.symm X.t) = liftMap tensorOne (interchange oneObj.t X.t)
  -- since liftMap tensorOne is injective (has left inverse liftMap tensorOne.symm)
  suffices liftMap (fun i => (tensorOne (K := K) (V := X.V i)).toLinearMap)
      (liftMap (fun i => (tensorOne (K := K) (V := X.V i)).symm.toLinearMap) X.t) =
      liftMap (fun i => (tensorOne (K := K) (V := X.V i)).toLinearMap) (interchange oneObj.t X.t) by
    have hinj : Function.Injective
        (liftMap (fun i => (tensorOne (K := K) (V := X.V i)).toLinearMap)) := by
      intro a b hab
      have := congr_arg (liftMap (fun i => (tensorOne (K := K) (V := X.V i)).symm.toLinearMap)) hab
      rw [liftMap_comp, liftMap_comp] at this
      rw [hTO_symm_TO] at this
      unfold liftMap at this; simp at this
      exact this
    exact hinj this
  rw [liftMap_comp, hTO_TO_symm, liftMap_id]
  -- Now prove X.t = liftMap tensorOne (interchange oneObj.t X.t)
  symm
  induction X.t using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    change liftMap (fun i => tensorOne.toLinearMap)
      (interchange (tprod K (fun _ => ULift.up 1)) (c • tprod K v)) = c • tprod K v
    dsimp only [interchange, liftMap, interchangeMap, interchangeAux]
    simp only [map_smul, PiTensorProduct.lift.tprod, MultilinearMap.coe_mk,
               MultilinearMap.compLinearMap_apply]
    congr 1; apply congr_arg; funext i
    simp [tensorOne, uliftEquiv, TensorProduct.lid, TensorProduct.congr]
  | add t1 t2 ih1 ih2 =>
    simp only [(interchange oneObj.t).map_add]
    rw [show (liftMap (fun i => (tensorOne (K := K) (V := X.V i)).toLinearMap)
                ((interchange oneObj.t) t1 + (interchange oneObj.t) t2)) =
            (liftMap (fun i => (tensorOne (K := K) (V := X.V i)).toLinearMap)) ((interchange oneObj.t) t1) +
            (liftMap (fun i => (tensorOne (K := K) (V := X.V i)).toLinearMap)) ((interchange oneObj.t) t2)
          from (liftMap _).map_add _ _]
    rw [ih1, ih2]

-- Restrict X (oneObj * X): f : (oneObj*X).V i = ULift K ⊗ X.V i →ₗ X.V i, i.e. tensorOne
-- liftMap tensorOne (interchange oneObj.t X.t) = X.t
theorem one_mul_isomorphic {X : TensorObj K d} :
    Restrict (oneObj * X) X ∧ Restrict X (oneObj * X) :=
  ⟨one_mul_restrict_fwd X,
   ⟨fun i => tensorOne.toLinearMap, by
    change liftMap (fun i => tensorOne.toLinearMap) (interchange oneObj.t X.t) = X.t
    induction X.t using PiTensorProduct.induction_on with
    | smul_tprod c v =>
      change liftMap (fun i => tensorOne.toLinearMap) (interchange (tprod K (fun _ => ULift.up 1)) (c • tprod K v)) = c • tprod K v
      dsimp only [interchange, liftMap, interchangeMap, interchangeAux]
      simp only [map_smul, PiTensorProduct.lift.tprod, MultilinearMap.coe_mk, MultilinearMap.compLinearMap_apply]
      congr 1; apply congr_arg; funext i
      simp [tensorOne, uliftEquiv, TensorProduct.lid, TensorProduct.congr]
    | add t1 t2 ih1 ih2 =>
      dsimp only [interchange, liftMap] at ih1 ih2 ⊢
      simp only [map_add, ih1, ih2]⟩⟩

theorem mul_one_isomorphic {X : TensorObj K d} :
    Restrict (X * oneObj) X ∧ Restrict X (X * oneObj) :=
  let hc := mul_comm_isomorphic (X := X) (Y := oneObj)
  let h1 := one_mul_isomorphic (X := X)
  ⟨restrict_trans hc.1 h1.1, restrict_trans h1.2 hc.2⟩

-- Restrict (X*(Y+Z)) (X*Y+X*Z): f : (X*Y+X*Z).V i →ₗ (X*(Y+Z)).V i = distribLeft.symm
-- liftMap distribLeft.symm (X*Y+X*Z).t = (X*(Y+Z)).t
private theorem mul_add_restrict_fwd (X Y Z : TensorObj K d) : Restrict (X * (Y + Z)) (X * Y + X * Z) :=
  ⟨fun i => distribLeft.symm.toLinearMap, by
    simp only [mul_t, add_t]
    -- need: liftMap distribLeft.symm ((liftMap inl) (interchange X.t Y.t) + (liftMap inr) (interchange X.t Z.t))
    --     = interchange X.t ((liftMap inl) Y.t + (liftMap inr) Z.t)
    have h1 : (fun i => (distribLeft (K := K) (M := X.V i) (N := Y.V i) (P := Z.V i)).symm.toLinearMap ∘ₗ
               LinearMap.inl K (X.V i ⊗ Y.V i) (X.V i ⊗ Z.V i)) =
              fun i => TensorProduct.map LinearMap.id (LinearMap.inl K (Y.V i) (Z.V i)) := by
      funext i; apply LinearMap.ext; intro v
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        simp only [LinearMap.comp_apply, LinearMap.inl_apply, distribLeft]
        change (TensorProduct.prodRight K K (X.V i) (Y.V i) (Z.V i)).symm (x ⊗ₜ[K] y, 0) = _
        rw [show (0 : X.V i ⊗[K] Z.V i) = x ⊗ₜ[K] (0 : Z.V i) by simp,
            TensorProduct.prodRight_symm_tmul]
        simp [TensorProduct.map_tmul]
      | add a b iha ihb => simp [map_add, iha, ihb]
    have h2 : (fun i => (distribLeft (K := K) (M := X.V i) (N := Y.V i) (P := Z.V i)).symm.toLinearMap ∘ₗ
               LinearMap.inr K (X.V i ⊗ Y.V i) (X.V i ⊗ Z.V i)) =
              fun i => TensorProduct.map LinearMap.id (LinearMap.inr K (Y.V i) (Z.V i)) := by
      funext i; apply LinearMap.ext; intro v
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul x z =>
        simp only [LinearMap.comp_apply, LinearMap.inr_apply, distribLeft]
        change (TensorProduct.prodRight K K (X.V i) (Y.V i) (Z.V i)).symm (0, x ⊗ₜ[K] z) = _
        rw [show (0 : X.V i ⊗[K] Y.V i) = x ⊗ₜ[K] (0 : Y.V i) by simp,
            TensorProduct.prodRight_symm_tmul]
        simp [TensorProduct.map_tmul]
      | add a b iha ihb => simp [map_add, iha, ihb]
    have key : (liftMap (fun i => (distribLeft (K := K) (M := X.V i) (N := Y.V i) (P := Z.V i)).symm.toLinearMap))
        ((liftMap (fun i => LinearMap.inl K (X.V i ⊗ Y.V i) (X.V i ⊗ Z.V i))) ((interchange X.t) Y.t) +
         (liftMap (fun i => LinearMap.inr K (X.V i ⊗ Y.V i) (X.V i ⊗ Z.V i))) ((interchange X.t) Z.t)) =
        (interchange X.t) ((liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i))) Y.t +
         (liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i))) Z.t) := by
      rw [(liftMap _).map_add, liftMap_comp, liftMap_comp, h1, h2,
          liftMap_interchange, liftMap_interchange]
      simp only [liftMap_id, ← map_add]
    exact key⟩

-- Restrict (X*Y+X*Z) (X*(Y+Z)): f : (X*(Y+Z)).V i →ₗ (X*Y+X*Z).V i = distribLeft
-- liftMap distribLeft (interchange X.t (Y+Z).t) = (X*Y+X*Z).t
theorem mul_add_isomorphic {X Y Z : TensorObj K d} :
    Restrict (X * (Y + Z)) (X * Y + X * Z) ∧ Restrict (X * Y + X * Z) (X * (Y + Z)) :=
  ⟨mul_add_restrict_fwd X Y Z,
   ⟨fun i => distribLeft.toLinearMap, by
    change liftMap (fun i => distribLeft.toLinearMap) (interchange X.t (Y + Z).t) = (X * Y + X * Z).t
    change liftMap (fun i => distribLeft.toLinearMap) (interchange X.t (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) Y.t + liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) Z.t)) = _
    rw [map_add, map_add]
    congr 1
    · have h1 : interchange X.t (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) Y.t) =
                liftMap (fun i => TensorProduct.map LinearMap.id (LinearMap.inl K (Y.V i) (Z.V i))) (interchange X.t Y.t) := by
        conv_lhs => rw [← liftMap_id X]
        rw [← liftMap_interchange]
      rw [h1, liftMap_comp]
      apply congr_arg (fun h => liftMap h _)
      funext i; apply LinearMap.ext; intro v
      simp only [LinearMap.comp_apply, distribLeft, TensorProduct.prodRight, LinearEquiv.coe_coe]
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp; change _ = (LinearMap.inl K (X.V i ⊗ Y.V i) (X.V i ⊗ Z.V i)) (x ⊗ₜ y); erw [LinearMap.inl_apply]
      | add a b iha ihb => simp only [map_add, iha, ihb]
    · have h1 : interchange X.t (liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) Z.t) =
                liftMap (fun i => TensorProduct.map LinearMap.id (LinearMap.inr K (Y.V i) (Z.V i))) (interchange X.t Z.t) := by
        conv_lhs => rw [← liftMap_id X]
        rw [← liftMap_interchange]
      rw [h1, liftMap_comp]
      apply congr_arg (fun h => liftMap h _)
      funext i; apply LinearMap.ext; intro v
      simp only [LinearMap.comp_apply, distribLeft, TensorProduct.prodRight, LinearEquiv.coe_coe]
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul x z => simp; change _ = (LinearMap.inr K (X.V i ⊗ Y.V i) (X.V i ⊗ Z.V i)) (x ⊗ₜ z); erw [LinearMap.inr_apply]
      | add a b iha ihb => simp only [map_add, iha, ihb]⟩⟩

theorem add_mul_isomorphic {X Y Z : TensorObj K d} :
    Restrict ((X + Y) * Z) (X * Z + Y * Z) ∧ Restrict (X * Z + Y * Z) ((X + Y) * Z) :=
  let hc1 := mul_comm_isomorphic (X := X + Y) (Y := Z)
  let hma := mul_add_isomorphic (X := Z) (Y := X) (Z := Y)
  let hcX := mul_comm_isomorphic (X := Z) (Y := X)
  let hcY := mul_comm_isomorphic (X := Z) (Y := Y)
  let hadd := add_isomorphic hcX hcY
  ⟨restrict_trans hc1.1 (restrict_trans hma.1 hadd.1),
   restrict_trans hadd.2 (restrict_trans hma.2 hc1.2)⟩

theorem zero_mul_isomorphic {X : TensorObj K d} :
    Restrict (zeroObj * X) zeroObj ∧ Restrict zeroObj (zeroObj * X) :=
  -- Both zeroObj.t and (zeroObj * X).t are 0, so liftMap of any f applied to 0 = 0
  have hzm : (zeroObj * X).t = 0 := by
    simp only [mul_t, zeroObj]
    exact (interchange (0 : PiTensorProduct K (fun _ : Fin d => PUnit))).map_zero
  ⟨⟨fun _ => 0, by simp only [show (zeroObj : TensorObj K d).t = 0 from rfl, map_zero, hzm]⟩,
   ⟨fun _ => 0, by simp only [hzm, map_zero, show (zeroObj : TensorObj K d).t = 0 from rfl]⟩⟩
end TensorObj

/-- The quotient of `TensorObj` by linear isomorphism. -/
def Tensor (K : Type u) [Field K] (d : ℕ) [Fact (1 < d)] :=
  Quotient (TensorObj.tensorSetoid.{u, max u v} K d)

namespace Tensor

open TensorObj
variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

/-- Decategorification map. -/
def toTensor (X : TensorObj.{u, max u v} K d) : Tensor.{u, v} K d :=
  Quotient.mk (tensorSetoid.{u, max u v} K d) X

/-- Zero and One objects (minimal placeholders). -/
noncomputable def zeroObj : TensorObj.{u, max u v} K d := TensorObj.zeroObj
noncomputable def oneObj : TensorObj.{u, max u v} K d := TensorObj.oneObj

noncomputable instance : Zero (Tensor.{u, v} K d) := ⟨toTensor zeroObj⟩
noncomputable instance : One (Tensor.{u, v} K d) := ⟨toTensor oneObj⟩

/-- Lift addition to the quotient. -/
noncomputable def add (x y : Tensor K d) : Tensor K d :=
  Quotient.liftOn₂ x y
    (fun X Y => toTensor (X + Y))
    (fun _ _ _ _ hab hcd => Quotient.sound (add_isomorphic hab hcd))

/-- Lift multiplication to the quotient. -/
noncomputable def mul (x y : Tensor K d) : Tensor K d :=
  Quotient.liftOn₂ x y
    (fun X Y => toTensor (X * Y))
    (fun _ _ _ _ hab hcd => Quotient.sound (mul_isomorphic hab hcd))

noncomputable instance : Add (Tensor.{u, v} K d) := ⟨add⟩
noncomputable instance : Mul (Tensor.{u, v} K d) := ⟨mul⟩

section QuotientHelpers

variable {X Y Z : TensorObj.{u, max u v} K d}

/-- Helper to lift a unary operation equality proof from TensorObj to Tensor. -/
theorem lift_unary_iso {f g : Tensor K d → Tensor K d} {F G : TensorObj K d → TensorObj K d}
    (h_lift_f : ∀ X, f (toTensor X) = toTensor (F X))
    (h_lift_g : ∀ X, g (toTensor X) = toTensor (G X))
    (h_iso : ∀ X, Restrict (F X) (G X) ∧ Restrict (G X) (F X)) : ∀ x, f x = g x := by
  intro x
  induction x using Quotient.inductionOn with | h X =>
  change f (toTensor X) = g (toTensor X)
  rw [h_lift_f, h_lift_g]
  exact Quotient.sound (h_iso X)

/-- Helper to lift a binary operation equality proof from TensorObj to Tensor. -/
theorem lift_binary_iso {f g : Tensor K d → Tensor K d → Tensor K d}
    {F G : TensorObj K d → TensorObj K d → TensorObj K d}
    (h_lift_f : ∀ X Y, f (toTensor X) (toTensor Y) = toTensor (F X Y))
    (h_lift_g : ∀ X Y, g (toTensor X) (toTensor Y) = toTensor (G X Y))
    (h_iso : ∀ X Y, Restrict (F X Y) (G X Y) ∧ Restrict (G X Y) (F X Y)) : ∀ x y, f x y = g x y := by
  intro x y
  induction x using Quotient.inductionOn with | h X =>
  induction y using Quotient.inductionOn with | h Y =>
  change f (toTensor X) (toTensor Y) = g (toTensor X) (toTensor Y)
  rw [h_lift_f, h_lift_g]
  exact Quotient.sound (h_iso X Y)

/-- Helper to lift a ternary operation equality proof from TensorObj to Tensor. -/
theorem lift_ternary_iso {f g : Tensor K d → Tensor K d → Tensor K d → Tensor K d}
    {F G : TensorObj K d → TensorObj K d → TensorObj K d → TensorObj K d}
    (h_lift_f : ∀ X Y Z, f (toTensor X) (toTensor Y) (toTensor Z) = toTensor (F X Y Z))
    (h_lift_g : ∀ X Y Z, g (toTensor X) (toTensor Y) (toTensor Z) = toTensor (G X Y Z))
    (h_iso : ∀ X Y Z, Restrict (F X Y Z) (G X Y Z) ∧ Restrict (G X Y Z) (F X Y Z)) : ∀ x y z, f x y z = g x y z := by
  intro x y z
  induction x using Quotient.inductionOn with | h X =>
  induction y using Quotient.inductionOn with | h Y =>
  induction z using Quotient.inductionOn with | h Z =>
  change f (toTensor X) (toTensor Y) (toTensor Z) = g (toTensor X) (toTensor Y) (toTensor Z)
  rw [h_lift_f, h_lift_g]
  exact Quotient.sound (h_iso X Y Z)

end QuotientHelpers

section Isomorphisms

variable {X Y Z : TensorObj.{u, max u v} K d}

theorem add_comm (x y : Tensor K d) : x + y = y + x :=
  lift_binary_iso (f := Tensor.add) (g := fun a b => b + a) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => add_comm_isomorphic) x y

theorem add_assoc (x y z : Tensor K d) : x + y + z = x + (y + z) :=
  lift_ternary_iso (f := fun a b c => a + b + c) (g := fun a b c => a + (b + c))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => add_assoc_isomorphic) x y z

theorem zero_add (x : Tensor K d) : 0 + x = x :=
  lift_unary_iso (f := fun a => 0 + a) (g := id)
    (fun _ => rfl) (fun _ => rfl) (fun _ => zero_add_isomorphic) x

theorem add_zero (x : Tensor K d) : x + 0 = x :=
  lift_unary_iso (f := fun a => a + 0) (g := id)
    (fun _ => rfl) (fun _ => rfl) (fun _ => add_zero_isomorphic) x

theorem mul_comm (x y : Tensor K d) : x * y = y * x :=
  lift_binary_iso (f := Tensor.mul) (g := fun a b => b * a)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => mul_comm_isomorphic) x y

theorem mul_assoc (x y z : Tensor K d) : x * y * z = x * (y * z) :=
  lift_ternary_iso (f := fun a b c => a * b * c) (g := fun a b c => a * (b * c))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => mul_assoc_isomorphic) x y z

theorem one_mul (x : Tensor K d) : 1 * x = x :=
  lift_unary_iso (f := fun a => 1 * a) (g := id)
    (fun _ => rfl) (fun _ => rfl) (fun _ => one_mul_isomorphic) x

theorem mul_one (x : Tensor K d) : x * 1 = x :=
  lift_unary_iso (f := fun a => a * 1) (g := id)
    (fun _ => rfl) (fun _ => rfl) (fun _ => mul_one_isomorphic) x

theorem mul_add (x y z : Tensor K d) : x * (y + z) = x * y + x * z :=
  lift_ternary_iso (f := fun a b c => a * (b + c)) (g := fun a b c => a * b + a * c)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => mul_add_isomorphic) x y z

theorem add_mul (x y z : Tensor K d) : (x + y) * z = x * z + y * z :=
  lift_ternary_iso (f := fun a b c => (a + b) * c) (g := fun a b c => a * c + b * c)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => add_mul_isomorphic) x y z

theorem zero_mul (x : Tensor K d) : 0 * x = 0 :=
  lift_unary_iso (f := fun a => 0 * a) (g := fun _ => 0)
    (fun _ => rfl) (fun _ => rfl) (fun _ => zero_mul_isomorphic) x

theorem mul_zero (x : Tensor K d) : x * 0 = 0 :=
  by rw [mul_comm, zero_mul]

private noncomputable def natCast (n : ℕ) : Tensor K d := nsmulRec n 1

end Isomorphisms

noncomputable instance : CommSemiring (Tensor.{u, v} K d) where
  add := add
  zero := 0
  mul := mul
  one := 1
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul

  mul_zero := mul_zero
  nsmul := nsmulRec
  npow := npowRec
  natCast := natCast
  natCast_zero := rfl
  natCast_succ n := by
    simp only [natCast, nsmulRec, add_comm]

end Tensor
