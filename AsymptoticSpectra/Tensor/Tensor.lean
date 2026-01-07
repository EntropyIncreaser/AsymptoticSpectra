import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Logic.Basic
import Mathlib.Algebra.Module.ULift

universe u v w

open BigOperators TensorProduct

-- We open PiTensorProduct, but distinct names prevent clashes with the type
open PiTensorProduct

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

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

/-- Functoriality of PiTensorProduct: a family of linear maps induces a map on the tensor product.
    Renamed to `liftMap` to avoid namespace conflicts. -/
noncomputable def liftMap {ι : Type*} [Fintype ι] {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) : PiTensorProduct K V →ₗ[K] PiTensorProduct K W :=
  lift <| (tprod K).compLinearMap f

/-- Helper to construct interchange map definition -/
noncomputable def interchangeAux {ι : Type*} [Fintype ι] [DecidableEq ι] {V W : ι → Type*}
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

/-- Interchange map: (⨂ V_i) ⊗ (⨂ W_i) → ⨂ (V_i ⊗ W_i). -/
noncomputable def interchange {ι : Type*} [Fintype ι] [DecidableEq ι] {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] :
    PiTensorProduct K V →ₗ[K] PiTensorProduct K W →ₗ[K] PiTensorProduct K (fun i => V i ⊗[K] W i) :=
  lift interchangeMap

/-- Direct sum of two tensor objects. -/
noncomputable def add (X Y : TensorObj K d) : TensorObj K d where
  V := fun i => X.V i × Y.V i
  t := liftMap (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
       liftMap (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t

/-- Tensor product of two tensor objects. -/
noncomputable def mul (X Y : TensorObj K d) : TensorObj K d where
  V := fun i => X.V i ⊗[K] Y.V i
  t := interchange X.t Y.t

noncomputable instance : Add (TensorObj K d) := ⟨add⟩
noncomputable instance : Mul (TensorObj K d) := ⟨mul⟩

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
theorem isomorphic_refl (X : TensorObj K d) : Isomorphic X X := by
  refine ⟨{ equiv := fun i => LinearEquiv.refl _ _, map_t := ?_ }⟩
  simp only [LinearEquiv.refl_toLinearMap]
  -- Show lift of identity is identity
  have h_id : liftMap (fun (i : Fin d) => (LinearMap.id : X.V i →ₗ[K] X.V i)) = LinearMap.id := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro m
    simp [liftMap, lift_tprod]
  exact DFunLike.congr_fun h_id X.t

theorem isomorphic_symm {X Y : TensorObj K d} : Isomorphic X Y → Isomorphic Y X := sorry
theorem isomorphic_trans {X Y Z : TensorObj K d} : Isomorphic X Y → Isomorphic Y Z → Isomorphic X Z := sorry

/-- The setoid structure on `TensorObj` defined by isomorphism. -/
def tensorSetoid (K : Type u) [Field K] (d : ℕ) [Fact (1 < d)] : Setoid (TensorObj.{u, max u v} K d) where
  r := Isomorphic
  iseqv := {
    refl := isomorphic_refl
    symm := isomorphic_symm
    trans := isomorphic_trans
  }

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
    (fun a b c d hab hcd => by
       dsimp [toTensor]
       apply Quotient.sound
       -- Isomorphic.add hab hcd
       sorry)

/-- Lift multiplication to the quotient. -/
noncomputable def mul (x y : Tensor K d) : Tensor K d :=
  Quotient.liftOn₂ x y
    (fun X Y => toTensor (X * Y))
    (fun a b c d hab hcd => by
       dsimp [toTensor]
       apply Quotient.sound
       -- Isomorphic.mul hab hcd
       sorry)

noncomputable instance : Add (Tensor.{u, v} K d) := ⟨add⟩
noncomputable instance : Mul (Tensor.{u, v} K d) := ⟨mul⟩

section Isomorphisms

variable {X Y Z : TensorObj.{u, max u v} K d}

theorem add_comm (x y : Tensor K d) : x + y = y + x := by
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  dsimp [add, toTensor]
  apply Quotient.sound
  exact ⟨{ equiv := fun i => sorry, map_t := sorry }⟩

theorem add_assoc (x y z : Tensor K d) : x + y + z = x + (y + z) := by
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  induction z using Quotient.inductionOn
  dsimp [add, toTensor]
  apply Quotient.sound
  exact ⟨{ equiv := fun i => sorry, map_t := sorry }⟩

theorem zero_add (x : Tensor K d) : 0 + x = x := by
  induction x using Quotient.inductionOn
  dsimp [add, toTensor]
  apply Quotient.sound
  exact ⟨{ equiv := fun i => sorry, map_t := sorry }⟩

theorem add_zero (x : Tensor K d) : x + 0 = x := by
  rw [add_comm, zero_add]

theorem mul_comm (x y : Tensor K d) : x * y = y * x := by
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  dsimp [mul, toTensor]
  apply Quotient.sound
  exact ⟨{ equiv := fun i => sorry, map_t := sorry }⟩

theorem mul_assoc (x y z : Tensor K d) : x * y * z = x * (y * z) := by
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  induction z using Quotient.inductionOn
  dsimp [mul, toTensor]
  apply Quotient.sound
  exact ⟨{ equiv := fun i => sorry, map_t := sorry }⟩

theorem one_mul (x : Tensor K d) : 1 * x = x := by
  induction x using Quotient.inductionOn
  dsimp [mul, toTensor]
  apply Quotient.sound
  exact ⟨{ equiv := fun i => sorry , map_t := sorry }⟩

theorem mul_one (x : Tensor K d) : x * 1 = x := by
  rw [mul_comm, one_mul]

theorem mul_add (x y z : Tensor K d) : x * (y + z) = x * y + x * z := by
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  induction z using Quotient.inductionOn
  dsimp [mul, add, toTensor]
  apply Quotient.sound
  exact ⟨{ equiv := fun i => sorry, map_t := sorry }⟩

theorem add_mul (x y z : Tensor K d) : (x + y) * z = x * z + y * z := by
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  induction z using Quotient.inductionOn
  dsimp [mul, add, toTensor]
  apply Quotient.sound
  exact ⟨{ equiv := fun i => sorry, map_t := sorry }⟩

theorem zero_mul (x : Tensor K d) : 0 * x = 0 := by
  induction x using Quotient.inductionOn
  dsimp [mul, toTensor]
  apply Quotient.sound
  exact ⟨{ equiv := fun i => sorry, map_t := sorry }⟩

theorem mul_zero (x : Tensor K d) : x * 0 = 0 := by
  rw [mul_comm, zero_mul]

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
  natCast_zero := sorry
  natCast_succ := sorry

end Tensor
