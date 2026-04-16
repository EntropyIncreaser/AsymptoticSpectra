import AsymptoticSpectra.Tensor.Tensor
import AsymptoticSpectra.Tensor.Restriction
import AsymptoticSpectra.Spectrum
import Mathlib.GroupTheory.Perm.Basic

universe u

open TensorObj PiTensorProduct BigOperators

/-!
# Mode permutations for tensors

This file defines the action of permutations on tensors (permuting mode spaces),
proves it descends to the quotient `Tensor K d`, and constructs the permuted
spectrum point `φ^σ` for any asymptotic spectrum point `φ`.

Convention: `permuteSpaces σ X` has mode spaces `V i := X.V (σ.symm i)`,
matching `PiTensorProduct.reindex`:
  `reindex R s σ : (⨂ i, s i) ≃ₗ (⨂ i, s (σ.symm i))`.
-/

variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

/-! ## reindex commutes with interchange -/

/-- Reindexing commutes with the interchange map:
    `reindex σ (interchange t₁ t₂) = interchange (reindex σ t₁) (reindex σ t₂)`. -/
theorem reindex_interchange {ι : Type*} [Fintype ι] [DecidableEq ι] {ι₂ : Type*} [Fintype ι₂]
    [DecidableEq ι₂] {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (σ : ι ≃ ι₂) (t₁ : PiTensorProduct K V) (t₂ : PiTensorProduct K W) :
    (reindex K (fun i => TensorProduct K (V i) (W i)) σ) (TensorObj.interchange t₁ t₂) =
    TensorObj.interchange (reindex K V σ t₁) (reindex K W σ t₂) := by
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c₁ v₁ =>
    induction t₂ using PiTensorProduct.induction_on with
    | smul_tprod c₂ v₂ =>
      simp [map_smul, TensorObj.interchange_tprod_K, PiTensorProduct.reindex_tprod]
    | add x y ihx ihy =>
      simp only [map_add, map_smul, LinearMap.smul_apply, LinearMap.map_add,
                 LinearMap.add_apply]
      -- ihx and ihy have c₁ • tprod v₁, but after simp the smul is distributed
      -- Use map linearity: simp pulls c₁ • outside, leaving tprod v₁
      -- The IH with c₁ • : reindex (interchange (c₁ • tprod v₁) x) = interchange (reindex (c₁ • tprod v₁)) (reindex x)
      -- Which equals c₁ • reindex (interchange (tprod v₁) x) = c₁ • interchange (reindex (tprod v₁)) (reindex x)
      -- So we need: c₁ • reindex (...x) + c₁ • reindex (...y) = c₁ • interchange ... (reindex x) + c₁ • interchange ... (reindex y)
      -- Pull out c₁ from ihx/ihy using smul_right linearity
      have hx : (reindex K (fun i => TensorProduct K (V i) (W i)) σ)
          ((TensorObj.interchange (c₁ • tprod K v₁)) x) =
          (TensorObj.interchange ((reindex K V σ) (c₁ • tprod K v₁))) ((reindex K W σ) x) := ihx
      have hy : (reindex K (fun i => TensorProduct K (V i) (W i)) σ)
          ((TensorObj.interchange (c₁ • tprod K v₁)) y) =
          (TensorObj.interchange ((reindex K V σ) (c₁ • tprod K v₁))) ((reindex K W σ) y) := ihy
      simp only [map_smul, LinearMap.smul_apply] at hx hy
      rw [hx, hy]
  | add x y ihx ihy =>
    simp only [map_add, LinearMap.add_apply, LinearMap.map_add, ihx, ihy]

namespace TensorObj

/-! ## permuteSpaces on TensorObj -/

/-- Permute the mode spaces of a `TensorObj` by `σ : Equiv.Perm (Fin d)`.
    Mode `i` in the result comes from mode `σ.symm i` in the input. -/
@[reducible] noncomputable def permuteSpaces (σ : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    TensorObj K d where
  V i := X.V (σ.symm i)
  addCommGroup i := X.addCommGroup (σ.symm i)
  module i := X.module (σ.symm i)
  finiteDimensional i := X.finiteDimensional (σ.symm i)
  t := PiTensorProduct.reindex K X.V σ X.t

/-- `permuteSpaces σ` respects `TensorObj.Restrict`. -/
theorem permuteSpaces_restrict (σ : Equiv.Perm (Fin d)) {X Y : TensorObj K d}
    (h : TensorObj.Restrict X Y) :
    TensorObj.Restrict (permuteSpaces σ X) (permuteSpaces σ Y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun i => f (σ.symm i), ?_⟩
  simp only [permuteSpaces]
  -- Goal: liftMap (fun i => f (σ.symm i)) (reindex K Y.V σ Y.t) = reindex K X.V σ X.t
  -- Key: map_comp_reindex_eq says:
  --   (map fun i => f (σ.symm i)) ∘ (reindex K Y.V σ) = (reindex K X.V σ) ∘ (map f)
  -- i.e., as linear maps applied to Y.t:
  --   liftMap (fun i => f (σ.symm i)) (reindex σ Y.t) = reindex σ (liftMap f Y.t)
  -- and liftMap f Y.t = X.t by hf.
  -- Use map_reindex: (map fun i => f (σ.symm i)) (reindex σ Y.t) = reindex σ (map f Y.t)
  -- liftMap f = PiTensorProduct.map f definitionally
  show PiTensorProduct.map (fun i => f (σ.symm i)) ((PiTensorProduct.reindex K Y.V σ) Y.t) =
      (PiTensorProduct.reindex K X.V σ) X.t
  rw [PiTensorProduct.map_reindex]
  congr 1

/-- `permuteSpaces` preserves mutual `TensorObj.Restrict`. -/
theorem permuteSpaces_isomorphic (σ : Equiv.Perm (Fin d)) {X Y : TensorObj K d}
    (h : TensorObj.Restrict X Y ∧ TensorObj.Restrict Y X) :
    TensorObj.Restrict (permuteSpaces σ X) (permuteSpaces σ Y) ∧
    TensorObj.Restrict (permuteSpaces σ Y) (permuteSpaces σ X) :=
  ⟨permuteSpaces_restrict σ h.1, permuteSpaces_restrict σ h.2⟩

/-- `permuteSpaces σ (X + Y)` is (mutually) isomorphic to `permuteSpaces σ X + permuteSpaces σ Y`. -/
theorem permuteSpaces_add_restrict (σ : Equiv.Perm (Fin d)) (X Y : TensorObj K d) :
    TensorObj.Restrict (permuteSpaces σ (X + Y)) (permuteSpaces σ X + permuteSpaces σ Y) ∧
    TensorObj.Restrict (permuteSpaces σ X + permuteSpaces σ Y) (permuteSpaces σ (X + Y)) := by
  -- Key: both sides have the same V i = X.V (σ.symm i) × Y.V (σ.symm i),
  -- and the tensor elements are related by: reindex commutes with inl/inr via map_reindex.
  -- Specifically: reindex σ (liftMap inl X.t) = liftMap inl (reindex σ X.t)
  -- (and same for inr), which gives the isomorphism.
  constructor
  · refine ⟨fun i => LinearMap.id, ?_⟩
    simp only [permuteSpaces, add_t]
    show PiTensorProduct.map (fun i => LinearMap.id)
        (PiTensorProduct.map (fun i => LinearMap.inl K (X.V (σ.symm i)) (Y.V (σ.symm i))) ((PiTensorProduct.reindex K X.V σ) X.t) +
         PiTensorProduct.map (fun i => LinearMap.inr K (X.V (σ.symm i)) (Y.V (σ.symm i))) ((PiTensorProduct.reindex K Y.V σ) Y.t)) =
      (PiTensorProduct.reindex K (fun i => X.V i × Y.V i) σ)
        (PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
         PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t)
    rw [PiTensorProduct.map_id, LinearMap.id_apply,
        (PiTensorProduct.reindex K (fun i => X.V i × Y.V i) σ).map_add,
        ← PiTensorProduct.map_reindex (f := fun i => LinearMap.inl K (X.V i) (Y.V i)) σ X.t,
        ← PiTensorProduct.map_reindex (f := fun i => LinearMap.inr K (X.V i) (Y.V i)) σ Y.t]
  · refine ⟨fun i => LinearMap.id, ?_⟩
    simp only [permuteSpaces, add_t]
    show PiTensorProduct.map (fun i => LinearMap.id)
        ((PiTensorProduct.reindex K (fun i => X.V i × Y.V i) σ)
          (PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
           PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t)) =
      PiTensorProduct.map (fun i => LinearMap.inl K (X.V (σ.symm i)) (Y.V (σ.symm i))) ((PiTensorProduct.reindex K X.V σ) X.t) +
      PiTensorProduct.map (fun i => LinearMap.inr K (X.V (σ.symm i)) (Y.V (σ.symm i))) ((PiTensorProduct.reindex K Y.V σ) Y.t)
    rw [PiTensorProduct.map_id, LinearMap.id_apply,
        (PiTensorProduct.reindex K (fun i => X.V i × Y.V i) σ).map_add,
        ← PiTensorProduct.map_reindex (f := fun i => LinearMap.inl K (X.V i) (Y.V i)) σ X.t,
        ← PiTensorProduct.map_reindex (f := fun i => LinearMap.inr K (X.V i) (Y.V i)) σ Y.t]

end TensorObj

namespace Tensor

open TensorObj

variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

/-! ## permuteSpaces on Tensor (quotient) -/

/-- Permute the mode spaces on the quotient `Tensor K d`. -/
noncomputable def permuteSpaces (σ : Equiv.Perm (Fin d)) (x : Tensor K d) : Tensor K d :=
  Quotient.liftOn x
    (fun X => toTensor (X.permuteSpaces σ))
    (fun X Y h => Quotient.sound (TensorObj.permuteSpaces_isomorphic σ h))

@[simp]
theorem permuteSpaces_toTensor (σ : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    permuteSpaces σ (toTensor X) = toTensor (X.permuteSpaces σ) := rfl

/-- `permuteSpaces σ` preserves addition. -/
theorem permuteSpaces_add (σ : Equiv.Perm (Fin d)) (x y : Tensor K d) :
    permuteSpaces σ (x + y) = permuteSpaces σ x + permuteSpaces σ y := by
  induction x using Quotient.inductionOn with | h X =>
  induction y using Quotient.inductionOn with | h Y =>
  -- ⟦X⟧ + ⟦Y⟧ = ⟦X + Y⟧ by definition of Tensor.add
  show toTensor ((X + Y).permuteSpaces σ) = toTensor (X.permuteSpaces σ) + toTensor (Y.permuteSpaces σ)
  apply Quotient.sound
  exact TensorObj.permuteSpaces_add_restrict σ X Y

/-- `permuteSpaces σ` preserves multiplication. -/
theorem permuteSpaces_mul (σ : Equiv.Perm (Fin d)) (x y : Tensor K d) :
    permuteSpaces σ (x * y) = permuteSpaces σ x * permuteSpaces σ y := by
  induction x using Quotient.inductionOn with | h X =>
  induction y using Quotient.inductionOn with | h Y =>
  show toTensor ((X * Y).permuteSpaces σ) = toTensor (X.permuteSpaces σ) * toTensor (Y.permuteSpaces σ)
  apply Quotient.sound
  -- Both sides have V i = X.V (σ.symm i) ⊗ Y.V (σ.symm i), restrict via id
  -- t of (X * Y).permuteSpaces σ = reindex σ (interchange X.t Y.t)
  -- t of permuteSpaces σ X * permuteSpaces σ Y = interchange (reindex σ X.t) (reindex σ Y.t)
  -- These are equal by reindex_interchange
  -- liftMap id = id as a linear map on any PiTensorProduct
  -- Key equality: reindex σ (interchange X.t Y.t) = interchange (reindex X.t) (reindex Y.t)
  have hkey := reindex_interchange σ X.t Y.t
  -- Both permuteSpaces σ (X*Y) and permuteSpaces σ X * permuteSpaces σ Y have
  -- V i = X.V (σ.symm i) ⊗ Y.V (σ.symm i)
  -- and their t's are equal by hkey.
  -- For Restrict: we need f : (second).V i →ₗ[K] (first).V i and liftMap f (second).t = (first).t
  -- Use f = LinearMap.id (which works since V i is definitionally equal on both sides)
  -- liftMap id = id on permuteSpaces σ X * permuteSpaces σ Y spaces
  -- V i = X.V (σ.symm i) ⊗ Y.V (σ.symm i) for both TensorObjs
  have liftId : ∀ (t : PiTensorProduct K (fun i => TensorProduct K (X.V (σ.symm i)) (Y.V (σ.symm i)))),
      liftMap (fun i => (LinearMap.id : TensorProduct K (X.V (σ.symm i)) (Y.V (σ.symm i)) →ₗ[K] _)) t = t := by
    intro t
    have : liftMap (fun i => (LinearMap.id : TensorProduct K (X.V (σ.symm i)) (Y.V (σ.symm i)) →ₗ[K] _)) =
        LinearMap.id := by
      apply PiTensorProduct.ext; apply MultilinearMap.ext; intro v; simp [liftMap]
    simp [this]
  constructor
  · refine ⟨fun i => LinearMap.id, ?_⟩
    simp only [TensorObj.permuteSpaces, TensorObj.mul_t]
    exact liftId _ |>.trans hkey.symm
  · refine ⟨fun i => LinearMap.id, ?_⟩
    simp only [TensorObj.permuteSpaces, TensorObj.mul_t]
    -- goal: liftMap id (reindex (X*Y).V σ (interchange X.t Y.t)) = interchange (reindex X.t) (reindex Y.t)
    -- (X*Y).V is definitionally fun i => X.V i ⊗ Y.V i, so reindex agrees with hkey
    have heqV : (reindex K (X * Y).V σ) ((interchange X.t) Y.t) =
        (reindex K (fun i => TensorProduct K (X.V i) (Y.V i)) σ) ((interchange X.t) Y.t) := rfl
    rw [heqV, hkey]; exact liftId _

/-- `permuteSpaces σ` preserves zero. -/
theorem permuteSpaces_zero (σ : Equiv.Perm (Fin d)) :
    permuteSpaces σ (0 : Tensor K d) = 0 := by
  apply Quotient.sound
  -- Both zeroObj.permuteSpaces σ and zeroObj have t = 0.
  -- liftMap (fun _ => 0) 0 = 0 and reindex σ 0 = 0.
  -- permuteSpaces σ zeroObj has V i = PUnit and t = 0, same as zeroObj
  -- both t's are 0 (PiTensorProduct over PUnit is trivial), so restrict via zero maps
  have hzt : (zeroObj (K := K) (d := d)).t = 0 := rfl
  have hpt : (TensorObj.permuteSpaces σ (zeroObj (K := K) (d := d))).t = 0 := by
    show (PiTensorProduct.reindex K zeroObj.V σ) zeroObj.t = 0
    rw [hzt, map_zero]
  constructor <;> refine ⟨fun _ => 0, ?_⟩
  · show (liftMap fun _ => (0 : _ →ₗ[K] _)) zeroObj.t = (TensorObj.permuteSpaces σ zeroObj).t
    rw [hzt, hpt, map_zero]
  · show (liftMap fun _ => (0 : _ →ₗ[K] _)) (TensorObj.permuteSpaces σ zeroObj).t = zeroObj.t
    rw [hpt, hzt, map_zero]

/-- `permuteSpaces σ` preserves one. -/
theorem permuteSpaces_one (σ : Equiv.Perm (Fin d)) :
    permuteSpaces σ (1 : Tensor K d) = 1 := by
  apply Quotient.sound
  -- permuteSpaces σ oneObj has V i = ULift K and
  -- t = reindex σ (tprod K (fun _ => ULift.up 1)) = tprod K (fun _ => ULift.up 1) = oneObj.t
  -- So both sides equal oneObj; restrict via id maps
  have ht : (TensorObj.permuteSpaces σ (TensorObj.oneObj (K := K) (d := d))).t =
      TensorObj.oneObj.t := by
    simp only [TensorObj.permuteSpaces, TensorObj.oneObj]
    convert PiTensorProduct.reindex_tprod σ (fun _ => (⟨1⟩ : ULift K)) using 1
  constructor
  · refine ⟨fun _ => LinearMap.id, ?_⟩
    show liftMap (fun _ => LinearMap.id) TensorObj.oneObj.t = (TensorObj.permuteSpaces σ TensorObj.oneObj).t
    rw [liftMap_id TensorObj.oneObj]; exact ht.symm
  · refine ⟨fun _ => LinearMap.id, ?_⟩
    show liftMap (fun _ => LinearMap.id) (TensorObj.permuteSpaces σ TensorObj.oneObj).t = TensorObj.oneObj.t
    rw [ht]; exact liftMap_id TensorObj.oneObj

/-- `permuteSpaces σ` as a ring homomorphism `Tensor K d →+* Tensor K d`. -/
noncomputable def permuteSpacesRingHom (σ : Equiv.Perm (Fin d)) : Tensor K d →+* Tensor K d where
  toFun := permuteSpaces σ
  map_one' := permuteSpaces_one σ
  map_mul' := permuteSpaces_mul σ
  map_zero' := permuteSpaces_zero σ
  map_add' := permuteSpaces_add σ

/-- `permuteSpaces σ` is monotone for the canonical `Tensor.Restrict` preorder. -/
theorem permuteSpaces_mono (σ : Equiv.Perm (Fin d)) {x y : Tensor K d}
    (h : x ≤ y) : permuteSpaces σ x ≤ permuteSpaces σ y := by
  induction x using Quotient.inductionOn with | h X =>
  induction y using Quotient.inductionOn with | h Y =>
  exact TensorObj.permuteSpaces_restrict σ h

end Tensor

/-! ## Permuted spectrum points -/

namespace AsymptoticSpectrumPoint

variable (P : StrassenPreorder (Tensor K d))

/-- Given a spectrum point `φ`, a permutation `σ`, and a proof that `permuteSpaces σ` is
    monotone for `P.le`, define the permuted spectrum point `φ^σ(x) = φ(permuteSpaces σ x)`. -/
noncomputable def perm (φ : AsymptoticSpectrumPoint (Tensor K d) P)
    (σ : Equiv.Perm (Fin d))
    (h_mono : ∀ a b : Tensor K d, P.le a b → P.le (Tensor.permuteSpaces σ a) (Tensor.permuteSpaces σ b)) :
    AsymptoticSpectrumPoint (Tensor K d) P where
  toRingHom :=
  { toFun := fun x => φ (Tensor.permuteSpaces σ x)
    map_one' := by simp [Tensor.permuteSpaces_one, map_one]
    map_mul' := fun x y => by simp [Tensor.permuteSpaces_mul, map_mul]
    map_zero' := by simp [Tensor.permuteSpaces_zero, map_zero]
    map_add' := fun x y => by simp [Tensor.permuteSpaces_add, map_add] }
  monotone' := by
    intro a b h
    exact φ.monotone' (h_mono a b h)

theorem perm_apply (φ : AsymptoticSpectrumPoint (Tensor K d) P) (σ : Equiv.Perm (Fin d))
    (h_mono : ∀ a b : Tensor K d, P.le a b → P.le (Tensor.permuteSpaces σ a) (Tensor.permuteSpaces σ b))
    (x : Tensor K d) :
    φ.perm P σ h_mono x = φ (Tensor.permuteSpaces σ x) := rfl

end AsymptoticSpectrumPoint
