import AsymptoticSpectra.Tensor.Tensor
import AsymptoticSpectra.Tensor.Flattening
import AsymptoticSpectra.Structures
import AsymptoticSpectra.Spectrum
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

universe u v w

open TensorObj PiTensorProduct

namespace Tensor

open TensorObj PiTensorProduct

variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

/-- Restriction on the quotient: X ≤ Y if the TensorObj representative of X restricts to Y's. -/
def Restrict (x y : Tensor K d) : Prop :=
  Quotient.liftOn₂ x y TensorObj.Restrict
    (fun _ _ _ _ ⟨h1, h2⟩ ⟨h3, h4⟩ => propext
      ⟨fun h => restrict_trans (restrict_trans h2 h) h3,
       fun h => restrict_trans (restrict_trans h1 h) h4⟩)

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

private theorem restrict_add_right (X Y Z : TensorObj K d)
    (h : TensorObj.Restrict X Y) : TensorObj.Restrict (X + Z) (Y + Z) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun i => LinearMap.prodMap (f i) LinearMap.id, ?_⟩
  simp only [add_t]
  erw [map_add, liftMap_comp, liftMap_comp]
  have h1 : liftMap (fun i => (f i).prodMap LinearMap.id ∘ₗ LinearMap.inl K (Y.V i) (Z.V i)) Y.t =
      liftMap (fun i => LinearMap.inl K (X.V i) (Z.V i)) X.t := by
    have heq : (fun i => (f i).prodMap LinearMap.id ∘ₗ LinearMap.inl K (Y.V i) (Z.V i)) =
        (fun i => LinearMap.inl K (X.V i) (Z.V i) ∘ₗ f i) := by
      funext i; ext x <;> simp [LinearMap.prodMap, LinearMap.inl]
    erw [heq, ← liftMap_comp, hf]
  have h2 : liftMap (fun i => (f i).prodMap LinearMap.id ∘ₗ LinearMap.inr K (Y.V i) (Z.V i)) Z.t =
      liftMap (fun i => LinearMap.inr K (X.V i) (Z.V i)) Z.t := by
    have heq : (fun i => (f i).prodMap LinearMap.id ∘ₗ LinearMap.inr K (Y.V i) (Z.V i)) =
        (fun i => LinearMap.inr K (X.V i) (Z.V i)) := by
      funext i; ext x <;> simp [LinearMap.prodMap, LinearMap.inr]
    erw [heq]
  exact h1 ▸ h2 ▸ rfl

private theorem restrict_mul_right (X Y Z : TensorObj K d)
    (h : TensorObj.Restrict X Y) : TensorObj.Restrict (X * Z) (Y * Z) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun i => TensorProduct.map (f i) LinearMap.id, ?_⟩
  simp only [mul_t]
  erw [liftMap_interchange, hf, liftMap_id]

private theorem restrict_zero_le (X : TensorObj K d) : TensorObj.Restrict zeroObj X := by
  refine ⟨fun i => 0, ?_⟩
  show (liftMap fun _ => (0 : X.V _ →ₗ[K] PUnit)) X.t = 0
  have : liftMap (fun _ => (0 : X.V _ →ₗ[K] PUnit)) = (0 : PiTensorProduct K (X.V) →ₗ[K] _) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext; intro v
    simp [liftMap]
    exact PiTensorProduct.zero_tprodCoeff' 1 _ 0 (Subsingleton.elim _ _)
  rw [this, LinearMap.zero_apply]

instance instSemiringPreorder : SemiringPreorder (Tensor K d) where
  add_right := fun x y h z => by
    induction x using Quotient.inductionOn with | h X => ?_
    induction y using Quotient.inductionOn with | h Y => ?_
    induction z using Quotient.inductionOn with | h Z => ?_
    exact restrict_add_right X Y Z h
  mul_right := fun x y h z => by
    induction x using Quotient.inductionOn with | h X => ?_
    induction y using Quotient.inductionOn with | h Y => ?_
    induction z using Quotient.inductionOn with | h Z => ?_
    exact restrict_mul_right X Y Z h
  zero_le := fun x => by
    induction x using Quotient.inductionOn with | h X => ?_
    exact restrict_zero_le X

theorem flatteningRank_mono (σ : AsymptoticSpectra.Split (Fin d)) :
  ∀ {x y : Tensor K d}, x ≤ y → AsymptoticSpectra.Tensor.flatteningRankReal σ x ≤ AsymptoticSpectra.Tensor.flatteningRankReal σ y := by
    intro x y h
    induction x using Quotient.inductionOn with | h X => ?_
    induction y using Quotient.inductionOn with | h Y => ?_
    simp only [AsymptoticSpectra.Tensor.flatteningRankReal]
    exact_mod_cast AsymptoticSpectra.flatteningRank_mono σ h

open PiTensorProduct in
/-- A `TensorObj` where each component space is `Fin r → K`, and whose tensor element is
    the "diagonal" tensor `∑ j, ⊗_i eⱼ` (standard basis vectors). This is the canonical
    object representing a sum of r pure tensors. -/
noncomputable def diagObj (r : ℕ) : TensorObj K d where
  V := fun _ => Fin r → K
  t := ∑ j : Fin r, tprod K (fun (_ : Fin d) => Pi.single j (1 : K))

/-- X restricts to diagObj r iff X.t is a sum of r pure tensors -/
theorem restrict_iff_sum_tprod {X : TensorObj K d} {r : ℕ} :
    TensorObj.Restrict X (diagObj r) ↔
    ∃ v : Fin r → ∀ i, X.V i, X.t = ∑ j, PiTensorProduct.tprod K (fun i => v j i) := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun j i => f i (Pi.single j 1), ?_⟩
    rw [← hf]
    simp only [diagObj]
    have liftMap_tprod_eq : ∀ (w : ∀ i : Fin d, (diagObj r).V i),
        liftMap f (PiTensorProduct.tprod K w) = PiTensorProduct.tprod K (fun i => f i (w i)) :=
      fun w => by simp [liftMap]
    calc liftMap f (∑ j : Fin r, (PiTensorProduct.tprod K) fun x => Pi.single j (1 : K))
        = ∑ j : Fin r, liftMap f ((PiTensorProduct.tprod K) fun x => Pi.single j (1 : K)) := by
          induction r with
          | zero => simp [liftMap]
          | succ n ih => simp
      _ = ∑ j : Fin r, PiTensorProduct.tprod K (fun i : Fin d => f i (Pi.single j 1)) := by
          congr 1; ext j; exact liftMap_tprod_eq _
  · rintro ⟨v, hv⟩
    refine ⟨fun i => (Pi.basisFun K (Fin r)).constr K (fun j => v j i), ?_⟩
    simp only [diagObj]
    have liftMap_tprod_eq : ∀ (w : ∀ i : Fin d, (diagObj r).V i),
        liftMap (fun i => (Pi.basisFun K (Fin r)).constr K (fun j => v j i))
          (PiTensorProduct.tprod K w) =
        PiTensorProduct.tprod K (fun i => (Pi.basisFun K (Fin r)).constr K (fun j => v j i) (w i)) :=
      fun w => by simp [liftMap]
    calc liftMap (fun i => (Pi.basisFun K (Fin r)).constr K (fun j => v j i))
          (∑ j : Fin r, (PiTensorProduct.tprod K) fun x => Pi.single j (1 : K))
        = ∑ j : Fin r, liftMap (fun i => (Pi.basisFun K (Fin r)).constr K (fun j => v j i))
            ((PiTensorProduct.tprod K) fun x => Pi.single j (1 : K)) := by
          induction r with
          | zero => simp [liftMap]
          | succ n ih => simp
      _ = ∑ j : Fin r, PiTensorProduct.tprod K (fun i : Fin d => v j i) := by
          congr 1; ext j
          rw [liftMap_tprod_eq]
          congr 1; ext i
          simp
      _ = X.t := hv.symm

/-- diagObj r ≤ (r : Tensor K d) -/
theorem diagObj_le_natCast (r : ℕ) :
    (toTensor (diagObj r) : Tensor K d) ≤ (r : Tensor K d) := by
  induction r with
  | zero =>
      -- diagObj 0 has t = 0, so it restricts to zeroObj
      show TensorObj.Restrict (diagObj (K := K) (d := d) 0) (zeroObj (K := K) (d := d))
      refine ⟨fun _ => 0, ?_⟩
      show liftMap (fun _ => (0 : (zeroObj (K := K) (d := d)).V _ →ₗ[K]
          (diagObj (K := K) (d := d) 0).V _)) (zeroObj.t) = (diagObj 0).t
      have hzt : (zeroObj (K := K) (d := d)).t = 0 := rfl
      have hdt : (diagObj (K := K) (d := d) 0).t = 0 := by simp [diagObj]; rfl
      rw [hzt, map_zero, hdt]
  | succ n ih =>
      -- We show diagObj (n+1) ≤ diagObj n + oneObj in TensorObj,
      -- using restrict_iff_sum_tprod (backward direction):
      -- exhibit v : Fin (n+1) → ∀ i, (diagObj n + oneObj).V i such that
      -- (diagObj n + oneObj).t = ∑ j, tprod K (v j)
      -- Then combine with ih and the SemiringPreorder monotonicity.
      -- Strategy: use diagObj 1 (V i = Fin 1 → K, Type u) instead of oneObj (V i = ULift K)
      -- to avoid universe mismatch. Then:
      --   diagObj (n+1) ≤ diagObj n + diagObj 1   (TensorObj restriction, all in Type u)
      --   toTensor (diagObj 1) = 1                 (iso with oneObj)
      --   diagObj n + diagObj 1 ≤ ↑n + 1 = ↑(n+1) (by ih)
      -- First: diagObj (n+1) ≤ diagObj n + diagObj 1 (as TensorObj, all Type u)
      have hstep : TensorObj.Restrict (diagObj (K := K) (d := d) (n + 1))
          (diagObj (K := K) (d := d) n + diagObj (K := K) (d := d) 1) := by
        -- Work with explicit types: (diagObj n + diagObj 1).V i = (Fin n → K) × (Fin 1 → K)
        --                           (diagObj (n+1)).V i = Fin (n+1) → K
        -- f i maps (v, w) ↦ Fin.lastCases (w 0) (v ·)
        let fFst : (Fin n → K) →ₗ[K] (Fin (n + 1) → K) :=
          (Pi.basisFun K (Fin n)).constr K
            (fun j' => Pi.basisFun K (Fin (n + 1)) (Fin.castSucc j'))
        let fSnd : (Fin 1 → K) →ₗ[K] (Fin (n + 1) → K) :=
          (Pi.basisFun K (Fin 1)).constr K
            (fun _ => Pi.basisFun K (Fin (n + 1)) (Fin.last n))
        -- The key computation: liftMap (fFst.coprod fSnd) (diagObj n + diagObj 1).t
        --   = (diagObj (n+1)).t
        -- We prove this by showing both equal ∑ j : Fin (n+1), tprod K (fun _ => Pi.single j 1)
        have hkey : liftMap (fun _ : Fin d => fFst.coprod fSnd)
            ((diagObj (K := K) (d := d) n + diagObj (K := K) (d := d) 1).t) =
            (diagObj (K := K) (d := d) (n + 1)).t := by
          simp only [diagObj, add_t]
          -- Both sums are in PiTensorProduct K (fun _ : Fin d => (Fin n → K) × (Fin 1 → K))
          -- The liftMap is of type:
          --   PiTensorProduct K (fun _ => (Fin n → K) × (Fin 1 → K)) →ₗ PiTensorProduct K (fun _ => Fin (n+1) → K)
          -- Proceed by pure tensor computation
          -- Apply map_add, then liftMap_comp to merge the two nested liftMaps
          rw [map_add,
              liftMap_comp (fun _ => fFst.coprod fSnd) (fun _ => LinearMap.inl K (Fin n → K) (Fin 1 → K)),
              liftMap_comp (fun _ => fFst.coprod fSnd) (fun _ => LinearMap.inr K (Fin n → K) (Fin 1 → K))]
          -- Now simplify: (coprod fFst fSnd) ∘ inl = fFst, (coprod fFst fSnd) ∘ inr = fSnd
          simp only [LinearMap.coprod_inl, LinearMap.coprod_inr]
          -- Compute liftMap fFst and liftMap fSnd on pure tensor sums
          simp only [map_sum, liftMap_tprod]
          -- fFst (Pi.single j' 1) = Pi.basisFun K (Fin n) → Pi.basisFun K (Fin (n+1)) (castSucc)
          -- by Basis.constr_basis
          have hfFst : ∀ j' : Fin n, fFst (Pi.single j' 1) =
              Pi.single (Fin.castSucc j') (1 : K) := fun j' => by
            have hb : Pi.single j' (1 : K) = Pi.basisFun K (Fin n) j' := by
              simp [Pi.basisFun_apply]
            rw [hb]
            show ((Pi.basisFun K (Fin n)).constr K
              (fun j'' => Pi.basisFun K (Fin (n + 1)) (Fin.castSucc j'')))
              (Pi.basisFun K (Fin n) j') = Pi.single (Fin.castSucc j') 1
            rw [Module.Basis.constr_basis]
            simp [Pi.basisFun_apply]
          have hfSnd : fSnd (Pi.single (0 : Fin 1) (1 : K)) =
              Pi.single (Fin.last n) (1 : K) := by
            have hb : Pi.single (0 : Fin 1) (1 : K) = Pi.basisFun K (Fin 1) 0 := by
              simp [Pi.basisFun_apply]
            rw [hb]
            show ((Pi.basisFun K (Fin 1)).constr K
              (fun _ => Pi.basisFun K (Fin (n + 1)) (Fin.last n)))
              (Pi.basisFun K (Fin 1) 0) = Pi.single (Fin.last n) 1
            rw [Module.Basis.constr_basis]
            simp [Pi.basisFun_apply]
          simp only [hfFst]
          -- For fSnd sum: ∑ j : Fin 1, ... = the single term at j = 0
          simp only [Fin.sum_univ_one]
          -- goal shape: (∑ x, tprod (castSucc)) + tprod (fSnd (Pi.single 0 1))
          --           = ∑ j : Fin (n+1), tprod (Pi.single j 1)
          conv_lhs =>
            rw [show (fun _ : Fin d => fSnd (Pi.single (0 : Fin 1) (1 : K))) =
                fun _ : Fin d => Pi.single (Fin.last n) (1 : K) from
              funext (fun _ => hfSnd)]
          -- RHS: split ∑ j : Fin (n+1) into castSucc part + last part
          conv_rhs => rw [Fin.sum_univ_castSucc]
        exact ⟨fun _ => fFst.coprod fSnd, hkey⟩
      -- Second: toTensor (diagObj 1) = (1 : Tensor K d)
      -- Both diagObj 1 and oneObj live in TensorObj.{u, max u v}, so restriction is well-typed.
      have hone : toTensor (diagObj (K := K) (d := d) 1) = (1 : Tensor K d) := by
        apply Quotient.sound
        constructor
        · -- Restrict (diagObj 1) oneObj: f i : oneObj.V i →ₗ (diagObj 1).V i
          --   i.e., ULift.{v} K →ₗ Fin 1 → K,  via u ↦ fun _ => u.down
          refine ⟨fun _ => (show (oneObj (K := K) (d := d)).V 0 →ₗ[K]
                (diagObj (K := K) (d := d) 1).V 0 from
                { toFun    := fun u _ => u.down
                  map_add' := fun _ _ => rfl
                  map_smul' := fun _ _ => rfl }), ?_⟩
          -- Goal: liftMap f oneObj.t = (diagObj 1).t
          -- Unfold oneObj.t and diagObj.t explicitly
          change liftMap _ (tprod K (fun _ : Fin d => ULift.up (1 : K))) =
              ∑ j : Fin 1, tprod K (fun _ : Fin d => Pi.single j (1 : K))
          rw [liftMap_tprod, Finset.univ_unique, Finset.sum_singleton]
          -- goal: tprod K (fun i => f (ULift.up 1)) = tprod K (fun _ => Pi.single 0 1)
          -- f (ULift.up 1) = fun _ => 1 = Pi.single 0 1  (Fin 1 has one element)
          congr 1; funext _
          ext j; fin_cases j; rfl
        · -- Restrict oneObj (diagObj 1): f i : (diagObj 1).V i →ₗ oneObj.V i
          --   i.e., Fin 1 → K →ₗ ULift.{v} K,  via v ↦ ULift.up (v 0)
          let fDown : (diagObj (K := K) (d := d) 1).V 0 →ₗ[K] (oneObj (K := K) (d := d)).V 0 :=
            { toFun    := fun v => ULift.up (v 0)
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          refine ⟨fun _ => fDown, ?_⟩
          -- Goal: liftMap (fun _ => fDown) (diagObj 1).t = oneObj.t
          change liftMap (fun _ : Fin d => fDown)
              (∑ j : Fin 1, tprod K (fun _ : Fin d => Pi.single j (1 : K))) =
              tprod K (fun _ : Fin d => ULift.up (1 : K))
          simp only [Finset.univ_unique, Finset.sum_singleton, liftMap_tprod, fDown]
          congr 1
      -- Chain: diagObj (n+1) ≤ diagObj n + diagObj 1 ≤ ↑n + 1 = ↑(n+1)
      have hle1 : (toTensor (diagObj (K := K) (d := d) (n + 1)) : Tensor K d) ≤
          toTensor (diagObj n) + toTensor (diagObj 1) := hstep
      have hle2 : (toTensor (diagObj (K := K) (d := d) n) : Tensor K d) + toTensor (diagObj 1) ≤
          (n : Tensor K d) + 1 := by
        rw [hone]; exact instSemiringPreorder.add_right _ _ ih 1
      have hcast : (n : Tensor K d) + 1 = ↑(n + 1) := by push_cast; ring
      exact le_trans hle1 (hcast ▸ hle2)

/-- X.t = 0 implies toTensor X = 0 -/
private theorem toTensor_eq_zero_of_t_eq_zero {X : TensorObj K d} (h : X.t = 0) :
    (toTensor X : Tensor K d) = 0 := by
  apply Quotient.sound
  refine ⟨⟨fun _ => 0, ?_⟩, restrict_zero_le X⟩
  -- Goal: liftMap (fun _ => 0) zeroObj.t = X.t
  -- zeroObj.t = 0, so liftMap _ 0 = 0 = X.t by hypothesis
  change liftMap (fun _ => (0 : _ →ₗ[K] _)) 0 = X.t
  simp only [h, liftMap]; exact LinearMap.map_zero _

private theorem restrict_one_le_of_t_ne_zero (X : TensorObj K d) (hX : X.t ≠ 0) :
    TensorObj.Restrict oneObj X := by
  haveI : ∀ i, Module.Free K (X.V i) := fun i => Module.Free.of_divisionRing K _
  haveI : ∀ i, Module.Finite K (X.V i) := fun i => inferInstance
  -- Step 1: find φ_i : Dual K (X.V i) with (dualDistrib (⊗ φ_i)) X.t ≠ 0
  have ⟨ψ_pure, hψ⟩ : ∃ (φ : ∀ i, Module.Dual K (X.V i)),
      PiTensorProduct.dualDistrib (tprod K φ) X.t ≠ 0 := by
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hX
    obtain ⟨ψ, hψ⟩ := (PiTensorProduct.dualDistribEquiv (R := K)
      (ι := Fin d) (M := fun i => X.V i)).surjective φ
    have hne : PiTensorProduct.dualDistrib ψ X.t ≠ 0 := by
      have : PiTensorProduct.dualDistribEquiv (R := K) (ι := Fin d) (M := fun i => X.V i) ψ
          = PiTensorProduct.dualDistrib ψ := rfl
      rw [← this, hψ, hφ]; exact one_ne_zero
    have key : ∀ (t : PiTensorProduct K (fun i : Fin d => Module.Dual K (X.V i))),
        PiTensorProduct.dualDistrib t X.t ≠ 0 →
        ∃ (φ : ∀ i, Module.Dual K (X.V i)),
          PiTensorProduct.dualDistrib (tprod K φ) X.t ≠ 0 := by
      intro t
      induction t using PiTensorProduct.induction_on with
      | smul_tprod r g =>
        rw [map_smul, LinearMap.smul_apply, smul_ne_zero_iff]
        exact fun h => ⟨g, h.2⟩
      | add a b iha ihb =>
        rw [map_add, LinearMap.add_apply]
        intro hne'
        by_cases ha : PiTensorProduct.dualDistrib a X.t = 0
        · have : PiTensorProduct.dualDistrib b X.t ≠ 0 := by
            intro hb; exact hne' (by simp [ha, hb])
          exact ihb this
        · exact iha ha
    exact key ψ hne
  -- Step 2: let c = dualDistrib (tprod ψ_pure) X.t ≠ 0
  set c := PiTensorProduct.dualDistrib (tprod K ψ_pure) X.t with hc_def
  have hc : c ≠ 0 := hψ
  -- Step 3: define f i : X.V i → oneObj.V i = ULift.{v} K
  have hd_pos : 0 < d := Nat.lt_trans Nat.zero_lt_one Fact.out
  let f : ∀ i : Fin d, X.V i →ₗ[K] oneObj.V i :=
    fun i => {
      toFun := fun x => ULift.up (if i = ⟨0, hd_pos⟩ then c⁻¹ * ψ_pure i x else ψ_pure i x)
      map_add' := fun x y => by
        simp only [map_add]
        congr 1
        split_ifs <;> ring
      map_smul' := fun r x => by
        simp only [map_smul, RingHom.id_apply]
        show (ULift.up _) = (RingHom.id K) r • (ULift.up _)
        split_ifs with h
        · congr 1; simp [smul_eq_mul]; ring
        · exact congr_arg ULift.up (by simp [smul_eq_mul])
    }
  refine ⟨f, ?_⟩
  -- Let g i = uliftEquiv ∘ f i : X.V i →ₗ K
  let g : ∀ i : Fin d, X.V i →ₗ[K] K :=
    fun i => (uliftEquiv (K := K)).toLinearMap ∘ₗ f i
  -- Key computation: (constantBaseRingEquiv) (liftMap g X.t) = 1
  have hg_val : (constantBaseRingEquiv (Fin d) K) (liftMap g X.t) = 1 := by
    suffices h : (constantBaseRingEquiv (Fin d) K).toLinearMap ∘ₗ liftMap g =
        c⁻¹ • PiTensorProduct.dualDistrib (tprod K ψ_pure) by
      have h' : ((constantBaseRingEquiv (Fin d) K).toLinearMap ∘ₗ liftMap g) X.t =
          (c⁻¹ • PiTensorProduct.dualDistrib (tprod K ψ_pure)) X.t := by rw [h]
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
                 LinearMap.smul_apply] at h'
      rw [h', hc_def]
      exact inv_mul_cancel₀ hc
    apply PiTensorProduct.ext; apply MultilinearMap.ext; intro w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
               AlgEquiv.toLinearMap_apply, LinearMap.smul_apply, liftMap_tprod,
               PiTensorProduct.dualDistrib_apply, constantBaseRingEquiv_tprod]
    simp only [g, f, uliftEquiv, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    show (∏ x, if x = ⟨0, hd_pos⟩ then c⁻¹ * ψ_pure x (w x) else ψ_pure x (w x)) =
        c⁻¹ • ∏ i, ψ_pure i (w i)
    conv_lhs => arg 2; ext i; rw [show (if i = ⟨0, hd_pos⟩ then c⁻¹ * ψ_pure i (w i) else
        ψ_pure i (w i)) = (if i = ⟨0, hd_pos⟩ then c⁻¹ else 1) * ψ_pure i (w i) from by
      split_ifs <;> ring]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq' Finset.univ (⟨0, hd_pos⟩ : Fin d), Finset.mem_univ, ite_true,
               smul_eq_mul]
  -- liftMap g X.t = tprod K (fun _ => 1) (in ⨂ K)
  have hg_tprod : liftMap g X.t = tprod K (fun _ : Fin d => (1 : K)) := by
    apply (constantBaseRingEquiv (Fin d) K).injective
    rw [hg_val, constantBaseRingEquiv_tprod]
    simp [Finset.prod_const_one]
  -- Derive liftMap f X.t = oneObj.t = tprod K (fun _ => ULift.up 1)
  -- Strategy: liftMap g = liftMap uliftEquiv ∘ liftMap f (by definition of g and functoriality)
  -- Therefore liftMap uliftEquiv (liftMap f X.t) = tprod K (fun _ => 1)
  -- Apply uliftEquiv.symm to each component.
  -- We prove liftMap uliftEquiv (liftMap f X.t) = tprod K (fun _ => 1) directly:
  have huf : liftMap (fun _ : Fin d => (uliftEquiv (K := K)).toLinearMap) (liftMap f X.t) =
      tprod K (fun _ : Fin d => (1 : K)) := by
    -- liftMap uliftEquiv ∘ liftMap f = liftMap g by functoriality applied pointwise
    have : liftMap (fun _ : Fin d => (uliftEquiv (K := K)).toLinearMap) ∘ₗ
        liftMap f = liftMap g := by
      apply PiTensorProduct.ext; apply MultilinearMap.ext; intro w
      simp [liftMap, g]
    exact (LinearMap.ext_iff.mp this X.t).trans hg_tprod
  -- Apply liftMap uliftEquiv.symm to huf to recover liftMap f X.t
  -- Goal: liftMap f X.t = oneObj.t = tprod K (fun _ => ULift.up 1)
  -- We use huf: liftMap uliftEquiv (liftMap f X.t) = tprod K (fun _ => 1)
  -- and the fact that liftMap uliftEquiv (tprod K (fun _ => ULift.up 1)) = tprod K (fun _ => 1)
  -- so liftMap uliftEquiv is injective (linear bijection) gives the result.
  have hone : liftMap (fun _ : Fin d => (uliftEquiv (K := K)).toLinearMap) oneObj.t =
      tprod K (fun _ : Fin d => (1 : K)) := by
    show liftMap (fun _ : Fin d => (uliftEquiv (K := K)).toLinearMap)
        (tprod K (fun _ => ULift.up (1 : K))) = tprod K (fun _ => 1)
    rw [liftMap_tprod]; simp [uliftEquiv]
  -- liftMap uliftEquiv is injective: its left-inverse is liftMap uliftEquiv.symm
  have hinj : Function.Injective
      (liftMap (fun _ : Fin d => (uliftEquiv (K := K)).toLinearMap)) :=
    fun a b hab => by
      -- liftMap uliftEquiv.symm (liftMap uliftEquiv a) = a, same for b
      have inv : ∀ t : PiTensorProduct K (fun _ : Fin d => oneObj.V (K := K) (d := d) 0),
          liftMap (fun _ : Fin d => (uliftEquiv (K := K)).symm.toLinearMap)
            (liftMap (fun _ : Fin d => (uliftEquiv (K := K)).toLinearMap) t) = t := by
        intro t
        have hmap : liftMap (fun _ : Fin d => (uliftEquiv (K := K)).symm.toLinearMap) ∘ₗ
            liftMap (fun _ : Fin d => (uliftEquiv (K := K)).toLinearMap) =
            liftMap (fun _ : Fin d => LinearMap.id) := by
          apply PiTensorProduct.ext; apply MultilinearMap.ext; intro w
          simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
                     liftMap_tprod, LinearMap.id_coe, id_eq]
          simp [uliftEquiv]
        have hid : liftMap (fun _ : Fin d => (LinearMap.id : oneObj.V (K := K) (d := d) 0 →ₗ[K] _)) =
            LinearMap.id := by
          apply PiTensorProduct.ext; apply MultilinearMap.ext; intro w
          simp [liftMap_tprod]
        have : liftMap (fun _ : Fin d => (uliftEquiv (K := K)).symm.toLinearMap) ∘ₗ
            liftMap (fun _ : Fin d => (uliftEquiv (K := K)).toLinearMap) = LinearMap.id :=
          hmap.trans hid
        exact LinearMap.congr_fun this t
      calc a = liftMap (fun _ => (uliftEquiv (K := K)).symm.toLinearMap)
                (liftMap (fun _ => (uliftEquiv (K := K)).toLinearMap) a) := (inv a).symm
           _ = liftMap (fun _ => (uliftEquiv (K := K)).symm.toLinearMap)
                (liftMap (fun _ => (uliftEquiv (K := K)).toLinearMap) b) := by rw [hab]
           _ = b := inv b
  exact hinj (huf.trans hone.symm)

private theorem diagObj_one_eq_one :
    (toTensor (diagObj (K := K) (d := d) 1) : Tensor K d) = 1 := by
  apply Quotient.sound
  constructor
  · refine ⟨fun _ => (show (oneObj (K := K) (d := d)).V 0 →ₗ[K]
          (diagObj (K := K) (d := d) 1).V 0 from
          { toFun    := fun u _ => u.down
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }), ?_⟩
    change liftMap _ (tprod K (fun _ : Fin d => ULift.up (1 : K))) =
        ∑ j : Fin 1, tprod K (fun _ : Fin d => Pi.single j (1 : K))
    rw [liftMap_tprod, Finset.univ_unique, Finset.sum_singleton]
    congr 1; funext _; ext j; fin_cases j; rfl
  · let fDown : (diagObj (K := K) (d := d) 1).V 0 →ₗ[K] (oneObj (K := K) (d := d)).V 0 :=
      { toFun    := fun v => ULift.up (v 0)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine ⟨fun _ => fDown, ?_⟩
    change liftMap (fun _ : Fin d => fDown)
        (∑ j : Fin 1, tprod K (fun _ : Fin d => Pi.single j (1 : K))) =
        tprod K (fun _ : Fin d => ULift.up (1 : K))
    simp only [Finset.univ_unique, Finset.sum_singleton, liftMap_tprod, fDown]
    congr 1

/-- (r : Tensor K d) ≤ toTensor (diagObj r) -/
theorem natCast_le_diagObj (r : ℕ) :
    (r : Tensor K d) ≤ (toTensor (diagObj (K := K) (d := d) r) : Tensor K d) := by
  induction r with
  | zero =>
    simp only [Nat.cast_zero]
    exact instSemiringPreorder.zero_le _
  | succ n ih =>
    -- (n+1 : Tensor K d) = n + 1 ≤ toTensor (diagObj n) + toTensor (diagObj 1)
    --                                = toTensor (diagObj n + diagObj 1)
    --                               ≤ toTensor (diagObj (n+1))
    -- The last step: diagObj n + diagObj 1 restricts to diagObj (n+1).
    -- This is the reverse of hstep in diagObj_le_natCast.
    -- We use restrict_iff_sum_tprod: (diagObj n + diagObj 1).t =
    --   ∑ j : Fin (n+1), tprod K (fun _ => Pi.single j 1)  =  (diagObj (n+1)).t
    -- so TensorObj.Restrict (diagObj n + diagObj 1) (diagObj (n+1))
    have hstep : TensorObj.Restrict (diagObj (K := K) (d := d) n + diagObj (K := K) (d := d) 1)
        (diagObj (K := K) (d := d) (n + 1)) := by
      -- Strategy: use restrict_iff_sum_tprod to reduce to showing (diagObj n + diagObj 1).t
      -- is a sum of (n+1) pure tensors in V i = (Fin n → K) × (Fin 1 → K).
      -- v (castSucc k) _ = (Pi.single k 1, 0)
      -- v (last n)     _ = (0, Pi.single 0 1)
      rw [restrict_iff_sum_tprod]
      refine ⟨fun j _ => Fin.lastCases (0, Pi.single 0 1) (fun k => (Pi.single k 1, 0)) j, ?_⟩
      simp only [add_t, diagObj]
      -- Goal: liftMap inl (∑ j:Fin n, tprod (Pi.single j 1)) + liftMap inr (∑ j:Fin 1, ...) =
      --       ∑ x:Fin(n+1), tprod (lastCases ... x)
      -- Expand RHS via Fin.sum_univ_castSucc, simplify lastCases, then distribute liftMap on LHS
      conv_rhs => rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
      -- RHS = (∑ k:Fin n, tprod (fun _ => (Pi.single k 1, 0))) + tprod (fun _ => (0, Pi.single 0 1))
      -- Distribute liftMap inl and inr on LHS
      rw [map_sum, Fin.sum_univ_one]
      -- LHS = (∑ k:Fin n, liftMap inl (tprod (Pi.single k 1))) + liftMap inr (tprod (Pi.single 0 1))
      simp only [liftMap_tprod, LinearMap.inl_apply, LinearMap.inr_apply]
      rfl
    have hone : toTensor (diagObj (K := K) (d := d) 1) = (1 : Tensor K d) := diagObj_one_eq_one
    rw [show (↑(n + 1) : Tensor K d) = ↑n + 1 by push_cast; ring]
    calc (↑n : Tensor K d) + 1
        = ↑n + toTensor (diagObj 1) := by rw [hone]
      _ ≤ toTensor (diagObj n) + toTensor (diagObj 1) :=
            instSemiringPreorder.add_right _ _ ih _
      _ ≤ toTensor (diagObj (n + 1)) := hstep

/-- `⟦X⟧ ≤ (r : Tensor K d)` iff `X.t` is a sum of `r` pure tensors.
    (Stated for `X : TensorObj.{u, u} K d`, i.e., component spaces in the same universe as `K`.) -/
theorem tensor_le_natCast_iff {X : TensorObj.{u, u} K d} {r : ℕ} :
    (toTensor X : Tensor K d) ≤ (r : Tensor K d) ↔
    ∃ v : Fin r → ∀ i, X.V i, X.t = ∑ j, tprod K (fun i => v j i) := by
  constructor
  · intro h
    exact restrict_iff_sum_tprod.mp (le_trans h (natCast_le_diagObj r))
  · rintro ⟨v, hv⟩
    exact le_trans (restrict_iff_sum_tprod.mpr ⟨v, hv⟩) (diagObj_le_natCast r)

private theorem restrict_lower (X : TensorObj K d) :
    (toTensor X : Tensor K d) = 0 ∨ TensorObj.Restrict oneObj X := by
  by_cases h : X.t = 0
  · left; exact toTensor_eq_zero_of_t_eq_zero h
  · right; exact restrict_one_le_of_t_ne_zero X h

instance : StrassenPreorder (Tensor K d) where
  toSemiringPreorder := instSemiringPreorder
  nat_order_embedding := by
    have σ : AsymptoticSpectra.Split (Fin d) :=
      ⟨{0}, Finset.singleton_nonempty _, ⟨1, by simp; exact Nat.ne_of_gt Fact.out⟩⟩
    exact spectrumPoint_implies_nat_order_embedding (AsymptoticSpectra.Tensor.FlatteningRankPoint σ instSemiringPreorder (flatteningRank_mono σ))
  lower_archimedean := fun x => by
    induction x using Quotient.inductionOn with | h X => ?_
    exact restrict_lower X
  upper_archimedean := fun x => by
    induction x using Quotient.inductionOn with | h X => ?_
    -- Strategy: express X.t as a sum of r pure tensors, then use restrict_iff_sum_tprod + diagObj_le_natCast.
    -- Step 1: choose a basis bᵢ for each X.V i (possible since X.V i is finite-dimensional over K).
    haveI hfree : ∀ i, Module.Free K (X.V i) := fun _ => inferInstance
    haveI hfin  : ∀ i, Module.Finite K (X.V i) := fun _ => inferInstance
    -- Step 2: build the basis of ⨂ X.V i via Basis.piTensorProduct.
    let b : ∀ i : Fin d, Module.Basis (Module.Free.ChooseBasisIndex K (X.V i)) K (X.V i) :=
      fun i => Module.Free.chooseBasis K (X.V i)
    haveI hκ_fintype : ∀ i : Fin d, Fintype (Module.Free.ChooseBasisIndex K (X.V i)) :=
      fun i => inferInstance
    haveI hκ_decidable : ∀ i : Fin d, DecidableEq (Module.Free.ChooseBasisIndex K (X.V i)) :=
      fun _ => Classical.decEq _
    let B : Module.Basis (∀ i : Fin d, Module.Free.ChooseBasisIndex K (X.V i)) K
                  (PiTensorProduct K (X.V)) :=
      Basis.piTensorProduct b
    -- Step 3: r = Fintype.card of the basis index type.
    let κ := fun i : Fin d => Module.Free.ChooseBasisIndex K (X.V i)
    haveI : Fintype (∀ i : Fin d, κ i) := inferInstance
    let r := Fintype.card (∀ i : Fin d, κ i)
    -- Enumerate ∀ i, κ i as Fin r via Fintype.equivFin.
    let e : (∀ i : Fin d, κ i) ≃ Fin r := Fintype.equivFin _
    -- Step 4: express X.t as sum of r pure tensors, absorbing B.repr coefficients into component 0.
    -- Use the first index i₀ : Fin d (exists since 1 < d implies 0 < d).
    have h0d : 0 < d := Nat.lt_trans Nat.zero_lt_one Fact.out
    let i₀ : Fin d := ⟨0, h0d⟩
    -- For each p : ∀ i, κ i, define the pure tensor with scalar absorbed into component i₀:
    --   w p i := if i = i₀ then (B.repr X.t p) • b i (p i) else b i (p i)
    -- Then tprod K (w p) = (B.repr X.t p) • B p  (by multilinearity of tprod).
    let w : (∀ i : Fin d, κ i) → ∀ i : Fin d, X.V i :=
      fun p i => if i = i₀ then (B.repr X.t p) • b i (p i) else b i (p i)
    -- Key: c • tprod K (fun i => b i (p i)) = tprod K (fun i => w p i)
    -- by MultilinearMap.map_update_smul:
    --   tprod K (update f i₀ (c • f i₀)) = c • tprod K (update f i₀ (f i₀))
    --                                     = c • tprod K f  (update_eq_self)
    -- and w p = update (fun i => b i (p i)) i₀ (c • b i₀ (p i₀))
    have hw : ∀ p : ∀ i, κ i,
        (B.repr X.t p) • B p = tprod K (fun i => w p i) := fun p => by
      rw [Basis.piTensorProduct_apply]
      set f := fun i : Fin d => b i (p i)
      set c := B.repr X.t p
      -- Show tprod K (fun i => w p i) = tprod K (Function.update f i₀ (c • f i₀))
      have hw_eq : (fun i => w p i) = Function.update f i₀ (c • f i₀) := by
        funext i
        simp only [w, f, i₀]
        split_ifs with h
        · subst h; simp [c, Function.update_self]
        · exact (Function.update_of_ne h (f := fun i => b i (p i)) _).symm
      rw [hw_eq]
      -- MultilinearMap.map_update_smul: tprod K (update f i₀ (c • f i₀)) = c • tprod K (update f i₀ (f i₀))
      rw [(tprod K (s := X.V)).map_update_smul f i₀ c (f i₀), Function.update_eq_self]
    -- v : Fin r → ∀ i, X.V i  (enumerate basis index via e)
    let v : Fin r → ∀ i : Fin d, X.V i := fun j => w (e.symm j)
    have hsum : X.t = ∑ j : Fin r, tprod K (fun i => v j i) := by
      have hrepr : X.t = ∑ p : ∀ i, κ i, (B.repr X.t p) • B p := (B.sum_repr X.t).symm
      -- rewrite each summand using hw, then reindex by e.symm
      rw [hrepr]
      conv_lhs => arg 2; ext p; rw [hw p]
      -- now: ∑ p : ∀ i, κ i, ⨂ₜ[K] i, w p i = ∑ j : Fin r, ⨂ₜ[K] i, w (e.symm j) i
      exact (Fintype.sum_equiv e.symm _ _ (fun j => rfl)).symm
    -- Now use restrict_iff_sum_tprod to get TensorObj.Restrict X (diagObj r)
    have hrestr : TensorObj.Restrict X (diagObj r) := restrict_iff_sum_tprod.mpr ⟨v, hsum⟩
    -- Chain: toTensor X ≤ toTensor (diagObj r) ≤ ↑r
    exact ⟨r, le_trans hrestr (diagObj_le_natCast r)⟩

end Tensor
