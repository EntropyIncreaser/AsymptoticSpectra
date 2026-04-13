import AsymptoticSpectra.Tensor.Tensor
import AsymptoticSpectra.Tensor.Flattening
import AsymptoticSpectra.Structures
import AsymptoticSpectra.Spectrum
import Mathlib.LinearAlgebra.PiTensorProduct.Dual

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
    simp only [AsymptoticSpectra.Tensor.flatteningRankReal, AsymptoticSpectra.Tensor.flatteningRank_mk]
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
          | succ n ih => simp [map_add, ih]
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
          | succ n ih => simp [map_add, ih]
      _ = ∑ j : Fin r, PiTensorProduct.tprod K (fun i : Fin d => v j i) := by
          congr 1; ext j
          rw [liftMap_tprod_eq]
          congr 1; ext i
          simp
      _ = X.t := hv.symm

/-- diagObj r ≤ (r : Tensor K d) -/
private theorem diagObj_le_natCast (r : ℕ) :
    (toTensor (diagObj r) : Tensor K d) ≤ (r : Tensor K d) := by
  sorry

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
    simp only [g, f, uliftEquiv, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk,
               AddHom.coe_mk, LinearEquiv.coe_mk, ULift.down_up]
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
    sorry

end Tensor
