import AsymptoticSpectra.Tensor.Restriction
import AsymptoticSpectra.Tensor.BaseChange
import AsymptoticSpectra.Tensor.Permutation
import AsymptoticSpectra.Spectrum
import AsymptoticSpectra.Rank
import AsymptoticSpectra.Duality
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.MeanValue

universe u

open TensorObj PiTensorProduct BigOperators TensorProduct

namespace Tensor

variable {K : Type u} [Field K]

instance instFact13 : Fact (1 < 3) := ⟨by norm_num⟩

/-! ## Matrix multiplication tensors -/

/-- The three mode spaces for `MM n m p`, indexed by `Fin 3`. -/
@[reducible] private def MMSpace (K : Type u) (n m p : ℕ) : Fin 3 → Type u
  | ⟨0, _⟩ => Fin n × Fin m → K
  | ⟨1, _⟩ => Fin m × Fin p → K
  | ⟨2, _⟩ => Fin p × Fin n → K

@[reducible] private instance MMSpace_addCommGroup (n m p : ℕ) (i : Fin 3) :
    AddCommGroup (MMSpace K n m p i) :=
  match i with
  | ⟨0, _⟩ => Pi.addCommGroup
  | ⟨1, _⟩ => Pi.addCommGroup
  | ⟨2, _⟩ => Pi.addCommGroup

@[reducible] private instance MMSpace_module (n m p : ℕ) (i : Fin 3) :
    Module K (MMSpace K n m p i) :=
  match i with
  | ⟨0, _⟩ => Pi.module _ _ _
  | ⟨1, _⟩ => Pi.module _ _ _
  | ⟨2, _⟩ => Pi.module _ _ _

private instance MMSpace_finiteDimensional (n m p : ℕ) (i : Fin 3) :
    FiniteDimensional K (MMSpace K n m p i) :=
  match i with
  | ⟨0, _⟩ => inferInstance
  | ⟨1, _⟩ => inferInstance
  | ⟨2, _⟩ => inferInstance

/-- The pure tensor `e_{ij} ⊗ e_{jk} ⊗ e_{ki}` for indices `(i,j,k)`. -/
private noncomputable def MMPureTensor (n m p : ℕ) (i : Fin n) (j : Fin m) (k : Fin p) :
    PiTensorProduct K (MMSpace K n m p) :=
  tprod K (fun (s : Fin 3) =>
    match s with
    | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → K)
    | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → K)
    | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → K))

/-- The matrix multiplication TensorObj `⟨n, m, p⟩`:
    mode spaces are `Fin n × Fin m → K`, `Fin m × Fin p → K`, `Fin p × Fin n → K`,
    with tensor element `∑ i j k, e_{ij} ⊗ e_{jk} ⊗ e_{ki}`. -/
@[reducible] noncomputable def MMObj (n m p : ℕ) : TensorObj.{u, u} K 3 where
  V := MMSpace K n m p
  addCommGroup := MMSpace_addCommGroup n m p
  module := MMSpace_module n m p
  finiteDimensional := MMSpace_finiteDimensional n m p
  t := ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p, MMPureTensor n m p i j k

@[simp] theorem MMObj_V (n m p : ℕ) : (MMObj (K := K) n m p).V = MMSpace K n m p := rfl

@[simp] theorem MMObj_t (n m p : ℕ) : (MMObj (K := K) n m p).t =
    ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p, MMPureTensor n m p i j k := rfl

/-- The matrix multiplication tensor `MM n m p` as an element of `Tensor K 3`. -/
noncomputable def MM (n m p : ℕ) : Tensor K 3 := toTensor (MMObj n m p)

/-! ## Basic lemmas (sorry stubs) -/

/-- `MM 1 1 1 = 1` in `Tensor K 3`. -/
theorem MM_one : MM (K := K) 1 1 1 = 1 := by
  show toTensor (MMObj 1 1 1) = toTensor oneObj
  apply Quotient.sound
  -- The setoid relation is Restrict(MMObj 1 1 1, oneObj) ∧ Restrict(oneObj, MMObj 1 1 1)
  -- For each mode i, Fin 1 × Fin 1 → K ≅ ULift K via evaluation at (0,0) / constant function
  let toMM : ∀ i : Fin 3, (oneObj : TensorObj K 3).V i →ₗ[K] (MMObj 1 1 1).V i
    | ⟨0, _⟩ => { toFun := fun c _ => c.down, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    | ⟨1, _⟩ => { toFun := fun c _ => c.down, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    | ⟨2, _⟩ => { toFun := fun c _ => c.down, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    | ⟨n + 3, h⟩ => absurd h (by omega)
  let toOne : ∀ i : Fin 3, (MMObj 1 1 1).V i →ₗ[K] (oneObj : TensorObj K 3).V i
    | ⟨0, _⟩ => { toFun := fun f => ULift.up (f (0, 0)), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    | ⟨1, _⟩ => { toFun := fun f => ULift.up (f (0, 0)), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    | ⟨2, _⟩ => { toFun := fun f => ULift.up (f (0, 0)), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    | ⟨n + 3, h⟩ => absurd h (by omega)
  constructor
  · -- Restrict (MMObj 1 1 1) oneObj: liftMap toMM oneObj.t = (MMObj 1 1 1).t
    refine ⟨toMM, ?_⟩
    erw [liftMap_tprod]
    simp only [MMObj, Fin.sum_univ_one, MMPureTensor]
    congr 1; ext s; fin_cases s <;> (ext ⟨a, b⟩; simp [Pi.single_apply, Fin.fin_one_eq_zero]; rfl)
  · -- Restrict oneObj (MMObj 1 1 1): liftMap toOne (MMObj 1 1 1).t = oneObj.t
    refine ⟨toOne, ?_⟩
    simp only [MMObj, Fin.sum_univ_one, MMPureTensor]
    have h := @liftMap_tprod K _ (Fin 3) _ (MMSpace K 1 1 1) oneObj.V
        (MMSpace_addCommGroup 1 1 1) (MMSpace_module 1 1 1) _ _ toOne
        (fun s => match s with
          | ⟨0, _⟩ => Pi.single (0, 0) 1
          | ⟨1, _⟩ => Pi.single (0, 0) 1
          | ⟨2, _⟩ => Pi.single (0, 0) 1)
    refine h.trans ?_
    congr 1; ext s; fin_cases s <;> rfl

/-- `MM` is monotone: if `n ≤ n'`, `m ≤ m'`, `p ≤ p'` then `MM n m p ≤ MM n' m' p'`. -/
theorem MM_le_of_le {n n' m m' p p' : ℕ}
    (hn : n ≤ n') (hm : m ≤ m') (hp : p ≤ p') :
    MM (K := K) n m p ≤ MM n' m' p' := by
  show Restrict (MM n m p) (MM n' m' p')
  show TensorObj.Restrict (MMObj n m p) (MMObj n' m' p')
  -- restriction maps: precompose with the inclusion Fin n × Fin m ↪ Fin n' × Fin m', etc.
  -- Use `let` (transparent) so simp can unfold the definitions.
  let f₀ : (MMObj n' m' p').V 0 →ₗ[K] (MMObj n m p).V 0 :=
    LinearMap.funLeft K K (fun ab : Fin n × Fin m => (Fin.castLE hn ab.1, Fin.castLE hm ab.2))
  let f₁ : (MMObj n' m' p').V 1 →ₗ[K] (MMObj n m p).V 1 :=
    LinearMap.funLeft K K (fun ab : Fin m × Fin p => (Fin.castLE hm ab.1, Fin.castLE hp ab.2))
  let f₂ : (MMObj n' m' p').V 2 →ₗ[K] (MMObj n m p).V 2 :=
    LinearMap.funLeft K K (fun ab : Fin p × Fin n => (Fin.castLE hp ab.1, Fin.castLE hn ab.2))
  let hf : ∀ s : Fin 3, (MMObj n' m' p').V s →ₗ[K] (MMObj n m p).V s :=
    fun s => Fin.cases f₀ (fun s => Fin.cases f₁ (fun s => Fin.cases f₂
      (fun s => absurd s.isLt (by omega)) s) s) s
  refine ⟨hf, ?_⟩
  -- Key: liftMap hf (MMPureTensor n' m' p' (Fin.castLE hn i) ...) = MMPureTensor n m p i ...
  have key : ∀ (i : Fin n) (j : Fin m) (k : Fin p),
      liftMap hf (MMPureTensor n' m' p' (Fin.castLE hn i) (Fin.castLE hm j) (Fin.castLE hp k)) =
      MMPureTensor n m p i j k := by
    intro i j k
    simp only [MMPureTensor, hf, f₀, f₁, f₂]
    erw [liftMap_tprod]
    congr 1; funext s; fin_cases s
    · change f₀ (Pi.single (Fin.castLE hn i, Fin.castLE hm j) 1) = Pi.single (i, j) 1
      funext ⟨a, b⟩; erw [LinearMap.funLeft_apply]
      simp [Pi.single_apply, Prod.mk.injEq, Fin.ext_iff]
    · change f₁ (Pi.single (Fin.castLE hm j, Fin.castLE hp k) 1) = Pi.single (j, k) 1
      funext ⟨a, b⟩; erw [LinearMap.funLeft_apply]
      simp [Pi.single_apply, Prod.mk.injEq, Fin.ext_iff]
    · change f₂ (Pi.single (Fin.castLE hp k, Fin.castLE hn i) 1) = Pi.single (k, i) 1
      funext ⟨a, b⟩; erw [LinearMap.funLeft_apply]
      simp [Pi.single_apply, Prod.mk.injEq, Fin.ext_iff]
  -- Out of range terms give 0: liftMap hf (MMPureTensor ... i' j' k') = 0 when some index out of range
  have h_out : ∀ (i' : Fin n') (j' : Fin m') (k' : Fin p'),
      (¬ i'.val < n ∨ ¬ j'.val < m ∨ ¬ k'.val < p) →
      liftMap hf (MMPureTensor n' m' p' i' j' k') = 0 := by
    intro i' j' k' h
    dsimp only [f₀, f₁, f₂, hf, MMPureTensor]
    erw [liftMap_tprod]
    rcases h with h | h | h
    · apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
      show (LinearMap.funLeft K K fun ab : Fin n × Fin m => (Fin.castLE hn ab.1, Fin.castLE hm ab.2))
        (Pi.single (i', j') 1) = 0
      funext ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      simp only [LinearMap.funLeft_apply, Pi.single_apply, Pi.zero_apply, Prod.mk.injEq, Fin.ext_iff,
        Fin.val_castLE]
      split_ifs with hif
      · exact absurd (hif.1 ▸ ha) h
      · rfl
    · apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
      show (LinearMap.funLeft K K fun ab : Fin m × Fin p => (Fin.castLE hm ab.1, Fin.castLE hp ab.2))
        (Pi.single (j', k') 1) = 0
      funext ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      simp only [LinearMap.funLeft_apply, Pi.single_apply, Pi.zero_apply, Prod.mk.injEq, Fin.ext_iff,
        Fin.val_castLE]
      split_ifs with hif
      · exact absurd (hif.1 ▸ ha) h
      · rfl
    · apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
      show (LinearMap.funLeft K K fun ab : Fin p × Fin n => (Fin.castLE hp ab.1, Fin.castLE hn ab.2))
        (Pi.single (k', i') 1) = 0
      funext ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      simp only [LinearMap.funLeft_apply, Pi.single_apply, Pi.zero_apply, Prod.mk.injEq, Fin.ext_iff,
        Fin.val_castLE]
      split_ifs with hif
      · exact absurd (hif.1 ▸ ha) h
      · rfl
  -- Now compute the sum using key and h_out
  simp only [MMObj, map_sum]
  -- Helper: sum over Fin n2 = sum over Fin n1 when out-of-range terms vanish
  have sum_le : ∀ {M : Type u} [AddCommMonoid M] (n1 n2 : ℕ) (h12 : n1 ≤ n2) (f : Fin n2 → M)
      (hf0 : ∀ i : Fin n2, ¬ i.val < n1 → f i = 0),
      ∑ i : Fin n2, f i = ∑ i : Fin n1, f (Fin.castLE h12 i) := by
    intro M _ n1 n2 h12 f hf0
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h12
    rw [Fin.sum_univ_add]
    have tail_zero : ∑ i : Fin d, f (Fin.natAdd n1 i) = 0 :=
      Finset.sum_eq_zero (fun i _ => hf0 _ (by simp [Fin.natAdd]))
    have step : ∑ i : Fin n1, f (Fin.castAdd d i) = ∑ i : Fin n1, f (Fin.castLE h12 i) :=
      Finset.sum_congr rfl fun i _ => by congr 1
    simp [tail_zero, step]
  -- Reindex: push liftMap hf through the triple sum and apply key
  have step1 : ∑ i : Fin n', ∑ j : Fin m', ∑ k : Fin p', (liftMap hf) (MMPureTensor n' m' p' i j k) =
      ∑ i : Fin n, ∑ j : Fin m', ∑ k : Fin p', (liftMap hf) (MMPureTensor n' m' p' (Fin.castLE hn i) j k) :=
    sum_le n n' hn _ (fun i' hi' =>
      Finset.sum_eq_zero (fun j' _ => Finset.sum_eq_zero (fun k' _ => h_out i' j' k' (Or.inl hi'))))
  have step2 : ∀ i : Fin n,
      ∑ j : Fin m', ∑ k : Fin p', (liftMap hf) (MMPureTensor n' m' p' (Fin.castLE hn i) j k) =
      ∑ j : Fin m, ∑ k : Fin p', (liftMap hf) (MMPureTensor n' m' p' (Fin.castLE hn i) (Fin.castLE hm j) k) :=
    fun i => sum_le m m' hm _ (fun j' hj' =>
      Finset.sum_eq_zero (fun k' _ => h_out (Fin.castLE hn i) j' k' (Or.inr (Or.inl hj'))))
  have step3 : ∀ (i : Fin n) (j : Fin m),
      ∑ k : Fin p', (liftMap hf) (MMPureTensor n' m' p' (Fin.castLE hn i) (Fin.castLE hm j) k) =
      ∑ k : Fin p, MMPureTensor n m p i j k :=
    fun i j => by
      rw [sum_le p p' hp _ (fun k' hk' => h_out (Fin.castLE hn i) (Fin.castLE hm j) k' (Or.inr (Or.inr hk')))]
      apply Finset.sum_congr rfl; intro k _; exact key i j k
  calc ∑ i, ∑ j, ∑ k, (liftMap hf) (MMPureTensor n' m' p' i j k)
      = ∑ i, ∑ j, ∑ k, (liftMap hf) (MMPureTensor n' m' p' (Fin.castLE hn i) j k) := step1
    _ = ∑ i, ∑ j, ∑ k, MMPureTensor n m p i j k := by
        apply Finset.sum_congr rfl; intro i _
        rw [step2]; apply Finset.sum_congr rfl; intro j _
        exact step3 i j

/-! ### Helper: Kronecker-style mode equiv for `MM_mul`

For each mode, we need a linear equivalence
  `(Fin a × Fin b → K) ⊗[K] (Fin c × Fin d → K) ≃ₗ[K] (Fin (a*c) × Fin (b*d) → K)`
sending `Pi.single (i,j) 1 ⊗ₜ Pi.single (i',j') 1 ↦ Pi.single ((i,i')*, (j,j')*) 1`
where `(i,i')* = finProdFinEquiv (i,i')`. We build this from `TensorProduct.piScalarRight`
and reindexing equivs. -/

/-- Curry/uncurry for function types on product domains: a plain `LinearEquiv`. -/
private def uncurryEquiv (α β γ : Type*) [AddCommGroup γ] [Module K γ] :
    (α → β → γ) ≃ₗ[K] (α × β → γ) where
  toFun f p := f p.1 p.2
  map_add' _ _ := by funext ⟨_, _⟩; rfl
  map_smul' _ _ := by funext ⟨_, _⟩; rfl
  invFun f a b := f (a, b)
  left_inv _ := by funext _ _; rfl
  right_inv _ := by funext ⟨_, _⟩; rfl

/-- Kronecker mode equiv:
`(Fin a × Fin b → K) ⊗[K] (Fin c × Fin d → K) ≃ₗ[K] (Fin (a*c) × Fin (b*d) → K)`. -/
private noncomputable def kronEquiv (a b c d : ℕ) :
    ((Fin a × Fin b → K) ⊗[K] (Fin c × Fin d → K)) ≃ₗ[K]
      (Fin (a * c) × Fin (b * d) → K) :=
  let e2 : ((Fin a × Fin b → K) ⊗[K] (Fin c × Fin d → K)) ≃ₗ[K]
      (Fin c × Fin d → (Fin a × Fin b → K)) :=
    TensorProduct.piScalarRight K K (Fin a × Fin b → K) (Fin c × Fin d)
  let e3 : (Fin c × Fin d → (Fin a × Fin b → K)) ≃ₗ[K]
      ((Fin c × Fin d) × (Fin a × Fin b) → K) :=
    uncurryEquiv (K := K) (Fin c × Fin d) (Fin a × Fin b) K
  let reindex : (Fin a × Fin c) × (Fin b × Fin d) ≃ (Fin c × Fin d) × (Fin a × Fin b) :=
    (Equiv.prodProdProdComm (Fin a) (Fin c) (Fin b) (Fin d)).trans
      (Equiv.prodComm _ _)
  let e4 : ((Fin c × Fin d) × (Fin a × Fin b) → K) ≃ₗ[K]
      ((Fin a × Fin c) × (Fin b × Fin d) → K) :=
    LinearEquiv.funCongrLeft K K reindex
  let e5 : ((Fin a × Fin c) × (Fin b × Fin d) → K) ≃ₗ[K]
      (Fin (a * c) × Fin (b * d) → K) :=
    LinearEquiv.funCongrLeft K K
      (Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm)
  e2.trans (e3.trans (e4.trans e5))

/-- Action of `kronEquiv` on a pure tensor of basis elements. -/
private theorem kronEquiv_single {a b c d : ℕ}
    (i : Fin a) (j : Fin b) (i' : Fin c) (j' : Fin d) :
    kronEquiv (K := K) a b c d ((Pi.single (i, j) 1) ⊗ₜ[K] (Pi.single (i', j') 1)) =
      Pi.single (finProdFinEquiv (i, i'), finProdFinEquiv (j, j')) 1 := by
  funext ⟨I, J⟩
  -- Reduce LHS to `(single i'j' 1 at (I'.2,J'.2)) * (single ij 1 at (I'.1, J'.1))` where
  -- I' = finProdFinEquiv.symm I, J' = finProdFinEquiv.symm J.
  have lhs_val :
      ((kronEquiv (K := K) a b c d)
          ((Pi.single (i, j) 1) ⊗ₜ[K] (Pi.single (i', j') 1))) (I, J) =
        ((Pi.single (i', j') 1 : Fin c × Fin d → K)
            ((finProdFinEquiv.symm I).2, (finProdFinEquiv.symm J).2)) *
          ((Pi.single (i, j) 1 : Fin a × Fin b → K)
            ((finProdFinEquiv.symm I).1, (finProdFinEquiv.symm J).1)) := by
    simp only [kronEquiv, uncurryEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_mk,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Equiv.prodCongr_apply, Prod.map_apply, Equiv.trans_apply,
      Equiv.prodProdProdComm_apply, Equiv.prodComm_apply, Prod.swap]
    rfl
  rw [lhs_val]
  -- Now analyze: both sides are 1 if the indices match, else 0.
  simp only [Pi.single_apply, Prod.mk.injEq]
  -- Let I' = fpe.symm I, J' = fpe.symm J. Then I = fpe (I') and J = fpe (J').
  set I' : Fin a × Fin c := finProdFinEquiv.symm I with hIdef
  set J' : Fin b × Fin d := finProdFinEquiv.symm J with hJdef
  have hIeq : I = finProdFinEquiv I' := by rw [hIdef]; exact (finProdFinEquiv.apply_symm_apply I).symm
  have hJeq : J = finProdFinEquiv J' := by rw [hJdef]; exact (finProdFinEquiv.apply_symm_apply J).symm
  -- Rewrite I, J everywhere via hIeq, hJeq.
  rw [hIeq, hJeq]
  -- After substitution, equivalence: (I'.2 = i' ∧ J'.2 = j') ∧ (I'.1 = i ∧ J'.1 = j)
  --   ↔ finProdFinEquiv I' = finProdFinEquiv (i,i') ∧ finProdFinEquiv J' = finProdFinEquiv (j,j')
  simp only [finProdFinEquiv.injective.eq_iff]
  -- The ifs become conditions on I'.1, I'.2, J'.1, J'.2.
  obtain ⟨I'1, I'2⟩ := I'
  obtain ⟨J'1, J'2⟩ := J'
  by_cases hI2 : I'2 = i'
  · by_cases hJ2 : J'2 = j'
    · by_cases hI1 : I'1 = i
      · by_cases hJ1 : J'1 = j
        · simp [hI1, hI2, hJ1, hJ2]
        · simp [hI1, hI2, hJ1, hJ2]
      · simp [hI1, hI2, hJ2]
    · simp [hJ2, hI2]
  · simp [hI2]

/-- `MM` is multiplicative: `MM n m p * MM n' m' p' = MM (n*n') (m*m') (p*p')`. -/
theorem MM_mul (n m p n' m' p' : ℕ) :
    MM (K := K) n m p * MM n' m' p' = MM (n * n') (m * m') (p * p') := by
  -- Package the per-mode equivalence.
  let equiv : ∀ i : Fin 3,
      (MMObj (K := K) n m p * MMObj n' m' p').V i ≃ₗ[K] (MMObj (K := K) (n*n') (m*m') (p*p')).V i
    | ⟨0, _⟩ => kronEquiv n m n' m'
    | ⟨1, _⟩ => kronEquiv m p m' p'
    | ⟨2, _⟩ => kronEquiv p n p' n'
    | ⟨s + 3, h⟩ => absurd h (by omega)
  -- Key pointwise fact: the induced map sends each pure tensor of basis vectors
  -- to the corresponding basis pure tensor on the product object.
  have pure_eq : ∀ (i : Fin n) (j : Fin m) (k : Fin p)
      (i' : Fin n') (j' : Fin m') (k' : Fin p'),
      TensorObj.liftMap (fun s => (equiv s).toLinearMap)
        (TensorObj.interchange (MMPureTensor n m p i j k) (MMPureTensor n' m' p' i' j' k')) =
      MMPureTensor (n*n') (m*m') (p*p')
        (finProdFinEquiv (i, i')) (finProdFinEquiv (j, j')) (finProdFinEquiv (k, k')) := by
    intro i j k i' j' k'
    simp only [MMPureTensor, TensorObj.interchange_tprod_K]
    show (TensorObj.liftMap (K := K) (V := fun s => (MMSpace K n m p s) ⊗[K] (MMSpace K n' m' p' s))
          (W := MMSpace K (n*n') (m*m') (p*p'))
          (fun s => (equiv s).toLinearMap))
        ((PiTensorProduct.tprod K) _) = _
    rw [TensorObj.liftMap_tprod]
    apply congrArg
    funext s
    fin_cases s
    · exact kronEquiv_single (K := K) i j i' j'
    · exact kronEquiv_single (K := K) j k j' k'
    · exact kronEquiv_single (K := K) k i k' i'
  -- Build the TensorIso and reduce to mutual restriction.
  suffices h : TensorObj.Isomorphic
      (MMObj (K := K) n m p * MMObj n' m' p') (MMObj (n*n') (m*m') (p*p')) by
    show toTensor (MMObj n m p) * toTensor (MMObj n' m' p') =
         toTensor (MMObj (n*n') (m*m') (p*p'))
    change toTensor (MMObj n m p * MMObj n' m' p') = _
    exact Quotient.sound (TensorObj.isomorphic_restrict_equiv h)
  refine ⟨⟨equiv, ?_⟩⟩
  -- Goal: liftMap equiv ((MMObj n m p * MMObj n' m' p').t) = (MMObj (n*n') (m*m') (p*p')).t
  show TensorObj.liftMap (fun s => (equiv s).toLinearMap)
      (TensorObj.interchange (MMObj n m p).t (MMObj n' m' p').t) =
      (MMObj (n*n') (m*m') (p*p')).t
  -- Unfold both sides to their sum forms, push interchange-sums outside on LHS.
  show TensorObj.liftMap (fun s => (equiv s).toLinearMap)
      ((TensorObj.interchange
        (∑ i, ∑ j, ∑ k, MMPureTensor n m p i j k))
        (∑ i, ∑ j, ∑ k, MMPureTensor n' m' p' i j k)) =
      ∑ i, ∑ j, ∑ k, MMPureTensor (n*n') (m*m') (p*p') i j k
  simp only [map_sum, LinearMap.sum_apply]
  -- Reindex RHS via finProdFinEquiv, then split into product sums.
  rw [show (∑ i : Fin (n*n'), ∑ j : Fin (m*m'), ∑ k : Fin (p*p'),
        MMPureTensor (n*n') (m*m') (p*p') i j k) =
      ∑ ii' : Fin n × Fin n', ∑ jj' : Fin m × Fin m', ∑ kk' : Fin p × Fin p',
        MMPureTensor (n*n') (m*m') (p*p')
          (finProdFinEquiv ii') (finProdFinEquiv jj') (finProdFinEquiv kk')
      from by
        rw [← finProdFinEquiv.sum_comp]
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [← finProdFinEquiv.sum_comp]
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [← finProdFinEquiv.sum_comp]]
  simp_rw [Fintype.sum_prod_type]
  -- Reorder LHS sums from (i',j',k',i,j,k) to (i,i',j,j',k,k') via Finset.sum_comm.
  have hLHS :
      (∑ i' : Fin n', ∑ j' : Fin m', ∑ k' : Fin p',
        ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p,
          (TensorObj.interchange (K := K) (MMPureTensor n m p i j k))
            (MMPureTensor n' m' p' i' j' k')) =
      (∑ i : Fin n, ∑ i' : Fin n', ∑ j : Fin m, ∑ j' : Fin m',
        ∑ k : Fin p, ∑ k' : Fin p',
          (TensorObj.interchange (K := K) (MMPureTensor n m p i j k))
            (MMPureTensor n' m' p' i' j' k')) := by
    simp_rw [Finset.sum_comm (γ := Fin n)]
    refine Finset.sum_congr rfl fun _ _ => ?_
    simp_rw [Finset.sum_comm (γ := Fin m)]
    refine Finset.sum_congr rfl fun _ _ => ?_
    simp_rw [Finset.sum_comm (γ := Fin p)]
  rw [hLHS]
  -- Push liftMap through each of the 6 sums and apply pure_eq.
  refine (map_sum _ _ _).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (map_sum _ _ _).trans ?_
  refine Finset.sum_congr rfl fun i' _ => ?_
  refine (map_sum _ _ _).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (map_sum _ _ _).trans ?_
  refine Finset.sum_congr rfl fun j' _ => ?_
  refine (map_sum _ _ _).trans ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine (map_sum _ _ _).trans ?_
  refine Finset.sum_congr rfl fun k' _ => ?_
  exact pure_eq i j k i' j' k'

/-- Lower bound: `1 ≤ MM n m p` when all dimensions are positive. -/
theorem one_le_MM {n m p : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    (1 : Tensor K 3) ≤ MM n m p := by
  have h := MM_le_of_le (K := K) hn hm hp
  rwa [MM_one] at h

/-- Upper bound: `MM n m p ≤ n * m * p`. -/
theorem MM_le_mul (n m p : ℕ) :
    MM (K := K) n m p ≤ (n * m * p : Tensor K 3) := by
  rw [show (n : Tensor K 3) * m * p = ((n * m * p : ℕ) : Tensor K 3) from by push_cast; ring]
  rw [show MM (K := K) n m p = toTensor (MMObj n m p) from rfl]
  rw [tensor_le_natCast_iff]
  have e : Fin (n * m * p) ≃ Fin n × Fin m × Fin p :=
    finProdFinEquiv.symm.trans
      (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _) |>.trans (Equiv.prodAssoc _ _ _))
  refine ⟨fun j s => match s with
    | ⟨0, _⟩ => Pi.single ((e j).1, (e j).2.1) 1
    | ⟨1, _⟩ => Pi.single ((e j).2.1, (e j).2.2) 1
    | ⟨2, _⟩ => Pi.single ((e j).2.2, (e j).1) 1
    | ⟨k + 3, h⟩ => absurd h (by omega), ?_⟩
  simp only [MMObj]
  rw [show (∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p, MMPureTensor n m p i j k) =
      ∑ ijk : Fin n × Fin m × Fin p, MMPureTensor n m p ijk.1 ijk.2.1 ijk.2.2 from by
    simp_rw [← Finset.sum_product']; rfl]
  rw [← Equiv.sum_comp e.symm]
  congr 1; ext j; simp only [MMPureTensor]
  congr 1; ext s; fin_cases s <;> simp

/-- `MM n m p ≠ 0` whenever all dimensions are positive. -/
theorem MM_ne_zero {n m p : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    MM (K := K) n m p ≠ 0 := by
  intro h
  have h1 : (1 : Tensor K 3) ≤ MM n m p := one_le_MM hn hm hp
  rw [h] at h1
  -- Now `(1 : Tensor K 3) ≤ (0 : Tensor K 3)`. Use the canonical Strassen
  -- preorder's `nat_order_embedding`.
  have h1' : ((1 : ℕ) : Tensor K 3) ≤ ((0 : ℕ) : Tensor K 3) := by
    simpa using h1
  have : (1 : ℕ) ≤ 0 :=
    (Tensor.instStrassenPreorder.nat_order_embedding 1 0).mp h1'
  exact Nat.not_succ_le_zero 0 this

/-- Power identity: `(MM n m p)^k = MM (n^k) (m^k) (p^k)`. -/
theorem MM_pow (n m p k : ℕ) :
    (MM (K := K) n m p) ^ k = MM (n ^ k) (m ^ k) (p ^ k) := by
  induction k with
  | zero => simp [MM_one]
  | succ k ih =>
    rw [pow_succ, ih, MM_mul]
    rw [pow_succ, pow_succ, pow_succ]

/-! ## Parametrization of spectrum points -/

variable (P : StrassenPreorder (Tensor K 3))

/-- Hypothesis that an abstract Strassen preorder `P` refines the canonical `Restrict`-based
    one. Needed so that canonical inequalities (`one_le_MM`, `MM_le_mul`, `MM_le_of_le`)
    become usable in `P.le` and hence via `φ.monotone'`. For the canonical instance itself,
    this is trivially satisfied. -/
abbrev RefinesCanonical : Prop :=
  ∀ {a b : Tensor K 3}, a ≤ b → P.le a b

/-- The first exponent parameter: `θ₁(φ) = log φ(MM 2 1 1) / log 2`. -/
noncomputable def θ₁ (φ : AsymptoticSpectrumPoint (Tensor K 3) P) : ℝ :=
  Real.log (φ (MM 2 1 1)) / Real.log 2

/-- The second exponent parameter: `θ₂(φ) = log φ(MM 1 2 1) / log 2`. -/
noncomputable def θ₂ (φ : AsymptoticSpectrumPoint (Tensor K 3) P) : ℝ :=
  Real.log (φ (MM 1 2 1)) / Real.log 2

/-- The third exponent parameter: `θ₃(φ) = log φ(MM 1 1 2) / log 2`. -/
noncomputable def θ₃ (φ : AsymptoticSpectrumPoint (Tensor K 3) P) : ℝ :=
  Real.log (φ (MM 1 1 2)) / Real.log 2

/-- Helper: if `P` refines the canonical preorder, then `1 ≤ φ(MM n m p)` whenever
    `1 ≤ n, 1 ≤ m, 1 ≤ p`. -/
private theorem one_le_phi_MM (hP : RefinesCanonical P)
    (φ : AsymptoticSpectrumPoint (Tensor K 3) P) {n m p : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    1 ≤ φ (MM n m p) := by
  have h1 : P.le 1 (MM (K := K) n m p) := hP (one_le_MM hn hm hp)
  have := φ.monotone' h1
  rwa [map_one] at this

/-- Helper: if `P` refines the canonical preorder, then `φ(MM n m p) ≤ n*m*p`. -/
private theorem phi_MM_le_mul (hP : RefinesCanonical P)
    (φ : AsymptoticSpectrumPoint (Tensor K 3) P) (n m p : ℕ) :
    φ (MM n m p) ≤ (n * m * p : ℕ) := by
  have h1 : P.le (MM (K := K) n m p) ((n * m * p : ℕ) : Tensor K 3) := by
    have := MM_le_mul (K := K) n m p
    have heq : ((n : Tensor K 3) * m * p) = ((n * m * p : ℕ) : Tensor K 3) := by push_cast; ring
    rw [heq] at this
    exact hP this
  have := φ.monotone' h1
  rwa [map_natCast] at this

/-- Helper: `0 < φ(MM n m p)` when `1 ≤ n, m, p`. -/
private theorem phi_MM_pos (hP : RefinesCanonical P)
    (φ : AsymptoticSpectrumPoint (Tensor K 3) P) {n m p : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    0 < φ (MM n m p) :=
  lt_of_lt_of_le zero_lt_one (one_le_phi_MM P hP φ hn hm hp)

theorem θ₁_nonneg (hP : RefinesCanonical P)
    (φ : AsymptoticSpectrumPoint (Tensor K 3) P) : 0 ≤ θ₁ P φ := by
  unfold θ₁
  apply div_nonneg
  · exact Real.log_nonneg (one_le_phi_MM P hP φ (by norm_num) (by norm_num) (by norm_num))
  · exact Real.log_nonneg (by norm_num)

theorem θ₁_le_one (hP : RefinesCanonical P)
    (φ : AsymptoticSpectrumPoint (Tensor K 3) P) : θ₁ P φ ≤ 1 := by
  unfold θ₁
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_one hlog2]
  have h1 : φ (MM (K := K) 2 1 1) ≤ ((2 * 1 * 1 : ℕ) : ℝ) := by
    exact_mod_cast phi_MM_le_mul P hP φ 2 1 1
  have h2 : ((2 * 1 * 1 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2] at h1
  have hpos : 0 < φ (MM (K := K) 2 1 1) :=
    phi_MM_pos P hP φ (by norm_num) (by norm_num) (by norm_num)
  calc Real.log (φ (MM 2 1 1)) ≤ Real.log 2 := Real.log_le_log hpos h1
    _ = Real.log 2 := rfl

theorem θ₂_nonneg (hP : RefinesCanonical P)
    (φ : AsymptoticSpectrumPoint (Tensor K 3) P) : 0 ≤ θ₂ P φ := by
  unfold θ₂
  apply div_nonneg
  · exact Real.log_nonneg (one_le_phi_MM P hP φ (by norm_num) (by norm_num) (by norm_num))
  · exact Real.log_nonneg (by norm_num)

theorem θ₂_le_one (hP : RefinesCanonical P)
    (φ : AsymptoticSpectrumPoint (Tensor K 3) P) : θ₂ P φ ≤ 1 := by
  unfold θ₂
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_one hlog2]
  have h1 : φ (MM (K := K) 1 2 1) ≤ ((1 * 2 * 1 : ℕ) : ℝ) := by
    exact_mod_cast phi_MM_le_mul P hP φ 1 2 1
  have h2 : ((1 * 2 * 1 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2] at h1
  have hpos : 0 < φ (MM (K := K) 1 2 1) :=
    phi_MM_pos P hP φ (by norm_num) (by norm_num) (by norm_num)
  exact Real.log_le_log hpos h1

theorem θ₃_nonneg (hP : RefinesCanonical P)
    (φ : AsymptoticSpectrumPoint (Tensor K 3) P) : 0 ≤ θ₃ P φ := by
  unfold θ₃
  apply div_nonneg
  · exact Real.log_nonneg (one_le_phi_MM P hP φ (by norm_num) (by norm_num) (by norm_num))
  · exact Real.log_nonneg (by norm_num)

theorem θ₃_le_one (hP : RefinesCanonical P)
    (φ : AsymptoticSpectrumPoint (Tensor K 3) P) : θ₃ P φ ≤ 1 := by
  unfold θ₃
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_one hlog2]
  have h1 : φ (MM (K := K) 1 1 2) ≤ ((1 * 1 * 2 : ℕ) : ℝ) := by
    exact_mod_cast phi_MM_le_mul P hP φ 1 1 2
  have h2 : ((1 * 1 * 2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2] at h1
  have hpos : 0 < φ (MM (K := K) 1 1 2) :=
    phi_MM_pos P hP φ (by norm_num) (by norm_num) (by norm_num)
  exact Real.log_le_log hpos h1

/-! ### Erdős–Hewitt: monotone multiplicative functions on ℕ are powers

We prove a self-contained lemma `mono_mult_eq_rpow`: if `f : ℕ → ℝ` is multiplicative,
`f 1 = 1`, monotone, and `1 ≤ f n` for `n ≥ 1`, plus `f n ≤ n` for some growth bound,
then for all `n ≥ 1`, `f n = n ^ (log (f 2) / log 2)`. -/

/-- For real-valued `f` satisfying multiplicativity, monotonicity, `f 1 = 1`, `1 ≤ f n` for
    `n ≥ 1`, and a polynomial bound, the squeeze gives `f n = n ^ (log f 2 / log 2)` for
    every `n ≥ 1`. The proof is the classical Erdős–Hewitt argument: bracket `n^k` between
    consecutive powers of 2, take logs, and let `k → ∞`. -/
private theorem mono_mult_eq_rpow (f : ℕ → ℝ)
    (h_mul : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → f (a * b) = f a * f b)
    (h_one : f 1 = 1)
    (h_mono : ∀ a b : ℕ, 1 ≤ a → a ≤ b → f a ≤ f b)
    (h_one_le : ∀ a : ℕ, 1 ≤ a → 1 ≤ f a)
    (h_le_n : ∀ a : ℕ, 1 ≤ a → f a ≤ a) :
    ∀ n : ℕ, 1 ≤ n → f n = (n : ℝ) ^ (Real.log (f 2) / Real.log 2) := by
  set α := Real.log (f 2) / Real.log 2 with hα_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf2_pos : 0 < f 2 := lt_of_lt_of_le zero_lt_one (h_one_le 2 (by norm_num))
  have hf2_ge_one : 1 ≤ f 2 := h_one_le 2 (by norm_num)
  have hlogf2_nonneg : 0 ≤ Real.log (f 2) := Real.log_nonneg hf2_ge_one
  have h_pow : ∀ (n k : ℕ), 1 ≤ n → f (n ^ k) = f n ^ k := by
    intro n k hn
    induction k with
    | zero => simp [h_one]
    | succ k ih =>
        rw [pow_succ, h_mul _ _ (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))) hn, ih, pow_succ]
  have hfn_pos : ∀ n : ℕ, 1 ≤ n → 0 < f n := fun n hn =>
    lt_of_lt_of_le zero_lt_one (h_one_le n hn)
  intro n hn
  rcases eq_or_lt_of_le hn with h1 | h1
  · rw [← h1, h_one]; simp
  have hn2 : 2 ≤ n := h1
  have hn_pos : 0 < n := by omega
  have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hn_real_ge_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have hfn_ge_one : 1 ≤ f n := h_one_le n (by omega)
  have hlogfn_nonneg : 0 ≤ Real.log (f n) := Real.log_nonneg hfn_ge_one
  set β := Real.log (f n) / Real.log n with hβ_def
  suffices h : β = α by
    have : Real.log (f n) = α * Real.log n := by
      have := h ▸ hβ_def
      field_simp at this
      linarith
    have heq : f n = (n : ℝ) ^ α := by
      have hfn_pos' : 0 < f n := hfn_pos n (by omega)
      have hthis : Real.log ((n : ℝ) ^ α) = Real.log (f n) := by
        rw [Real.log_rpow hn_real_pos, ← this]
      have := Real.log_injOn_pos (Set.mem_Ioi.mpr (Real.rpow_pos_of_pos hn_real_pos _))
                                  (Set.mem_Ioi.mpr hfn_pos') hthis
      exact this.symm
    exact heq
  by_cases hf2_eq : f 2 = 1
  · have hα_zero : α = 0 := by simp [hα_def, hf2_eq]
    have hfn_eq_one : f n = 1 := by
      obtain ⟨k, hk⟩ : ∃ k : ℕ, n ≤ 2 ^ k := ⟨n, Nat.lt_two_pow_self.le⟩
      have h2k_ge_one : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
      have h_fle : f n ≤ f (2 ^ k) := h_mono _ _ (by omega) hk
      rw [h_pow 2 k (by norm_num), hf2_eq, one_pow] at h_fle
      linarith
    have hβ_zero : β = 0 := by simp [hβ_def, hfn_eq_one, Real.log_one]
    rw [hβ_zero, hα_zero]
  have hlogf2_pos : 0 < Real.log (f 2) := by
    apply lt_of_le_of_ne hlogf2_nonneg
    intro h
    apply hf2_eq
    have : f 2 = 1 := by
      have := Real.exp_log hf2_pos
      rw [← h, Real.exp_zero] at this
      exact this.symm
    exact this
  have hα_pos : 0 < α := div_pos hlogf2_pos hlog2_pos
  have hsqueeze : ∀ k : ℕ, 1 ≤ k → |β - α| ≤ α / k := by
    intro k hk
    have hnk_pos : 0 < n ^ k := pow_pos hn_pos _
    set a := Nat.log 2 (n ^ k) with ha_def
    have ha_le : 2 ^ a ≤ n ^ k := Nat.pow_log_le_self 2 (by omega)
    have ha_lt : n ^ k < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have ha_le_real : (2 : ℝ) ^ a ≤ (n : ℝ) ^ k := by exact_mod_cast ha_le
    have ha_lt_real : (n : ℝ) ^ k < (2 : ℝ) ^ (a + 1) := by exact_mod_cast ha_lt
    have hlog_n_lo : (a : ℝ) * Real.log 2 ≤ (k : ℝ) * Real.log n := by
      have h1 : Real.log ((2 : ℝ) ^ a) ≤ Real.log ((n : ℝ) ^ k) := by
        apply Real.log_le_log
        · exact pow_pos (by norm_num) _
        · exact ha_le_real
      rwa [Real.log_pow, Real.log_pow] at h1
    have hlog_n_hi : (k : ℝ) * Real.log n ≤ ((a : ℝ) + 1) * Real.log 2 := by
      have h1 : Real.log ((n : ℝ) ^ k) ≤ Real.log ((2 : ℝ) ^ (a + 1)) := by
        apply Real.log_le_log
        · exact pow_pos hn_real_pos _
        · exact ha_lt_real.le
      rw [Real.log_pow, Real.log_pow] at h1
      push_cast at h1 ⊢
      linarith
    have h_f_lo : f (2 ^ a) ≤ f (n ^ k) := h_mono _ _ (Nat.one_le_pow _ _ (by norm_num)) ha_le
    have h_f_hi : f (n ^ k) ≤ f (2 ^ (a + 1)) := h_mono _ _ (Nat.one_le_pow _ _ hn_pos) ha_lt.le
    rw [h_pow 2 a (by norm_num), h_pow n k (by omega)] at h_f_lo
    rw [h_pow n k (by omega), h_pow 2 (a + 1) (by norm_num)] at h_f_hi
    have hf2_pow_pos : ∀ j : ℕ, 0 < f 2 ^ j := fun j => pow_pos hf2_pos j
    have hfn_pow_pos : 0 < f n ^ k := pow_pos (hfn_pos n (by omega)) k
    have hlog_f_lo : (a : ℝ) * Real.log (f 2) ≤ (k : ℝ) * Real.log (f n) := by
      have h1 : Real.log (f 2 ^ a) ≤ Real.log (f n ^ k) :=
        Real.log_le_log (hf2_pow_pos a) h_f_lo
      rwa [Real.log_pow, Real.log_pow] at h1
    have hlog_f_hi : (k : ℝ) * Real.log (f n) ≤ ((a : ℝ) + 1) * Real.log (f 2) := by
      have h1 : Real.log (f n ^ k) ≤ Real.log (f 2 ^ (a + 1)) :=
        Real.log_le_log hfn_pow_pos h_f_hi
      rw [Real.log_pow, Real.log_pow] at h1
      push_cast at h1 ⊢
      linarith
    have k_pos : (0 : ℝ) < k := by exact_mod_cast hk
    have hα'_lo : (a : ℝ) / k ≤ Real.log n / Real.log 2 := by
      rw [div_le_div_iff₀ k_pos hlog2_pos]
      linarith
    have hα'_hi : Real.log n / Real.log 2 ≤ ((a : ℝ) + 1) / k := by
      rw [div_le_div_iff₀ hlog2_pos k_pos]
      linarith
    have hγ_lo : (a : ℝ) / k ≤ Real.log (f n) / Real.log (f 2) := by
      rw [div_le_div_iff₀ k_pos hlogf2_pos]
      linarith
    have hγ_hi : Real.log (f n) / Real.log (f 2) ≤ ((a : ℝ) + 1) / k := by
      rw [div_le_div_iff₀ hlogf2_pos k_pos]
      linarith
    have hsub : ((a : ℝ) + 1) / k - (a : ℝ) / k = 1 / k := by
      field_simp; ring
    have habs : |Real.log n / Real.log 2 - Real.log (f n) / Real.log (f 2)| ≤ 1 / k := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have : Real.log (f n) / Real.log (f 2) ≤ Real.log n / Real.log 2 + 1 / k := by
          calc Real.log (f n) / Real.log (f 2)
              ≤ ((a : ℝ) + 1) / k := hγ_hi
            _ = (a : ℝ) / k + 1 / k := by field_simp
            _ ≤ Real.log n / Real.log 2 + 1 / k := by linarith
        linarith
      · have : Real.log n / Real.log 2 ≤ Real.log (f n) / Real.log (f 2) + 1 / k := by
          calc Real.log n / Real.log 2
              ≤ ((a : ℝ) + 1) / k := hα'_hi
            _ = (a : ℝ) / k + 1 / k := by field_simp
            _ ≤ Real.log (f n) / Real.log (f 2) + 1 / k := by linarith
        linarith
    have habs_β_α : |β - α| = |Real.log n / Real.log 2 - Real.log (f n) / Real.log (f 2)| *
                              (Real.log (f 2) / Real.log n) := by
      have hβα : β - α = -(Real.log n / Real.log 2 - Real.log (f n) / Real.log (f 2)) *
                          (Real.log (f 2) / Real.log n) := by
        rw [hβ_def, hα_def]
        field_simp
        ring
      rw [hβα, abs_mul, abs_neg, abs_of_pos (div_pos hlogf2_pos hlogn_pos)]
    rw [habs_β_α]
    have h1 : |Real.log n / Real.log 2 - Real.log (f n) / Real.log (f 2)| *
                (Real.log (f 2) / Real.log n) ≤ (1 / k) * (Real.log (f 2) / Real.log n) := by
      apply mul_le_mul_of_nonneg_right habs
      exact div_nonneg hlogf2_nonneg hlogn_pos.le
    apply le_trans h1
    have hlog2_le_logn : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have hkey : Real.log (f 2) / Real.log n ≤ Real.log (f 2) / Real.log 2 := by
      rw [div_le_div_iff₀ hlogn_pos hlog2_pos]
      have := mul_le_mul_of_nonneg_left hlog2_le_logn hlogf2_nonneg
      linarith
    have hk_inv_nonneg : (0 : ℝ) ≤ 1 / k := by positivity
    calc (1 / (k : ℝ)) * (Real.log (f 2) / Real.log n)
        ≤ (1 / (k : ℝ)) * (Real.log (f 2) / Real.log 2) :=
          mul_le_mul_of_nonneg_left hkey hk_inv_nonneg
      _ = α / k := by rw [hα_def]; ring
  by_contra hne
  have hdiff_pos : 0 < |β - α| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := exists_nat_gt (α / |β - α|)
  have hk_pos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso; rw [h] at hk; push_cast at hk
      have : (0 : ℝ) < α / |β - α| := div_pos hα_pos hdiff_pos
      linarith
    · exact h
  have hbound := hsqueeze k hk_pos
  have hk_pos_real : (0 : ℝ) < k := by exact_mod_cast hk_pos
  rw [div_lt_iff₀ hdiff_pos] at hk
  have : |β - α| * k > α := by linarith
  have hk_α : α / k < |β - α| := by
    rw [div_lt_iff₀ hk_pos_real]
    linarith
  linarith

/-- Main parametrization theorem (Proposition 4.3 of main.tex):
    every spectrum point satisfies `φ(MM n m p) = n^θ₁ · m^θ₂ · p^θ₃`
    for `n, m, p ≥ 1`. -/
theorem MM_eval (hP : RefinesCanonical P)
    (φ : AsymptoticSpectrumPoint (Tensor K 3) P)
    {n m p : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    φ (MM n m p) = (n : ℝ) ^ θ₁ P φ * (m : ℝ) ^ θ₂ P φ * (p : ℝ) ^ θ₃ P φ := by
  let f₁ : ℕ → ℝ := fun a => φ (MM a 1 1)
  let f₂ : ℕ → ℝ := fun a => φ (MM 1 a 1)
  let f₃ : ℕ → ℝ := fun a => φ (MM 1 1 a)
  have h_one_eq : ∀ axis : Fin 3, ([f₁, f₂, f₃].get ⟨axis, by simp⟩) 1 = 1 := by
    intro axis
    fin_cases axis
    all_goals (show φ (MM _ _ _) = 1; rw [MM_one]; exact map_one _)
  have h_mul₁ : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → f₁ (a * b) = f₁ a * f₁ b := by
    intro a b _ _
    show φ (MM (a * b) 1 1) = φ (MM a 1 1) * φ (MM b 1 1)
    have : MM (K := K) (a * b) (1 * 1) (1 * 1) = MM a 1 1 * MM b 1 1 := (MM_mul a 1 1 b 1 1).symm
    rw [show (a * b : ℕ) = a * b from rfl, ← (by simp : 1 * 1 = 1), this]
    exact map_mul _ _ _
  have h_mul₂ : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → f₂ (a * b) = f₂ a * f₂ b := by
    intro a b _ _
    show φ (MM 1 (a * b) 1) = φ (MM 1 a 1) * φ (MM 1 b 1)
    have : MM (K := K) (1 * 1) (a * b) (1 * 1) = MM 1 a 1 * MM 1 b 1 := (MM_mul 1 a 1 1 b 1).symm
    rw [show (a * b : ℕ) = a * b from rfl, ← (by simp : 1 * 1 = 1), this]
    exact map_mul _ _ _
  have h_mul₃ : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → f₃ (a * b) = f₃ a * f₃ b := by
    intro a b _ _
    show φ (MM 1 1 (a * b)) = φ (MM 1 1 a) * φ (MM 1 1 b)
    have : MM (K := K) (1 * 1) (1 * 1) (a * b) = MM 1 1 a * MM 1 1 b := (MM_mul 1 1 a 1 1 b).symm
    rw [show (a * b : ℕ) = a * b from rfl, ← (by simp : 1 * 1 = 1), this]
    exact map_mul _ _ _
  have h_one₁ : f₁ 1 = 1 := by show φ (MM 1 1 1) = 1; rw [MM_one]; exact map_one _
  have h_one₂ : f₂ 1 = 1 := by show φ (MM 1 1 1) = 1; rw [MM_one]; exact map_one _
  have h_one₃ : f₃ 1 = 1 := by show φ (MM 1 1 1) = 1; rw [MM_one]; exact map_one _
  have h_mono_general : ∀ {n n' m m' p p' : ℕ}, 1 ≤ n → 1 ≤ m → 1 ≤ p →
      n ≤ n' → m ≤ m' → p ≤ p' → φ (MM n m p) ≤ φ (MM n' m' p') := by
    intro n n' m m' p p' _ _ _ hnn hmm hpp
    have h := MM_le_of_le (K := K) hnn hmm hpp
    exact φ.monotone' (hP h)
  have h_mono₁ : ∀ a b : ℕ, 1 ≤ a → a ≤ b → f₁ a ≤ f₁ b := fun a b ha hab =>
    h_mono_general ha (le_refl _) (le_refl _) hab (le_refl _) (le_refl _)
  have h_mono₂ : ∀ a b : ℕ, 1 ≤ a → a ≤ b → f₂ a ≤ f₂ b := fun a b ha hab =>
    h_mono_general (le_refl _) ha (le_refl _) (le_refl _) hab (le_refl _)
  have h_mono₃ : ∀ a b : ℕ, 1 ≤ a → a ≤ b → f₃ a ≤ f₃ b := fun a b ha hab =>
    h_mono_general (le_refl _) (le_refl _) ha (le_refl _) (le_refl _) hab
  have h_one_le₁ : ∀ a : ℕ, 1 ≤ a → 1 ≤ f₁ a := fun a ha =>
    one_le_phi_MM P hP φ ha (le_refl _) (le_refl _)
  have h_one_le₂ : ∀ a : ℕ, 1 ≤ a → 1 ≤ f₂ a := fun a ha =>
    one_le_phi_MM P hP φ (le_refl _) ha (le_refl _)
  have h_one_le₃ : ∀ a : ℕ, 1 ≤ a → 1 ≤ f₃ a := fun a ha =>
    one_le_phi_MM P hP φ (le_refl _) (le_refl _) ha
  have h_le_n₁ : ∀ a : ℕ, 1 ≤ a → f₁ a ≤ a := by
    intro a _
    have h := phi_MM_le_mul P hP φ a 1 1
    have heq : ((a * 1 * 1 : ℕ) : ℝ) = a := by push_cast; ring
    rwa [heq] at h
  have h_le_n₂ : ∀ a : ℕ, 1 ≤ a → f₂ a ≤ a := by
    intro a _
    have h := phi_MM_le_mul P hP φ 1 a 1
    have heq : ((1 * a * 1 : ℕ) : ℝ) = a := by push_cast; ring
    rwa [heq] at h
  have h_le_n₃ : ∀ a : ℕ, 1 ≤ a → f₃ a ≤ a := by
    intro a _
    have h := phi_MM_le_mul P hP φ 1 1 a
    have heq : ((1 * 1 * a : ℕ) : ℝ) = a := by push_cast; ring
    rwa [heq] at h
  have hf₁_eq : ∀ a : ℕ, 1 ≤ a → f₁ a = (a : ℝ) ^ (Real.log (f₁ 2) / Real.log 2) :=
    mono_mult_eq_rpow f₁ h_mul₁ h_one₁ h_mono₁ h_one_le₁ h_le_n₁
  have hf₂_eq : ∀ a : ℕ, 1 ≤ a → f₂ a = (a : ℝ) ^ (Real.log (f₂ 2) / Real.log 2) :=
    mono_mult_eq_rpow f₂ h_mul₂ h_one₂ h_mono₂ h_one_le₂ h_le_n₂
  have hf₃_eq : ∀ a : ℕ, 1 ≤ a → f₃ a = (a : ℝ) ^ (Real.log (f₃ 2) / Real.log 2) :=
    mono_mult_eq_rpow f₃ h_mul₃ h_one₃ h_mono₃ h_one_le₃ h_le_n₃
  have hθ₁_eq : Real.log (f₁ 2) / Real.log 2 = θ₁ P φ := rfl
  have hθ₂_eq : Real.log (f₂ 2) / Real.log 2 = θ₂ P φ := rfl
  have hθ₃_eq : Real.log (f₃ 2) / Real.log 2 = θ₃ P φ := rfl
  have hMM_decomp : MM (K := K) n m p = MM n 1 1 * MM 1 m 1 * MM 1 1 p := by
    have h1 : MM (K := K) n m 1 = MM n 1 1 * MM 1 m 1 := by
      have := MM_mul (K := K) n 1 1 1 m 1
      simp only [Nat.mul_one, Nat.one_mul] at this
      exact this.symm
    have h2 : MM (K := K) n m p = MM n m 1 * MM 1 1 p := by
      have := MM_mul (K := K) n m 1 1 1 p
      simp only [Nat.mul_one, Nat.one_mul] at this
      exact this.symm
    rw [h2, h1]
  rw [hMM_decomp, map_mul, map_mul]
  show f₁ n * f₂ m * f₃ p = _
  rw [hf₁_eq n hn, hf₂_eq m hm, hf₃_eq p hp, hθ₁_eq, hθ₂_eq, hθ₃_eq]

/-! ## specMM: the spectrum of matrix multiplication -/

/-- The spectrum of matrix multiplication `specMM ⊆ ℝ³`:
    the image of the asymptotic spectrum under `φ ↦ (θ₁(φ), θ₂(φ), θ₃(φ))`. -/
noncomputable def specMM : Set (ℝ × ℝ × ℝ) :=
  (fun φ => (θ₁ P φ, θ₂ P φ, θ₃ P φ)) '' Set.univ

/-- `specMM ⊆ [0,1]³`. -/
theorem specMM_subset_unitCube (hP : RefinesCanonical P) :
    specMM P ⊆ Set.Icc 0 1 ×ˢ (Set.Icc 0 1 ×ˢ Set.Icc 0 1) := by
  rintro ⟨a, b, c⟩ ⟨φ, -, h⟩
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj h |>.imp_right Prod.mk.inj
  exact ⟨⟨θ₁_nonneg P hP φ, θ₁_le_one P hP φ⟩,
         ⟨θ₂_nonneg P hP φ, θ₂_le_one P hP φ⟩,
         ⟨θ₃_nonneg P hP φ, θ₃_le_one P hP φ⟩⟩

/-- The parametrization map is continuous. -/
private theorem specMM_map_continuous (hP : RefinesCanonical P) :
    Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) P =>
      (θ₁ P φ, θ₂ P φ, θ₃ P φ)) := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have h_eval₁ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) P =>
      φ (MM (K := K) 2 1 1)) := continuous_eval P _
  have h_eval₂ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) P =>
      φ (MM (K := K) 1 2 1)) := continuous_eval P _
  have h_eval₃ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) P =>
      φ (MM (K := K) 1 1 2)) := continuous_eval P _
  have hlog₁ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) P =>
      Real.log (φ (MM (K := K) 2 1 1))) := by
    refine Real.continuousOn_log.comp_continuous h_eval₁ ?_
    intro φ
    exact ne_of_gt (phi_MM_pos P hP φ (by norm_num) (by norm_num) (by norm_num))
  have hlog₂ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) P =>
      Real.log (φ (MM (K := K) 1 2 1))) := by
    refine Real.continuousOn_log.comp_continuous h_eval₂ ?_
    intro φ
    exact ne_of_gt (phi_MM_pos P hP φ (by norm_num) (by norm_num) (by norm_num))
  have hlog₃ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) P =>
      Real.log (φ (MM (K := K) 1 1 2))) := by
    refine Real.continuousOn_log.comp_continuous h_eval₃ ?_
    intro φ
    exact ne_of_gt (phi_MM_pos P hP φ (by norm_num) (by norm_num) (by norm_num))
  exact (hlog₁.div_const _).prodMk ((hlog₂.div_const _).prodMk (hlog₃.div_const _))

/-- `specMM` is compact. -/
theorem specMM_compact (hP : RefinesCanonical P) : IsCompact (specMM P) :=
  isCompact_univ.image (specMM_map_continuous P hP)

/-! ## The matrix multiplication exponent ω -/

/-- The matrix multiplication exponent `ω`, defined as
    `inf_{n ≥ 2} { log Rk(MM n n n) / log n }` where `Rk` is the ordinary
    integer rank with respect to the canonical `Restrict`-based Strassen
    preorder on `Tensor K 3`. This is an intrinsic invariant of the
    semiring, not depending on any abstract preorder `P`. -/
noncomputable def matMulExp : ℝ :=
  iInf (fun n : ℕ =>
    if 1 < n then
      Real.log (StrassenPreorder.rank Tensor.instStrassenPreorder
        (MM (K := K) n n n) : ℝ) / Real.log n
    else 3)

/-- For positive dimensions and the canonical preorder, `rank(MM n m p) ≥ 1`. -/
private lemma one_le_rank_MM {n m p : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    1 ≤ StrassenPreorder.rank (Tensor.instStrassenPreorder)
      (MM (K := K) n m p) := by
  have hMM : MM (K := K) n m p ≠ 0 := MM_ne_zero hn hm hp
  rcases Tensor.instStrassenPreorder.lower_archimedean (MM (K := K) n m p) with h | h
  · exact absurd h hMM
  · have := StrassenPreorder.rank_monotone Tensor.instStrassenPreorder 1
      (MM n m p) h
    rwa [StrassenPreorder.rank_one] at this

/-- The summand inside the iInf defining `matMulExp`. -/
private noncomputable def matMulExpFun (n : ℕ) : ℝ :=
  if 1 < n then
    Real.log (StrassenPreorder.rank Tensor.instStrassenPreorder
      (MM (K := K) n n n) : ℝ) / Real.log n
  else 3

private lemma matMulExpFun_nonneg (n : ℕ) : 0 ≤ matMulExpFun (K := K) n := by
  unfold matMulExpFun
  split_ifs with hn
  · refine div_nonneg ?_ ?_
    · apply Real.log_nonneg
      exact_mod_cast one_le_rank_MM (K := K) (by omega) (by omega) (by omega)
    · exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  · norm_num

private lemma matMulExp_bddBelow :
    BddBelow (Set.range (matMulExpFun (K := K))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact matMulExpFun_nonneg n

private lemma matMulExp_eq_iInf :
    matMulExp (K := K) = iInf (matMulExpFun (K := K)) := rfl

/-- For each `n ≥ 2`, the iInf is at most the value at `n`. -/
private lemma matMulExp_le_at {n : ℕ} (hn : 1 < n) :
    matMulExp (K := K) ≤
      Real.log (StrassenPreorder.rank Tensor.instStrassenPreorder
        (MM (K := K) n n n) : ℝ) / Real.log n := by
  have h := ciInf_le (matMulExp_bddBelow (K := K)) n
  unfold matMulExpFun at h
  rw [if_pos hn] at h
  exact h

/-- Forward direction of the canonical normalization:
    `ω ≤ log_2 AR(MM 2 2 2)`. -/
private lemma matMulExp_le_log_AR_222 :
    matMulExp (K := K) ≤
      Real.log (StrassenPreorder.asymptotic_rank Tensor.instStrassenPreorder
        (MM (K := K) 2 2 2)) / Real.log 2 := by
  set Pcan : StrassenPreorder (Tensor K 3) := Tensor.instStrassenPreorder with hPcan
  set M : Tensor K 3 := MM (K := K) 2 2 2 with hM
  have hM_ne : M ≠ 0 := MM_ne_zero (by norm_num) (by norm_num) (by norm_num)
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have hAR : Filter.Tendsto
      (fun k : ℕ => (StrassenPreorder.rank Pcan (M ^ k) : ℝ) ^ (1 / (k : ℝ)))
      Filter.atTop (nhds (StrassenPreorder.asymptotic_rank Pcan M)) :=
    StrassenPreorder.tends_to_asymptotic_rank Pcan M hM_ne
  have hAR_pos : 0 < StrassenPreorder.asymptotic_rank Pcan M := by
    have h_eventually : ∀ᶠ k : ℕ in Filter.atTop,
        (1 : ℝ) ≤ (StrassenPreorder.rank Pcan (M ^ k) : ℝ) ^ (1 / (k : ℝ)) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with k hk
      have hrk : (1 : ℝ) ≤ (StrassenPreorder.rank Pcan (M ^ k) : ℝ) := by
        have hMk_ne : M ^ k ≠ 0 := Pcan.pow_ne_zero _ hM_ne
        rcases Pcan.lower_archimedean (M ^ k) with h | h
        · exact absurd h hMk_ne
        · have := StrassenPreorder.rank_monotone Pcan 1 (M ^ k) h
          rw [StrassenPreorder.rank_one] at this
          exact_mod_cast this
      have hk' : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
      calc (1 : ℝ) = (1 : ℝ) ^ (1 / (k : ℝ)) := by rw [Real.one_rpow]
        _ ≤ (StrassenPreorder.rank Pcan (M ^ k) : ℝ) ^ (1 / (k : ℝ)) := by
            exact Real.rpow_le_rpow (by norm_num) hrk hk'
    have h_lim_ge_1 : (1 : ℝ) ≤ StrassenPreorder.asymptotic_rank Pcan M :=
      ge_of_tendsto hAR h_eventually
    linarith
  have hLog : Filter.Tendsto
      (fun k : ℕ => Real.log ((StrassenPreorder.rank Pcan (M ^ k) : ℝ) ^
        (1 / (k : ℝ))))
      Filter.atTop (nhds (Real.log (StrassenPreorder.asymptotic_rank Pcan M))) := by
    exact (Real.continuousAt_log (ne_of_gt hAR_pos)).tendsto.comp hAR
  have hLog_eq : ∀ᶠ k : ℕ in Filter.atTop,
      Real.log ((StrassenPreorder.rank Pcan (M ^ k) : ℝ) ^ (1 / (k : ℝ))) =
      Real.log (StrassenPreorder.rank Pcan (M ^ k) : ℝ) / k := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hrk_pos : (0 : ℝ) < (StrassenPreorder.rank Pcan (M ^ k) : ℝ) := by
      have hMk_ne : M ^ k ≠ 0 := Pcan.pow_ne_zero _ hM_ne
      have h1 : 1 ≤ StrassenPreorder.rank Pcan (M ^ k) := by
        rcases Pcan.lower_archimedean (M ^ k) with h | h
        · exact absurd h hMk_ne
        · have := StrassenPreorder.rank_monotone Pcan 1 (M ^ k) h
          rwa [StrassenPreorder.rank_one] at this
      have : (0 : ℕ) < StrassenPreorder.rank Pcan (M ^ k) := by omega
      exact_mod_cast this
    rw [Real.log_rpow hrk_pos]
    ring
  have hLog' : Filter.Tendsto
      (fun k : ℕ => Real.log (StrassenPreorder.rank Pcan (M ^ k) : ℝ) / k)
      Filter.atTop (nhds (Real.log (StrassenPreorder.asymptotic_rank Pcan M))) :=
    hLog.congr' hLog_eq
  have hLog_div : Filter.Tendsto
      (fun k : ℕ => Real.log (StrassenPreorder.rank Pcan (M ^ k) : ℝ) /
        ((k : ℝ) * Real.log 2))
      Filter.atTop (nhds (Real.log (StrassenPreorder.asymptotic_rank Pcan M) /
        Real.log 2)) := by
    have : Filter.Tendsto
        (fun k : ℕ => (Real.log (StrassenPreorder.rank Pcan (M ^ k) : ℝ) / k) /
          Real.log 2)
        Filter.atTop (nhds (Real.log (StrassenPreorder.asymptotic_rank Pcan M) /
          Real.log 2)) := hLog'.div_const _
    refine this.congr ?_
    intro k
    rw [div_div]
  have h_le_each : ∀ᶠ k : ℕ in Filter.atTop,
      matMulExp (K := K) ≤
        Real.log (StrassenPreorder.rank Pcan (M ^ k) : ℝ) /
          ((k : ℝ) * Real.log 2) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have h2k : 1 < 2 ^ k := by
      have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      omega
    have h_apply := matMulExp_le_at (K := K) (n := 2 ^ k) h2k
    have hpow_eq : M ^ k = MM (K := K) (2 ^ k) (2 ^ k) (2 ^ k) := by
      simpa [hM] using MM_pow (K := K) 2 2 2 k
    have hlog_pow : Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
      push_cast
      rw [Real.log_pow]
    rw [hlog_pow, ← hpow_eq] at h_apply
    exact h_apply
  exact ge_of_tendsto hLog_div h_le_each

/-- Reverse direction of the canonical normalization:
    `log_2 AR(MM 2 2 2) ≤ ω`. -/
private lemma log_AR_222_le_matMulExp :
    Real.log (StrassenPreorder.asymptotic_rank Tensor.instStrassenPreorder
      (MM (K := K) 2 2 2)) / Real.log 2 ≤ matMulExp (K := K) := by
  set Pcan : StrassenPreorder (Tensor K 3) := Tensor.instStrassenPreorder with hPcan
  set M : Tensor K 3 := MM (K := K) 2 2 2 with hM
  have hM_ne : M ≠ 0 := MM_ne_zero (by norm_num) (by norm_num) (by norm_num)
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have hAR_tend : Filter.Tendsto
      (fun k : ℕ => (StrassenPreorder.rank Pcan (M ^ k) : ℝ) ^ (1 / (k : ℝ)))
      Filter.atTop (nhds (StrassenPreorder.asymptotic_rank Pcan M)) :=
    StrassenPreorder.tends_to_asymptotic_rank Pcan M hM_ne
  refine le_ciInf ?_
  intro n
  by_cases hn : 1 < n
  · simp only [if_pos hn]
    set N : Tensor K 3 := MM (K := K) n n n with hN
    have hN_ne : N ≠ 0 :=
      MM_ne_zero (by omega) (by omega) (by omega)
    have hrN_ge_1 : 1 ≤ StrassenPreorder.rank Pcan N := one_le_rank_MM
      (K := K) (by omega) (by omega) (by omega)
    have hrN_pos : (0 : ℝ) < (StrassenPreorder.rank Pcan N : ℝ) := by
      have : (0 : ℕ) < StrassenPreorder.rank Pcan N := by omega
      exact_mod_cast this
    have hlogn_pos : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
    rw [div_le_div_iff₀ hlog2_pos hlogn_pos]
    suffices h_pow : StrassenPreorder.asymptotic_rank Pcan M ≤
        (StrassenPreorder.rank Pcan N : ℝ) ^ (Real.log 2 / Real.log n) by
      have hAR_pos : 0 < StrassenPreorder.asymptotic_rank Pcan M := by
        have h_eventually : ∀ᶠ k : ℕ in Filter.atTop,
            (1 : ℝ) ≤ (StrassenPreorder.rank Pcan (M ^ k) : ℝ) ^ (1 / (k : ℝ)) := by
          filter_upwards [Filter.eventually_ge_atTop 1] with k hk
          have hMk_ne : M ^ k ≠ 0 := Pcan.pow_ne_zero _ hM_ne
          have hrk : (1 : ℝ) ≤ (StrassenPreorder.rank Pcan (M ^ k) : ℝ) := by
            rcases Pcan.lower_archimedean (M ^ k) with h | h
            · exact absurd h hMk_ne
            · have := StrassenPreorder.rank_monotone Pcan 1 (M ^ k) h
              rw [StrassenPreorder.rank_one] at this
              exact_mod_cast this
          have hk' : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
          calc (1 : ℝ) = (1 : ℝ) ^ (1 / (k : ℝ)) := by rw [Real.one_rpow]
            _ ≤ _ := Real.rpow_le_rpow (by norm_num) hrk hk'
        linarith [ge_of_tendsto hAR_tend h_eventually]
      have h_log :=
        Real.log_le_log hAR_pos h_pow
      rw [Real.log_rpow hrN_pos] at h_log
      have : Real.log (StrassenPreorder.asymptotic_rank Pcan M) * Real.log n ≤
          Real.log (StrassenPreorder.rank Pcan N : ℝ) * Real.log 2 := by
        have hh : Real.log (StrassenPreorder.asymptotic_rank Pcan M) ≤
            Real.log 2 / Real.log n * Real.log (StrassenPreorder.rank Pcan N : ℝ) :=
          h_log
        have hmul := mul_le_mul_of_nonneg_right hh (le_of_lt hlogn_pos)
        have hsimp : Real.log 2 / Real.log n * Real.log (StrassenPreorder.rank Pcan N : ℝ) *
            Real.log n = Real.log (StrassenPreorder.rank Pcan N : ℝ) * Real.log 2 := by
          field_simp
        rw [hsimp] at hmul
        exact hmul
      linarith
    have hN_target_pos : (0 : ℝ) < (StrassenPreorder.rank Pcan N : ℝ) ^
        (Real.log 2 / Real.log n) := Real.rpow_pos_of_pos hrN_pos _
    set α : ℝ := Real.log 2 / Real.log n with hα
    have hα_pos : 0 < α := div_pos hlog2_pos hlogn_pos
    let φ : ℕ → ℕ := fun k => ⌈k * α⌉₊
    have hφ_ge : ∀ k : ℕ, (k : ℝ) * α ≤ φ k := fun k => Nat.le_ceil _
    have hn_pow_ge : ∀ k : ℕ, (2 : ℝ) ^ k ≤ (n : ℝ) ^ (φ k) := by
      intro k
      have h1 : Real.log ((2 : ℝ) ^ k) = (k : ℝ) * Real.log 2 := by
        rw [Real.log_pow]
      have h2 : (k : ℝ) * Real.log 2 ≤ (φ k : ℝ) * Real.log n := by
        have hineq : (k : ℝ) * α * Real.log n ≤ (φ k : ℝ) * Real.log n :=
          mul_le_mul_of_nonneg_right (hφ_ge k) (le_of_lt hlogn_pos)
        have heq : (k : ℝ) * α * Real.log n = (k : ℝ) * Real.log 2 := by
          rw [hα]; field_simp
        linarith
      have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have h2_pow_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have hn_pow_pos : (0 : ℝ) < (n : ℝ) ^ (φ k) := by positivity
      rw [← Real.log_le_log_iff h2_pow_pos hn_pow_pos]
      rw [h1, Real.log_pow]
      exact h2
    have hn_pow_ge_nat : ∀ k : ℕ, 2 ^ k ≤ n ^ (φ k) := by
      intro k
      have := hn_pow_ge k
      exact_mod_cast this
    have h_le_canon : ∀ k : ℕ,
        StrassenPreorder.rank Pcan (M ^ k) ≤
          StrassenPreorder.rank Pcan (N ^ (φ k)) := by
      intro k
      apply StrassenPreorder.rank_monotone
      rw [show (M ^ k : Tensor K 3) = MM (K := K) (2 ^ k) (2 ^ k) (2 ^ k) by
        simpa [hM] using MM_pow (K := K) 2 2 2 k]
      rw [show (N ^ (φ k) : Tensor K 3) = MM (K := K) (n ^ (φ k)) (n ^ (φ k)) (n ^ (φ k)) by
        simpa [hN] using MM_pow (K := K) n n n (φ k)]
      exact MM_le_of_le (hn_pow_ge_nat k) (hn_pow_ge_nat k) (hn_pow_ge_nat k)
    have h_rank_N_pow : ∀ k : ℕ,
        StrassenPreorder.rank Pcan (N ^ (φ k)) ≤
          (StrassenPreorder.rank Pcan N) ^ (φ k) := by
      intro k
      induction φ k with
      | zero => simp [StrassenPreorder.rank_one]
      | succ j ih =>
        rw [pow_succ, pow_succ]
        calc StrassenPreorder.rank Pcan (N ^ j * N) ≤
            StrassenPreorder.rank Pcan (N ^ j) * StrassenPreorder.rank Pcan N :=
              StrassenPreorder.rank_submultiplicative _ _ _
          _ ≤ (StrassenPreorder.rank Pcan N) ^ j * StrassenPreorder.rank Pcan N :=
              Nat.mul_le_mul_right _ ih
    have h_combined : ∀ k : ℕ,
        (StrassenPreorder.rank Pcan (M ^ k) : ℝ) ≤
          (StrassenPreorder.rank Pcan N : ℝ) ^ (φ k) := by
      intro k
      have h1 := h_le_canon k
      have h2 := h_rank_N_pow k
      have : StrassenPreorder.rank Pcan (M ^ k) ≤
          (StrassenPreorder.rank Pcan N) ^ (φ k) := le_trans h1 h2
      exact_mod_cast this
    have hφ_div_tend : Filter.Tendsto (fun k : ℕ => (φ k : ℝ) / k)
        Filter.atTop (nhds α) := by
      have h_lb : ∀ k : ℕ, (k : ℝ) * α ≤ φ k := hφ_ge
      have h_ub : ∀ k : ℕ, (φ k : ℝ) < (k : ℝ) * α + 1 := by
        intro k
        have hk_α_nn : 0 ≤ (k : ℝ) * α := mul_nonneg (Nat.cast_nonneg _) (le_of_lt hα_pos)
        have := Nat.ceil_lt_add_one hk_α_nn
        exact_mod_cast this
      have h_squeeze : ∀ k : ℕ, k ≥ 1 →
          α ≤ (φ k : ℝ) / k ∧ (φ k : ℝ) / k < α + 1 / k := by
        intro k hk
        have hkR_pos : (0 : ℝ) < k := by exact_mod_cast hk
        constructor
        · rw [le_div_iff₀ hkR_pos]
          have := h_lb k
          linarith
        · rw [div_lt_iff₀ hkR_pos]
          have hub := h_ub k
          have heq : (α + 1 / (k : ℝ)) * k = α * k + 1 := by
            field_simp
          rw [heq]
          linarith
      have h_α_le : ∀ᶠ k : ℕ in Filter.atTop, α ≤ (φ k : ℝ) / k := by
        filter_upwards [Filter.eventually_ge_atTop 1] with k hk
        exact (h_squeeze k hk).1
      have h_lt_α_plus : ∀ᶠ k : ℕ in Filter.atTop,
          (φ k : ℝ) / k < α + 1 / k := by
        filter_upwards [Filter.eventually_ge_atTop 1] with k hk
        exact (h_squeeze k hk).2
      have h_one_div_tend : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / k)
          Filter.atTop (nhds 0) :=
        tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h_const_α : Filter.Tendsto (fun _ : ℕ => α) Filter.atTop (nhds α) :=
        tendsto_const_nhds
      have h_α_plus : Filter.Tendsto (fun k : ℕ => α + 1 / (k : ℝ))
          Filter.atTop (nhds α) := by
        have h := h_const_α.add h_one_div_tend
        simpa using h
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_const_α h_α_plus
        h_α_le (h_lt_α_plus.mono fun _ h => le_of_lt h)
    have h_continuous_rpow : Filter.Tendsto
        (fun k : ℕ => (StrassenPreorder.rank Pcan N : ℝ) ^ ((φ k : ℝ) / k))
        Filter.atTop (nhds ((StrassenPreorder.rank Pcan N : ℝ) ^ α)) := by
      exact (Real.continuousAt_const_rpow (ne_of_gt hrN_pos)).tendsto.comp hφ_div_tend
    have h_le_each : ∀ᶠ k : ℕ in Filter.atTop,
        (StrassenPreorder.rank Pcan (M ^ k) : ℝ) ^ (1 / (k : ℝ)) ≤
        (StrassenPreorder.rank Pcan N : ℝ) ^ ((φ k : ℝ) / k) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with k hk
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
      have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
      have hMk_pos : (0 : ℝ) ≤ (StrassenPreorder.rank Pcan (M ^ k) : ℝ) := by
        exact Nat.cast_nonneg _
      have h1 : (StrassenPreorder.rank Pcan (M ^ k) : ℝ) ^ (1 / (k : ℝ)) ≤
          ((StrassenPreorder.rank Pcan N : ℝ) ^ (φ k : ℕ)) ^ (1 / (k : ℝ)) := by
        refine Real.rpow_le_rpow hMk_pos ?_ (by positivity)
        have := h_combined k
        rw [show ((StrassenPreorder.rank Pcan N : ℝ) ^ (φ k : ℕ)) =
          (StrassenPreorder.rank Pcan N : ℝ) ^ (φ k) from by norm_cast]
        exact this
      have h2 : ((StrassenPreorder.rank Pcan N : ℝ) ^ (φ k : ℕ)) ^ (1 / (k : ℝ)) =
          (StrassenPreorder.rank Pcan N : ℝ) ^ ((φ k : ℝ) / k) := by
        rw [← Real.rpow_natCast (StrassenPreorder.rank Pcan N : ℝ) (φ k)]
        rw [← Real.rpow_mul (le_of_lt hrN_pos)]
        congr 1
        field_simp
      linarith [h1, h2 ▸ h1]
    exact le_of_tendsto_of_tendsto hAR_tend h_continuous_rpow h_le_each
  · simp only [if_neg hn]
    have hM_le_8 : Pcan.le M ((8 : ℕ) : Tensor K 3) := by
      have h := MM_le_mul (K := K) 2 2 2
      have h8 : ((2 : ℕ) : Tensor K 3) * ((2 : ℕ) : Tensor K 3) * ((2 : ℕ) : Tensor K 3) =
          ((8 : ℕ) : Tensor K 3) := by push_cast; ring
      rw [show (M : Tensor K 3) = MM 2 2 2 from hM, ← h8]
      convert h using 0
    have hrank_8 : ∀ n : ℕ, StrassenPreorder.rank Pcan ((n : Tensor K 3)) ≤ n := by
      intro n
      classical
      apply Nat.find_min'
      exact Pcan.le_refl _
    have hrank_M_le_8 : StrassenPreorder.rank Pcan M ≤ 8 := by
      calc StrassenPreorder.rank Pcan M
          ≤ StrassenPreorder.rank Pcan ((8 : ℕ) : Tensor K 3) :=
            StrassenPreorder.rank_monotone _ _ _ hM_le_8
        _ ≤ 8 := hrank_8 8
    have hrank_pow : ∀ k : ℕ, StrassenPreorder.rank Pcan (M ^ k) ≤ 8 ^ k := by
      intro k
      induction k with
      | zero => simp [StrassenPreorder.rank_one]
      | succ k ih =>
        rw [pow_succ, pow_succ]
        calc StrassenPreorder.rank Pcan (M ^ k * M)
            ≤ StrassenPreorder.rank Pcan (M ^ k) * StrassenPreorder.rank Pcan M :=
              StrassenPreorder.rank_submultiplicative _ _ _
          _ ≤ 8 ^ k * 8 := Nat.mul_le_mul ih hrank_M_le_8
    have h_eventually_le_8 : ∀ᶠ k : ℕ in Filter.atTop,
        (StrassenPreorder.rank Pcan (M ^ k) : ℝ) ^ (1 / (k : ℝ)) ≤ 8 := by
      filter_upwards [Filter.eventually_ge_atTop 1] with k hk
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
      have h1 : ((StrassenPreorder.rank Pcan (M ^ k)) : ℝ) ≤ ((8 ^ k : ℕ) : ℝ) := by
        exact_mod_cast hrank_pow k
      have h_nonneg : (0 : ℝ) ≤ (StrassenPreorder.rank Pcan (M ^ k) : ℝ) :=
        Nat.cast_nonneg _
      have h_step : (StrassenPreorder.rank Pcan (M ^ k) : ℝ) ^ (1 / (k : ℝ)) ≤
          ((8 ^ k : ℕ) : ℝ) ^ (1 / (k : ℝ)) :=
        Real.rpow_le_rpow h_nonneg h1 (by positivity)
      have h_8k : ((8 ^ k : ℕ) : ℝ) = (8 : ℝ) ^ k := by push_cast; rfl
      rw [h_8k] at h_step
      have h_8_pos : (0 : ℝ) < 8 := by norm_num
      have : (8 : ℝ) ^ k = (8 : ℝ) ^ (k : ℝ) := by
        rw [Real.rpow_natCast]
      rw [this] at h_step
      rw [← Real.rpow_mul (le_of_lt h_8_pos)] at h_step
      have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
      have h_kk : (k : ℝ) * (1 / (k : ℝ)) = 1 := by field_simp
      rw [h_kk, Real.rpow_one] at h_step
      exact h_step
    have hAR_le_8 : StrassenPreorder.asymptotic_rank Pcan M ≤ 8 := by
      have hAR_tend' : Filter.Tendsto
          (fun k : ℕ => (StrassenPreorder.rank Pcan (M ^ k) : ℝ) ^ (1 / (k : ℝ)))
          Filter.atTop (nhds (StrassenPreorder.asymptotic_rank Pcan M)) := hAR_tend
      exact le_of_tendsto_of_tendsto hAR_tend' tendsto_const_nhds h_eventually_le_8
    have hAR_pos : 0 < StrassenPreorder.asymptotic_rank Pcan M := by
      have h_eventually : ∀ᶠ k : ℕ in Filter.atTop,
          (1 : ℝ) ≤ (StrassenPreorder.rank Pcan (M ^ k) : ℝ) ^ (1 / (k : ℝ)) := by
        filter_upwards [Filter.eventually_ge_atTop 1] with k hk
        have hMk_ne : M ^ k ≠ 0 := Pcan.pow_ne_zero _ hM_ne
        have hrk : (1 : ℝ) ≤ (StrassenPreorder.rank Pcan (M ^ k) : ℝ) := by
          rcases Pcan.lower_archimedean (M ^ k) with h | h
          · exact absurd h hMk_ne
          · have := StrassenPreorder.rank_monotone Pcan 1 (M ^ k) h
            rw [StrassenPreorder.rank_one] at this
            exact_mod_cast this
        have hk' : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
        calc (1 : ℝ) = (1 : ℝ) ^ (1 / (k : ℝ)) := by rw [Real.one_rpow]
          _ ≤ _ := Real.rpow_le_rpow (by norm_num) hrk hk'
      linarith [ge_of_tendsto hAR_tend h_eventually]
    have h_log_le : Real.log (StrassenPreorder.asymptotic_rank Pcan M) ≤ Real.log 8 :=
      Real.log_le_log hAR_pos hAR_le_8
    have h_log8 : Real.log 8 = 3 * Real.log 2 := by
      have : (8 : ℝ) = 2 ^ 3 := by norm_num
      rw [this, Real.log_pow]
      ring
    rw [h_log8] at h_log_le
    rw [div_le_iff₀ hlog2_pos]
    linarith

/-- Canonical normalization: `ω = log_2 AR(MM 2 2 2)`. -/
theorem matMulExp_eq_log_AR_222 :
    matMulExp (K := K) =
      Real.log (StrassenPreorder.asymptotic_rank Tensor.instStrassenPreorder
        (MM (K := K) 2 2 2)) / Real.log 2 :=
  le_antisymm matMulExp_le_log_AR_222 log_AR_222_le_matMulExp

/-- The canonical Strassen preorder trivially refines itself. -/
private lemma refinesCanonical_self : RefinesCanonical (Tensor.instStrassenPreorder (K := K)) :=
  fun {_ _} h => h

/-- `ω` equals the supremum of `θ₁ + θ₂ + θ₃` over the spectrum of the canonical
    Strassen preorder on `Tensor K 3` (Strassen duality). -/
theorem matMulExp_eq_sup_specMM :
    matMulExp (K := K) =
      ⨆ φ : AsymptoticSpectrumPoint (Tensor K 3) Tensor.instStrassenPreorder,
        θ₁ Tensor.instStrassenPreorder φ +
        θ₂ Tensor.instStrassenPreorder φ +
        θ₃ Tensor.instStrassenPreorder φ := by
  set Pcan : StrassenPreorder (Tensor K 3) := Tensor.instStrassenPreorder with hPcan
  set M : Tensor K 3 := MM (K := K) 2 2 2 with hM
  have hP_refines : RefinesCanonical Pcan := refinesCanonical_self
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  rw [matMulExp_eq_log_AR_222]
  rw [StrassenPreorder.asymptotic_rank_eq_max_spectrum Pcan M]
  set S : AsymptoticSpectrumPoint (Tensor K 3) Pcan → ℝ :=
    fun φ => θ₁ Pcan φ + θ₂ Pcan φ + θ₃ Pcan φ with hS
  have h_eval : ∀ φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan,
      φ M = (2 : ℝ) ^ S φ := by
    intro φ
    have h := MM_eval Pcan hP_refines φ (n := 2) (m := 2) (p := 2)
      (by norm_num) (by norm_num) (by norm_num)
    rw [hM, h, hS]
    simp only []
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [hcast]
    rw [← Real.rpow_add h2pos, ← Real.rpow_add h2pos]
  haveI : Nonempty (AsymptoticSpectrumPoint (Tensor K 3) Pcan) := inferInstance
  have h_compact : IsCompact (Set.univ : Set (AsymptoticSpectrumPoint (Tensor K 3) Pcan)) :=
    isCompact_univ
  have h_cont_S : Continuous S := by
    have h_cont_eval₁ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan =>
        φ (MM (K := K) 2 1 1)) := continuous_eval Pcan _
    have h_cont_eval₂ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan =>
        φ (MM (K := K) 1 2 1)) := continuous_eval Pcan _
    have h_cont_eval₃ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan =>
        φ (MM (K := K) 1 1 2)) := continuous_eval Pcan _
    have hθ₁ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan => θ₁ Pcan φ) := by
      unfold θ₁
      refine Continuous.div_const ?_ _
      exact (Real.continuousOn_log.comp_continuous h_cont_eval₁
        (fun φ => ne_of_gt
          (phi_MM_pos Pcan hP_refines φ (by norm_num) (by norm_num) (by norm_num))))
    have hθ₂ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan => θ₂ Pcan φ) := by
      unfold θ₂
      refine Continuous.div_const ?_ _
      exact (Real.continuousOn_log.comp_continuous h_cont_eval₂
        (fun φ => ne_of_gt
          (phi_MM_pos Pcan hP_refines φ (by norm_num) (by norm_num) (by norm_num))))
    have hθ₃ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan => θ₃ Pcan φ) := by
      unfold θ₃
      refine Continuous.div_const ?_ _
      exact (Real.continuousOn_log.comp_continuous h_cont_eval₃
        (fun φ => ne_of_gt
          (phi_MM_pos Pcan hP_refines φ (by norm_num) (by norm_num) (by norm_num))))
    exact (hθ₁.add hθ₂).add hθ₃
  obtain ⟨φ_max, -, hmax⟩ := h_compact.exists_isMaxOn Set.univ_nonempty h_cont_S.continuousOn
  have h_supS : ⨆ φ, S φ = S φ_max := by
    apply le_antisymm
    · refine ciSup_le ?_
      intro φ
      exact hmax (Set.mem_univ φ)
    · exact le_ciSup (f := S)
        ⟨S φ_max, fun y ⟨φ, hφ⟩ => hφ ▸ hmax (Set.mem_univ φ)⟩ φ_max
  have h_supφM : ⨆ φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan, φ M = (2 : ℝ) ^ S φ_max := by
    apply le_antisymm
    · refine ciSup_le ?_
      intro φ
      rw [h_eval φ]
      exact Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2) |>.mpr
        (hmax (Set.mem_univ φ))
    · rw [← h_eval φ_max]
      refine le_ciSup (f := fun φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan => φ M) ?_ φ_max
      refine ⟨(2 : ℝ) ^ S φ_max, ?_⟩
      rintro _ ⟨φ, rfl⟩
      show φ M ≤ (2 : ℝ) ^ S φ_max
      rw [h_eval φ]
      exact Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2) |>.mpr
        (hmax (Set.mem_univ φ))
  rw [h_supφM, h_supS]
  rw [Real.log_rpow (by norm_num : (0:ℝ) < 2)]
  field_simp

/-! ## Mode permutations for MM -/

/-- The cyclic permutation of `Fin 3`: `0 ↦ 1 ↦ 2 ↦ 0`.
    Defined via explicit match so that `cyclicPerm.symm` reduces definitionally on each case. -/
def cyclicPerm : Equiv.Perm (Fin 3) where
  toFun
    | ⟨0, _⟩ => ⟨1, by norm_num⟩
    | ⟨1, _⟩ => ⟨2, by norm_num⟩
    | ⟨2, _⟩ => ⟨0, by norm_num⟩
    | ⟨n + 3, h⟩ => absurd h (by omega)
  invFun
    | ⟨0, _⟩ => ⟨2, by norm_num⟩
    | ⟨1, _⟩ => ⟨0, by norm_num⟩
    | ⟨2, _⟩ => ⟨1, by norm_num⟩
    | ⟨n + 3, h⟩ => absurd h (by omega)
  left_inv := by decide
  right_inv := by decide

/-- The transposition of modes 0 and 1 in `Fin 3`. -/
noncomputable def transpPerm : Equiv.Perm (Fin 3) :=
  Equiv.swap ⟨0, by norm_num⟩ ⟨1, by norm_num⟩

/-- Cyclic permutation of modes sends `MMObj n m p` to `MMObj p n m`
    (up to isomorphism via the canonical mode-space bijections, which are identities). -/
theorem MMObj_permuteSpaces_cyclic (n m p : ℕ) :
    TensorObj.Isomorphic
      ((MMObj (K := K) n m p).permuteSpaces cyclicPerm)
      (MMObj (K := K) p n m) := by
  apply Nonempty.intro
  let fwd : ∀ s : Fin 3,
      (TensorObj.permuteSpaces cyclicPerm (MMObj (K := K) n m p)).V s →ₗ[K]
      (MMObj (K := K) p n m).V s := fun ⟨s, hs⟩ => by
    match s, hs with
    | 0, _ => change (Fin p × Fin n → K) →ₗ[K] (Fin p × Fin n → K); exact LinearMap.id
    | 1, _ => change (Fin n × Fin m → K) →ₗ[K] (Fin n × Fin m → K); exact LinearMap.id
    | 2, _ => change (Fin m × Fin p → K) →ₗ[K] (Fin m × Fin p → K); exact LinearMap.id
    | s + 3, h => exact absurd h (by omega)
  let bwd : ∀ s : Fin 3,
      (MMObj (K := K) p n m).V s →ₗ[K]
      (TensorObj.permuteSpaces cyclicPerm (MMObj (K := K) n m p)).V s := fun ⟨s, hs⟩ => by
    match s, hs with
    | 0, _ => change (Fin p × Fin n → K) →ₗ[K] (Fin p × Fin n → K); exact LinearMap.id
    | 1, _ => change (Fin n × Fin m → K) →ₗ[K] (Fin n × Fin m → K); exact LinearMap.id
    | 2, _ => change (Fin m × Fin p → K) →ₗ[K] (Fin m × Fin p → K); exact LinearMap.id
    | s + 3, h => exact absurd h (by omega)
  refine ⟨fun s => LinearEquiv.ofLinear (fwd s) (bwd s) ?_ ?_, ?_⟩
  · obtain ⟨s, hs⟩ := s
    match s, hs with
    | 0, _ => apply LinearMap.ext; intro f; simp only [fwd, bwd]; rfl
    | 1, _ => apply LinearMap.ext; intro f; simp only [fwd, bwd]; rfl
    | 2, _ => apply LinearMap.ext; intro f; simp only [fwd, bwd]; rfl
    | s + 3, h => exact absurd h (by omega)
  · obtain ⟨s, hs⟩ := s
    match s, hs with
    | 0, _ => apply LinearMap.ext; intro f; simp only [fwd, bwd]; rfl
    | 1, _ => apply LinearMap.ext; intro f; simp only [fwd, bwd]; rfl
    | 2, _ => apply LinearMap.ext; intro f; simp only [fwd, bwd]; rfl
    | s + 3, h => exact absurd h (by omega)
  · -- map_t: liftMap fwd (reindex cyclicPerm MMObj.t) = (MMObj p n m).t
    simp only [TensorObj.permuteSpaces, MMObj, map_sum, MMPureTensor, PiTensorProduct.reindex_tprod]
    simp_rw [liftMap_tprod, LinearEquiv.ofLinear_toLinearMap]
    simp only [fwd, cyclicPerm]
    -- LHS sums (Fin n, Fin m, Fin p) with tprod arms (slot 0: (x_2, x), slot 1: (x, x_1), slot 2: (x_1, x_2)).
    -- RHS sums (Fin p, Fin n, Fin m) with arms (slot 0: (X, X_1), slot 1: (X_1, X_2), slot 2: (X_2, X)).
    -- Reorder RHS: move outer Fin p inside via two sum_comm swaps.
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs => enter [2, X_1]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x_1 _ => Finset.sum_congr rfl fun x_2 _ => ?_
    congr 1; ext ⟨s, hs⟩; match s, hs with
      | 0, _ =>
          change (LinearMap.id : (Fin p × Fin n → K) →ₗ[K] _) (Pi.single (x_2, x) 1) = Pi.single (x_2, x) 1
          rfl
      | 1, _ =>
          change (LinearMap.id : (Fin n × Fin m → K) →ₗ[K] _) (Pi.single (x, x_1) 1) = Pi.single (x, x_1) 1
          rfl
      | 2, _ =>
          change (LinearMap.id : (Fin m × Fin p → K) →ₗ[K] _) (Pi.single (x_1, x_2) 1) = Pi.single (x_1, x_2) 1
          rfl
      | s + 3, h => exact absurd h (by omega)

/-- Transposing modes 0 and 1 sends `MMObj n m p` to `MMObj p m n`
    (up to isomorphism, via pair-swap `[A×B→K] ≃ [B×A→K]` on each mode). -/
theorem MMObj_permuteSpaces_transp (n m p : ℕ) :
    TensorObj.Isomorphic
      ((MMObj (K := K) n m p).permuteSpaces transpPerm)
      (MMObj (K := K) p m n) := by
  -- permuteSpaces transpPerm (MMObj n m p) modes (transpPerm.symm = transpPerm, 0↔1, 2 fixed):
  --   mode 0 ← MMSpace n m p 1 = Fin m × Fin p → K   →  MMObj p m n mode 0 = Fin p × Fin m → K
  --   mode 1 ← MMSpace n m p 0 = Fin n × Fin m → K   →  MMObj p m n mode 1 = Fin m × Fin n → K
  --   mode 2 ← MMSpace n m p 2 = Fin p × Fin n → K   →  MMObj p m n mode 2 = Fin n × Fin p → K
  apply Nonempty.intro
  have hL : ∀ (s : Fin 3),
      (TensorObj.permuteSpaces transpPerm (MMObj (K := K) n m p)).V s =
      (MMObj (K := K) n m p).V (transpPerm.symm s) := fun s => rfl
  let swap_lm : ∀ (α β : Type 0), (α × β → K) →ₗ[K] (β × α → K) := fun α β =>
    { toFun := fun f p => f p.swap
      map_add' := fun f g => by ext; rfl
      map_smul' := fun c f => by ext; rfl }
  let fwd : ∀ s : Fin 3,
      (TensorObj.permuteSpaces transpPerm (MMObj (K := K) n m p)).V s →ₗ[K]
      (MMObj (K := K) p m n).V s := fun ⟨s, hs⟩ => by
    match s, hs with
    | 0, _ => change (Fin m × Fin p → K) →ₗ[K] (Fin p × Fin m → K); exact swap_lm _ _
    | 1, _ => change (Fin n × Fin m → K) →ₗ[K] (Fin m × Fin n → K); exact swap_lm _ _
    | 2, _ => change (Fin p × Fin n → K) →ₗ[K] (Fin n × Fin p → K); exact swap_lm _ _
    | s + 3, h => exact absurd h (by omega)
  let bwd : ∀ s : Fin 3,
      (MMObj (K := K) p m n).V s →ₗ[K]
      (TensorObj.permuteSpaces transpPerm (MMObj (K := K) n m p)).V s := fun ⟨s, hs⟩ => by
    match s, hs with
    | 0, _ => change (Fin p × Fin m → K) →ₗ[K] (Fin m × Fin p → K); exact swap_lm _ _
    | 1, _ => change (Fin m × Fin n → K) →ₗ[K] (Fin n × Fin m → K); exact swap_lm _ _
    | 2, _ => change (Fin n × Fin p → K) →ₗ[K] (Fin p × Fin n → K); exact swap_lm _ _
    | s + 3, h => exact absurd h (by omega)
  refine ⟨fun s => LinearEquiv.ofLinear (fwd s) (bwd s) ?_ ?_, ?_⟩
  · -- fwd s ∘ bwd s = id for each s : Fin 3
    obtain ⟨s, hs⟩ := s
    match s, hs with
    | 0, _ =>
        apply LinearMap.ext; intro f; ext ⟨a, b⟩
        simp only [fwd, bwd, LinearMap.coe_comp, Function.comp, swap_lm, LinearMap.id_apply]; rfl
    | 1, _ =>
        apply LinearMap.ext; intro f; ext ⟨a, b⟩
        simp only [fwd, bwd, LinearMap.coe_comp, Function.comp, swap_lm, LinearMap.id_apply]; rfl
    | 2, _ =>
        apply LinearMap.ext; intro f; ext ⟨a, b⟩
        simp only [fwd, bwd, LinearMap.coe_comp, Function.comp, swap_lm, LinearMap.id_apply]; rfl
    | s + 3, h => exact absurd h (by omega)
  · -- bwd s ∘ fwd s = id for each s : Fin 3
    obtain ⟨s, hs⟩ := s
    match s, hs with
    | 0, _ =>
        apply LinearMap.ext; intro f
        change swap_lm _ _ (swap_lm _ _ f) = f; ext ⟨a, b⟩; simp [swap_lm]
    | 1, _ =>
        apply LinearMap.ext; intro f
        change swap_lm _ _ (swap_lm _ _ f) = f; ext ⟨a, b⟩; simp [swap_lm]
    | 2, _ =>
        apply LinearMap.ext; intro f
        change swap_lm _ _ (swap_lm _ _ f) = f; ext ⟨a, b⟩; simp [swap_lm]
    | s + 3, h => exact absurd h (by omega)
  · -- map_t: liftMap fwd (reindex transpPerm MMObj.t) = (MMObj p m n).t
    simp only [TensorObj.permuteSpaces, MMObj, map_sum, MMPureTensor, PiTensorProduct.reindex_tprod]
    simp_rw [liftMap_tprod, LinearEquiv.ofLinear_toLinearMap]
    simp only [fwd, transpPerm, swap_lm]
    -- Reindex: (x_n, x_m, x_p) ↦ (x_p, x_m, x_n) via three sum_comm applications
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    conv_lhs => arg 2; ext y; rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    -- Now LHS and RHS have same summation order; simplify the tprod bodies
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x_1 _ => Finset.sum_congr rfl fun x_2 _ => ?_
    congr 1; ext ⟨s, hs⟩; match s, hs with
      | 0, _ =>
          change swap_lm _ _ (Pi.single (x_1, x) 1) = Pi.single (x, x_1) 1
          ext ⟨a, b⟩; simp [swap_lm, Pi.single_apply, Prod.swap, and_comm]
      | 1, _ =>
          change swap_lm _ _ (Pi.single (x_2, x_1) 1) = Pi.single (x_1, x_2) 1
          ext ⟨a, b⟩; simp [swap_lm, Pi.single_apply, Prod.swap, and_comm]
      | 2, _ =>
          change swap_lm _ _ (Pi.single (x, x_2) 1) = Pi.single (x_2, x) 1
          ext ⟨a, b⟩; simp [swap_lm, Pi.single_apply, Prod.swap, and_comm]
      | s + 3, h => exact absurd h (by omega)

/-- Hypothesis: `P` is monotone under `permuteSpaces σ`. Holds tautologically for the
    canonical `Restrict`-based preorder via `Tensor.permuteSpaces_mono`, but in general a
    user-supplied `P` need not respect mode permutations, so we require this as a hypothesis
    rather than deriving it from `RefinesCanonical`. -/
abbrev PermMono : Prop :=
  ∀ (σ : Equiv.Perm (Fin 3)) (a b : Tensor K 3),
    P.le a b → P.le (Tensor.permuteSpaces σ a) (Tensor.permuteSpaces σ b)

/-- Extract per-σ monotonicity from `PermMono P`. -/
private def permMono (hP : PermMono P) (σ : Equiv.Perm (Fin 3)) :
    ∀ a b : Tensor K 3, P.le a b → P.le (Tensor.permuteSpaces σ a) (Tensor.permuteSpaces σ b) :=
  hP σ

/-- Quotient-level cyclic permutation: `permuteSpaces cyclicPerm (MM n m p) = MM p n m`. -/
theorem MM_permuteSpaces_cyclic (n m p : ℕ) :
    Tensor.permuteSpaces cyclicPerm (MM (K := K) n m p) = MM (K := K) p n m := by
  show toTensor ((MMObj (K := K) n m p).permuteSpaces cyclicPerm) = toTensor (MMObj (K := K) p n m)
  exact Quotient.sound (TensorObj.isomorphic_restrict_equiv (MMObj_permuteSpaces_cyclic n m p))

/-- Quotient-level transposition: `permuteSpaces transpPerm (MM n m p) = MM p m n`. -/
theorem MM_permuteSpaces_transp (n m p : ℕ) :
    Tensor.permuteSpaces transpPerm (MM (K := K) n m p) = MM (K := K) p m n := by
  show toTensor ((MMObj (K := K) n m p).permuteSpaces transpPerm) = toTensor (MMObj (K := K) p m n)
  exact Quotient.sound (TensorObj.isomorphic_restrict_equiv (MMObj_permuteSpaces_transp n m p))

/-- Cyclic permutation acts on θ: `θ₁(φ^c) = θ₃(φ)`, `θ₂(φ^c) = θ₁(φ)`, `θ₃(φ^c) = θ₂(φ)`.

    Note: `(φ.perm cyclicPerm) (MM 2 1 1) = φ (permuteSpaces cyclicPerm (MM 2 1 1)) = φ (MM 1 2 1)`,
    so `θ₁(φ^c) = log φ(MM 1 2 1)/log 2 = θ₂(φ)`. -/
theorem θ_perm_cyclic (hP : PermMono P) (φ : AsymptoticSpectrumPoint (Tensor K 3) P) :
    θ₁ P (φ.perm P cyclicPerm (permMono P hP cyclicPerm)) = θ₂ P φ ∧
    θ₂ P (φ.perm P cyclicPerm (permMono P hP cyclicPerm)) = θ₃ P φ ∧
    θ₃ P (φ.perm P cyclicPerm (permMono P hP cyclicPerm)) = θ₁ P φ := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp only [θ₁, θ₂, θ₃, AsymptoticSpectrumPoint.perm_apply, MM_permuteSpaces_cyclic]

/-- Transposition (swap of modes 0,1) acts on θ:
    `θ₁(φ^t) = θ₃(φ)`, `θ₂(φ^t) = θ₂(φ)`, `θ₃(φ^t) = θ₁(φ)`.

    Since `permuteSpaces transpPerm (MM n m p) = MM p m n`,
    `(φ^t)(MM 2 1 1) = φ(MM 1 1 2)`, giving `θ₁(φ^t) = θ₃(φ)`. -/
theorem θ_perm_transp (hP : PermMono P) (φ : AsymptoticSpectrumPoint (Tensor K 3) P) :
    θ₁ P (φ.perm P transpPerm (permMono P hP transpPerm)) = θ₃ P φ ∧
    θ₂ P (φ.perm P transpPerm (permMono P hP transpPerm)) = θ₂ P φ ∧
    θ₃ P (φ.perm P transpPerm (permMono P hP transpPerm)) = θ₁ P φ := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp only [θ₁, θ₂, θ₃, AsymptoticSpectrumPoint.perm_apply, MM_permuteSpaces_transp]

/-- `specMM` is invariant under cyclic permutation of coordinates. -/
theorem specMM_perm_cyclic (hP : PermMono P) (θ : ℝ × ℝ × ℝ) (h : θ ∈ specMM P) :
    (θ.2.1, θ.2.2, θ.1) ∈ specMM P := by
  obtain ⟨φ, -, rfl⟩ := h
  refine ⟨φ.perm P cyclicPerm (permMono P hP cyclicPerm), Set.mem_univ _, ?_⟩
  obtain ⟨h1, h2, h3⟩ := θ_perm_cyclic P hP φ
  simp only [h1, h2, h3]

/-- `specMM` is invariant under swap of the first and last coordinates
    (induced by transposing modes 0 and 1 of the tensor). -/
theorem specMM_perm_transp (hP : PermMono P) (θ : ℝ × ℝ × ℝ) (h : θ ∈ specMM P) :
    (θ.2.2, θ.2.1, θ.1) ∈ specMM P := by
  obtain ⟨φ, -, rfl⟩ := h
  refine ⟨φ.perm P transpPerm (permMono P hP transpPerm), Set.mem_univ _, ?_⟩
  obtain ⟨h1, h2, h3⟩ := θ_perm_transp P hP φ
  simp only [h1, h2, h3]

/-- Apply a permutation of `Fin 3` to a triple `(ℝ × ℝ × ℝ)`, viewed as a function `Fin 3 → ℝ`. -/
noncomputable def permuteTriple (σ : Equiv.Perm (Fin 3)) (θ : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let f : Fin 3 → ℝ := ![θ.1, θ.2.1, θ.2.2]
  (f (σ.symm ⟨0, by norm_num⟩), f (σ.symm ⟨1, by norm_num⟩), f (σ.symm ⟨2, by norm_num⟩))

/-- The 6 elements of `S₃` enumerated by their action on `(0, 1)`. -/
private lemma S₃_enumerate (σ : Equiv.Perm (Fin 3)) :
    σ = Equiv.refl _ ∨
    σ = transpPerm ∨
    σ = cyclicPerm ∨
    σ = cyclicPerm * cyclicPerm ∨
    σ = cyclicPerm * transpPerm ∨
    σ = transpPerm * cyclicPerm := by
  fin_cases σ <;> decide

/-- `specMM` is invariant under all permutations of the three coordinates.
    Follows from `specMM_perm_cyclic`, `specMM_perm_transp`, and the fact that S₃ is
    generated by `cyclicPerm` and `transpPerm`. -/
theorem specMM_perm (hP : PermMono P) (σ : Equiv.Perm (Fin 3))
    (θ : ℝ × ℝ × ℝ) (h : θ ∈ specMM P) :
    permuteTriple σ θ ∈ specMM P := by
  obtain ⟨a, b, c⟩ := θ
  rcases S₃_enumerate σ with h_id | h_t | h_c | h_c2 | h_ct | h_tc
  · subst h_id; convert h using 1
  · subst h_t
    have h1 := specMM_perm_transp P hP (a, b, c) h
    have h2 := specMM_perm_cyclic P hP (c, b, a) h1
    convert h2 using 1
  · subst h_c
    have h1 := specMM_perm_cyclic P hP (a, b, c) h
    have h2 := specMM_perm_cyclic P hP (b, c, a) h1
    convert h2 using 1
  · subst h_c2
    have h1 := specMM_perm_cyclic P hP (a, b, c) h
    convert h1 using 1
  · subst h_ct
    have h1 := specMM_perm_transp P hP (a, b, c) h
    convert h1 using 1
  · subst h_tc
    have h1 := specMM_perm_cyclic P hP (a, b, c) h
    have h2 := specMM_perm_transp P hP (b, c, a) h1
    convert h2 using 1

/-! ## Asymptotic Sum Inequality -/

/-- The function `F(x,y,z) = ∑ i, nᵢˣ · mᵢʸ · pᵢᶻ` is convex on `ℝ³`. -/
theorem sum_rpow_convex {ι : Type*} [Fintype ι]
    (n m p : ι → ℝ) (hn : ∀ i, 0 < n i) (hm : ∀ i, 0 < m i) (hp : ∀ i, 0 < p i) :
    ConvexOn ℝ Set.univ (fun v : ℝ × ℝ × ℝ =>
      ∑ i, (n i) ^ v.1 * (m i) ^ v.2.1 * (p i) ^ v.2.2) := by
  -- Each summand `gᵢ(v) = exp(v.1 · log nᵢ + v.2.1 · log mᵢ + v.2.2 · log pᵢ)`
  -- is convex (composition of `exp` with a linear/affine map). The sum of convex
  -- functions is convex.
  -- For each i, define the linear functional Lᵢ : ℝ³ → ℝ.
  let L : ι → (ℝ × ℝ × ℝ →ₗ[ℝ] ℝ) := fun i =>
    { toFun := fun v => v.1 * Real.log (n i) + v.2.1 * Real.log (m i) +
        v.2.2 * Real.log (p i)
      map_add' := by intros; simp; ring
      map_smul' := by intros; simp; ring }
  have hg_eq : ∀ i (v : ℝ × ℝ × ℝ),
      (n i) ^ v.1 * (m i) ^ v.2.1 * (p i) ^ v.2.2 = Real.exp (L i v) := by
    intro i v
    show (n i) ^ v.1 * (m i) ^ v.2.1 * (p i) ^ v.2.2 =
      Real.exp (v.1 * Real.log (n i) + v.2.1 * Real.log (m i) + v.2.2 * Real.log (p i))
    rw [Real.rpow_def_of_pos (hn i), Real.rpow_def_of_pos (hm i),
        Real.rpow_def_of_pos (hp i)]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hg_convex : ∀ i, ConvexOn ℝ Set.univ (fun v : ℝ × ℝ × ℝ =>
      (n i) ^ v.1 * (m i) ^ v.2.1 * (p i) ^ v.2.2) := by
    intro i
    -- f = exp ∘ Lᵢ.
    have h_comp : ConvexOn ℝ ((L i) ⁻¹' Set.univ) (Real.exp ∘ (L i)) :=
      convexOn_exp.comp_linearMap (L i)
    have : (L i) ⁻¹' (Set.univ : Set ℝ) = Set.univ := by
      ext x; simp
    rw [this] at h_comp
    convert h_comp using 1
    ext v
    exact hg_eq i v
  -- Sum of convex functions is convex (induction over Finset.univ).
  have h_sum : ∀ s : Finset ι, ConvexOn ℝ Set.univ (fun v : ℝ × ℝ × ℝ =>
      ∑ i ∈ s, (n i) ^ v.1 * (m i) ^ v.2.1 * (p i) ^ v.2.2) := by
    intro s
    induction s using Finset.cons_induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact convexOn_const _ convex_univ
    | cons _ _ hni ih =>
      simp only [Finset.sum_cons]
      exact (hg_convex _).add ih
  exact h_sum Finset.univ

/-- Jensen's inequality applied over the S₃-orbit:
    if `f` is convex and `f(permuteTriple σ θ) ≤ r` for all `σ ∈ S₃`,
    then `f` at the barycenter of the orbit is also `≤ r`.
    The barycenter of the S₃-orbit of `(a, b, c)` has all three coordinates equal to `(a+b+c)/3`. -/
theorem jensen_S3_convex {f : ℝ × ℝ × ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (θ : ℝ × ℝ × ℝ)
    (r : ℝ) (hσ : ∀ σ ∈ ({Equiv.refl _, cyclicPerm, cyclicPerm * cyclicPerm} :
        Set (Equiv.Perm (Fin 3))), f (permuteTriple σ θ) ≤ r) :
    f ((θ.1 + θ.2.1 + θ.2.2) / 3, (θ.1 + θ.2.1 + θ.2.2) / 3,
       (θ.1 + θ.2.1 + θ.2.2) / 3) ≤ r := by
  -- Use 3 cyclic permutations: id, cyclic, cyclic² which give (a,b,c), (c,a,b), (b,c,a).
  -- Their average is ((a+b+c)/3, (a+b+c)/3, (a+b+c)/3).
  set a := θ.1
  set b := θ.2.1
  set c := θ.2.2
  -- Concretize the 3 permuted triples.
  have h_id : permuteTriple (Equiv.refl _) θ = (a, b, c) := by
    show (![θ.1, θ.2.1, θ.2.2] ((Equiv.refl (Fin 3)).symm ⟨0, _⟩),
          ![θ.1, θ.2.1, θ.2.2] ((Equiv.refl (Fin 3)).symm ⟨1, _⟩),
          ![θ.1, θ.2.1, θ.2.2] ((Equiv.refl (Fin 3)).symm ⟨2, _⟩)) = (a, b, c)
    rfl
  have h_cyc : permuteTriple cyclicPerm θ = (c, a, b) := by
    show (![θ.1, θ.2.1, θ.2.2] (cyclicPerm.symm ⟨0, _⟩),
          ![θ.1, θ.2.1, θ.2.2] (cyclicPerm.symm ⟨1, _⟩),
          ![θ.1, θ.2.1, θ.2.2] (cyclicPerm.symm ⟨2, _⟩)) = (c, a, b)
    rfl
  have h_cyc2 : permuteTriple (cyclicPerm * cyclicPerm) θ = (b, c, a) := by
    show (![θ.1, θ.2.1, θ.2.2] ((cyclicPerm * cyclicPerm).symm ⟨0, _⟩),
          ![θ.1, θ.2.1, θ.2.2] ((cyclicPerm * cyclicPerm).symm ⟨1, _⟩),
          ![θ.1, θ.2.1, θ.2.2] ((cyclicPerm * cyclicPerm).symm ⟨2, _⟩)) = (b, c, a)
    rfl
  -- The bounds at these 3 triples.
  have h1 : f (a, b, c) ≤ r := h_id ▸ hσ (Equiv.refl _) (by simp)
  have h2 : f (c, a, b) ≤ r := h_cyc ▸ hσ cyclicPerm (by simp)
  have h3 : f (b, c, a) ≤ r := h_cyc2 ▸ hσ (cyclicPerm * cyclicPerm) (by simp)
  have h_avg_pt : ((a + b + c) / 3, (a + b + c) / 3, (a + b + c) / 3) =
      (1/3 : ℝ) • (a, b, c) + (1/3 : ℝ) • (c, a, b) + (1/3 : ℝ) • (b, c, a) := by
    show (((a + b + c) / 3 : ℝ), ((a + b + c) / 3 : ℝ), ((a + b + c) / 3 : ℝ)) = _
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩⟩ <;> ring
  rw [h_avg_pt]
  have h13 : (0 : ℝ) ≤ 1/3 := by norm_num
  have h12 : (1/3 : ℝ) • (a, b, c) + (1/3 : ℝ) • (c, a, b) =
      (2/3 : ℝ) • ((1/2 : ℝ) • (a, b, c) + (1/2 : ℝ) • (c, a, b)) := by
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩⟩ <;> ring
  rw [h12]
  have hf_at_M : f ((1/2 : ℝ) • (a, b, c) + (1/2 : ℝ) • (c, a, b)) ≤ r := by
    have := hf.2 (Set.mem_univ (a, b, c)) (Set.mem_univ (c, a, b))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    calc f ((1/2 : ℝ) • (a, b, c) + (1/2 : ℝ) • (c, a, b))
        ≤ (1/2 : ℝ) • f (a, b, c) + (1/2 : ℝ) • f (c, a, b) := this
      _ ≤ (1/2 : ℝ) • r + (1/2 : ℝ) • r := by
          gcongr
      _ = r := by simp; ring
  have h_two_step :=
    hf.2 (Set.mem_univ ((1/2 : ℝ) • (a, b, c) + (1/2 : ℝ) • (c, a, b)))
      (Set.mem_univ (b, c, a))
      (by norm_num : (0:ℝ) ≤ 2/3) (by norm_num : (0:ℝ) ≤ 1/3)
      (by norm_num : (2/3 : ℝ) + 1/3 = 1)
  calc f ((2/3 : ℝ) • ((1/2 : ℝ) • (a, b, c) + (1/2 : ℝ) • (c, a, b)) + (1/3 : ℝ) • (b, c, a))
      ≤ (2/3 : ℝ) • f ((1/2 : ℝ) • (a, b, c) + (1/2 : ℝ) • (c, a, b)) + (1/3 : ℝ) • f (b, c, a) :=
        h_two_step
    _ ≤ (2/3 : ℝ) • r + (1/3 : ℝ) • r := by
        gcongr
    _ = r := by simp; ring

/-- **Asymptotic Sum Inequality** (variant of Schönhage's τ-theorem):
    If `AR(⊕ᵢ MM(nᵢ, mᵢ, pᵢ)) ≤ r` then `∑ᵢ (nᵢ · mᵢ · pᵢ)^{ω/3} ≤ r`.

    Proof sketch:
    1. By Strassen duality, for all spectrum points φ: `∑ᵢ φ(MM nᵢ mᵢ pᵢ) ≤ r`.
    2. By `MM_eval`: `∑ᵢ nᵢ^θ₁ · mᵢ^θ₂ · pᵢ^θ₃ ≤ r` for all (θ₁,θ₂,θ₃) ∈ specMM.
    3. By `specMM_perm`, the same holds for all 6 permutations of (θ₁,θ₂,θ₃).
    4. Averaging over S₃ and applying Jensen (the function is convex),
       `∑ᵢ (nᵢ mᵢ pᵢ)^{(θ₁+θ₂+θ₃)/3} ≤ r`.
    5. Taking sup over specMM: `(θ₁+θ₂+θ₃)/3 ≤ ω/3`, giving `∑ᵢ (nᵢ mᵢ pᵢ)^{ω/3} ≤ r`. -/
theorem asymptotic_sum_inequality
    {ι : Type*} [Fintype ι]
    (n m p : ι → ℕ)
    (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i) (hp : ∀ i, 1 ≤ p i)
    (r : ℕ)
    (h : StrassenPreorder.asymptotic_rank
        (Tensor.instStrassenPreorder (K := K)) (∑ i, MM (n i) (m i) (p i)) ≤ r) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (matMulExp (K := K) / 3) ≤ r := by
  set Pcan : StrassenPreorder (Tensor K 3) := Tensor.instStrassenPreorder with hPcan
  have hP_refines : RefinesCanonical Pcan := refinesCanonical_self
  have hP_perm : PermMono Pcan := fun σ a b hab => Tensor.permuteSpaces_mono σ hab
  have hspec : ∀ φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan,
      ∑ i, φ (MM (n i) (m i) (p i)) ≤ r := by
    intro φ
    have h_dual := StrassenPreorder.asymptotic_rank_eq_max_spectrum Pcan
      (∑ i, MM (n i) (m i) (p i))
    set a := ∑ i, MM (K := K) (n i) (m i) (p i) with ha_def
    obtain ⟨N, hN⟩ := Pcan.upper_archimedean a
    have hbdd : BddAbove (Set.range
        (fun ϕ : AsymptoticSpectrum (Tensor K 3) Pcan => ϕ a)) := by
      refine ⟨(N : ℝ), ?_⟩
      rintro _ ⟨ϕ, rfl⟩
      have := ϕ.monotone' hN
      rw [map_natCast] at this
      exact this
    have h_le_AR : φ (∑ i, MM (n i) (m i) (p i)) ≤
        StrassenPreorder.asymptotic_rank Pcan (∑ i, MM (n i) (m i) (p i)) := by
      rw [h_dual]; exact le_ciSup hbdd φ
    have hphi : φ (∑ i, MM (n i) (m i) (p i)) ≤ (r : ℝ) := le_trans h_le_AR (by exact_mod_cast h)
    rw [map_sum] at hphi
    exact hphi
  have htheta : ∀ φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan,
      ∑ i, (n i : ℝ) ^ θ₁ Pcan φ * (m i : ℝ) ^ θ₂ Pcan φ * (p i : ℝ) ^ θ₃ Pcan φ ≤ r := by
    intro φ
    have hsum := hspec φ
    have heq : ∀ i, φ (MM (n i) (m i) (p i)) =
        (n i : ℝ) ^ θ₁ Pcan φ * (m i : ℝ) ^ θ₂ Pcan φ * (p i : ℝ) ^ θ₃ Pcan φ :=
      fun i => MM_eval Pcan hP_refines φ (hn i) (hm i) (hp i)
    rw [show (∑ i, (n i : ℝ) ^ θ₁ Pcan φ * (m i : ℝ) ^ θ₂ Pcan φ * (p i : ℝ) ^ θ₃ Pcan φ) =
        ∑ i, φ (MM (n i) (m i) (p i)) from
      Finset.sum_congr rfl fun i _ => (heq i).symm]
    exact hsum
  have hn_pos : ∀ i, (0 : ℝ) < (n i : ℝ) := fun i => by
    have : (1 : ℝ) ≤ (n i : ℝ) := by exact_mod_cast hn i
    linarith
  have hm_pos : ∀ i, (0 : ℝ) < (m i : ℝ) := fun i => by
    have : (1 : ℝ) ≤ (m i : ℝ) := by exact_mod_cast hm i
    linarith
  have hp_pos : ∀ i, (0 : ℝ) < (p i : ℝ) := fun i => by
    have : (1 : ℝ) ≤ (p i : ℝ) := by exact_mod_cast hp i
    linarith
  set F : ℝ × ℝ × ℝ → ℝ :=
    fun v => ∑ i, (n i : ℝ) ^ v.1 * (m i : ℝ) ^ v.2.1 * (p i : ℝ) ^ v.2.2 with hF
  have hF_convex : ConvexOn ℝ Set.univ F :=
    sum_rpow_convex (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) (fun i => (p i : ℝ))
      hn_pos hm_pos hp_pos
  have hF_perm : ∀ φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan,
      ∀ σ ∈ ({Equiv.refl _, cyclicPerm, cyclicPerm * cyclicPerm} :
          Set (Equiv.Perm (Fin 3))),
        F (permuteTriple σ (θ₁ Pcan φ, θ₂ Pcan φ, θ₃ Pcan φ)) ≤ r := by
    intro φ σ hσ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rcases hσ with h_id | h_c | h_c2
    · subst h_id
      have h_pt : permuteTriple (Equiv.refl _) (θ₁ Pcan φ, θ₂ Pcan φ, θ₃ Pcan φ) =
          (θ₁ Pcan φ, θ₂ Pcan φ, θ₃ Pcan φ) := by
        show (![θ₁ Pcan φ, θ₂ Pcan φ, θ₃ Pcan φ] ((Equiv.refl (Fin 3)).symm ⟨0, _⟩),
              ![θ₁ Pcan φ, θ₂ Pcan φ, θ₃ Pcan φ] ((Equiv.refl (Fin 3)).symm ⟨1, _⟩),
              ![θ₁ Pcan φ, θ₂ Pcan φ, θ₃ Pcan φ] ((Equiv.refl (Fin 3)).symm ⟨2, _⟩)) = _
        rfl
      rw [h_pt]; exact htheta φ
    · subst h_c
      have h_pt : permuteTriple cyclicPerm (θ₁ Pcan φ, θ₂ Pcan φ, θ₃ Pcan φ) =
          (θ₃ Pcan φ, θ₁ Pcan φ, θ₂ Pcan φ) := by
        show (![θ₁ Pcan φ, θ₂ Pcan φ, θ₃ Pcan φ] (cyclicPerm.symm ⟨0, _⟩),
              ![θ₁ Pcan φ, θ₂ Pcan φ, θ₃ Pcan φ] (cyclicPerm.symm ⟨1, _⟩),
              ![θ₁ Pcan φ, θ₂ Pcan φ, θ₃ Pcan φ] (cyclicPerm.symm ⟨2, _⟩)) = _
        rfl
      rw [h_pt]
      let φ' := φ.perm Pcan cyclicPerm (permMono Pcan hP_perm cyclicPerm)
      let φ'' := φ'.perm Pcan cyclicPerm (permMono Pcan hP_perm cyclicPerm)
      have ⟨h1, h2, h3⟩ := θ_perm_cyclic Pcan hP_perm φ
      have ⟨k1, k2, k3⟩ := θ_perm_cyclic Pcan hP_perm φ'
      have hh := htheta φ''
      change ∑ i, (n i : ℝ) ^ θ₁ Pcan φ'' * (m i : ℝ) ^ θ₂ Pcan φ'' *
        (p i : ℝ) ^ θ₃ Pcan φ'' ≤ r at hh
      rw [k1, k2, k3, h1, h2, h3] at hh; exact hh
    · subst h_c2
      have h_pt : permuteTriple (cyclicPerm * cyclicPerm) (θ₁ Pcan φ, θ₂ Pcan φ, θ₃ Pcan φ) =
          (θ₂ Pcan φ, θ₃ Pcan φ, θ₁ Pcan φ) := by
        show (![θ₁ Pcan φ, θ₂ Pcan φ, θ₃ Pcan φ] ((cyclicPerm*cyclicPerm).symm ⟨0, _⟩),
              ![θ₁ Pcan φ, θ₂ Pcan φ, θ₃ Pcan φ] ((cyclicPerm*cyclicPerm).symm ⟨1, _⟩),
              ![θ₁ Pcan φ, θ₂ Pcan φ, θ₃ Pcan φ] ((cyclicPerm*cyclicPerm).symm ⟨2, _⟩)) = _
        rfl
      rw [h_pt]
      have ⟨h1, h2, h3⟩ := θ_perm_cyclic Pcan hP_perm φ
      have hh := htheta (φ.perm Pcan cyclicPerm (permMono Pcan hP_perm cyclicPerm))
      rw [h1, h2, h3] at hh; exact hh
  have h_avg : ∀ φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan,
      F ((θ₁ Pcan φ + θ₂ Pcan φ + θ₃ Pcan φ) / 3,
         (θ₁ Pcan φ + θ₂ Pcan φ + θ₃ Pcan φ) / 3,
         (θ₁ Pcan φ + θ₂ Pcan φ + θ₃ Pcan φ) / 3) ≤ r := by
    intro φ
    exact jensen_S3_convex hF_convex (θ₁ Pcan φ, θ₂ Pcan φ, θ₃ Pcan φ) r (hF_perm φ)
  rw [matMulExp_eq_sup_specMM]
  set S : AsymptoticSpectrumPoint (Tensor K 3) Pcan → ℝ :=
    fun φ => θ₁ Pcan φ + θ₂ Pcan φ + θ₃ Pcan φ with hS_def
  haveI : Nonempty (AsymptoticSpectrumPoint (Tensor K 3) Pcan) := inferInstance
  have h_compact : IsCompact (Set.univ : Set (AsymptoticSpectrumPoint (Tensor K 3) Pcan)) :=
    isCompact_univ
  have h_cont_S : Continuous S := by
    have h_cont_eval₁ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan =>
        φ (MM (K := K) 2 1 1)) := continuous_eval Pcan _
    have h_cont_eval₂ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan =>
        φ (MM (K := K) 1 2 1)) := continuous_eval Pcan _
    have h_cont_eval₃ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan =>
        φ (MM (K := K) 1 1 2)) := continuous_eval Pcan _
    have hθ₁ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan => θ₁ Pcan φ) := by
      unfold θ₁
      refine Continuous.div_const ?_ _
      exact (Real.continuousOn_log.comp_continuous h_cont_eval₁
        (fun φ => ne_of_gt
          (phi_MM_pos Pcan hP_refines φ (by norm_num) (by norm_num) (by norm_num))))
    have hθ₂ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan => θ₂ Pcan φ) := by
      unfold θ₂
      refine Continuous.div_const ?_ _
      exact (Real.continuousOn_log.comp_continuous h_cont_eval₂
        (fun φ => ne_of_gt
          (phi_MM_pos Pcan hP_refines φ (by norm_num) (by norm_num) (by norm_num))))
    have hθ₃ : Continuous (fun φ : AsymptoticSpectrumPoint (Tensor K 3) Pcan => θ₃ Pcan φ) := by
      unfold θ₃
      refine Continuous.div_const ?_ _
      exact (Real.continuousOn_log.comp_continuous h_cont_eval₃
        (fun φ => ne_of_gt
          (phi_MM_pos Pcan hP_refines φ (by norm_num) (by norm_num) (by norm_num))))
    exact (hθ₁.add hθ₂).add hθ₃
  obtain ⟨φ_max, -, hmax⟩ := h_compact.exists_isMaxOn Set.univ_nonempty h_cont_S.continuousOn
  have h_supS : ⨆ φ, S φ = S φ_max := by
    apply le_antisymm
    · refine ciSup_le ?_; intro φ; exact hmax (Set.mem_univ φ)
    · exact le_ciSup (f := S)
        ⟨S φ_max, fun y ⟨φ, hφ⟩ => hφ ▸ hmax (Set.mem_univ φ)⟩ φ_max
  rw [h_supS]
  have h_at_max := h_avg φ_max
  have h_eq : ∀ i, ((n i * m i * p i : ℕ) : ℝ) ^ (S φ_max / 3) =
      (n i : ℝ) ^ (S φ_max / 3) * (m i : ℝ) ^ (S φ_max / 3) * (p i : ℝ) ^ (S φ_max / 3) := by
    intro i
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (le_of_lt (hn_pos i)) (le_of_lt (hm_pos i))]
  calc ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^ (S φ_max / 3)
      = ∑ i, (n i : ℝ) ^ (S φ_max / 3) * (m i : ℝ) ^ (S φ_max / 3) *
          (p i : ℝ) ^ (S φ_max / 3) :=
        Finset.sum_congr rfl fun i _ => h_eq i
    _ = F ((S φ_max) / 3, (S φ_max) / 3, (S φ_max) / 3) := rfl
    _ ≤ r := h_at_max

end Tensor
