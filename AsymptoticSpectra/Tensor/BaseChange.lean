import AsymptoticSpectra.Tensor.Tensor

universe u v v' w

open BigOperators TensorProduct PiTensorProduct

namespace TensorObj

variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

section BaseChange

variable (L : Type w) [Field L] [Algebra K L]
variable {V : Fin d → Type v}
         [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- Helper: extension of scalars for PiTensorProduct elements involved in base change.
    Maps v₁ ⊗ ... ⊗ vₙ to (1 ⊗ v₁) ⊗ ... ⊗ (1 ⊗ vₙ) in the L-tensor product. -/
def scalarExtensionMap :
    PiTensorProduct K V →ₗ[K] PiTensorProduct L (fun i => L ⊗[K] V i) :=
  lift <| {
    toFun := fun v => tprod L (fun i => (1 : L) ⊗ₜ[K] v i)
    map_update_add' := fun v i x y => by
      have h : (fun j => (1 : L) ⊗ₜ[K] Function.update v i (x + y) j) =
               Function.update (fun j => (1 : L) ⊗ₜ[K] v j) i ((1 : L) ⊗ₜ[K] x + (1 : L) ⊗ₜ[K] y) := by
        ext j
        simp only [Function.update]
        split_ifs with h
        · subst h
          simp only [TensorProduct.tmul_add]
        · rfl
      rw [h, MultilinearMap.map_update_add]
      congr 1
      · congr 1; ext j; simp [Function.update]; split_ifs with h; subst h; rfl; rfl
      · congr 1; ext j; simp [Function.update]; split_ifs with h; subst h; rfl; rfl
    map_update_smul' := fun v i c x => by
      have h : (fun j => (1 : L) ⊗ₜ[K] Function.update v i (c • x) j) =
               Function.update (fun j => (1 : L) ⊗ₜ[K] v j) i (algebraMap K L c • ((1 : L) ⊗ₜ[K] x)) := by
        ext j
        simp only [Function.update]
        split_ifs with h
        · subst h
          simp only [TensorProduct.tmul_smul]
          rw [IsScalarTower.algebraMap_smul]
        · rfl
      rw [h, MultilinearMap.map_update_smul, IsScalarTower.algebraMap_smul]
      congr 1
      congr 1; ext j; simp [Function.update]; split_ifs with h; subst h; rfl; rfl
  }

/-- Helper: rearrangement map L ⊗ (⨂ V) → ⨂ (L ⊗ V).
    Used to construct the tensor element of the base-changed object. -/
def baseChangeRearrange :
    L ⊗[K] PiTensorProduct K V →ₗ[K] PiTensorProduct L (fun i => L ⊗[K] V i) :=
  TensorProduct.lift {
    toFun := fun l => l • (scalarExtensionMap L)
    map_add' := fun x y => by
      apply LinearMap.ext; intro t
      simp only [add_smul, LinearMap.add_apply, LinearMap.smul_apply]
    map_smul' := fun c x => by
      apply LinearMap.ext; intro t
      simp only [LinearMap.smul_apply]
      rw [Algebra.smul_def, mul_smul]
      rw [IsScalarTower.algebraMap_smul]
      rfl
  }

omit [Fact (1 < d)] in
lemma baseChangeRearrange_tmul (L : Type w) [Field L] [Algebra K L]
    {V : Fin d → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (l : L) (v : PiTensorProduct K V) :
    baseChangeRearrange L (l ⊗ₜ[K] v) = l • scalarExtensionMap L v := by
  rw [baseChangeRearrange, TensorProduct.lift.tmul]
  rfl

attribute [irreducible] baseChangeRearrange

end BaseChange

/-- Base change of a tensor object along a field extension K → L. -/
def baseChange (L : Type w) [Field L] [Algebra K L] (X : TensorObj K d) :
    TensorObj L d where
  V := fun i => L ⊗[K] X.V i
  t := baseChangeRearrange L ((1 : L) ⊗ₜ[K] X.t)

/-- L-linear map induced by base change on individual vector spaces. -/
def baseChangeMap (L : Type w) [Field L] [Algebra K L]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type v'} [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    (L ⊗[K] V) →ₗ[L] (L ⊗[K] W) where
  toFun := TensorProduct.map LinearMap.id f
  map_add' := map_add (TensorProduct.map LinearMap.id f)
  map_smul' := fun c x => by
    dsimp
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, smul_zero]
    | tmul l v =>
      simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
                 TensorProduct.smul_tmul', smul_eq_mul]
    | add x y ih1 ih2 =>
      simp only [map_add, smul_add, ih1, ih2]

@[simp]
theorem baseChangeMap_tmul (L : Type w) [Field L] [Algebra K L]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type v'} [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (l : L) (v : V) :
    baseChangeMap L f (l ⊗ₜ[K] v) = l ⊗ₜ[K] (f v) := rfl

/-- L-linear equivalence induced by base change on individual vector spaces. -/
def baseChangeEquiv (L : Type w) [Field L] [Algebra K L]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type v'} [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) :
    (L ⊗[K] V) ≃ₗ[L] (L ⊗[K] W) :=
  LinearEquiv.ofLinear
    (baseChangeMap L e)
    (baseChangeMap L e.symm)
    (by
      apply LinearMap.ext; intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul l v =>
        rw [LinearMap.comp_apply, LinearMap.id_apply, baseChangeMap_tmul, baseChangeMap_tmul]
        congr 1; exact e.apply_symm_apply v
      | add x y ih1 ih2 =>
        rw [map_add, map_add, ih1, ih2])
    (by
      apply LinearMap.ext; intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul l v =>
        rw [LinearMap.comp_apply, LinearMap.id_apply, baseChangeMap_tmul, baseChangeMap_tmul]
        congr 1; exact e.symm_apply_apply v
      | add x y ih1 ih2 =>
        rw [map_add, map_add, ih1, ih2])

/-- Base change distributes over direct products (L-linearly). -/
def baseChangeProdEquiv (L : Type w) [Field L] [Algebra K L]
    (V W : Type v) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] :
    (L ⊗[K] (V × W)) ≃ₗ[L] (L ⊗[K] V) × (L ⊗[K] W) :=
  TensorProduct.prodRight K L L V W

/-- Base change distributes over tensor products (L-linearly). -/
def baseChangeTensorEquiv (L : Type w) [Field L] [Algebra K L]
    (V W : Type v) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] :
    (L ⊗[K] (V ⊗[K] W)) ≃ₗ[L] (L ⊗[K] V) ⊗[L] (L ⊗[K] W) := by
  letI : Module L (L ⊗[K] V) := TensorProduct.leftModule
  letI : Module L (L ⊗[K] W) := TensorProduct.leftModule
  letI : IsScalarTower K L (L ⊗[K] V) := TensorProduct.isScalarTower_left
  letI : IsScalarTower K L (L ⊗[K] W) := TensorProduct.isScalarTower_left
  exact AlgebraTensorModule.distribBaseChange K L V W

@[simp]
theorem baseChangeTensorEquiv_tmul (L : Type w) [Field L] [Algebra K L]
    (V W : Type v) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (l : L) (v : V) (w : W) :
    letI : Module L (L ⊗[K] V) := TensorProduct.leftModule
    letI : Module L (L ⊗[K] W) := TensorProduct.leftModule
    letI : IsScalarTower K L (L ⊗[K] V) := TensorProduct.isScalarTower_left
    letI : IsScalarTower K L (L ⊗[K] W) := TensorProduct.isScalarTower_left
    baseChangeTensorEquiv L V W (l ⊗ₜ[K] (v ⊗ₜ[K] w)) = (l ⊗ₜ[K] v) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] w) := by
  dsimp [baseChangeTensorEquiv]
  -- Logic: distribBaseChange R A M N (a ⊗ₜ (m ⊗ₜ n)) = (a ⊗ₜ m) ⊗ₜ (1 ⊗ₜ n)
  -- This is a property of AlgebraTensorModule.distribBaseChange
  -- In mathlib/LinearAlgebra/TensorProduct/Tower.lean:
  -- distribBaseChange := (cancelBaseChange _ _ _ _ _ ≪≫ₗ assoc _ _ _ _ _ _).symm
  rfl

@[simp]
theorem baseChangeProdEquiv_comp_baseChangeMap_inl (L : Type w) [Field L] [Algebra K L]
    (V W : Type v) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] :
    ((baseChangeProdEquiv L V W).toLinearMap.comp (baseChangeMap L (LinearMap.inl K V W))) =
    LinearMap.inl L (L ⊗[K] V) (L ⊗[K] W) := by
  apply LinearMap.ext; intro x
  induction x using TensorProduct.induction_on with
  | zero => ext <;> simp
  | tmul l v => ext <;> simp [baseChangeProdEquiv, baseChangeMap_tmul]
  | add a b iha ihb =>
    ext <;> simp only [map_add, iha, ihb, Prod.add_def]

@[simp]
theorem baseChangeProdEquiv_comp_baseChangeMap_inr (L : Type w) [Field L] [Algebra K L]
    (V W : Type v) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] :
    ((baseChangeProdEquiv L V W).toLinearMap.comp (baseChangeMap L (LinearMap.inr K V W))) =
    LinearMap.inr L (L ⊗[K] V) (L ⊗[K] W) := by
  apply LinearMap.ext; intro x
  induction x using TensorProduct.induction_on with
  | zero => ext <;> simp
  | tmul l v => ext <;> simp [baseChangeProdEquiv, baseChangeMap_tmul]
  | add a b iha ihb =>
    ext <;> simp only [map_add, iha, ihb, Prod.add_def]

theorem liftMap_tprod {ι : Type*} [Fintype ι] {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) (v : ∀ i, V i) :
    liftMap f (tprod K v) = tprod K (fun i => f i (v i)) := by
  simp only [liftMap, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply]

omit [Fact (1 < d)] in
theorem scalarExtensionMap_tprod (L : Type w) [Field L] [Algebra K L]
    {V : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (v : ∀ i, V i) :
    scalarExtensionMap L (tprod K v) = tprod L (fun i => (1 : L) ⊗ₜ[K] v i) := by
  dsimp [scalarExtensionMap]
  rw [PiTensorProduct.lift.tprod]
  exact rfl

lemma baseChange_t (L : Type w) [Field L] [Algebra K L] (X : TensorObj K d) :
    (X.baseChange L).t = baseChangeRearrange L (1 ⊗ₜ[K] X.t) := rfl

lemma baseChangeEquiv_toLinearMap (L : Type w) [Field L] [Algebra K L] {V : Type v} {W : Type v'}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) :
    (baseChangeEquiv L e).toLinearMap = baseChangeMap L e.toLinearMap := rfl

theorem interchange_tprod_L {ι : Type*} [Fintype ι] [DecidableEq ι] {V W : ι → Type*}
    [Field L] [∀ i, AddCommGroup (V i)] [∀ i, Module L (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module L (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (K := L) (tprod L v) (tprod L w) = tprod L (fun i => v i ⊗ₜ[L] w i) := by
  dsimp [interchange]
  rw [PiTensorProduct.lift.tprod]
  dsimp [interchangeMap]
  rw [PiTensorProduct.lift.tprod]
  rfl

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

omit [Fact (1 < d)] in
/-- Naturality of baseChangeRearrange with respect to maps on V. -/
theorem baseChangeRearrange_naturality (L : Type w) [Field L] [Algebra K L]
    {V : Fin d → Type v} {W : Fin d → Type v'}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) (t : L ⊗[K] PiTensorProduct K V) :
    liftMap (K := L) (fun i => baseChangeMap L (f i)) (baseChangeRearrange L t) =
    baseChangeRearrange L (TensorProduct.map (LinearMap.id : L →ₗ[K] L) (liftMap (K := K) f) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l v =>
    rw [baseChangeRearrange_tmul]
    rw [LinearMap.map_smul]
    rw [TensorProduct.map_tmul]
    rw [LinearMap.id_apply]
    rw [baseChangeRearrange_tmul]
    congr 1
    induction v using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [LinearMap.map_smul (fₗ := scalarExtensionMap L)]
      rw [LinearMap.map_smul_of_tower (R := K)] -- liftMap
      rw [scalarExtensionMap_tprod]
      rw [liftMap_tprod]
      simp only [baseChangeMap_tmul] -- Simplifies LHS term
      rw [LinearMap.map_smul] -- liftMap (K-linear) on RHS
      rw [LinearMap.map_smul (fₗ := scalarExtensionMap L)] -- scalarExtensionMap on RHS
      congr 1 -- removes r •
      rw [liftMap_tprod]
      rw [scalarExtensionMap_tprod]
    | add x y ihx ihy =>
      rw [map_add, map_add, ihx, ihy, map_add, map_add]
  | add x y ih1 ih2 =>
    simp only [map_add, ih1, ih2]

/-- Base change preserves isomorphism. -/
theorem baseChange_isomorphic (L : Type w) [Field L] [Algebra K L]
    {X Y : TensorObj K d} (h : Isomorphic X Y) :
    Isomorphic (X.baseChange L) (Y.baseChange L) := by
  obtain ⟨iso⟩ := h
  let e (i : Fin d) := baseChangeEquiv L (iso.equiv i)
  let f (i : Fin d) := (iso.equiv i).toLinearMap
  refine ⟨⟨e, ?_⟩⟩
  have he : (fun i => (e i).toLinearMap) = (fun i => baseChangeMap L (f i)) :=
    funext (fun i => baseChangeEquiv_toLinearMap L (iso.equiv i))
  have h_nat := baseChangeRearrange_naturality L f (1 ⊗ₜ[K] X.t)
  have h_map_t : TensorProduct.map (LinearMap.id : L →ₗ[K] L) (liftMap f) (1 ⊗ₜ[K] X.t) = 1 ⊗ₜ[K] Y.t := by
    rw [TensorProduct.map_tmul, LinearMap.id_apply, iso.map_t]
  rw [baseChange_t, he]
  erw [h_nat]
  rw [h_map_t]
  exact (baseChange_t L Y).symm

/-- Base change preserves addition up to isomorphism. -/
theorem baseChange_add (L : Type w) [Field L] [Algebra K L] (X Y : TensorObj K d) :
    Isomorphic ((X + Y).baseChange L) (X.baseChange L + Y.baseChange L) := by
  let e (i : Fin d) := baseChangeProdEquiv (K := K) L (X.V i) (Y.V i)
  refine ⟨⟨e, ?_⟩⟩
  simp only [baseChange_t]
  show (liftMap fun i => (e i).toLinearMap) (baseChangeRearrange L (1 ⊗ₜ[K] (add X Y).t)) =
       (X.baseChange L + Y.baseChange L).t
  dsimp [add]
  rw [TensorProduct.tmul_add, map_add, map_add]
  erw [← baseChangeRearrange_naturality L (fun i => LinearMap.inl K (X.V i) (Y.V i)) (1 ⊗ₜ[K] X.t)]
  erw [← baseChangeRearrange_naturality L (fun i => LinearMap.inr K (X.V i) (Y.V i)) (1 ⊗ₜ[K] Y.t)]
  have h_inl (i : Fin d) : ((e i).toLinearMap.comp (baseChangeMap L (LinearMap.inl K (X.V i) (Y.V i)))) =
                           LinearMap.inl L (L ⊗[K] X.V i) (L ⊗[K] Y.V i) :=
    baseChangeProdEquiv_comp_baseChangeMap_inl L (X.V i) (Y.V i)
  have h_inr (i : Fin d) : ((e i).toLinearMap.comp (baseChangeMap L (LinearMap.inr K (X.V i) (Y.V i)))) =
                           LinearMap.inr L (L ⊗[K] X.V i) (L ⊗[K] Y.V i) :=
    baseChangeProdEquiv_comp_baseChangeMap_inr L (X.V i) (Y.V i)
  rw [liftMap_comp, liftMap_comp]
  have hl : (fun i => (e i).toLinearMap.comp (baseChangeMap L (LinearMap.inl K (X.V i) (Y.V i)))) =
            (fun i => LinearMap.inl L (L ⊗[K] X.V i) (L ⊗[K] Y.V i)) := funext h_inl
  rw [hl]
  have hr : (fun i => (e i).toLinearMap.comp (baseChangeMap L (LinearMap.inr K (X.V i) (Y.V i)))) =
            (fun i => LinearMap.inr L (L ⊗[K] X.V i) (L ⊗[K] Y.V i)) := funext h_inr
  rw [hr]
  rfl

omit [Fact (1 < d)] in
/-- Auxiliary lemma: interchange is linear in the first argument. -/
lemma interchange_add_left {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (x y : PiTensorProduct K V) (z : PiTensorProduct K W) :
    interchange (x + y) z = interchange x z + interchange y z := by
  simp [interchange, map_add]

omit [Fact (1 < d)] in
/-- Auxiliary lemma: interchange is linear in the second argument. -/
lemma interchange_add_right {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (x : PiTensorProduct K V) (y z : PiTensorProduct K W) :
    interchange x (y + z) = interchange x y + interchange x z := by
  simp [interchange, map_add]

omit [Fact (1 < d)] in
/-- Auxiliary lemma: interchange is scalar-linear in the first argument. -/
lemma interchange_smul_left {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (c : K) (x : PiTensorProduct K V) (y : PiTensorProduct K W) :
    interchange (c • x) y = c • interchange x y := by
  simp [interchange, map_smul]

omit [Fact (1 < d)] in
/-- Auxiliary lemma: interchange is scalar-linear in the second argument. -/
lemma interchange_smul_right {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (c : K) (x : PiTensorProduct K V) (y : PiTensorProduct K W) :
    interchange x (c • y) = c • interchange x y := by
  dsimp [interchange]
  simp only [map_smul]

-- Local abbreviations to reduce proof term size
private noncomputable def equivMap (L : Type w) [Field L] [Algebra K L]
    {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (i : Fin d) :
    (L ⊗[K] (V i ⊗[K] W i)) →ₗ[L] (L ⊗[K] V i) ⊗[L] (L ⊗[K] W i) :=
  (baseChangeTensorEquiv L (V i) (W i)).toLinearMap

private noncomputable def lhs_term (L : Type w) [Field L] [Algebra K L]
    {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (tV : PiTensorProduct K V) (tW : PiTensorProduct K W) :=
  liftMap (equivMap L)
    (baseChangeRearrange L (1 ⊗ₜ[K] interchange tV tW))

private noncomputable def rhs_term (L : Type w) [Field L] [Algebra K L]
    {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (tV : PiTensorProduct K V) (tW : PiTensorProduct K W) :=
  interchange (baseChangeRearrange L (1 ⊗ₜ[K] tV)) (baseChangeRearrange L (1 ⊗ₜ[K] tW))

omit [Fact (1 < d)] in
private lemma lhs_add_left (L : Type w) [Field L] [Algebra K L]
    {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (x y : PiTensorProduct K V) (z : PiTensorProduct K W) :
    lhs_term L (x + y) z = lhs_term L x z + lhs_term L y z := by
  dsimp [lhs_term]
  rw [interchange_add_left]
  rw [TensorProduct.tmul_add]
  rw [map_add, map_add] -- bcR

omit [Fact (1 < d)] in
private lemma rhs_add_left (L : Type w) [Field L] [Algebra K L]
    {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (x y : PiTensorProduct K V) (z : PiTensorProduct K W) :
    rhs_term L (x + y) z = rhs_term L x z + rhs_term L y z := by
  dsimp [rhs_term]
  rw [TensorProduct.tmul_add]
  rw [map_add] -- bcR
  rw [interchange_add_left]

omit [Fact (1 < d)] in
private lemma lhs_add_right (L : Type w) [Field L] [Algebra K L]
    {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (x : PiTensorProduct K V) (y z : PiTensorProduct K W) :
    lhs_term L x (y + z) = lhs_term L x y + lhs_term L x z := by
  dsimp [lhs_term]
  rw [interchange_add_right]
  rw [TensorProduct.tmul_add]
  rw [map_add, map_add]

omit [Fact (1 < d)] in
private lemma rhs_add_right (L : Type w) [Field L] [Algebra K L]
    {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (x : PiTensorProduct K V) (y z : PiTensorProduct K W) :
    rhs_term L x (y + z) = rhs_term L x y + rhs_term L x z := by
  dsimp [rhs_term]
  rw [TensorProduct.tmul_add]
  rw [map_add] -- bcR
  rw [interchange_add_right]

omit [Fact (1 < d)] in
private lemma lhs_smul (L : Type w) [Field L] [Algebra K L]
    {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (c : K) (x : PiTensorProduct K V) (c' : K) (y : PiTensorProduct K W) :
    lhs_term L (c • x) (c' • y) = (c * c') • lhs_term L x y := by
  rw [lhs_term]
  rw [interchange_smul_left]
  rw [interchange_smul_right]
  rw [smul_smul] -- (c * c')
  rw [TensorProduct.tmul_smul] -- pulls (c*c') out of tmul
  rw [(baseChangeRearrange L).map_smul] -- bcR
  rw [← IsScalarTower.algebraMap_smul (R := K) (A := L) (c * c') (baseChangeRearrange L (1 ⊗ₜ[K] interchange x y))]
  rw [(liftMap (equivMap L)).map_smul] -- liftMap
  rw [IsScalarTower.algebraMap_smul (R := K) (A := L)]
  rfl

omit [Fact (1 < d)] in
private lemma rhs_smul (L : Type w) [Field L] [Algebra K L]
    {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (c : K) (x : PiTensorProduct K V) (c' : K) (y : PiTensorProduct K W) :
    rhs_term L (c • x) (c' • y) = (c * c') • rhs_term L x y := by
  rw [rhs_term]
  rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  rw [LinearMap.map_smul (fₗ := baseChangeRearrange L)]
  rw [LinearMap.map_smul (fₗ := baseChangeRearrange L)]
  rw [← IsScalarTower.algebraMap_smul (R := K) (A := L) c (baseChangeRearrange L (1 ⊗ₜ[K] x))]
  rw [← IsScalarTower.algebraMap_smul (R := K) (A := L) c' (baseChangeRearrange L (1 ⊗ₜ[K] y))]
  have h_left : ∀ (a : L) (u : PiTensorProduct L (fun i => L ⊗[K] V i)) (v : PiTensorProduct L (fun i => L ⊗[K] W i)), interchange (a • u) v = a • interchange u v :=
    fun a u v => interchange_smul_left a u v
  have h_right : ∀ (a : L) (u : PiTensorProduct L (fun i => L ⊗[K] V i)) (v : PiTensorProduct L (fun i => L ⊗[K] W i)), interchange u (a • v) = a • interchange u v :=
    fun a u v => interchange_smul_right a u v
  erw [h_right, h_left]
  rw [smul_smul, mul_comm]
  rw [← map_mul]
  rw [IsScalarTower.algebraMap_smul (R := K) (A := L)]
  rfl

omit [Fact (1 < d)] in
private lemma bcR_one (L : Type w) [Field L] [Algebra K L]
    {V : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (x : PiTensorProduct K V) :
    baseChangeRearrange L ((1 : L) ⊗ₜ[K] x) = scalarExtensionMap L x := by
  rw [baseChangeRearrange_tmul]
  simp only [one_smul]

omit [Fact (1 < d)] in
private lemma baseChange_interchange_pure (L : Type w) [Field L] [Algebra K L]
    {V W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (c : K) (v : (i : Fin d) → V i) (c' : K) (w : (i : Fin d) → W i) :
    lhs_term L (c • tprod K v) (c' • tprod K w) = rhs_term L (c • tprod K v) (c' • tprod K w) := by
  rw [lhs_smul, rhs_smul]
  congr 1
  have h_lhs : lhs_term L (tprod K v) (tprod K w) =
      tprod L (fun i => ((1 : L) ⊗ₜ[K] v i) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] w i)) := by
    rw [lhs_term]
    rw [interchange_tprod_K]
    rw [bcR_one]
    rw [scalarExtensionMap_tprod]
    rw [liftMap_tprod]
    congr 1
  have h_rhs : rhs_term L (tprod K v) (tprod K w) =
      tprod L (fun i => ((1 : L) ⊗ₜ[K] v i) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] w i)) := by
    rw [rhs_term]
    rw [bcR_one, bcR_one]
    rw [scalarExtensionMap_tprod, scalarExtensionMap_tprod]
    rw [interchange_tprod_L]
  rw [h_lhs, h_rhs]

omit [Fact (1 < d)] in
/-- Key naturality lemma: base change rearrangement commutes with interchange.
    Both sides are bilinear in (tV, tW), so it suffices to check on pure tensors. -/
theorem baseChange_interchange (L : Type w) [Field L] [Algebra K L]
    {V : Fin d → Type v} {W : Fin d → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (tV : PiTensorProduct K V) (tW : PiTensorProduct K W) :
    liftMap (fun i => (baseChangeTensorEquiv L (V i) (W i)).toLinearMap)
      (baseChangeRearrange L (1 ⊗ₜ[K] interchange tV tW)) =
    interchange (baseChangeRearrange L (1 ⊗ₜ[K] tV)) (baseChangeRearrange L (1 ⊗ₜ[K] tW)) := by
  change lhs_term L tV tW = rhs_term L tV tW
  induction tV using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction tW using PiTensorProduct.induction_on with
    | smul_tprod c' w =>
      exact baseChange_interchange_pure L c v c' w
    | add x y ihx ihy =>
      rw [lhs_add_right, rhs_add_right, ihx, ihy]
  | add x y ihx ihy =>
    rw [lhs_add_left, rhs_add_left, ihx, ihy]

/-- Base change preserves multiplication up to isomorphism. -/
theorem baseChange_mul (L : Type w) [Field L] [Algebra K L] (X Y : TensorObj K d) :
    Isomorphic ((X * Y).baseChange L) (X.baseChange L * Y.baseChange L) := by
  -- Construct factor-wise equivalence with explicit type annotation
  let e : ∀ i, (L ⊗[K] (X.V i ⊗[K] Y.V i)) ≃ₗ[L] ((L ⊗[K] X.V i) ⊗[L] (L ⊗[K] Y.V i)) :=
    fun i => baseChangeTensorEquiv L (X.V i) (Y.V i)
  refine ⟨⟨e, ?_⟩⟩
  -- Use naturality lemma with explicit types
  simp only [baseChange_t]
  exact @baseChange_interchange K _ d L _ _ X.V Y.V _ X.module _ Y.module X.t Y.t

/-- Base change preserves zero up to isomorphism. -/
theorem baseChange_zero (L : Type w) [Field L] [Algebra K L] :
    Isomorphic ((zeroObj (K := K) (d := d)).baseChange L) (zeroObj (K := L) (d := d)) := by
  let e (i : Fin d) : (L ⊗[K] PUnit) ≃ₗ[L] PUnit :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => 0
      left_inv := fun x => by dsimp; apply Subsingleton.elim
      right_inv := fun x => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨⟨e, ?_⟩⟩
  dsimp [zeroObj, baseChange_t, liftMap]
  rw [TensorProduct.tmul_zero, map_zero, map_zero]

/-- Base change preserves one up to isomorphism. -/
theorem baseChange_one (L : Type w) [Field L] [Algebra K L] :
    Isomorphic ((oneObj (K := K) (d := d)).baseChange L) (oneObj (K := L) (d := d)) := by
  let e (i : Fin d) : (L ⊗[K] ULift K) ≃ₗ[L] ULift L :=
    LinearEquiv.trans (baseChangeEquiv L (uliftEquiv (K := K)))
      (LinearEquiv.trans (Algebra.TensorProduct.rid K L L).toLinearEquiv (uliftEquiv (K := L)).symm)
  refine ⟨⟨e, ?_⟩⟩
  dsimp [oneObj, baseChange_t, liftMap]
  rw [baseChangeRearrange_tmul]
  rw [scalarExtensionMap_tprod]
  change (liftMap fun i => (e i).toLinearMap) ((1 : L) • tprod L fun i => 1 ⊗ₜ[K] { down := 1 }) = _
  rw [LinearMap.map_smul, liftMap_tprod, one_smul]
  congr; funext i
  dsimp [e, baseChangeEquiv, uliftEquiv]
  norm_num

end TensorObj

namespace Tensor

variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

/-- Base change of a tensor along a field extension K → L. -/
def baseChange (L : Type w) [Field L] [Algebra K L] : Tensor.{u, v} K d →+* Tensor.{w, max u v w} L d where
  toFun := Quotient.map (TensorObj.baseChange L) (fun _ _ h => TensorObj.baseChange_isomorphic L h)
  map_zero' := by
    apply Quotient.sound
    exact TensorObj.baseChange_zero L
  map_one' := by
    apply Quotient.sound
    exact TensorObj.baseChange_one L
  map_add' := by
    apply Quotient.ind₂
    intro X Y
    apply Quotient.sound
    exact TensorObj.baseChange_add L X Y
  map_mul' := by
    apply Quotient.ind₂
    intro X Y
    apply Quotient.sound
    exact TensorObj.baseChange_mul L X Y

end Tensor
