import AsymptoticSpectra.Tensor.Tensor
import AsymptoticSpectra.Tensor.Restriction
import AsymptoticSpectra.AsymptoticClosure
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
# Tensor degeneration (border-restriction)

A tensor `Y.t : ⨂ V_i` degenerates to `X.t : ⨂ W_i` of order `h` iff there
exist `K[T]`-linear maps `A_i : V_i ⊗_K K[T] → W_i ⊗_K K[T]` with
`(A_1 ⊗ ⋯ ⊗ A_d)(Y.t) = T^h · X.t + O(T^{h+1})`.

Working representation (equivalent): a finite-support family
`A_i^{(j)} : Y.V i →ₗ[K] X.V i` indexed by `j : ℕ`. Under this encoding the
`T^k` coefficient of `(A_1 ⊗ ⋯ ⊗ A_d)(Y.t)` is a finite sum of
`liftMap (fun i => A_i^{(j_i)}) Y.t` over `(j_1, …, j_d) ∈ ℕ^d` with
`∑ j_i = k`.

Mirroring `TensorObj.Restrict`, `DegeneratesOfOrder X Y h` means `Y`
degenerates to `X` of order `h` (so `X` is the "smaller" object);
`Degenerates X Y` is the same without fixing the order.

This file is currently a **skeleton**: the main theorems are in place but
proofs are `sorry`.
-/

universe u

open PiTensorProduct

namespace TensorObj

variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

/-- Polynomial family `(A_i^{(j)})_{j : ℕ}` of `K`-linear maps per mode `i`,
with finite support in `j`.  Equivalent to a `K[T]`-linear map
`Y.V i ⊗ K[T] → X.V i ⊗ K[T]`. -/
structure PolyFamily (X Y : TensorObj K d) where
  /-- For each mode `i`, a `Finsupp` assigning each power `j : ℕ` a
  `K`-linear map `Y.V i →ₗ[K] X.V i`. -/
  A : ∀ i, ℕ →₀ (Y.V i →ₗ[K] X.V i)

namespace PolyFamily

variable {X Y : TensorObj K d}

/-- The `T^k` coefficient of `(⨂ᵢ A_i)(Y.t)` under the scalar-family
encoding.  Expanded, this is the finite sum
`∑_{(j_1,…,j_d) : ∑ j_i = k} liftMap (fun i => Φ.A i (j i)) Y.t`,
where the index ranges over `Finset.antidiagonalTuple d k` (tuples of
length `d` summing to `k`).  Each summand whose index falls outside the
support of some `Φ.A i` contributes zero (since `liftMap` is multilinear in
the family and a zero map forces the result to be zero). -/
noncomputable def coeff (Φ : PolyFamily X Y) (k : ℕ) : PiTensorProduct K X.V :=
  (Finset.Nat.antidiagonalTuple d k).sum
    (fun j => liftMap (fun i => Φ.A i (j i)) Y.t)

/-- A plain restriction `f` viewed as a `PolyFamily` supported at `T^0`. -/
noncomputable def ofRestrict (f : ∀ i, Y.V i →ₗ[K] X.V i) : PolyFamily X Y where
  A := fun i => Finsupp.single 0 (f i)

/-- `ofRestrict f` has `T^0` coefficient equal to `liftMap f Y.t`. -/
theorem ofRestrict_coeff_zero (f : ∀ i, Y.V i →ₗ[K] X.V i) :
    (ofRestrict f : PolyFamily X Y).coeff 0 = liftMap f Y.t := by
  simp [coeff, ofRestrict, Finset.Nat.antidiagonalTuple_zero_right]

/-- All `T^k` coefficients of `ofRestrict f` vanish for `k > 0`. -/
theorem ofRestrict_coeff_of_pos (f : ∀ i, Y.V i →ₗ[K] X.V i) {k : ℕ} (hk : 0 < k) :
    (ofRestrict f : PolyFamily X Y).coeff k = 0 := by
  unfold coeff ofRestrict
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.Nat.mem_antidiagonalTuple] at hj
  -- `∑ i, j i = k > 0` forces some `j i₀ > 0`; but `Finsupp.single 0 (f i₀)` is
  -- zero off 0, so the component at `i₀` is the zero linear map, making
  -- `liftMap` of a family with a zero entry vanish on any input.
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, j i₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hsum : ∑ i, j i = 0 := Finset.sum_eq_zero (fun i _ => hall i)
    rw [hj] at hsum
    exact hk.ne' hsum
  have hsingle : (Finsupp.single (0 : ℕ) (f i₀) : ℕ →₀ _) (j i₀) = 0 := by
    rw [Finsupp.single_apply, if_neg (Ne.symm hi₀)]
  -- `liftMap` of a family with a zero entry at `i₀` vanishes on `Y.t`.
  have hmap : liftMap
      (fun i => (Finsupp.single (0 : ℕ) (f i) : ℕ →₀ _) (j i)) Y.t =
        (0 : PiTensorProduct K X.V) := by
    have hlm_zero :
        liftMap (fun i => (Finsupp.single (0 : ℕ) (f i) : ℕ →₀ _) (j i)) =
          (0 : PiTensorProduct K Y.V →ₗ[K] PiTensorProduct K X.V) := by
      unfold liftMap
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro v
      simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod,
        MultilinearMap.compLinearMap_apply, LinearMap.zero_apply]
      apply MultilinearMap.map_coord_zero (tprod K) (i := i₀)
      show Finsupp.single (0 : ℕ) (f i₀) (j i₀) (v i₀) = 0
      rw [hsingle]
      exact LinearMap.zero_apply _
    rw [hlm_zero]; rfl
  exact hmap

/-- Tensor product of two polynomial families, used to take tensor powers
in the passage from single degeneration to asymptotic restriction.  For each
mode `i` and index `j`, the coefficient is the convolution
`∑_{j₁+j₂=j} TensorProduct.map (Φ.A i j₁) (Ψ.A i j₂)`.  Encoded as a
`Finsupp.onFinset` supported in `(Φ.A i).support + (Ψ.A i).support`. -/
noncomputable def tensor {X' Y' : TensorObj K d}
    (Φ : PolyFamily X Y) (Ψ : PolyFamily X' Y') :
    PolyFamily (X * X') (Y * Y') where
  A := fun i =>
    Finsupp.onFinset
      (((Φ.A i).support ×ˢ (Ψ.A i).support).image (fun p => p.1 + p.2))
      (fun j => ∑ p ∈ Finset.antidiagonal j,
          TensorProduct.map (Φ.A i p.1) (Ψ.A i p.2))
      (fun j hj => by
        by_contra hmem
        apply hj
        refine Finset.sum_eq_zero ?_
        intro p hp
        rw [Finset.mem_antidiagonal] at hp
        by_contra hne
        apply hmem
        simp only [Finset.mem_image, Finset.mem_product, Finsupp.mem_support_iff]
        refine ⟨p, ⟨?_, ?_⟩, hp⟩
        · intro h1
          apply hne
          rw [h1]; exact TensorProduct.map_zero_left _
        · intro h2
          apply hne
          rw [h2]; exact TensorProduct.map_zero_right _)

/-- Coefficient formula for `tensor`: `(Φ.tensor Ψ).A i j` is the convolution sum. -/
@[simp]
theorem tensor_A_apply {X Y X' Y' : TensorObj K d}
    (Φ : PolyFamily X Y) (Ψ : PolyFamily X' Y') (i : Fin d) (j : ℕ) :
    (Φ.tensor Ψ).A i j =
      ∑ p ∈ Finset.antidiagonal j,
        TensorProduct.map (Φ.A i p.1) (Ψ.A i p.2) :=
  rfl

end PolyFamily

/-- `X` is a degeneration of `Y` of order `h`: there exists a polynomial
family whose coefficients vanish below `h` and whose `T^h` coefficient is
`X.t`. -/
def DegeneratesOfOrder (X Y : TensorObj K d) (h : ℕ) : Prop :=
  ∃ Φ : PolyFamily X Y, (∀ k, k < h → Φ.coeff k = 0) ∧ Φ.coeff h = X.t

/-- Border-restriction: `X` degenerates from `Y` at some order. -/
def Degenerates (X Y : TensorObj K d) : Prop :=
  ∃ h, DegeneratesOfOrder X Y h

/-! ### Fact 1: Restriction implies degeneration -/

/-- Restriction implies degeneration of order `0`. -/
theorem Restrict.degeneratesOfOrder {X Y : TensorObj K d} (h : X.Restrict Y) :
    DegeneratesOfOrder X Y 0 := by
  obtain ⟨f, hf⟩ := h
  refine ⟨PolyFamily.ofRestrict f, ?_, ?_⟩
  · intro k hk
    exact absurd hk (Nat.not_lt_zero k)
  · rw [PolyFamily.ofRestrict_coeff_zero, hf]

/-- Restriction implies (unindexed) degeneration. -/
theorem Restrict.degenerates {X Y : TensorObj K d} (h : X.Restrict Y) :
    Degenerates X Y :=
  ⟨0, Restrict.degeneratesOfOrder h⟩

/-! ### Closure properties of `DegeneratesOfOrder` -/

/-- Reflexivity: every tensor degenerates to itself at order `0`. -/
theorem DegeneratesOfOrder.refl (X : TensorObj K d) : DegeneratesOfOrder X X 0 :=
  Restrict.degeneratesOfOrder (restrict_refl X)

/-- Helper: `liftMap` of a constant `LinearMap.id` family is the identity. -/
private theorem liftMap_id_fun {Z : TensorObj K d} :
    liftMap (fun (i : Fin d) => (LinearMap.id : Z.V i →ₗ[K] Z.V i)) =
      (LinearMap.id : PiTensorProduct K Z.V →ₗ[K] PiTensorProduct K Z.V) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext; intro v
  simp [liftMap]

omit [Fact (1 < d)] in
/-- Helper: if a family of linear maps has a zero entry at some mode `i₀`,
then `liftMap` of that family is the zero map. -/
private theorem liftMap_eq_zero_of_zero_slot {V W : Fin d → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    {g : ∀ i, V i →ₗ[K] W i} {i₀ : Fin d} (hg : g i₀ = 0) :
    liftMap g = (0 : PiTensorProduct K V →ₗ[K] PiTensorProduct K W) := by
  unfold liftMap
  apply PiTensorProduct.ext
  apply MultilinearMap.ext; intro v
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, LinearMap.zero_apply]
  apply MultilinearMap.map_coord_zero (tprod K) (i := i₀)
  rw [hg]; rfl

private lemma sum_add_eq {ι β : Type*} [AddCommMonoid β] {s : Finset ι}
    {f g : ι → β} {a b : β} (hf : s.sum f = a) (hg : s.sum g = b) :
    s.sum (fun x => f x + g x) = a + b := by
  rw [Finset.sum_add_distrib, hf, hg]

/-- Direct-sum compatibility: adding the same tensor to both sides preserves
the degeneration order.  Construction: the polynomial family is block-diagonal
`prodMap (Φ.A i j) 0` plus a single `prodMap 0 id` correction concentrated at
a "special" mode with index `h` and `0` on other modes.  The `T^k` coefficient
splits as `liftMap inl (Φ.coeff k) + (if k = h then liftMap inr Z.t else 0)`. -/
theorem DegeneratesOfOrder.add_right {X Y Z : TensorObj K d} {h : ℕ}
    (hdeg : DegeneratesOfOrder X Y h) :
    DegeneratesOfOrder (X + Z) (Y + Z) h := by
  obtain ⟨Φ, hvan, hcoeff⟩ := hdeg
  have h1d : (1 : ℕ) < d := Fact.out
  let spMode : Fin d := ⟨0, by omega⟩
  let spIdx : Fin d → ℕ := fun i => if i = spMode then h else 0
  have hspIdxSum : ∑ i, spIdx i = h := by
    show (∑ i, if i = spMode then h else 0 : ℕ) = h
    rw [Finset.sum_ite_eq' Finset.univ spMode (fun _ => h)]
    simp
  let mkFam : PolyFamily (X + Z) (Y + Z) :=
    ⟨fun i => Finsupp.onFinset
      ((Φ.A i).support ∪ {spIdx i})
      (fun j => LinearMap.prodMap (Φ.A i j)
        (if spIdx i = j then (LinearMap.id : Z.V i →ₗ[K] Z.V i) else 0))
      (fun j hj => by
        by_contra hmem
        apply hj
        simp only
        rw [Finset.mem_union, Finsupp.mem_support_iff, Finset.mem_singleton] at hmem
        push_neg at hmem
        rw [hmem.1, if_neg (Ne.symm hmem.2), LinearMap.prodMap_zero]
        rfl)⟩
  -- Per mode-index value of the family.
  have hFamVal : ∀ i j, mkFam.A i j = LinearMap.prodMap (Φ.A i j)
      (if spIdx i = j then (LinearMap.id : Z.V i →ₗ[K] Z.V i) else 0) := by
    intro i j; rfl
  -- Per-tuple splitting of liftMap evaluated on `(Y+Z).t`.
  have hsplit : ∀ j : Fin d → ℕ,
      liftMap (fun i => mkFam.A i (j i)) (Y + Z).t =
        liftMap (fun i => LinearMap.inl K (X.V i) (Z.V i))
          (liftMap (fun i => Φ.A i (j i)) Y.t) +
        liftMap (fun i => LinearMap.inr K (X.V i) (Z.V i))
          (liftMap (fun i => if spIdx i = j i then
            (LinearMap.id : Z.V i →ₗ[K] Z.V i) else 0) Z.t) := by
    intro j
    -- Key equations for composing `prodMap` with `inl`/`inr`.
    have hinl : (fun i => LinearMap.prodMap (Φ.A i (j i))
          (if spIdx i = j i then (LinearMap.id : Z.V i →ₗ[K] Z.V i) else 0) ∘ₗ
            LinearMap.inl K (Y.V i) (Z.V i)) =
                (fun i => LinearMap.inl K (X.V i) (Z.V i) ∘ₗ Φ.A i (j i)) := by
      funext i
      apply LinearMap.ext; intro x
      split_ifs <;> rfl
    have hinr : (fun i => LinearMap.prodMap (Φ.A i (j i))
          (if spIdx i = j i then (LinearMap.id : Z.V i →ₗ[K] Z.V i) else 0) ∘ₗ
            LinearMap.inr K (Y.V i) (Z.V i)) =
                (fun i => LinearMap.inr K (X.V i) (Z.V i) ∘ₗ
                  (if spIdx i = j i then
                    (LinearMap.id : Z.V i →ₗ[K] Z.V i) else 0)) := by
      funext i
      apply LinearMap.ext; intro x
      split_ifs with hh <;>
        (show LinearMap.prodMap _ _ ((0 : Y.V i), x) = _;
         rw [LinearMap.prodMap_apply]; simp)
    show liftMap (fun i => mkFam.A i (j i))
        (liftMap (fun i => LinearMap.inl K (Y.V i) (Z.V i)) Y.t +
          liftMap (fun i => LinearMap.inr K (Y.V i) (Z.V i)) Z.t) = _
    -- The `rw` chain fails forward (type-alias `(Y+Z).V` vs `fun i => Y.V i × Z.V i`
    -- blocks `liftMap_comp` on the LHS).  Work backwards from RHS to LHS.
    symm
    rw [liftMap_comp, liftMap_comp, ← hinl, ← hinr, ← liftMap_comp, ← liftMap_comp,
      ← map_add]
    rfl
  -- Per-tuple Z-part value: `liftMap bl.j Z.t = if j = spIdx then Z.t else 0`.
  have hZ_per_tuple : ∀ j : Fin d → ℕ,
      liftMap (fun i => if spIdx i = j i then
        (LinearMap.id : Z.V i →ₗ[K] Z.V i) else 0) Z.t =
      (if j = spIdx then Z.t else 0) := by
    intro j
    by_cases hj : j = spIdx
    · rw [if_pos hj]
      subst hj
      have heq : (fun i => if spIdx i = spIdx i then
          (LinearMap.id : Z.V i →ₗ[K] Z.V i) else 0) =
        (fun i => LinearMap.id) := by
        funext i; rw [if_pos rfl]
      rw [heq, liftMap_id_fun]; rfl
    · rw [if_neg hj]
      obtain ⟨i₀, hi₀⟩ : ∃ i₀, spIdx i₀ ≠ j i₀ := by
        by_contra hall
        push_neg at hall
        apply hj
        funext i; exact (hall i).symm
      rw [liftMap_eq_zero_of_zero_slot (i₀ := i₀) (by rw [if_neg hi₀])]; rfl
  -- Key coefficient identity: sum split.
  have hkey : ∀ k, mkFam.coeff k =
      liftMap (fun i => LinearMap.inl K (X.V i) (Z.V i)) (Φ.coeff k) +
      (if k = h then liftMap (fun i => LinearMap.inr K (X.V i) (Z.V i)) Z.t else 0) := by
    intro k
    show (Finset.Nat.antidiagonalTuple d k).sum
        (fun j => liftMap (fun i => mkFam.A i (j i)) (Y + Z).t) = _
    have hbody : (fun j => liftMap (fun i => mkFam.A i (j i)) (Y + Z).t) =
        (fun j => liftMap (fun i => LinearMap.inl K (X.V i) (Z.V i))
            (liftMap (fun i => Φ.A i (j i)) Y.t) +
          liftMap (fun i => LinearMap.inr K (X.V i) (Z.V i))
            (if j = spIdx then Z.t else 0)) := by
      funext j; rw [hsplit, hZ_per_tuple]
    -- Compute the inl-part of the sum.
    have hinl_part : (Finset.Nat.antidiagonalTuple d k).sum
        (fun j => liftMap (fun i => LinearMap.inl K (X.V i) (Z.V i))
          (liftMap (fun i => Φ.A i (j i)) Y.t)) =
        liftMap (fun i => LinearMap.inl K (X.V i) (Z.V i)) (Φ.coeff k) := by
      rw [← map_sum]; rfl
    -- Compute the inr-part of the sum.
    have hinr_part : (Finset.Nat.antidiagonalTuple d k).sum
        (fun j => liftMap (fun i => LinearMap.inr K (X.V i) (Z.V i))
          (if j = spIdx then Z.t else 0)) =
        (if k = h then liftMap (fun i => LinearMap.inr K (X.V i) (Z.V i)) Z.t else 0) := by
      by_cases hk : k = h
      · subst hk
        rw [if_pos rfl]
        have hmem : spIdx ∈ Finset.Nat.antidiagonalTuple d k := by
          rw [Finset.Nat.mem_antidiagonalTuple]; exact hspIdxSum
        rw [Finset.sum_eq_single spIdx
          (fun j _ hj => by rw [if_neg hj, map_zero])
          (fun hnot => absurd hmem hnot),
          if_pos rfl]
      · rw [if_neg hk]
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.Nat.mem_antidiagonalTuple] at hj
        have hjne : j ≠ spIdx := by
          intro heq; subst heq
          exact hk (hj ▸ hspIdxSum)
        rw [if_neg hjne, map_zero]
    -- Combine: rewrite summand, split sum, use both halves.
    rw [hbody]
    exact sum_add_eq hinl_part hinr_part
  refine ⟨mkFam, ?_, ?_⟩
  · intro k hk
    rw [hkey k, hvan k hk]
    simp only [map_zero, zero_add]
    rw [if_neg (by omega : k ≠ h)]; rfl
  · show mkFam.coeff h = (X + Z).t
    rw [hkey h, hcoeff, if_pos rfl]
    show _ = liftMap _ X.t + liftMap _ Z.t
    rfl

/-- Tensor-product compatibility: tensoring with the same factor on the right
preserves the degeneration order.  The polynomial family `(Φ.A i j) ⊗ id`
yields `T^k` coefficient equal to `interchange (Φ.coeff k) Z.t`. -/
theorem DegeneratesOfOrder.mul_right {X Y Z : TensorObj K d} {h : ℕ}
    (hdeg : DegeneratesOfOrder X Y h) :
    DegeneratesOfOrder (X * Z) (Y * Z) h := by
  obtain ⟨Φ, hvan, hcoeff⟩ := hdeg
  let mkFam : PolyFamily (X * Z) (Y * Z) :=
    ⟨fun i => (Φ.A i).mapRange
      (fun L => TensorProduct.map L (LinearMap.id : Z.V i →ₗ[K] Z.V i))
      (by show TensorProduct.map 0 _ = 0; exact TensorProduct.map_zero_left _)⟩
  have heq : ∀ k, mkFam.coeff k = interchange (Φ.coeff k) Z.t := by
    intro k
    show (Finset.Nat.antidiagonalTuple d k).sum
        (fun j => liftMap (fun i => TensorProduct.map (Φ.A i (j i))
            (LinearMap.id : Z.V i →ₗ[K] Z.V i)) (interchange Y.t Z.t)) = _
    have step : ∀ j : Fin d → ℕ,
        liftMap (fun i => TensorProduct.map (Φ.A i (j i))
            (LinearMap.id : Z.V i →ₗ[K] Z.V i)) (interchange Y.t Z.t) =
          interchange (liftMap (fun i => Φ.A i (j i)) Y.t) Z.t := by
      intro j
      rw [liftMap_interchange, liftMap_id_fun]; rfl
    simp_rw [step]
    rw [show Φ.coeff k = (Finset.Nat.antidiagonalTuple d k).sum
        (fun j => liftMap (fun i => Φ.A i (j i)) Y.t) from rfl,
        map_sum]
    exact (LinearMap.sum_apply _ _ _).symm
  refine ⟨mkFam, ?_, ?_⟩
  · intro k hk
    rw [heq k, hvan k hk, (interchange (K := K)).map_zero, LinearMap.zero_apply]; rfl
  · rw [heq h, hcoeff]; rfl

/-! ### Helpers for `tensor_coeff_expand` -/

omit [Fact (1 < d)] in
private theorem liftMap_sum_piFinset
    {V W : Fin d → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    {α : Fin d → Type*} (S : ∀ i, Finset (α i))
    (g : ∀ i, α i → (V i →ₗ[K] W i)) :
    liftMap (fun i => ∑ j ∈ S i, g i j) =
      ∑ c ∈ Fintype.piFinset S, liftMap (fun i => g i (c i)) := by
  apply PiTensorProduct.ext; apply MultilinearMap.ext; intro v
  simp only [LinearMap.compMultilinearMap_apply, liftMap, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, LinearMap.sum_apply]
  exact MultilinearMap.map_sum_finset (tprod K) (fun i j => g i j (v i)) S

private theorem sum_antidiagTuple_piFinset_antidiag {β : Type*} [AddCommMonoid β]
    {d k : ℕ} (F : (Fin d → ℕ) → (Fin d → ℕ) → β) :
    ∑ j ∈ Finset.Nat.antidiagonalTuple d k,
      ∑ c ∈ Fintype.piFinset (fun i => Finset.antidiagonal (j i)),
        F (fun i => (c i).1) (fun i => (c i).2) =
    ∑ p ∈ Finset.antidiagonal k,
      ∑ j₁ ∈ Finset.Nat.antidiagonalTuple d p.1,
        ∑ j₂ ∈ Finset.Nat.antidiagonalTuple d p.2,
          F j₁ j₂ := by
  -- Flatten LHS into sigma, flatten RHS into nested sigma
  rw [Finset.sum_sigma']
  conv_rhs => rw [Finset.sum_sigma']
  simp_rw [Finset.sum_sigma']
  -- Now apply the bijection
  apply Finset.sum_nbij'
    (fun ⟨j, c⟩ => ⟨⟨(∑ i, (c i).1, ∑ i, (c i).2), fun i => (c i).1⟩, fun i => (c i).2⟩)
    (fun ⟨⟨_, j₁⟩, j₂⟩ => ⟨fun i => j₁ i + j₂ i, fun i => (j₁ i, j₂ i)⟩)
  · -- forward membership
    rintro ⟨j, c⟩ hm
    rw [Finset.mem_sigma] at hm
    dsimp only at hm
    have hj := Finset.Nat.mem_antidiagonalTuple.mp hm.1
    have hc : ∀ i, (c i) ∈ Finset.antidiagonal (j i) :=
      Fintype.mem_piFinset.mp hm.2
    refine Finset.mem_sigma.mpr ⟨Finset.mem_sigma.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_antidiagonal.mpr (by
        rw [← Finset.sum_add_distrib, ← hj]
        exact Finset.sum_congr rfl fun i _ => Finset.mem_antidiagonal.mp (hc i))
    · exact Finset.Nat.mem_antidiagonalTuple.mpr rfl
    · exact Finset.Nat.mem_antidiagonalTuple.mpr rfl
  · -- backward membership
    rintro ⟨⟨p, j₁⟩, j₂⟩ hm
    rw [Finset.mem_sigma] at hm
    rw [Finset.mem_sigma] at hm
    dsimp only at hm
    have hp := Finset.mem_antidiagonal.mp hm.1.1
    have hj₁ := Finset.Nat.mem_antidiagonalTuple.mp hm.1.2
    have hj₂ := Finset.Nat.mem_antidiagonalTuple.mp hm.2
    refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
    · rw [Finset.Nat.mem_antidiagonalTuple]
      rw [← hp, ← hj₁, ← hj₂, ← Finset.sum_add_distrib]
    · rw [Fintype.mem_piFinset]
      intro i; exact Finset.mem_antidiagonal.mpr rfl
  · -- left inverse
    rintro ⟨j, c⟩ hm
    rw [Finset.mem_sigma] at hm
    dsimp only at hm
    have hc := Fintype.mem_piFinset.mp hm.2
    simp only [Sigma.mk.inj_iff]
    refine ⟨funext fun i => Finset.mem_antidiagonal.mp (hc i),
            heq_of_eq (funext fun i => Prod.eta (c i))⟩
  · -- right inverse
    rintro ⟨⟨p, j₁⟩, j₂⟩ hm
    rw [Finset.mem_sigma] at hm
    rw [Finset.mem_sigma] at hm
    dsimp only at hm
    have hj₁ := Finset.Nat.mem_antidiagonalTuple.mp hm.1.2
    have hj₂ := Finset.Nat.mem_antidiagonalTuple.mp hm.2
    simp only [Sigma.mk.inj_iff]
    exact ⟨⟨Prod.ext hj₁ hj₂, heq_of_eq (funext fun _ => rfl)⟩,
           heq_of_eq (funext fun _ => rfl)⟩
  · -- values agree
    intro _ _; rfl

/-- The `T^k` coefficient of a tensor product of polynomial families is the
convolution of the individual coefficients through `interchange`. -/
theorem PolyFamily.tensor_coeff_expand {X Y X' Y' : TensorObj K d}
    (Φ : PolyFamily X Y) (Ψ : PolyFamily X' Y') (k : ℕ) :
    (Φ.tensor Ψ).coeff k = ∑ p ∈ Finset.antidiagonal k,
      interchange (Φ.coeff p.1) (Ψ.coeff p.2) := by
  unfold coeff
  -- Step 1: unfold convolution inside liftMap (definitional via tensor_A_apply)
  show ∑ j ∈ Finset.Nat.antidiagonalTuple d k,
      liftMap (fun i => ∑ p ∈ Finset.antidiagonal (j i),
        TensorProduct.map (Φ.A i p.1) (Ψ.A i p.2)) (Y * Y').t = _
  -- Step 2: expand liftMap of sum via multilinearity
  simp_rw [liftMap_sum_piFinset]
  -- Step 3: push application inside sum, rewrite interchange
  simp_rw [LinearMap.sum_apply, mul_t, liftMap_interchange]
  -- Step 4: reindex using sum_antidiagTuple_piFinset_antidiag
  rw [sum_antidiagTuple_piFinset_antidiag
    (fun j₁ j₂ => interchange (liftMap (fun i => Φ.A i (j₁ i)) Y.t)
      (liftMap (fun i => Ψ.A i (j₂ i)) Y'.t))]
  -- Step 5: pull sums through interchange (bilinearity)
  congr 1; ext ⟨p₁, p₂⟩; dsimp only; symm
  simp_rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_comm

/-! ### Helpers for `DegeneratesOfOrder.trans` -/

/-- Generalized `coeff`: apply the polynomial family maps to an arbitrary tensor
instead of the source `Y.t`.  This is linear in `t`. -/
private noncomputable def PolyFamily.applyTo {X Y : TensorObj K d}
    (Φ : PolyFamily X Y) (k : ℕ) : PiTensorProduct K Y.V →ₗ[K] PiTensorProduct K X.V :=
  (Finset.Nat.antidiagonalTuple d k).sum
    (fun j => liftMap (fun i => Φ.A i (j i)))

private theorem PolyFamily.applyTo_apply_t {X Y : TensorObj K d}
    (Φ : PolyFamily X Y) (k : ℕ) : Φ.applyTo k Y.t = Φ.coeff k :=
  LinearMap.sum_apply _ _ _

/-- Reparametrize a polynomial family by substituting `T ↦ T^s`:
`Ψ'.A i j = Ψ.A i (j / s)` if `s ∣ j`, else `0`. -/
private noncomputable def PolyFamily.reparametrize {X Y : TensorObj K d}
    (Ψ : PolyFamily X Y) (s : ℕ) : PolyFamily X Y where
  A := fun i =>
    Finsupp.onFinset
      ((Ψ.A i).support.image (· * s))
      (fun j => if s ∣ j then Ψ.A i (j / s) else 0)
      (fun j hj => by
        -- hj : (if s ∣ j then ...) ≠ 0, goal : j ∈ image (· * s) support
        simp only [Finset.mem_image, Finsupp.mem_support_iff]
        by_contra hmem
        push_neg at hmem
        -- hmem : ∀ a, Ψ.A i a ≠ 0 → a * s ≠ j
        apply hj
        show (if s ∣ j then Ψ.A i (j / s) else 0) = 0
        split_ifs with hdvd
        · by_contra hne
          exact hmem (j / s) hne (Nat.div_mul_cancel hdvd)
        · rfl)

private theorem PolyFamily.reparametrize_A_eq {X Y : TensorObj K d}
    (Ψ : PolyFamily X Y) (s : ℕ) (i : Fin d) (j : ℕ) :
    (Ψ.reparametrize s).A i j = if s ∣ j then Ψ.A i (j / s) else 0 := by
  simp [reparametrize]

/-- The coefficient of the reparametrized family at index `k`:
vanishes unless `s ∣ k`, in which case it equals `Ψ.coeff (k / s)`. -/
private theorem PolyFamily.reparametrize_coeff {X Y : TensorObj K d}
    (Ψ : PolyFamily X Y) {s : ℕ} (hs : 0 < s) (k : ℕ) :
    (Ψ.reparametrize s).coeff k = if s ∣ k then Ψ.coeff (k / s) else 0 := by
  unfold coeff
  split_ifs with hdvd
  · -- When s ∣ k: the nonzero summands biject with antidiagonalTuple d (k/s)
    have reparam_eq : ∀ j : Fin d → ℕ, (∀ i, s ∣ j i) →
        (fun i => (Ψ.reparametrize s).A i (j i)) = (fun i => Ψ.A i (j i / s)) := by
      intro j hall; ext i; rw [reparametrize_A_eq, if_pos (hall i)]
    have key : ∀ j ∈ Finset.Nat.antidiagonalTuple d k,
        liftMap (fun i => (Ψ.reparametrize s).A i (j i)) Y.t =
        if ∀ i, s ∣ j i then liftMap (fun i => Ψ.A i (j i / s)) Y.t else 0 := by
      intro j _
      split_ifs with hall
      · rw [reparam_eq j hall]
      · push_neg at hall
        obtain ⟨i₀, hi₀⟩ := hall
        have : (Ψ.reparametrize s).A i₀ (j i₀) = 0 := by
          rw [reparametrize_A_eq, if_neg hi₀]
        rw [liftMap_eq_zero_of_zero_slot this]; rfl
    rw [Finset.sum_congr rfl key, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    -- The divisible tuples biject with antidiagonalTuple d (k/s)
    symm
    apply Finset.sum_nbij' (fun j' i => j' i * s) (fun j i => j i / s)
    · -- forward membership
      intro j' hj'
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.Nat.mem_antidiagonalTuple]
        rw [Finset.Nat.mem_antidiagonalTuple] at hj'
        calc ∑ i, j' i * s = (∑ i, j' i) * s := (Finset.sum_mul ..).symm
          _ = (k / s) * s := by rw [hj']
          _ = k := Nat.div_mul_cancel hdvd
      · intro i; exact ⟨j' i, (mul_comm (j' i) s)⟩
    · -- backward membership
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.Nat.mem_antidiagonalTuple]
      have hsum := Finset.Nat.mem_antidiagonalTuple.mp hj.1
      have hdvd_all := hj.2
      have hmul : (∑ i, j i / s) * s = k := by
        calc (∑ i, j i / s) * s = ∑ i, j i / s * s := (Finset.sum_mul ..)
          _ = ∑ i, j i := Finset.sum_congr rfl (fun i _ => Nat.div_mul_cancel (hdvd_all i))
          _ = k := hsum
      rw [← hmul, Nat.mul_div_cancel _ hs]
    · -- left inverse
      intro j' _; funext i; exact Nat.mul_div_cancel _ hs
    · -- right inverse
      intro j hj
      rw [Finset.mem_filter] at hj
      funext i; exact Nat.div_mul_cancel (hj.2 i)
    · -- values agree
      intro j' _
      simp only [Nat.mul_div_cancel _ hs]
  · -- When s ∤ k: every summand vanishes
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.Nat.mem_antidiagonalTuple] at hj
    have : ¬ ∀ i, s ∣ j i := by
      intro hall; exact hdvd (hj ▸ Finset.dvd_sum (fun i _ => hall i))
    push_neg at this
    obtain ⟨i₀, hi₀⟩ := this
    have hzero : (Ψ.reparametrize s).A i₀ (j i₀) = 0 := by
      rw [reparametrize_A_eq, if_neg hi₀]
    rw [liftMap_eq_zero_of_zero_slot hzero]; rfl

/-- Composition of polynomial families: for each mode `i`,
`Θ.A i j = ∑_{a+b=j} (Φ.A i a) ∘ₗ (Ψ.A i b)`. -/
private noncomputable def PolyFamily.comp {X Y Z : TensorObj K d}
    (Φ : PolyFamily X Y) (Ψ : PolyFamily Y Z) : PolyFamily X Z where
  A := fun i =>
    Finsupp.onFinset
      (((Φ.A i).support ×ˢ (Ψ.A i).support).image (fun p => p.1 + p.2))
      (fun j => ∑ p ∈ Finset.antidiagonal j,
          (Φ.A i p.1).comp (Ψ.A i p.2))
      (fun j hj => by
        by_contra hmem
        apply hj
        refine Finset.sum_eq_zero ?_
        intro p hp
        rw [Finset.mem_antidiagonal] at hp
        by_contra hne
        apply hmem
        simp only [Finset.mem_image, Finset.mem_product, Finsupp.mem_support_iff]
        refine ⟨p, ⟨?_, ?_⟩, hp⟩
        · intro h1; apply hne; rw [h1]; exact LinearMap.zero_comp _
        · intro h2; apply hne; rw [h2]; exact LinearMap.comp_zero _)

/-- Key identity: the coefficient of a composition is a convolution via `applyTo`. -/
private theorem PolyFamily.comp_coeff_eq {X Y Z : TensorObj K d}
    (Φ : PolyFamily X Y) (Ψ : PolyFamily Y Z) (k : ℕ) :
    (Φ.comp Ψ).coeff k = ∑ p ∈ Finset.antidiagonal k,
      Φ.applyTo p.1 (Ψ.coeff p.2) := by
  unfold coeff
  -- Step 1: unfold the convolution inside liftMap (definitional)
  show ∑ j ∈ Finset.Nat.antidiagonalTuple d k,
      liftMap (fun i => ∑ p ∈ Finset.antidiagonal (j i),
        (Φ.A i p.1).comp (Ψ.A i p.2)) Z.t = _
  -- Step 2: expand liftMap of sum via multilinearity
  simp_rw [liftMap_sum_piFinset]
  -- Step 3: push Z.t through the inner sum, then split composition
  simp_rw [LinearMap.sum_apply, ← liftMap_comp]
  -- Step 4: reindex using sum_antidiagTuple_piFinset_antidiag
  rw [sum_antidiagTuple_piFinset_antidiag
    (fun j₁ j₂ => (liftMap (fun i => Φ.A i (j₁ i)))
      ((liftMap (fun i => Ψ.A i (j₂ i))) Z.t))]
  -- Step 5: pull inner sum through linear map
  unfold applyTo
  congr 1; ext ⟨p₁, p₂⟩
  rw [LinearMap.sum_apply]
  congr 1; ext j₁
  rw [map_sum]

/-- Transitivity: composing two degenerations of orders `h₁` and `h₂` gives
a degeneration of order `h₁ * h₂ + h₁ + h₂ = (h₁+1)(h₂+1) - 1`.  Proof idea:
reparametrize Ψ by `T ↦ T^{h₁+1}` before composing with Φ, so the
leading term appears at `T^{h₂(h₁+1) + h₁} = T^{(h₁+1)(h₂+1)-1}`. -/
theorem DegeneratesOfOrder.trans {X Y Z : TensorObj K d} {h₁ h₂ : ℕ}
    (hXY : X.DegeneratesOfOrder Y h₁) (hYZ : Y.DegeneratesOfOrder Z h₂) :
    X.DegeneratesOfOrder Z (h₁ * h₂ + h₁ + h₂) := by
  obtain ⟨Φ, hΦ_van, hΦ_lead⟩ := hXY
  obtain ⟨Ψ, hΨ_van, hΨ_lead⟩ := hYZ
  set s := h₁ + 1 with hs_def
  set Ψ' := Ψ.reparametrize s
  set Θ := Φ.comp Ψ'
  have hs_pos : (0 : ℕ) < s := Nat.succ_pos _
  -- h₁ * h₂ + h₁ + h₂ = h₂ * s + h₁
  have htarget : h₁ * h₂ + h₁ + h₂ = h₂ * s + h₁ := by rw [hs_def]; ring
  -- Coeff and reparametrization identities
  have hΘ_coeff : ∀ n, Θ.coeff n = ∑ p ∈ Finset.antidiagonal n,
      Φ.applyTo p.1 (Ψ'.coeff p.2) := fun n => Φ.comp_coeff_eq Ψ' n
  have hΨ'_coeff : ∀ n, Ψ'.coeff n = if s ∣ n then Ψ.coeff (n / s) else 0 :=
    fun n => Ψ.reparametrize_coeff hs_pos n
  -- Helper: for any term (p₁, p₂) with p₁ + p₂ = k, show it vanishes
  -- when k ≤ h₂ * s + h₁ and (p₁, p₂) ≠ (h₁, h₂ * s)
  have vanish_term : ∀ k p₁ p₂, p₁ + p₂ = k → k ≤ h₂ * s + h₁ →
      (k < h₂ * s + h₁ ∨ (p₁, p₂) ≠ (h₁, h₂ * s)) →
      Φ.applyTo p₁ (Ψ'.coeff p₂) = 0 := by
    intro k p₁ p₂ hp hle hdisj
    rw [hΨ'_coeff]
    split_ifs with hdvd
    · set q := p₂ / s
      by_cases hq : q < h₂
      · rw [hΨ_van q hq, map_zero]
      · push_neg at hq
        -- q ≥ h₂, so p₂ ≥ h₂ * s and p₁ ≤ k - h₂ * s ≤ h₁
        have hp₂_lb : h₂ * s ≤ p₂ := by
          calc h₂ * s = h₂ * s := rfl
            _ ≤ q * s := Nat.mul_le_mul_right s hq
            _ = p₂ := Nat.div_mul_cancel hdvd
        -- q > h₂ is impossible: p₂ ≥ (h₂+1)*s = h₂*s + s > h₂*s + h₁ ≥ k ≥ p₂
        have hq_eq : q = h₂ := by
          by_contra hne
          have hq_gt : h₂ + 1 ≤ q := Nat.lt_of_le_of_ne hq (Ne.symm hne)
          have : (h₂ + 1) * s ≤ p₂ := by
            calc (h₂ + 1) * s ≤ q * s := Nat.mul_le_mul_right s hq_gt
              _ = p₂ := Nat.div_mul_cancel hdvd
          have : (h₂ + 1) * s = h₂ * s + s := by ring
          linarith
        -- So q = h₂, p₂ = h₂ * s, p₁ = k - h₂ * s
        have hp₂_eq : p₂ = h₂ * s := by
          calc p₂ = q * s := (Nat.div_mul_cancel hdvd).symm
            _ = h₂ * s := by rw [hq_eq]
        have hp₁_eq : p₁ = k - h₂ * s := by omega
        by_cases hp₁_lt : p₁ < h₁
        · rw [hq_eq, hΨ_lead, PolyFamily.applyTo_apply_t, hΦ_van p₁ hp₁_lt]
        · push_neg at hp₁_lt
          have hp₁_le : p₁ ≤ h₁ := by omega
          have hp₁_final : p₁ = h₁ := le_antisymm hp₁_le hp₁_lt
          rcases hdisj with hlt | hne
          · linarith
          · exact absurd (Prod.ext hp₁_final hp₂_eq) hne
    · exact map_zero _
  refine ⟨Θ, ?_, ?_⟩
  · -- Vanishing: Θ.coeff k = 0 for k < h₁ * h₂ + h₁ + h₂
    intro k hk
    rw [hΘ_coeff]
    rw [htarget] at hk
    apply Finset.sum_eq_zero
    intro ⟨p₁, p₂⟩ hp
    exact vanish_term k p₁ p₂ (Finset.mem_antidiagonal.mp hp) (Nat.le_of_lt hk) (Or.inl hk)
  · -- Leading term: Θ.coeff (h₁ * h₂ + h₁ + h₂) = X.t
    rw [hΘ_coeff, htarget]
    have hmem : (h₁, h₂ * s) ∈ Finset.antidiagonal (h₂ * s + h₁) :=
      Finset.mem_antidiagonal.mpr (by omega)
    rw [Finset.sum_eq_single (h₁, h₂ * s)
      (fun ⟨p₁, p₂⟩ hp hne =>
        vanish_term _ p₁ p₂ (Finset.mem_antidiagonal.mp hp) le_rfl (Or.inr hne))
      (fun h => absurd hmem h)]
    rw [hΨ'_coeff, if_pos (dvd_mul_left s h₂), Nat.mul_div_cancel _ hs_pos,
      hΨ_lead, PolyFamily.applyTo_apply_t, hΦ_lead]

/-- Tensor product of two degenerations: orders add. -/
theorem DegeneratesOfOrder.mul {X₁ Y₁ X₂ Y₂ : TensorObj K d} {h₁ h₂ : ℕ}
    (hdeg₁ : X₁.DegeneratesOfOrder Y₁ h₁) (hdeg₂ : X₂.DegeneratesOfOrder Y₂ h₂) :
    (X₁ * X₂).DegeneratesOfOrder (Y₁ * Y₂) (h₁ + h₂) := by
  obtain ⟨Φ, hvan₁, hcoeff₁⟩ := hdeg₁
  obtain ⟨Ψ, hvan₂, hcoeff₂⟩ := hdeg₂
  refine ⟨Φ.tensor Ψ, ?_, ?_⟩
  · intro k hk
    rw [PolyFamily.tensor_coeff_expand]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    by_cases h : p.1 < h₁
    · rw [hvan₁ p.1 h, map_zero, LinearMap.zero_apply]; rfl
    · push_neg at h
      have hp2 : p.2 < h₂ := by omega
      rw [hvan₂ p.2 hp2, map_zero]; rfl
  · rw [PolyFamily.tensor_coeff_expand, Finset.sum_eq_single (h₁, h₂)]
    · rw [hcoeff₁, hcoeff₂]; rfl
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      by_cases h : p.1 < h₁
      · rw [hvan₁ p.1 h, map_zero, LinearMap.zero_apply]
      · push_neg at h
        have hp2 : p.2 < h₂ := by
          by_contra h2; push_neg at h2
          exact hne (Prod.ext (by omega) (by omega))
        rw [hvan₂ p.2 hp2, map_zero]
    · intro hmem; exfalso; exact hmem (Finset.mem_antidiagonal.mpr rfl)

/-- Degeneration is preserved by a restriction on the smaller (left) side.
Used to establish well-definedness on the `Tensor K d` quotient. -/
theorem DegeneratesOfOrder.of_restrict_left {X X' Y : TensorObj K d} {h : ℕ}
    (hRes : Restrict X' X) (hdeg : X.DegeneratesOfOrder Y h) :
    X'.DegeneratesOfOrder Y h := by
  obtain ⟨f, hf⟩ := hRes
  obtain ⟨Φ, hvan, hcoeff⟩ := hdeg
  refine ⟨⟨fun i => (Φ.A i).mapRange (fun L => (f i).comp L) (by simp)⟩, ?_, ?_⟩
  · intro k hk
    have : (PolyFamily.mk fun i => (Φ.A i).mapRange (fun L => (f i).comp L)
        (by simp) : PolyFamily X' Y).coeff k = liftMap f (Φ.coeff k) := by
      unfold PolyFamily.coeff
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.mapRange_apply]
      rw [← liftMap_comp]
    rw [this, hvan k hk, map_zero]
  · have : (PolyFamily.mk fun i => (Φ.A i).mapRange (fun L => (f i).comp L)
        (by simp) : PolyFamily X' Y).coeff h = liftMap f (Φ.coeff h) := by
      unfold PolyFamily.coeff
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.mapRange_apply]
      rw [← liftMap_comp]
    rw [this, hcoeff, hf]

/-- Degeneration is preserved by a restriction on the bigger (right) side. -/
theorem DegeneratesOfOrder.of_restrict_right {X Y Y' : TensorObj K d} {h : ℕ}
    (hRes : Restrict Y Y') (hdeg : X.DegeneratesOfOrder Y h) :
    X.DegeneratesOfOrder Y' h := by
  obtain ⟨g, hg⟩ := hRes
  obtain ⟨Φ, hvan, hcoeff⟩ := hdeg
  refine ⟨⟨fun i => (Φ.A i).mapRange (fun L => L.comp (g i)) (by simp)⟩, ?_, ?_⟩
  · intro k hk
    have : (PolyFamily.mk fun i => (Φ.A i).mapRange (fun L => L.comp (g i))
        (by simp) : PolyFamily X Y').coeff k = Φ.coeff k := by
      unfold PolyFamily.coeff
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.mapRange_apply]
      rw [← liftMap_comp, hg]
    rw [this]; exact hvan k hk
  · have : (PolyFamily.mk fun i => (Φ.A i).mapRange (fun L => L.comp (g i))
        (by simp) : PolyFamily X Y').coeff h = Φ.coeff h := by
      unfold PolyFamily.coeff
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.mapRange_apply]
      rw [← liftMap_comp, hg]
    rw [this, hcoeff]

/-! ### Closure properties of `Degenerates` (unindexed form) -/

theorem Degenerates.refl (X : TensorObj K d) : Degenerates X X :=
  ⟨0, DegeneratesOfOrder.refl X⟩

theorem Degenerates.add_right {X Y Z : TensorObj K d}
    (hdeg : Degenerates X Y) :
    Degenerates (X + Z) (Y + Z) :=
  hdeg.imp fun _ h' => h'.add_right

theorem Degenerates.mul_right {X Y Z : TensorObj K d}
    (hdeg : Degenerates X Y) :
    Degenerates (X * Z) (Y * Z) :=
  hdeg.imp fun _ h' => h'.mul_right

theorem Degenerates.trans {X Y Z : TensorObj K d}
    (hXY : Degenerates X Y) (hYZ : Degenerates Y Z) :
    Degenerates X Z := by
  obtain ⟨h₁, hXY⟩ := hXY
  obtain ⟨h₂, hYZ⟩ := hYZ
  exact ⟨h₁ * h₂ + h₁ + h₂, hXY.trans hYZ⟩

theorem Degenerates.mul {X₁ Y₁ X₂ Y₂ : TensorObj K d}
    (hdeg₁ : Degenerates X₁ Y₁) (hdeg₂ : Degenerates X₂ Y₂) :
    Degenerates (X₁ * X₂) (Y₁ * Y₂) := by
  obtain ⟨h₁, hdeg₁⟩ := hdeg₁
  obtain ⟨h₂, hdeg₂⟩ := hdeg₂
  exact ⟨h₁ + h₂, hdeg₁.mul hdeg₂⟩

/-! ### Fold lemma: a sum of restrictions gives a restriction from iterated direct sums -/

/-- Binary fold: if `X.t = t₁ + t₂` (in the same `PiTensorProduct`) then
`Restrict X (⟨X.V, t₁⟩ + ⟨X.V, t₂⟩)` via the codiagonal `(id, id)`. -/
theorem restrict_of_t_add {X : TensorObj K d}
    {t₁ t₂ : PiTensorProduct K X.V} (ht : X.t = t₁ + t₂) :
    Restrict X (⟨X.V, t₁⟩ + ⟨X.V, t₂⟩) := by
  refine ⟨fun i => LinearMap.id.coprod LinearMap.id, ?_⟩
  change liftMap _ ((⟨X.V, t₁⟩ + ⟨X.V, t₂⟩ : TensorObj K d).t) = X.t
  simp only [add_t]
  let f := liftMap (fun (i : Fin d) =>
    (LinearMap.id : X.V i →ₗ[K] X.V i).coprod (LinearMap.id : X.V i →ₗ[K] X.V i))
  show f _ = _
  rw [map_add f]
  have h1 : f (liftMap (fun i => LinearMap.inl K (X.V i) (X.V i)) t₁) = t₁ := by
    show liftMap _ (liftMap _ t₁) = t₁
    rw [liftMap_comp]; simp only [LinearMap.coprod_inl]; exact liftMap_id ⟨X.V, t₁⟩
  have h2 : f (liftMap (fun i => LinearMap.inr K (X.V i) (X.V i)) t₂) = t₂ := by
    show liftMap _ (liftMap _ t₂) = t₂
    rw [liftMap_comp]; simp only [LinearMap.coprod_inr]; exact liftMap_id ⟨X.V, t₂⟩
  rw [h1, h2, ht]

/-! ### Border-rank characterization via `diagObj` -/

open PiTensorProduct in
/-- The `T^k` coefficient of a `PolyFamily X (Tensor.diagObj r)` expands as a
sum of pure tensors indexed by `Fin r` and antidiagonal tuples. -/
theorem PolyFamily.coeff_diagObj_expand {X : TensorObj.{u, u} K d} {r : ℕ}
    (Φ : PolyFamily X (Tensor.diagObj r)) (k : ℕ) :
    Φ.coeff k = ∑ j : Fin r,
      (Finset.Nat.antidiagonalTuple d k).sum
        (fun m => tprod K (fun i => Φ.A i (m i) (Pi.single j 1))) := by
  unfold coeff
  have : (Tensor.diagObj (K := K) (d := d) r).t =
      ∑ j : Fin r, tprod K (fun (_ : Fin d) => Pi.single j (1 : K)) := rfl
  simp_rw [this]
  rw [Finset.sum_congr rfl (fun m _ => map_sum (liftMap fun i => (Φ.A i) (m i))
    (fun j : Fin r => PiTensorProduct.tprod K fun _ => Pi.single j (1 : K)) Finset.univ),
    Finset.sum_comm]
  congr 1; ext j; congr 1; ext m
  exact liftMap_tprod _ _

open PiTensorProduct in
/-- `DegeneratesOfOrder X (diagObj r) h` iff there exist finitely-supported
polynomial vectors `v j i : ℕ →₀ X.V i` (for `j < r`, `i < d`) such that the
`T^k` coefficient `∑_j ∑_{m : ∑ mᵢ = k} ⊗ᵢ v(j,i,mᵢ)` vanishes for `k < h`
and equals `X.t` at `k = h`. -/
theorem degeneratesOfOrder_diagObj_iff {X : TensorObj.{u, u} K d} {r h : ℕ} :
    DegeneratesOfOrder X (Tensor.diagObj r) h ↔
    ∃ v : Fin r → ∀ i : Fin d, ℕ →₀ X.V i,
      (∀ k, k < h → ∑ j : Fin r, (Finset.Nat.antidiagonalTuple d k).sum
        (fun m => tprod K (fun i => (v j i) (m i))) = 0) ∧
      (∑ j : Fin r, (Finset.Nat.antidiagonalTuple d h).sum
        (fun m => tprod K (fun i => (v j i) (m i))) = X.t) := by
  constructor
  · rintro ⟨Φ, hvan, hlead⟩
    refine ⟨fun j i => (Φ.A i).mapRange (· (Pi.single j 1))
      (LinearMap.zero_apply _), ?_, ?_⟩
    · intro k hk
      simp only [Finsupp.mapRange_apply, ← Φ.coeff_diagObj_expand]
      exact hvan k hk
    · simp only [Finsupp.mapRange_apply, ← Φ.coeff_diagObj_expand]
      exact hlead
  · rintro ⟨v, hvan, hlead⟩
    have hsup : ∀ i k, ((Pi.basisFun K (Fin r)).constr K (fun j => v j i k) :
        (Tensor.diagObj (K := K) (d := d) r).V i →ₗ[K] X.V i) ≠ 0 →
        k ∈ Finset.univ.biUnion (fun j => (v j i).support) := by
      intro i k hne; rw [Finset.mem_biUnion]
      by_contra hall; push_neg at hall
      exact hne (by
        have : (fun j => v j i k) = 0 :=
          funext fun j => Finsupp.notMem_support_iff.mp (hall j (Finset.mem_univ j))
        rw [this]; exact map_zero _)
    let Φ : PolyFamily X (Tensor.diagObj r) :=
      ⟨fun i => Finsupp.onFinset _ _ (hsup i)⟩
    have hcoeff : ∀ k, Φ.coeff k = ∑ j : Fin r,
        (Finset.Nat.antidiagonalTuple d k).sum
          (fun m => tprod K (fun i => (v j i) (m i))) := by
      intro k; rw [Φ.coeff_diagObj_expand]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
      show tprod K (fun i => ((Pi.basisFun K (Fin r)).constr K
        (fun j' => v j' i (m i))) (Pi.single j 1)) = _
      congr 1; funext i
      conv_lhs => rw [show Pi.single j (1 : K) = (Pi.basisFun K (Fin r)) j from
        (Pi.basisFun_apply K (Fin r) j).symm]
      exact Module.Basis.constr_basis (Pi.basisFun K (Fin r)) K _ j
    exact ⟨Φ, fun k hk => (hcoeff k).trans (hvan k hk),
      (hcoeff h).trans hlead⟩

end TensorObj

namespace Tensor

open TensorObj

variable {K : Type u} [Field K] {d : ℕ} [Fact (1 < d)]

/-- `DegeneratesOfOrder` descended to `Tensor K d`.  Well-definedness uses
`DegeneratesOfOrder.of_restrict_{left,right}` through the mutual-restriction
setoid. -/
def DegeneratesOfOrder (x y : Tensor K d) (h : ℕ) : Prop :=
  Quotient.liftOn₂ x y (fun X Y => TensorObj.DegeneratesOfOrder X Y h)
    (fun _ _ _ _ ⟨hXX', hX'X⟩ ⟨hYY', hY'Y⟩ => propext
      ⟨fun hdeg => (hdeg.of_restrict_left hX'X).of_restrict_right hYY',
       fun hdeg => (hdeg.of_restrict_left hXX').of_restrict_right hY'Y⟩)

/-- Border-restriction on the quotient: there is some order `h` witnessing
degeneration. -/
def Degenerates (x y : Tensor K d) : Prop :=
  ∃ h, DegeneratesOfOrder x y h

/-! ### Fact 1 on the quotient -/

/-- Restriction (i.e. `≤`) implies degeneration of order `0`. -/
theorem Restrict.degeneratesOfOrder {x y : Tensor K d} (hRes : x ≤ y) :
    DegeneratesOfOrder x y 0 := by
  induction x using Quotient.inductionOn with | h X => ?_
  induction y using Quotient.inductionOn with | h Y => ?_
  exact TensorObj.Restrict.degeneratesOfOrder hRes

theorem Restrict.degenerates {x y : Tensor K d} (hRes : x ≤ y) :
    Degenerates x y :=
  ⟨0, Restrict.degeneratesOfOrder hRes⟩

/-! ### Closure properties on the quotient -/

theorem DegeneratesOfOrder.refl (x : Tensor K d) : DegeneratesOfOrder x x 0 := by
  induction x using Quotient.inductionOn with | h X => ?_
  exact TensorObj.DegeneratesOfOrder.refl X

theorem DegeneratesOfOrder.add_right {x y z : Tensor K d} {h : ℕ}
    (hdeg : DegeneratesOfOrder x y h) :
    DegeneratesOfOrder (x + z) (y + z) h := by
  induction x using Quotient.inductionOn with | h X => ?_
  induction y using Quotient.inductionOn with | h Y => ?_
  induction z using Quotient.inductionOn with | h Z => ?_
  exact TensorObj.DegeneratesOfOrder.add_right hdeg

theorem DegeneratesOfOrder.mul_right {x y z : Tensor K d} {h : ℕ}
    (hdeg : DegeneratesOfOrder x y h) :
    DegeneratesOfOrder (x * z) (y * z) h := by
  induction x using Quotient.inductionOn with | h X => ?_
  induction y using Quotient.inductionOn with | h Y => ?_
  induction z using Quotient.inductionOn with | h Z => ?_
  exact TensorObj.DegeneratesOfOrder.mul_right hdeg

theorem DegeneratesOfOrder.trans {x y z : Tensor K d} {h₁ h₂ : ℕ}
    (hxy : x.DegeneratesOfOrder y h₁) (hyz : y.DegeneratesOfOrder z h₂) :
    x.DegeneratesOfOrder z (h₁ * h₂ + h₁ + h₂) := by
  induction x using Quotient.inductionOn with | h X => ?_
  induction y using Quotient.inductionOn with | h Y => ?_
  induction z using Quotient.inductionOn with | h Z => ?_
  exact TensorObj.DegeneratesOfOrder.trans hxy hyz

theorem DegeneratesOfOrder.mul {x₁ y₁ x₂ y₂ : Tensor K d} {h₁ h₂ : ℕ}
    (hdeg₁ : x₁.DegeneratesOfOrder y₁ h₁) (hdeg₂ : x₂.DegeneratesOfOrder y₂ h₂) :
    (x₁ * x₂).DegeneratesOfOrder (y₁ * y₂) (h₁ + h₂) := by
  induction x₁ using Quotient.inductionOn with | h X₁ => ?_
  induction y₁ using Quotient.inductionOn with | h Y₁ => ?_
  induction x₂ using Quotient.inductionOn with | h X₂ => ?_
  induction y₂ using Quotient.inductionOn with | h Y₂ => ?_
  exact TensorObj.DegeneratesOfOrder.mul hdeg₁ hdeg₂

theorem DegeneratesOfOrder.of_restrict_left {x x' y : Tensor K d} {h : ℕ}
    (hRes : x' ≤ x) (hdeg : DegeneratesOfOrder x y h) :
    DegeneratesOfOrder x' y h := by
  induction x using Quotient.inductionOn with | h X => ?_
  induction x' using Quotient.inductionOn with | h X' => ?_
  induction y using Quotient.inductionOn with | h Y => ?_
  exact TensorObj.DegeneratesOfOrder.of_restrict_left hRes hdeg

theorem DegeneratesOfOrder.of_restrict_right {x y y' : Tensor K d} {h : ℕ}
    (hRes : y ≤ y') (hdeg : DegeneratesOfOrder x y h) :
    DegeneratesOfOrder x y' h := by
  induction x using Quotient.inductionOn with | h X => ?_
  induction y using Quotient.inductionOn with | h Y => ?_
  induction y' using Quotient.inductionOn with | h Y' => ?_
  exact TensorObj.DegeneratesOfOrder.of_restrict_right hRes hdeg

open PiTensorProduct in
/-- **Border-rank characterization**: `DegeneratesOfOrder ⟦X⟧ r h` iff there
exist finitely-supported polynomial vectors `v j i : ℕ →₀ X.V i` such that the
`T^k` coefficient vanishes for `k < h` and the `T^h` coefficient equals `X.t`.
This is the degeneration analog of `tensor_le_natCast_iff`. -/
theorem tensor_degeneratesOfOrder_natCast_iff
    {X : TensorObj.{u, u} K d} {r : ℕ} {h : ℕ} :
    DegeneratesOfOrder (toTensor X) (r : Tensor.{u, u} K d) h ↔
    ∃ v : Fin r → ∀ i : Fin d, ℕ →₀ X.V i,
      (∀ k, k < h → ∑ j : Fin r, (Finset.Nat.antidiagonalTuple d k).sum
        (fun m => tprod K (fun i => (v j i) (m i))) = 0) ∧
      (∑ j : Fin r, (Finset.Nat.antidiagonalTuple d h).sum
        (fun m => tprod K (fun i => (v j i) (m i))) = X.t) := by
  constructor
  · intro hdeg
    have hdeg' : TensorObj.DegeneratesOfOrder X (diagObj r) h :=
      DegeneratesOfOrder.of_restrict_right (natCast_le_diagObj r) hdeg
    exact TensorObj.degeneratesOfOrder_diagObj_iff.mp hdeg'
  · intro hv
    show DegeneratesOfOrder (toTensor X) (r : Tensor K d) h
    exact DegeneratesOfOrder.of_restrict_right (diagObj_le_natCast r)
      (TensorObj.degeneratesOfOrder_diagObj_iff.mpr hv)

theorem Degenerates.refl (x : Tensor K d) : Degenerates x x :=
  ⟨0, DegeneratesOfOrder.refl x⟩

theorem Degenerates.add_right {x y z : Tensor K d}
    (hdeg : Degenerates x y) :
    Degenerates (x + z) (y + z) :=
  hdeg.imp fun _ h' => h'.add_right

theorem Degenerates.mul_right {x y z : Tensor K d}
    (hdeg : Degenerates x y) :
    Degenerates (x * z) (y * z) :=
  hdeg.imp fun _ h' => h'.mul_right

theorem Degenerates.trans {x y z : Tensor K d}
    (hxy : x.Degenerates y) (hyz : y.Degenerates z) :
    x.Degenerates z := by
  obtain ⟨h₁, hxy⟩ := hxy
  obtain ⟨h₂, hyz⟩ := hyz
  exact ⟨h₁ * h₂ + h₁ + h₂, hxy.trans hyz⟩

theorem Degenerates.mul {x₁ y₁ x₂ y₂ : Tensor K d}
    (hdeg₁ : x₁.Degenerates y₁) (hdeg₂ : x₂.Degenerates y₂) :
    (x₁ * x₂).Degenerates (y₁ * y₂) := by
  obtain ⟨h₁, hdeg₁⟩ := hdeg₁
  obtain ⟨h₂, hdeg₂⟩ := hdeg₂
  exact ⟨h₁ + h₂, hdeg₁.mul hdeg₂⟩

/-! ### Fact 2a: degeneration gives a restriction inequality -/

/-- If `X.t = ∑ j ∈ S, liftMap (g j) Y.t`, then `⟦X⟧ ≤ |S| * ⟦Y⟧`. -/
private theorem sum_liftMap_restrict_le {X Y : TensorObj K d}
    {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {g : ι → ∀ i, Y.V i →ₗ[K] X.V i}
    (hX : X.t = ∑ j ∈ S, liftMap (g j) Y.t) :
    (toTensor X : Tensor K d) ≤ S.card * toTensor Y := by
  induction S using Finset.induction_on generalizing X with
  | empty =>
    simp only [Finset.sum_empty] at hX
    have : toTensor X = 0 := by
      apply Quotient.sound
      show tensorSetoid K d |>.r X (TensorObj.zeroObj)
      constructor
      · exact ⟨fun _ => 0, by simp only [TensorObj.zeroObj, hX]; exact (liftMap _).map_zero⟩
      · exact ⟨fun _ => 0, by simp only [TensorObj.zeroObj, hX]; exact (liftMap _).map_zero⟩
    simp [this]
  | @insert a s has ih =>
    rw [Finset.sum_insert has] at hX
    have hfold := restrict_of_t_add hX
    have hle_a : (toTensor ⟨X.V, liftMap (g a) Y.t⟩ : Tensor K d) ≤ toTensor Y := ⟨g a, rfl⟩
    have hle_rest := ih (X := ⟨X.V, ∑ j ∈ s, liftMap (g j) Y.t⟩) rfl
    let ta := toTensor (K := K) (d := d) ⟨X.V, liftMap (g a) Y.t⟩
    let tr := toTensor (K := K) (d := d) ⟨X.V, ∑ j ∈ s, liftMap (g j) Y.t⟩
    have step1 : ta + tr ≤ toTensor Y + tr :=
      instSemiringPreorder.add_right _ _ hle_a _
    have step2 : toTensor Y + tr ≤ toTensor Y + (↑s.card * toTensor Y) := by
      rw [add_comm (toTensor Y) tr, add_comm (toTensor Y)]
      exact instSemiringPreorder.add_right _ _ hle_rest _
    calc toTensor X
        ≤ ta + tr := hfold
      _ ≤ toTensor Y + (↑s.card * toTensor Y) := le_trans step1 step2
      _ = (↑(insert a s).card) * toTensor Y := by
            rw [Finset.card_insert_of_notMem has]; push_cast; ring

/-- From a degeneration of order `h`, extract the restriction inequality
`x ≤ c * y` where `c = |antidiagonalTuple d h|`. -/
theorem DegeneratesOfOrder.restrict_le {x y : Tensor K d} {h : ℕ}
    (hdeg : DegeneratesOfOrder x y h) :
    instStrassenPreorder.le x ((Finset.Nat.antidiagonalTuple d h).card * y) := by
  induction x using Quotient.inductionOn with | h X => ?_
  induction y using Quotient.inductionOn with | h Y => ?_
  obtain ⟨Φ, _, hcoeff⟩ := hdeg
  exact sum_liftMap_restrict_le (by rw [← hcoeff]; rfl)

universe v' in
/-- Tensor power of a degeneration: orders multiply. -/
theorem DegeneratesOfOrder.pow {x y : Tensor.{u, v'} K d} {h : ℕ}
    (hdeg : DegeneratesOfOrder x y h) :
    ∀ n : ℕ, DegeneratesOfOrder (x ^ n) (y ^ n) (n * h)
  | 0 => by simp only [Nat.zero_mul, pow_zero]; exact DegeneratesOfOrder.refl 1
  | n + 1 => by
    rw [pow_succ, pow_succ, show (n + 1) * h = n * h + h from by ring]
    exact (hdeg.pow n).mul hdeg

/-! ### Fact 2b -/

/-- `(n + 1) ^ k` is subexponential for any fixed `k`. -/
private theorem IsSubexponential_pow_linear :
    ∀ k : ℕ, IsSubexponential (fun n => (n + 1) ^ k)
  | 0 => by simpa using IsSubexponential.const 1
  | k + 1 => by
    have : (fun n => (n + 1) ^ (k + 1)) = fun n => (n + 1) ^ k * (n + 1) := by
      ext n; exact pow_succ (n + 1) k
    rw [this]
    exact (IsSubexponential_pow_linear k).mul IsSubexponential.linear

/-- The cardinality of `antidiagonalTuple d k` is bounded by `(k + 1) ^ d`. -/
private theorem card_antidiagonalTuple_le (d k : ℕ) :
    (Finset.Nat.antidiagonalTuple d k).card ≤ (k + 1) ^ d := by
  calc (Finset.Nat.antidiagonalTuple d k).card
      ≤ (Fintype.piFinset (fun _ : Fin d => Finset.range (k + 1))).card := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.Nat.mem_antidiagonalTuple] at hj
        simp only [Fintype.mem_piFinset, Finset.mem_range]
        intro i
        exact Nat.lt_succ_of_le
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i) |>.trans hj.le)
    _ = (k + 1) ^ d := by simp [Fintype.card_piFinset]

/-- Fact 2b: degeneration implies asymptotic restriction.  The multiplier
`|antidiagonalTuple d (n * h)|` is at most `(n * h + 1) ^ d`, which is
subexponential in `n`. -/
theorem Degenerates.asymptoticLe {X Y : Tensor K d}
    (hdeg : Degenerates X Y) :
    AsymptoticLe Tensor.instStrassenPreorder X Y := by
  obtain ⟨h, hdeg⟩ := hdeg
  refine ⟨fun n => (n * h + 1) ^ d, ?_, fun n => ?_⟩
  · -- Subexponential: bound (n*h+1)^d ≤ (n+1)^d * (h+1)^d
    have hsub := (IsSubexponential_pow_linear d).mul (IsSubexponential.const ((h + 1) ^ d))
    intro ε hε
    filter_upwards [hsub ε hε] with n hn
    have hle : ((n * h + 1) ^ d : ℕ) ≤ (n + 1) ^ d * (h + 1) ^ d := by
      rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left (by nlinarith) d
    exact (Nat.cast_le.mpr hle).trans hn
  · -- Restriction inequality from degeneration of tensor powers
    show X ^ n ≤ ↑((n * h + 1) ^ d) * Y ^ n
    have hrestr := (hdeg.pow n).restrict_le
    have hcard_le : ((Finset.Nat.antidiagonalTuple d (n * h)).card : Tensor K d) ≤
        ↑((n * h + 1) ^ d) :=
      (instStrassenPreorder.nat_order_embedding _ _).mpr (card_antidiagonalTuple_le d _)
    exact le_trans hrestr (instSemiringPreorder.mul_right _ _ hcard_le (Y ^ n))

/-! ### Degeneration as a `StrassenPreorder` on `Tensor K d`

`Tensor.Degenerates` is packaged as a `StrassenPreorder`.  All closure
axioms except `nat_order_embedding` follow either from the closure properties
already proved in this file or — for `zero_le`, `lower_archimedean`,
`upper_archimedean` — from `Tensor.instStrassenPreorder` via
`Restrict.degenerates` (restriction implies degeneration).

The `nat_order_embedding` field is the only one that genuinely needs the
bridge `Degenerates.asymptoticLe` between degeneration and asymptotic
restriction. -/

/-- `Tensor.Degenerates` packaged as a `StrassenPreorder` on `Tensor K d`.

Note: `Tensor K d` already carries a `Preorder` instance whose `≤` is
`Restrict`, so we must explicitly supply the `lt` and `lt_iff_le_not_ge`
fields (the default would try to identify the new `le = Degenerates`
with the ambient `<` coming from `Restrict`). -/
noncomputable def strassenPreorderOfDegenerates :
    StrassenPreorder (Tensor K d) where
  le := Degenerates
  lt a b := Degenerates a b ∧ ¬ Degenerates b a
  le_refl := Degenerates.refl
  le_trans _ _ _ := Degenerates.trans
  lt_iff_le_not_ge _ _ := Iff.rfl
  add_right _ _ h _ := h.add_right
  mul_right _ _ h _ := h.mul_right
  zero_le a := Restrict.degenerates (instStrassenPreorder.zero_le a)
  nat_order_embedding n m := by
    refine ⟨fun hdeg => ?_, fun hle => ?_⟩
    · exact (AsymptoticLe.nat_order_embedding instStrassenPreorder n m).mp
        hdeg.asymptoticLe
    · exact Restrict.degenerates
        ((instStrassenPreorder.nat_order_embedding n m).mpr hle)
  lower_archimedean a := by
    rcases instStrassenPreorder.lower_archimedean a with h | h
    · exact Or.inl h
    · exact Or.inr (Restrict.degenerates h)
  upper_archimedean a := by
    obtain ⟨n, h⟩ := instStrassenPreorder.upper_archimedean a
    exact ⟨n, Restrict.degenerates h⟩

/-- Restriction refines into degeneration: as `StrassenPreorder`s on
`Tensor K d`, the restriction preorder is `≤` the degeneration preorder. -/
theorem restrict_le_degenerates :
    (instStrassenPreorder : StrassenPreorder (Tensor K d)) ≤
      strassenPreorderOfDegenerates :=
  fun _ _ h => Restrict.degenerates h

/-! ### Asymptotic closures coincide

Both directions go through `StrassenPreorder.asymptoticClosure_le_of_isClosed`
combined with `StrassenPreorder.asymptoticClosure_isClosed`:

* `strassenPreorderOfDegenerates.asymptoticClosure ≤ instStrassenPreorder.asymptoticClosure`:
  follows from `Degenerates.asymptoticLe` (degeneration ⊆ AC of restriction).
* `instStrassenPreorder.asymptoticClosure ≤ strassenPreorderOfDegenerates.asymptoticClosure`:
  follows from `Restrict.degenerates` and `AsymptoticLe.of_le` (restriction ⊆ AC
  of degeneration). -/
theorem asymptoticClosure_degenerates_eq :
    strassenPreorderOfDegenerates.asymptoticClosure =
      (instStrassenPreorder : StrassenPreorder (Tensor K d)).asymptoticClosure := by
  apply le_antisymm
  · apply StrassenPreorder.asymptoticClosure_le_of_isClosed
    · intro x y hdeg
      exact hdeg.asymptoticLe
    · exact StrassenPreorder.asymptoticClosure_isClosed _
  · apply StrassenPreorder.asymptoticClosure_le_of_isClosed
    · intro x y hres
      exact AsymptoticLe.of_le _ (Restrict.degenerates hres)
    · exact StrassenPreorder.asymptoticClosure_isClosed _

end Tensor
