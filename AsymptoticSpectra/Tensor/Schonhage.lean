import AsymptoticSpectra.Tensor.MatrixMult
import AsymptoticSpectra.Tensor.Degeneration

universe u

open TensorObj PiTensorProduct BigOperators TensorProduct Finset

namespace Tensor

variable {K : Type u} [Field K]

/-! ## Schönhage's direct sum construction

We prove that for `n, m ≥ 2`, the tensor `MM(n,1,m) + MM(1,(n-1)(m-1),1)` has
border rank at most `nm + 1`, via an explicit degeneration of order 2.
-/

section Setup

variable (K) (n m : ℕ)

private noncomputable abbrev X_obj : TensorObj.{u, u} K 3 :=
  MMObj n 1 m + MMObj 1 ((n - 1) * (m - 1)) 1

private abbrev k_dim : ℕ := (n - 1) * (m - 1)

private noncomputable def encode (i : Fin (n - 1)) (j : Fin (m - 1)) :
    Fin (k_dim n m) :=
  finProdFinEquiv (i, j)

end Setup

section BasisElements

variable (K) (n m : ℕ)

private noncomputable def basisA (i : Fin n) :
    (X_obj K n m).V ⟨0, by omega⟩ :=
  (Pi.single (i, (0 : Fin 1)) 1, 0)

private noncomputable def basisX (i : Fin (n - 1)) (j : Fin (m - 1)) :
    (X_obj K n m).V ⟨0, by omega⟩ :=
  (0, Pi.single ((0 : Fin 1), encode n m i j) 1)

private noncomputable def basisB (j : Fin m) :
    (X_obj K n m).V ⟨1, by omega⟩ :=
  (Pi.single ((0 : Fin 1), j) 1, 0)

private noncomputable def basisY (i : Fin (n - 1)) (j : Fin (m - 1)) :
    (X_obj K n m).V ⟨1, by omega⟩ :=
  (0, Pi.single (encode n m i j, (0 : Fin 1)) 1)

private noncomputable def basisC (j : Fin m) (i : Fin n) :
    (X_obj K n m).V ⟨2, by omega⟩ :=
  (Pi.single (j, i) 1, 0)

private noncomputable def basisZ :
    (X_obj K n m).V ⟨2, by omega⟩ :=
  (0, Pi.single ((0 : Fin 1), (0 : Fin 1)) 1)

end BasisElements

section PolyVectors

variable (K) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)

private noncomputable def polyVecMain (i₀ : Fin n) (j₀ : Fin m)
    (s : Fin 3) : ℕ →₀ (X_obj K n m).V s :=
  match s with
  | ⟨0, _⟩ =>
    Finsupp.single 0 (basisA K n m i₀) +
    if hi : i₀.val < n - 1 then
      if hj : j₀.val < m - 1 then
        Finsupp.single 1 (basisX K n m ⟨i₀.val, hi⟩ ⟨j₀.val, hj⟩)
      else 0
    else
      if hj : j₀.val < m - 1 then
        Finsupp.single 1 (-(∑ i : Fin (n - 1), basisX K n m i ⟨j₀.val, hj⟩))
      else 0
  | ⟨1, _⟩ =>
    Finsupp.single 0 (basisB K n m j₀) +
    if hi : i₀.val < n - 1 then
      if hj : j₀.val < m - 1 then
        Finsupp.single 1 (basisY K n m ⟨i₀.val, hi⟩ ⟨j₀.val, hj⟩)
      else
        Finsupp.single 1 (-(∑ j : Fin (m - 1), basisY K n m ⟨i₀.val, hi⟩ j))
    else 0
  | ⟨2, _⟩ =>
    Finsupp.single 0 (basisZ K n m) + Finsupp.single 2 (basisC K n m j₀ i₀)

private noncomputable def polyVecCorr
    (s : Fin 3) : ℕ →₀ (X_obj K n m).V s :=
  match s with
  | ⟨0, _⟩ => Finsupp.single 0 (-(∑ i : Fin n, basisA K n m i))
  | ⟨1, _⟩ => Finsupp.single 0 (∑ j : Fin m, basisB K n m j)
  | ⟨2, _⟩ => Finsupp.single 0 (basisZ K n m)

private noncomputable def indexEquiv :
    (Fin n × Fin m) ⊕ Unit ≃ Fin (n * m + 1) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.equivPUnit (Fin 1)).symm).trans
    finSumFinEquiv

private noncomputable def polyVec :
    Fin (n * m + 1) → ∀ s : Fin 3, ℕ →₀ (X_obj K n m).V s :=
  fun j =>
    match (indexEquiv n m).symm j with
    | Sum.inl (i₀, j₀) => polyVecMain K n m i₀ j₀
    | Sum.inr () => polyVecCorr K n m

end PolyVectors

section ProofHelpers

variable (K : Type u) [Field K] (n m : ℕ)

private lemma polyVec_inl (p : Fin n × Fin m) :
    polyVec K n m (indexEquiv n m (Sum.inl p)) = polyVecMain K n m p.1 p.2 := by
  simp only [polyVec, Equiv.symm_apply_apply]

private lemma polyVec_inr (u : Unit) :
    polyVec K n m (indexEquiv n m (Sum.inr u)) = polyVecCorr K n m := by
  cases u; simp only [polyVec, Equiv.symm_apply_apply]

end ProofHelpers

section MainTheorem

variable {n m : ℕ}

private lemma schonhage_t0 :
    (∑ j : Fin (n * m + 1), ∑ m_1 ∈ Nat.antidiagonalTuple 3 0,
      ⨂ₜ[K] (i : Fin 3), (polyVec K n m j i) (m_1 i)) = 0 := by
  simp only [Nat.antidiagonalTuple_zero_right, sum_singleton, Pi.zero_apply]
  rw [← Equiv.sum_comp (indexEquiv n m), Fintype.sum_sum_type]
  simp only [polyVec_inl, polyVec_inr]
  simp only [Finset.univ_unique, sum_singleton]
  set v₀ : ∀ i : Fin 3, (X_obj K n m).V i := fun i =>
    match i with
    | ⟨0, _⟩ => ∑ i₀ : Fin n, basisA K n m i₀
    | ⟨1, _⟩ => ∑ j₀ : Fin m, basisB K n m j₀
    | ⟨2, _⟩ => basisZ K n m with hv₀
  have h_main : (∑ x : Fin n × Fin m,
      ⨂ₜ[K] (i : Fin 3), (polyVecMain K n m x.1 x.2 i) 0) = tprod K v₀ := by
    -- Helper: evaluate (polyVecMain i₀ j₀ s) at 0 for each mode
    -- Auxiliary to close `x + 0 = x` on the product V-type
    have h_az : ∀ (s : Fin 3) (x : (X_obj K n m).V s), x + 0 = x := fun _ x => AddMonoid.add_zero x
    have h_eval0 : ∀ i₀ j₀, (polyVecMain K n m i₀ j₀ ⟨0, by omega⟩) 0 = basisA K n m i₀ := by
      intro i₀ j₀; simp only [polyVecMain]
      rw [Finsupp.add_apply, Finsupp.single_eq_same]
      split <;> split
      all_goals first
        | (rw [Finsupp.single_apply, if_neg (by omega)]; exact h_az _ _)
        | (rw [Finsupp.zero_apply]; exact h_az _ _)
    have h_eval1 : ∀ i₀ j₀, (polyVecMain K n m i₀ j₀ ⟨1, by omega⟩) 0 = basisB K n m j₀ := by
      intro i₀ j₀; simp only [polyVecMain]
      rw [Finsupp.add_apply, Finsupp.single_eq_same]
      split
      · split <;> (rw [Finsupp.single_apply, if_neg (by omega)]; exact h_az _ _)
      · rw [Finsupp.zero_apply]; exact h_az _ _
    have h_eval2 : ∀ i₀ j₀, (polyVecMain K n m i₀ j₀ ⟨2, by omega⟩) 0 = basisZ K n m := by
      intro i₀ j₀; simp only [polyVecMain]
      rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, if_neg (by omega)]
      exact h_az _ _
    -- Combine into Function.update form
    have h_eval : ∀ (i₀ : Fin n) (j₀ : Fin m),
        (fun i => (polyVecMain K n m i₀ j₀ i) 0) =
        Function.update (Function.update v₀ ⟨0, by omega⟩ (basisA K n m i₀))
          ⟨1, by omega⟩ (basisB K n m j₀) := by
      intro i₀ j₀; funext i; fin_cases i
      · rw [h_eval0, Function.update_of_ne (by decide), Function.update_self]
      · rw [h_eval1, Function.update_self]
      · rw [h_eval2, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    -- Rewrite and factor
    simp_rw [Fintype.sum_prod_type, h_eval]
    simp_rw [← (PiTensorProduct.tprod K).map_update_sum (t := Finset.univ)
      (i := (⟨1, by omega⟩ : Fin 3))]
    simp_rw [show (∑ j₀ : Fin m, basisB K n m j₀) = v₀ ⟨1, by omega⟩ from by simp [hv₀]]
    simp_rw [Function.update_comm (show (⟨0, by omega⟩ : Fin 3) ≠ ⟨1, by omega⟩ from by decide)]
    simp_rw [Function.update_eq_self]
    rw [← (PiTensorProduct.tprod K).map_update_sum (t := Finset.univ)
      (i := (⟨0, by omega⟩ : Fin 3))]
    simp_rw [show (∑ i₀ : Fin n, basisA K n m i₀) = v₀ ⟨0, by omega⟩ from by simp [hv₀]]
    rw [Function.update_eq_self]
  have h_corr : (⨂ₜ[K] (i : Fin 3), (polyVecCorr K n m i) 0) = -(tprod K v₀) := by
    have h_eq : (fun i => (polyVecCorr K n m i) 0) = Function.update v₀ ⟨0, by omega⟩ (-(v₀ ⟨0, by omega⟩)) := by
      funext i; fin_cases i <;> simp [polyVecCorr, Function.update_self, Function.update_of_ne, hv₀] <;> exact Finsupp.single_eq_same
    change (PiTensorProduct.tprod K) (fun i => (polyVecCorr K n m i) 0) = -(PiTensorProduct.tprod K) v₀
    rw [h_eq, (PiTensorProduct.tprod K).map_update_neg, Function.update_eq_self]
  rw [h_main, h_corr, add_neg_cancel]

private lemma polyVecCorr_eval_pos (s : Fin 3) {k : ℕ} (hk : 0 < k) :
    (polyVecCorr K n m s) k = 0 := by
  fin_cases s <;> simp only [polyVecCorr] <;>
    rw [Finsupp.single_apply, if_neg (by omega)]

private lemma polyVecMain_mode2_eval1 (i₀ : Fin n) (j₀ : Fin m) :
    (polyVecMain K n m i₀ j₀ ⟨2, by omega⟩) 1 = 0 := by
  simp only [polyVecMain]
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (show (0:ℕ) ≠ 1 from by omega),
      Finsupp.single_eq_of_ne' (show (2:ℕ) ≠ 1 from by omega)]
  exact AddMonoid.add_zero _

private lemma sum_mode0_eval1 (hn : 2 ≤ n) (j₀ : Fin m) :
    (∑ i₀ : Fin n, (polyVecMain K n m i₀ j₀ (0 : Fin 3)) (1 : ℕ)) = 0 := by
  have h_ev : ∀ i₀ : Fin n, (polyVecMain K n m i₀ j₀ (0 : Fin 3)) (1 : ℕ) =
      if hi : i₀.val < n - 1 then
        if hj : j₀.val < m - 1 then basisX K n m ⟨i₀.val, hi⟩ ⟨j₀.val, hj⟩ else 0
      else
        if hj : j₀.val < m - 1 then -(∑ i, basisX K n m i ⟨j₀.val, hj⟩) else 0 := by
    intro i₀; simp only [polyVecMain]
    change (Finsupp.single (0:ℕ) (basisA K n m i₀) + _) (1:ℕ) = _
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (show (0:ℕ) ≠ 1 from by omega),
        AddMonoid.zero_add]
    split <;> split <;> first | exact Finsupp.single_eq_same | exact Finsupp.zero_apply
  simp_rw [h_ev]
  by_cases hj : j₀.val < m - 1
  · simp_rw [dif_pos hj]
    have hn1 : (n - 1) + 1 = n := by omega
    rw [← Equiv.sum_comp (finCongr hn1), Fin.sum_univ_castSucc]
    have h_lt : ∀ i : Fin (n - 1),
        (if hi : (finCongr hn1 (Fin.castSucc i)).val < n - 1
          then basisX K n m ⟨(finCongr hn1 (Fin.castSucc i)).val, hi⟩ ⟨j₀.val, hj⟩
          else -(∑ i, basisX K n m i ⟨j₀.val, hj⟩)) =
        basisX K n m i ⟨j₀.val, hj⟩ := by
      intro i
      have hic : (finCongr hn1 (Fin.castSucc i)).val < n - 1 := by
        simp [finCongr, Fin.castSucc]
      rw [dif_pos hic]; congr 1
    have h_last :
        (if hi : (finCongr hn1 (Fin.last (n - 1))).val < n - 1
          then basisX K n m ⟨(finCongr hn1 (Fin.last (n - 1))).val, hi⟩ ⟨j₀.val, hj⟩
          else -(∑ i, basisX K n m i ⟨j₀.val, hj⟩)) =
        -(∑ i, basisX K n m i ⟨j₀.val, hj⟩) := by
      rw [dif_neg (by simp [finCongr, Fin.last])]
    simp_rw [h_lt]; rw [h_last]; exact add_neg_cancel _
  · simp_rw [dif_neg hj]; simp only [dite_eq_ite, ite_self, Finset.sum_const]; exact nsmul_zero _

private lemma sum_mode1_eval1 (hm : 2 ≤ m) (i₀ : Fin n) :
    (∑ j₀ : Fin m, (polyVecMain K n m i₀ j₀ (1 : Fin 3)) (1 : ℕ)) = 0 := by
  have h_ev : ∀ j₀ : Fin m, (polyVecMain K n m i₀ j₀ (1 : Fin 3)) (1 : ℕ) =
      if hi : i₀.val < n - 1 then
        if hj : j₀.val < m - 1 then basisY K n m ⟨i₀.val, hi⟩ ⟨j₀.val, hj⟩
        else -(∑ j, basisY K n m ⟨i₀.val, hi⟩ j)
      else 0 := by
    intro j₀; simp only [polyVecMain]
    change (Finsupp.single (0:ℕ) (basisB K n m j₀) + _) (1:ℕ) = _
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (show (0:ℕ) ≠ 1 from by omega),
        AddMonoid.zero_add]
    split
    · split <;> exact Finsupp.single_eq_same
    · exact Finsupp.zero_apply
  simp_rw [h_ev]
  by_cases hi : i₀.val < n - 1
  · simp_rw [dif_pos hi]
    have hm1 : (m - 1) + 1 = m := by omega
    rw [← Equiv.sum_comp (finCongr hm1), Fin.sum_univ_castSucc]
    have h_lt : ∀ j : Fin (m - 1),
        (if hj : (finCongr hm1 (Fin.castSucc j)).val < m - 1
          then basisY K n m ⟨i₀.val, hi⟩ ⟨(finCongr hm1 (Fin.castSucc j)).val, hj⟩
          else -(∑ j, basisY K n m ⟨i₀.val, hi⟩ j)) =
        basisY K n m ⟨i₀.val, hi⟩ j := by
      intro j
      have hjc : (finCongr hm1 (Fin.castSucc j)).val < m - 1 := by
        simp [finCongr, Fin.castSucc]
      rw [dif_pos hjc]; congr 1
    have h_last :
        (if hj : (finCongr hm1 (Fin.last (m - 1))).val < m - 1
          then basisY K n m ⟨i₀.val, hi⟩ ⟨(finCongr hm1 (Fin.last (m - 1))).val, hj⟩
          else -(∑ j, basisY K n m ⟨i₀.val, hi⟩ j)) =
        -(∑ j, basisY K n m ⟨i₀.val, hi⟩ j) := by
      rw [dif_neg (by simp [finCongr, Fin.last])]
    simp_rw [h_lt]; rw [h_last]; exact add_neg_cancel _
  · simp_rw [dif_neg hi]; exact Finset.sum_eq_zero (fun _ _ => rfl)

private lemma schonhage_t1 (hn : 2 ≤ n) (hm : 2 ≤ m) :
    (∑ j : Fin (n * m + 1), ∑ m_1 ∈ Nat.antidiagonalTuple 3 1,
      ⨂ₜ[K] (i : Fin 3), (polyVec K n m j i) (m_1 i)) = 0 := by
  rw [← Equiv.sum_comp (indexEquiv n m), Fintype.sum_sum_type]
  simp only [polyVec_inl, polyVec_inr, Finset.univ_unique, sum_singleton]
  -- Correction = 0: polyVecCorr only has degree 0 terms
  have h_corr : (∑ m_1 ∈ Nat.antidiagonalTuple 3 1,
      ⨂ₜ[K] (i : Fin 3), (polyVecCorr K n m i) (m_1 i)) = 0 := by
    apply Finset.sum_eq_zero; intro m1 hm1
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hm1
    have ⟨i, hi⟩ : ∃ i : Fin 3, 0 < m1 i := by
      by_contra h; push_neg at h
      have := (h 0).antisymm (Nat.zero_le _); have := (h 1).antisymm (Nat.zero_le _)
      have := (h 2).antisymm (Nat.zero_le _); omega
    exact (PiTensorProduct.tprod K).map_coord_zero i (polyVecCorr_eval_pos i hi)
  rw [h_corr]; simp
  -- Swap sums: show each antidiag tuple contributes 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero; intro m1 hm1
  rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hm1
  have h_az : ∀ (s : Fin 3) (x : (X_obj K n m).V s), x + 0 = x :=
    fun _ x => AddMonoid.add_zero x
  -- Degree 0 evaluation helpers
  have h_ev0 : ∀ i₀ j₀, (polyVecMain K n m i₀ j₀ ⟨0, by omega⟩) 0 = basisA K n m i₀ := by
    intro i₀ j₀; simp only [polyVecMain]
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
    split <;> split
    all_goals first
      | (rw [Finsupp.single_apply, if_neg (by omega)]; exact h_az _ _)
      | (rw [Finsupp.zero_apply]; exact h_az _ _)
  have h_ev1 : ∀ i₀ j₀, (polyVecMain K n m i₀ j₀ ⟨1, by omega⟩) 0 = basisB K n m j₀ := by
    intro i₀ j₀; simp only [polyVecMain]
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
    split
    · split <;> (rw [Finsupp.single_apply, if_neg (by omega)]; exact h_az _ _)
    · rw [Finsupp.zero_apply]; exact h_az _ _
  have h_ev2 : ∀ i₀ j₀, (polyVecMain K n m i₀ j₀ ⟨2, by omega⟩) 0 = basisZ K n m := by
    intro i₀ j₀; simp only [polyVecMain]
    rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, if_neg (by omega)]
    exact h_az _ _
  -- Case analysis: m1 0 + m1 1 + m1 2 = 1
  rcases Nat.eq_zero_or_pos (m1 2) with h2z | h2p
  · rcases Nat.eq_zero_or_pos (m1 1) with h1z | h1p
    · -- m1 = (1, 0, 0): cancellation in mode 0
      have h0e : m1 0 = 1 := by omega
      have h_func : ∀ (i₀ : Fin n) (j₀ : Fin m),
          (fun s => (polyVecMain K n m i₀ j₀ s) (m1 s)) =
          Function.update
            (Function.update (Function.update (0 : ∀ s : Fin 3, (X_obj K n m).V s)
              ⟨1, by omega⟩ (basisB K n m j₀)) ⟨2, by omega⟩ (basisZ K n m))
            ⟨0, by omega⟩ ((polyVecMain K n m i₀ j₀ ⟨0, by omega⟩) 1) := by
        have h1z' : m1 ⟨1, by omega⟩ = 0 := h1z
        have h2z' : m1 ⟨2, by omega⟩ = 0 := h2z
        intro i₀ j₀; funext s; fin_cases s <;> simp only []
        · simp only [Function.update_self]; congr 1
        · rw [Function.update_of_ne (by simp),
              Function.update_of_ne (by simp),
              Function.update_self, h1z']
          exact h_ev1 i₀ j₀
        · rw [Function.update_of_ne (by simp),
              Function.update_self, h2z']
          exact h_ev2 i₀ j₀
      simp_rw [h_func, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      simp_rw [← (PiTensorProduct.tprod K).map_update_sum (t := Finset.univ)
        (i := (⟨0, by omega⟩ : Fin 3))]
      exact Finset.sum_eq_zero fun j₀ _ =>
        (PiTensorProduct.tprod K).map_coord_zero ⟨0, by omega⟩ (by
          rw [Function.update_self]; exact sum_mode0_eval1 hn j₀)
    · -- m1 = (0, 1, 0): cancellation in mode 1
      have h1e : m1 1 = 1 := by omega
      have h0z : m1 0 = 0 := by omega
      have h_func : ∀ (i₀ : Fin n) (j₀ : Fin m),
          (fun s => (polyVecMain K n m i₀ j₀ s) (m1 s)) =
          Function.update
            (Function.update (Function.update (0 : ∀ s : Fin 3, (X_obj K n m).V s)
              ⟨0, by omega⟩ (basisA K n m i₀)) ⟨2, by omega⟩ (basisZ K n m))
            ⟨1, by omega⟩ ((polyVecMain K n m i₀ j₀ ⟨1, by omega⟩) 1) := by
        have h0z' : m1 ⟨0, by omega⟩ = 0 := h0z
        have h2z' : m1 ⟨2, by omega⟩ = 0 := h2z
        intro i₀ j₀; funext s; fin_cases s <;> simp only []
        · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp),
              Function.update_self, h0z']
          exact h_ev0 i₀ j₀
        · simp only [Function.update_self]; congr 1
        · rw [Function.update_of_ne (by simp), Function.update_self, h2z']
          exact h_ev2 i₀ j₀
      simp_rw [h_func, Fintype.sum_prod_type]
      simp_rw [← (PiTensorProduct.tprod K).map_update_sum (t := Finset.univ)
        (i := (⟨1, by omega⟩ : Fin 3))]
      exact Finset.sum_eq_zero fun i₀ _ =>
        (PiTensorProduct.tprod K).map_coord_zero ⟨1, by omega⟩ (by
          rw [Function.update_self]; exact sum_mode1_eval1 (K := K) (n := n) hm i₀)
  · -- m1 = (0, 0, 1): mode 2 at degree 1 = 0 for all polyVecMain
    have h2e : m1 2 = 1 := by omega
    apply Finset.sum_eq_zero; intro x _
    apply (PiTensorProduct.tprod K).map_coord_zero ⟨2, by omega⟩
    show (polyVecMain K n m x.1 x.2 ⟨2, by omega⟩) (m1 ⟨2, by omega⟩) = 0
    rw [show (m1 : Fin 3 → ℕ) ⟨2, by omega⟩ = 1 from h2e]
    exact polyVecMain_mode2_eval1 x.1 x.2

private lemma polyVecMain_mode0_eval_ge2 (i₀ : Fin n) (j₀ : Fin m) {k : ℕ} (hk : 2 ≤ k) :
    (polyVecMain K n m i₀ j₀ ⟨0, by omega⟩) k = 0 := by
  simp only [polyVecMain]
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by omega : (0 : ℕ) ≠ k)]
  split <;> split
  all_goals first
    | (rw [Finsupp.single_eq_of_ne' (by omega : (1 : ℕ) ≠ k)]; exact AddMonoid.zero_add _)
    | (rw [Finsupp.zero_apply]; exact AddMonoid.zero_add _)

private lemma polyVecMain_mode1_eval_ge2 (i₀ : Fin n) (j₀ : Fin m) {k : ℕ} (hk : 2 ≤ k) :
    (polyVecMain K n m i₀ j₀ ⟨1, by omega⟩) k = 0 := by
  simp only [polyVecMain]
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by omega : (0 : ℕ) ≠ k)]
  split
  · split
    all_goals (rw [Finsupp.single_eq_of_ne' (by omega : (1 : ℕ) ≠ k)]; exact AddMonoid.zero_add _)
  · rw [Finsupp.zero_apply]; exact AddMonoid.zero_add _

private lemma polyVecMain_mode2_eval2 (i₀ : Fin n) (j₀ : Fin m) :
    (polyVecMain K n m i₀ j₀ ⟨2, by omega⟩) 2 = basisC K n m j₀ i₀ := by
  simp only [polyVecMain]
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by omega : (0 : ℕ) ≠ 2),
      Finsupp.single_eq_same]
  exact AddMonoid.zero_add _

private lemma MMObj_t_explicit (n' m' p' : ℕ) : (MMObj (K := K) n' m' p').t =
    ∑ i : Fin n', ∑ j : Fin m', ∑ k : Fin p', tprod K (fun s : Fin 3 =>
      match s with
      | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n' × Fin m' → K)
      | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m' × Fin p' → K)
      | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p' × Fin n' → K)) := rfl

private lemma schonhage_t2 (hn : 2 ≤ n) (hm : 2 ≤ m) :
    (∑ j : Fin (n * m + 1), ∑ m_1 ∈ Nat.antidiagonalTuple 3 2,
      ⨂ₜ[K] (i : Fin 3), (polyVec K n m j i) (m_1 i)) =
    (MMObj (K := K) n 1 m + MMObj 1 ((n - 1) * (m - 1)) 1).t := by
  -- Step 1: Reindex and eliminate correction
  rw [← Equiv.sum_comp (indexEquiv n m), Fintype.sum_sum_type]
  simp only [polyVec_inl, polyVec_inr, Finset.univ_unique, sum_singleton]
  have h_corr : (∑ m_1 ∈ Nat.antidiagonalTuple 3 2,
      ⨂ₜ[K] (i : Fin 3), (polyVecCorr K n m i) (m_1 i)) = 0 := by
    apply Finset.sum_eq_zero; intro m1 hm1
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hm1
    have ⟨i, hi⟩ : ∃ i : Fin 3, 0 < m1 i := by
      by_contra h; push_neg at h
      have := (h 0).antisymm (Nat.zero_le _)
      have := (h 1).antisymm (Nat.zero_le _)
      have := (h 2).antisymm (Nat.zero_le _); omega
    exact (PiTensorProduct.tprod K).map_coord_zero i (polyVecCorr_eval_pos i hi)
  rw [h_corr, _root_.add_zero]
  -- Step 2: Expand RHS and swap sums
  rw [add_t, Finset.sum_comm]
  -- Step 3: Extract the two contributing degree tuples
  set d002 : Fin 3 → ℕ := fun i => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 0 | ⟨2,_⟩ => 2 with hd002_def
  set d110 : Fin 3 → ℕ := fun i => match i with | ⟨0,_⟩ => 1 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 0 with hd110_def
  have hd002 : d002 ∈ Nat.antidiagonalTuple 3 2 := by
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three]; rfl
  have hd110 : d110 ∈ Nat.antidiagonalTuple 3 2 := by
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three]; rfl
  have hne : d110 ≠ d002 := by
    intro h; exact absurd (congr_fun h ⟨0, by omega⟩) (by simp [d002, d110])
  rw [← Finset.add_sum_erase _ _ hd002]
  have hd110e : d110 ∈ (Nat.antidiagonalTuple 3 2).erase d002 :=
    Finset.mem_erase.mpr ⟨hne, hd110⟩
  rw [← Finset.add_sum_erase _ _ hd110e]
  -- Show residual is 0
  have h_resid : (∑ x ∈ ((Nat.antidiagonalTuple 3 2).erase d002).erase d110,
      ∑ x_1 : Fin n × Fin m,
        ⨂ₜ[K] (i : Fin 3), (polyVecMain K n m x_1.1 x_1.2 i) (x i)) = 0 := by
    apply Finset.sum_eq_zero; intro m1 hm1
    simp only [Finset.mem_erase] at hm1
    obtain ⟨hne1, hne2, hmem⟩ := hm1
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hmem
    apply Finset.sum_eq_zero; intro x _
    have key : m1 (0 : Fin 3) ≥ 2 ∨ m1 (1 : Fin 3) ≥ 2 ∨ m1 (2 : Fin 3) = 1 := by
      by_contra hc; push_neg at hc; obtain ⟨hc0, hc1, hc2⟩ := hc
      have : m1 (2 : Fin 3) = 0 ∨ m1 (2 : Fin 3) = 2 := by omega
      rcases this with h | h
      · exact hne1 (funext fun i => by fin_cases i <;> simp_all [d110] <;> omega)
      · exact hne2 (funext fun i => by fin_cases i <;> simp_all [d002] <;> omega)
    rcases key with h0 | h1 | h2
    · exact (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3) (polyVecMain_mode0_eval_ge2 x.1 x.2 h0)
    · exact (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3) (polyVecMain_mode1_eval_ge2 x.1 x.2 h1)
    · exact (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
        (by rw [h2]; exact polyVecMain_mode2_eval1 x.1 x.2)
  rw [h_resid, _root_.add_zero]
  -- Step 4: Match each contribution to RHS
  congr 1
  · -- d002 contribution = liftMap inl (MMObj n 1 m).t
    have h_az : ∀ (s : Fin 3) (x : (X_obj K n m).V s), x + 0 = x :=
      fun _ x => AddMonoid.add_zero x
    have h_ev0 : ∀ i₀ j₀, (polyVecMain K n m i₀ j₀ ⟨0, by omega⟩) 0 = basisA K n m i₀ := by
      intro i₀ j₀; simp only [polyVecMain]
      rw [Finsupp.add_apply, Finsupp.single_eq_same]
      split <;> split
      all_goals first
        | (rw [Finsupp.single_apply, if_neg (by omega)]; exact h_az _ _)
        | (rw [Finsupp.zero_apply]; exact h_az _ _)
    have h_ev1 : ∀ i₀ j₀, (polyVecMain K n m i₀ j₀ ⟨1, by omega⟩) 0 = basisB K n m j₀ := by
      intro i₀ j₀; simp only [polyVecMain]
      rw [Finsupp.add_apply, Finsupp.single_eq_same]
      split
      · split <;> (rw [Finsupp.single_apply, if_neg (by omega)]; exact h_az _ _)
      · rw [Finsupp.zero_apply]; exact h_az _ _
    simp only [Fin.sum_univ_one, map_sum]
    rw [Fintype.sum_prod_type]
    congr 1; ext i₀; congr 1; ext j₀
    erw [liftMap_tprod]
    congr 1; ext s; fin_cases s
    · exact h_ev0 i₀ j₀
    · exact h_ev1 i₀ j₀
    · exact polyVecMain_mode2_eval2 i₀ j₀
  · -- d110 contribution = liftMap inr (MMObj 1 k 1).t
    have h_az : ∀ (s : Fin 3) (x : (X_obj K n m).V s), x + 0 = x :=
      fun _ x => AddMonoid.add_zero x
    have h_zero_add : ∀ (s : Fin 3) (x : (X_obj K n m).V s), 0 + x = x :=
      fun _ x => AddMonoid.zero_add x
    -- Show terms where ¬(i₀ < n-1) or ¬(j₀ < m-1) vanish
    have h_zero_term : ∀ i₀ j₀, ¬i₀.val < n - 1 ∨ ¬j₀.val < m - 1 →
        (⨂ₜ[K] s, (polyVecMain K n m i₀ j₀ s) (d110 s)) = 0 := by
      intro i₀ j₀ h; rcases h with hi | hj
      · exact (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3) (by
          simp only [d110]; simp only [polyVecMain]
          change (Finsupp.single (0:ℕ) (basisB K n m j₀) + _) (1:ℕ) = _
          rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (show (0:ℕ) ≠ 1 from by omega),
              AddMonoid.zero_add, dif_neg hi]; rfl)
      · by_cases hi : i₀.val < n - 1
        · exact (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3) (by
            simp only [d110]; simp only [polyVecMain]
            change (Finsupp.single (0:ℕ) (basisA K n m i₀) + _) (1:ℕ) = _
            rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (show (0:ℕ) ≠ 1 from by omega),
                AddMonoid.zero_add, dif_pos hi, dif_neg hj]; rfl)
        · exact (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3) (by
            simp only [d110]; simp only [polyVecMain]
            change (Finsupp.single (0:ℕ) (basisB K n m j₀) + _) (1:ℕ) = _
            rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (show (0:ℕ) ≠ 1 from by omega),
                AddMonoid.zero_add, dif_neg hi]; rfl)
    -- Split sums and eliminate boundary terms
    rw [Fintype.sum_prod_type]
    have hn1 : (n - 1) + 1 = n := by omega
    have hm1 : (m - 1) + 1 = m := by omega
    rw [← Equiv.sum_comp (finCongr hn1), Fin.sum_univ_castSucc]
    rw [show (∑ j₀, (⨂ₜ[K] s, (polyVecMain K n m (finCongr hn1 (Fin.last _)) j₀ s) (d110 s))) = 0
      from Finset.sum_eq_zero fun j₀ _ =>
        h_zero_term _ j₀ (Or.inl (by simp [finCongr, Fin.last]))]
    rw [_root_.add_zero]
    -- Simplify RHS before simp_rw damages Fin 1 sums
    conv_rhs => simp only [Fin.sum_univ_one, map_sum]
    -- For each i < n-1, split inner sum and eliminate last j
    simp_rw [← Equiv.sum_comp (finCongr hm1), Fin.sum_univ_castSucc,
      show ∀ i, (⨂ₜ[K] s, (polyVecMain K n m (finCongr hn1 (Fin.castSucc i))
        (finCongr hm1 (Fin.last _)) s) (d110 s)) = 0
      from fun i => h_zero_term _ _ (Or.inr (by simp [finCongr, Fin.last])),
      _root_.add_zero]
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    congr 1; ext i; congr 1; ext j
    erw [liftMap_tprod]
    congr 1; ext s; fin_cases s
    · -- mode 0 at degree 1 = basisX = inr(Pi.single (0, encode i j) 1)
      simp only [d110]; simp only [polyVecMain]
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by omega), h_zero_add,
          dif_pos (show (finCongr hn1 (Fin.castSucc i)).val < n - 1 by simp [finCongr, Fin.castSucc]),
          dif_pos (show (finCongr hm1 (Fin.castSucc j)).val < m - 1 by simp [finCongr, Fin.castSucc]),
          Finsupp.single_eq_same]
      simp [basisX, encode, finCongr, Fin.castSucc]
    · -- mode 1 at degree 1 = basisY = inr(Pi.single (encode i j, 0) 1)
      simp only [d110]; simp only [polyVecMain]
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by omega), h_zero_add,
          dif_pos (show (finCongr hn1 (Fin.castSucc i)).val < n - 1 by simp [finCongr, Fin.castSucc]),
          dif_pos (show (finCongr hm1 (Fin.castSucc j)).val < m - 1 by simp [finCongr, Fin.castSucc]),
          Finsupp.single_eq_same]
      simp [basisY, encode, finCongr, Fin.castSucc]
    · -- mode 2 at degree 0 = basisZ = inr(Pi.single (0, 0) 1)
      simp only [d110]; simp only [polyVecMain]
      rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne' (by omega)]
      exact h_az _ _

theorem schonhage_direct_sum (hn : 2 ≤ n) (hm : 2 ≤ m) :
    Tensor.DegeneratesOfOrder
      (toTensor (MMObj (K := K) n 1 m + MMObj 1 ((n - 1) * (m - 1)) 1))
      ((n * m + 1 : ℕ) : Tensor.{u, u} K 3) 2 := by
  rw [tensor_degeneratesOfOrder_natCast_iff]
  refine ⟨polyVec K n m, ?_, ?_⟩
  · intro k hk
    interval_cases k
    · exact schonhage_t0
    · exact schonhage_t1 hn hm
  · exact schonhage_t2 hn hm

end MainTheorem

/-! ## Corollary: ω < 2.55

Plugging `n = m = 4` into `schonhage_direct_sum` gives border rank ≤ 17 for
`MM(4,1,4) + MM(1,9,1)`. The asymptotic sum inequality then gives
`16^{ω/3} + 9^{ω/3} ≤ 17`, from which `ω < 51/20 = 2.55`. -/

section OmegaBound

open StrassenPreorder Real

private theorem asymptotic_rank_le_of_asymptoticLe_natCast
    {R : Type u} [CommSemiring R] {P : StrassenPreorder R} {a : R} {r : ℕ}
    (h : AsymptoticLe P a (r : R)) : asymptotic_rank P a ≤ r := by
  rw [P.asymptotic_rank_eq_max_spectrum]
  apply ciSup_le
  intro ϕ
  have := (P.asymptotic_le_iff_spectrum_le a r).mp h ϕ
  rwa [map_natCast] at this

private theorem toTensor_add (X Y : TensorObj.{u, u} K 3) :
    toTensor (X + Y) = toTensor X + toTensor Y := by
  show toTensor (X + Y) = Tensor.add (toTensor X) (toTensor Y)
  simp [Tensor.add, toTensor]

private theorem rpow_16_bound : (211 : ℝ) / 20 < (16 : ℝ) ^ ((17 : ℝ) / 20) := by
  have h_eq : (16 : ℝ) ^ ((17 : ℝ) / 20) = ((2 : ℝ) ^ (17 : ℕ)) ^ ((1 : ℝ) / 5) := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) from by norm_num,
        ← rpow_natCast (2 : ℝ) 4,
        ← rpow_mul (by positivity : (0 : ℝ) ≤ 2),
        show ((4 : ℕ) : ℝ) * ((17 : ℝ) / 20) = ↑(17 : ℕ) * ((1 : ℝ) / 5) from by push_cast; ring,
        rpow_mul (by positivity : (0 : ℝ) ≤ 2),
        rpow_natCast]
  rw [h_eq, show (211 : ℝ) / 20 = (((211 : ℝ) / 20) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) from by
    rw [← rpow_natCast ((211 : ℝ) / 20) 5,
        ← rpow_mul (by positivity : (0 : ℝ) ≤ 211 / 20),
        show ((5 : ℕ) : ℝ) * ((1 : ℝ) / 5) = 1 from by push_cast; ring,
        rpow_one]]
  exact rpow_lt_rpow (by positivity) (by norm_num) (by positivity)

private theorem rpow_9_bound : (323 : ℝ) / 50 < (9 : ℝ) ^ ((17 : ℝ) / 20) := by
  have h_eq : (9 : ℝ) ^ ((17 : ℝ) / 20) = ((3 : ℝ) ^ (17 : ℕ)) ^ ((1 : ℝ) / 10) := by
    rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℕ) from by norm_num,
        ← rpow_natCast (3 : ℝ) 2,
        ← rpow_mul (by positivity : (0 : ℝ) ≤ 3),
        show ((2 : ℕ) : ℝ) * ((17 : ℝ) / 20) = ↑(17 : ℕ) * ((1 : ℝ) / 10) from by push_cast; ring,
        rpow_mul (by positivity : (0 : ℝ) ≤ 3),
        rpow_natCast]
  rw [h_eq, show (323 : ℝ) / 50 = (((323 : ℝ) / 50) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10) from by
    rw [← rpow_natCast ((323 : ℝ) / 50) 10,
        ← rpow_mul (by positivity : (0 : ℝ) ≤ 323 / 50),
        show ((10 : ℕ) : ℝ) * ((1 : ℝ) / 10) = 1 from by push_cast; ring,
        rpow_one]]
  exact rpow_lt_rpow (by positivity) (by norm_num) (by positivity)

theorem matMulExp_lt : matMulExp (K := K) < 51 / 20 := by
  by_contra h_ge
  push_neg at h_ge
  have h_deg := schonhage_direct_sum (K := K) (by norm_num : 2 ≤ 4) (by norm_num : 2 ≤ 4)
  simp only [show (4 : ℕ) - 1 = 3 from rfl, show 3 * 3 = 9 from rfl,
             show 4 * 4 + 1 = 17 from rfl] at h_deg
  have h_ar : asymptotic_rank Tensor.instStrassenPreorder
      (MM (K := K) 4 1 4 + MM 1 9 1) ≤ 17 := by
    show asymptotic_rank Tensor.instStrassenPreorder
      (toTensor (MMObj (K := K) 4 1 4) + toTensor (MMObj 1 9 1)) ≤ 17
    rw [← toTensor_add]
    exact asymptotic_rank_le_of_asymptoticLe_natCast
      (Degenerates.asymptoticLe ⟨2, h_deg⟩)
  have h_ineq : (16 : ℝ) ^ (matMulExp (K := K) / 3) +
      (9 : ℝ) ^ (matMulExp (K := K) / 3) ≤ 17 := by
    have := asymptotic_sum_inequality (K := K) (ι := Fin 2)
      ![4, 1] ![1, 9] ![4, 1]
      (by intro i; fin_cases i <;> simp)
      (by intro i; fin_cases i <;> simp)
      (by intro i; fin_cases i <;> simp)
      17
      (by rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact h_ar)
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    convert this using 2
  have h_exp : (17 : ℝ) / 20 ≤ matMulExp (K := K) / 3 := by linarith
  have h16 : (16 : ℝ) ^ ((17 : ℝ) / 20) ≤ (16 : ℝ) ^ (matMulExp (K := K) / 3) :=
    rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16) h_exp
  have h9 : (9 : ℝ) ^ ((17 : ℝ) / 20) ≤ (9 : ℝ) ^ (matMulExp (K := K) / 3) :=
    rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 9) h_exp
  linarith [rpow_16_bound, rpow_9_bound]

end OmegaBound

end Tensor
