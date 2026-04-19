import AsymptoticSpectra.Structures
import AsymptoticSpectra.Spectrum
import AsymptoticSpectra.Rank
import AsymptoticSpectra.AsymptoticClosure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

universe u

noncomputable section

open Filter Topology Classical

variable {R : Type u} [CommSemiring R] (P : StrassenPreorder R)

/-- The asymptotic spectrum is always non-empty. -/
instance (P : StrassenPreorder R) : Nonempty (AsymptoticSpectrum R P) := by
  obtain ⟨Q, hP_le_Q, hQ_max⟩ := StrassenPreorder.total_extension P
  have hQ_props := (StrassenPreorder.isMaximal_iff_isTotal_isClosed Q).mp hQ_max
  let E : MaxExtension R P := ⟨Q, hP_le_Q, hQ_props.1, hQ_props.2⟩
  exact ⟨(asymptoticSpectrumEquivMaxExtensions P).symm E⟩

namespace StrassenPreorder

/-- For a subexponential ℕ-valued sequence `f`, `(f k)^(1/k) ≤ 1 + ε` eventually. -/
private lemma subexp_rpow_eventually_le {f : ℕ → ℕ} (hf : IsSubexponential f)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, (f k : ℝ) ^ (1 / (k : ℝ)) ≤ 1 + ε := by
  filter_upwards [hf ε hε, Filter.eventually_gt_atTop 0] with k hk hk_pos
  have hk_cast_pos : (0 : ℝ) < k := by exact_mod_cast hk_pos
  have hk_cast_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_cast_pos
  have hfk_nonneg : 0 ≤ (f k : ℝ) := Nat.cast_nonneg _
  have h1e_nonneg : (0 : ℝ) ≤ 1 + ε := by linarith
  have h1k_nonneg : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  calc (f k : ℝ) ^ (1 / (k : ℝ))
      ≤ ((1 + ε) ^ (k : ℝ)) ^ (1 / (k : ℝ)) :=
        Real.rpow_le_rpow hfk_nonneg hk h1k_nonneg
    _ = (1 + ε) ^ ((k : ℝ) * (1 / (k : ℝ))) := by rw [← Real.rpow_mul h1e_nonneg]
    _ = (1 + ε) ^ (1 : ℝ) := by rw [mul_one_div_cancel hk_cast_ne]
    _ = 1 + ε := Real.rpow_one _

/-- Bridge lemma: if `a` is asymptotically bounded by a natural number `N`, then the
asymptotic rank of `a` is at most `N`. -/
lemma asymptotic_rank_le_of_asymptoticLe_natCast
    {a : R} {N : ℕ} (h : AsymptoticLe P a (N : R)) :
    asymptotic_rank P a ≤ (N : ℝ) := by
  obtain ⟨f, hf, h_le⟩ := h
  have h_rank_bound : ∀ m : ℕ, (rank P (a^m) : ℝ) ≤ (f m : ℝ) * (N : ℝ)^m := by
    intro m
    have h_cast : P.le (a^m) ((f m * N^m : ℕ) : R) := by
      have hlm := h_le m
      push_cast at hlm ⊢
      convert hlm using 1
    have hrm : rank P (a^m) ≤ f m * N^m := Nat.find_min' _ h_cast
    exact_mod_cast hrm
  by_cases ha : a = 0
  · rw [ha]; unfold asymptotic_rank; simp
  have h_lim : Tendsto (fun m : ℕ => (rank P (a^m) : ℝ) ^ (1 / (m : ℝ))) atTop
      (𝓝 (asymptotic_rank P a)) := tends_to_asymptotic_rank P a ha
  by_cases hN : N = 0
  · exfalso
    have h1 := h_le 1
    rw [hN] at h1
    simp at h1
    have h_rank_le : rank P a ≤ 0 := Nat.find_min' _ (by push_cast; exact h1)
    have h_rank_ge : 1 ≤ (rank P (a^1) : ℝ) := rank_pow_ge_one P a ha 1
    rw [pow_one] at h_rank_ge
    have : (1 : ℝ) ≤ (0 : ℝ) := by
      calc (1 : ℝ) ≤ (rank P a : ℝ) := h_rank_ge
        _ ≤ (0 : ℝ) := by exact_mod_cast h_rank_le
    linarith
  have hN_pos : 0 < N := Nat.pos_of_ne_zero hN
  have hN_cast_pos : (0 : ℝ) < N := by exact_mod_cast hN_pos
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  set δ := ε / (N : ℝ) with hδ_def
  have hδ_pos : 0 < δ := div_pos hε hN_cast_pos
  have h_eventually : ∀ᶠ m : ℕ in atTop,
      (rank P (a^m) : ℝ) ^ (1 / (m : ℝ)) ≤ (1 + δ) * N := by
    filter_upwards [subexp_rpow_eventually_le hf hδ_pos, Filter.eventually_gt_atTop 0]
      with m hm_fm hm_pos
    have hm_cast_pos : (0 : ℝ) < m := by exact_mod_cast hm_pos
    have hm_inv_nonneg : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
    have hfn_nonneg : 0 ≤ (f m : ℝ) := Nat.cast_nonneg _
    have hNm_nonneg : (0 : ℝ) ≤ (N : ℝ)^m := by positivity
    have h_rank_nonneg : (0 : ℝ) ≤ rank P (a^m) := Nat.cast_nonneg _
    calc (rank P (a^m) : ℝ) ^ (1 / (m : ℝ))
        ≤ ((f m : ℝ) * (N : ℝ)^m) ^ (1 / (m : ℝ)) :=
          Real.rpow_le_rpow h_rank_nonneg (h_rank_bound m) hm_inv_nonneg
      _ = (f m : ℝ) ^ (1 / (m : ℝ)) * ((N : ℝ)^m) ^ (1 / (m : ℝ)) :=
          Real.mul_rpow hfn_nonneg hNm_nonneg
      _ = (f m : ℝ) ^ (1 / (m : ℝ)) * (N : ℝ) := by
          congr 1
          rw [← Real.rpow_natCast (N : ℝ) m, ← Real.rpow_mul (le_of_lt hN_cast_pos),
              mul_one_div_cancel (ne_of_gt hm_cast_pos), Real.rpow_one]
      _ ≤ (1 + δ) * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hm_fm (le_of_lt hN_cast_pos)
  have h_bound : asymptotic_rank P a ≤ (1 + δ) * (N : ℝ) :=
    le_of_tendsto h_lim h_eventually
  have h_eq : (1 + δ) * (N : ℝ) = (N : ℝ) + ε := by
    rw [hδ_def, add_mul, one_mul, div_mul_cancel₀]
    exact ne_of_gt hN_cast_pos
  linarith [h_bound]

/-- Power law: asymptotic rank commutes with powers (for exponent ≥ 1). -/
lemma asymptotic_rank_pow (a : R) (k : ℕ) (hk : 1 ≤ k) :
    asymptotic_rank P (a^k) = (asymptotic_rank P a) ^ k := by
  by_cases ha : a = 0
  · have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
    have hak : a^k = 0 := by rw [ha]; exact zero_pow hk_ne
    rw [hak]
    unfold asymptotic_rank
    rw [if_pos rfl, if_pos ha, zero_pow hk_ne]
  have hak : a^k ≠ 0 := P.pow_ne_zero k ha
  have h_lhs : Tendsto (fun m : ℕ => (rank P ((a^k)^m) : ℝ) ^ (1 / (m : ℝ))) atTop
      (𝓝 (asymptotic_rank P (a^k))) := tends_to_asymptotic_rank P (a^k) hak
  have h_rhs_lim : Tendsto (fun n : ℕ => (rank P (a^n) : ℝ) ^ (1 / (n : ℝ))) atTop
      (𝓝 (asymptotic_rank P a)) := tends_to_asymptotic_rank P a ha
  have hk_pos : 0 < k := hk
  have hk_cast_pos : (0 : ℝ) < k := by exact_mod_cast hk_pos
  have hk_cast_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_cast_pos
  have h_km_atTop : Tendsto (fun m : ℕ => k * m) atTop atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro n
    refine ⟨n, fun m hm => ?_⟩
    calc n = 1 * n := (one_mul n).symm
      _ ≤ k * n := Nat.mul_le_mul_right n hk
      _ ≤ k * m := Nat.mul_le_mul_left k hm
  -- Along subsequence n = k*m (note cast form: ↑(k*m), which matches Tendsto.comp)
  have h_sub : Tendsto (fun m : ℕ => (rank P (a^(k*m)) : ℝ) ^ (1 / ((k*m : ℕ) : ℝ))) atTop
      (𝓝 (asymptotic_rank P a)) := h_rhs_lim.comp h_km_atTop
  -- Rewrite: (rank(a^(k*m)))^(1/↑(k*m)) = ((rank((a^k)^m))^(1/↑m))^(1/↑k)
  have h_pow_k : ∀ m : ℕ, 0 < m →
      (rank P (a^(k*m)) : ℝ) ^ (1 / ((k*m : ℕ) : ℝ)) =
      ((rank P ((a^k)^m) : ℝ) ^ (1 / (m : ℝ))) ^ (1 / (k : ℝ)) := by
    intro m hm_pos
    have hm_cast_pos : (0 : ℝ) < m := by exact_mod_cast hm_pos
    have hm_cast_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_cast_pos
    have h_pow_eq : (a^k)^m = a^(k*m) := by rw [← pow_mul]
    rw [← h_pow_eq]
    have h_rank_nonneg : (0 : ℝ) ≤ rank P ((a^k)^m) := Nat.cast_nonneg _
    rw [← Real.rpow_mul h_rank_nonneg]
    congr 1
    push_cast
    field_simp
  have h_sub' : Tendsto
      (fun m : ℕ => ((rank P ((a^k)^m) : ℝ) ^ (1 / (m : ℝ))) ^ (1 / (k : ℝ)))
      atTop (𝓝 (asymptotic_rank P a)) := by
    apply h_sub.congr'
    filter_upwards [Filter.eventually_gt_atTop 0] with m hm
    exact h_pow_k m hm
  -- Take nat k-th power: Tendsto.pow
  have h_k_pow : Tendsto
      (fun m : ℕ => (((rank P ((a^k)^m) : ℝ) ^ (1 / (m : ℝ))) ^ (1 / (k : ℝ))) ^ k)
      atTop (𝓝 ((asymptotic_rank P a) ^ k)) := h_sub'.pow k
  -- Simplify ((u_m)^(1/k))^k = u_m
  have h_simp : ∀ m : ℕ,
      (((rank P ((a^k)^m) : ℝ) ^ (1 / (m : ℝ))) ^ (1 / (k : ℝ))) ^ k =
      (rank P ((a^k)^m) : ℝ) ^ (1 / (m : ℝ)) := by
    intro m
    set u : ℝ := (rank P ((a^k)^m) : ℝ) ^ (1 / (m : ℝ)) with hu_def
    have hu_nonneg : 0 ≤ u := by
      rw [hu_def]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h1 : (u ^ (1/(k : ℝ)))^(k : ℕ) = (u ^ (1/(k : ℝ))) ^ ((k : ℕ) : ℝ) :=
      (Real.rpow_natCast _ k).symm
    rw [h1, ← Real.rpow_mul hu_nonneg, one_div, inv_mul_cancel₀ hk_cast_ne,
        Real.rpow_one]
  have h_simp' : Tendsto (fun m : ℕ => (rank P ((a^k)^m) : ℝ) ^ (1 / (m : ℝ)))
      atTop (𝓝 ((asymptotic_rank P a) ^ k)) := by
    apply h_k_pow.congr
    intro m
    exact h_simp m
  exact tendsto_nhds_unique h_lhs h_simp'

/-- The evaluation map `ϕ ↦ ϕ a` is bounded above by `rank P a`. -/
private lemma spectrum_eval_bddAbove (a : R) :
    BddAbove (Set.range fun (ϕ : AsymptoticSpectrum R P) => ϕ a) := by
  refine ⟨(rank P a : ℝ), ?_⟩
  rintro _ ⟨ϕ, rfl⟩
  have h_spec : P.le a ((rank P a : ℕ) : R) := Nat.find_spec (P.upper_archimedean a)
  have := ϕ.monotone' h_spec
  rwa [map_natCast] at this

/-- Forward direction: every spectrum-point value is bounded by the asymptotic rank. -/
private lemma spectrum_apply_le_asymptotic_rank
    (ϕ : AsymptoticSpectrum R P) (a : R) : ϕ a ≤ asymptotic_rank P a := by
  by_cases ha : a = 0
  · rw [ha, map_zero]
    unfold asymptotic_rank; simp
  have h_phi_nonneg : 0 ≤ ϕ a := by
    have := ϕ.monotone' (P.zero_le a)
    rwa [map_zero] at this
  have h_lim := tends_to_asymptotic_rank P a ha
  apply ge_of_tendsto h_lim
  filter_upwards [Filter.eventually_gt_atTop 0] with k hk_pos
  have hk_cast_pos : (0 : ℝ) < k := by exact_mod_cast hk_pos
  have hk_cast_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_cast_pos
  have h_rank_spec : P.le (a^k) ((rank P (a^k) : ℕ) : R) :=
    Nat.find_spec (P.upper_archimedean (a^k))
  have h_phi_monotone : ϕ (a^k) ≤ ϕ ((rank P (a^k) : ℕ) : R) := ϕ.monotone' h_rank_spec
  rw [map_natCast, map_pow] at h_phi_monotone
  have h_phi_pow_nonneg : 0 ≤ ϕ a ^ k := pow_nonneg h_phi_nonneg k
  have h_inv_nonneg : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have h_le_rpow : (ϕ a ^ k) ^ (1 / (k : ℝ)) ≤ (rank P (a^k) : ℝ) ^ (1 / (k : ℝ)) :=
    Real.rpow_le_rpow h_phi_pow_nonneg h_phi_monotone h_inv_nonneg
  have h_eq : (ϕ a ^ k) ^ (1 / (k : ℝ)) = ϕ a := by
    rw [← Real.rpow_natCast (ϕ a) k, ← Real.rpow_mul h_phi_nonneg,
        mul_one_div_cancel hk_cast_ne, Real.rpow_one]
  linarith [h_le_rpow, h_eq]

/-- For any nonzero `a`, every spectrum point satisfies `ϕ a ≥ 1`. Hence the
supremum of `ϕ a` over all spectrum points is at least 1. -/
private lemma one_le_sup_spectrum {a : R} (ha : a ≠ 0) :
    (1 : ℝ) ≤ ⨆ (ϕ : AsymptoticSpectrum R P), ϕ a := by
  have h1a : P.le 1 a := by
    cases P.lower_archimedean a with
    | inl h => exact absurd h ha
    | inr h => exact h
  obtain ⟨ϕ⟩ := (inferInstance : Nonempty (AsymptoticSpectrum R P))
  have h_mono : ϕ 1 ≤ ϕ a := ϕ.monotone' h1a
  rw [map_one] at h_mono
  exact le_ciSup_of_le (spectrum_eval_bddAbove P a) ϕ h_mono

/-- The Duality Theorem (Part 2): the asymptotic spectrum characterizes the asymptotic closure. -/
theorem asymptotic_le_iff_spectrum_le (a b : R) :
  AsymptoticLe P a b ↔ ∀ ϕ : AsymptoticSpectrum R P, ϕ a ≤ ϕ b := by
  change (StrassenPreorder.asymptoticClosure P).le a b ↔ ∀ ϕ : AsymptoticSpectrum R P, ϕ a ≤ ϕ b
  rw [StrassenPreorder.asymptoticClosure_eq_intersection_total_closed]
  constructor
  · intro h ϕ
    let E := spectrumToMaxExtension ϕ
    specialize h E.val E.property.1 E.property.2.1 E.property.2.2
    exact h
  · intro h Q hPQ h_total h_closed
    let E : MaxExtension R P := ⟨Q, hPQ, h_total, h_closed⟩
    let ϕ := maxExtensionToSpectrum E
    specialize h ϕ
    rw [← StrassenPreorder.rho_reflects_le Q h_total h_closed]
    exact h

/-- **Duality Theorem (Part 1)**: the asymptotic rank equals the maximum value of
`ϕ a` over all points `ϕ` in the asymptotic spectrum. -/
theorem asymptotic_rank_eq_max_spectrum (a : R) :
    asymptotic_rank P a = ⨆ (ϕ : AsymptoticSpectrum R P), ϕ a := by
  refine le_antisymm ?_ ?_
  · -- Reverse direction: asymptotic_rank P a ≤ ⨆ ϕ, ϕ a
    by_cases ha : a = 0
    · rw [ha]
      unfold asymptotic_rank
      simp
    -- a ≠ 0: use power+bridge approach
    set M : ℝ := ⨆ (ϕ : AsymptoticSpectrum R P), ϕ a with hM_def
    have hM_ge_one : 1 ≤ M := one_le_sup_spectrum P ha
    have hM_nonneg : 0 ≤ M := le_trans zero_le_one hM_ge_one
    have hM_pos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hM_ge_one
    -- Show asymptotic_rank P a ≤ M + ε for all ε > 0
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    -- We need: for some k large, (asymptotic_rank a)^k ≤ ⌈(M+ε/2)^k⌉, then k-th root → M+ε/2 < M+ε
    -- Simpler: asymptotic_rank a ≤ M + ε.
    -- Approach: for each k, set N_k = ⌈M^k⌉, then
    --   asymptotic_rank a ≤ N_k^(1/k), and N_k^(1/k) → M (using M ≥ 1).
    -- Then we need this limit argument. Let's use the full sequence approach.
    -- We want: ∀ k ≥ 1, (asymptotic_rank a)^k ≤ ⌈M^k⌉.
    have h_asymp_nonneg : 0 ≤ asymptotic_rank P a := by
      apply ge_of_tendsto (tends_to_asymptotic_rank P a ha)
      filter_upwards [Filter.eventually_gt_atTop 0] with k _
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h_asymp_pow_bound : ∀ k : ℕ, 1 ≤ k →
        (asymptotic_rank P a) ^ k ≤ (⌈M^k⌉₊ : ℝ) := by
      intro k hk
      have hk_pos : 0 < k := hk
      -- Step 1: AsymptoticLe P (a^k) (⌈M^k⌉₊ : R)
      have h_all_phi : ∀ ϕ : AsymptoticSpectrum R P, ϕ (a^k) ≤ ϕ ((⌈M^k⌉₊ : ℕ) : R) := by
        intro ϕ
        rw [map_natCast, map_pow]
        have h_phi_le : ϕ a ≤ M := by
          exact le_ciSup (spectrum_eval_bddAbove P a) ϕ
        have h_phi_nonneg : 0 ≤ ϕ a := by
          have := ϕ.monotone' (P.zero_le a)
          rwa [map_zero] at this
        calc ϕ a ^ k
            ≤ M ^ k := pow_le_pow_left₀ h_phi_nonneg h_phi_le k
          _ ≤ (⌈M^k⌉₊ : ℝ) := Nat.le_ceil _
      have h_asymp_le : AsymptoticLe P (a^k) ((⌈M^k⌉₊ : ℕ) : R) := by
        rw [asymptotic_le_iff_spectrum_le]
        exact h_all_phi
      -- Step 2: asymptotic_rank P (a^k) ≤ ⌈M^k⌉₊
      have h_bridge : asymptotic_rank P (a^k) ≤ (⌈M^k⌉₊ : ℝ) :=
        asymptotic_rank_le_of_asymptoticLe_natCast P h_asymp_le
      -- Step 3: asymptotic_rank P (a^k) = (asymptotic_rank P a)^k
      rw [← asymptotic_rank_pow P a k hk]
      exact h_bridge
    -- Now take k-th root and let k → ∞
    -- asymptotic_rank a ≤ (⌈M^k⌉₊)^(1/k), and (⌈M^k⌉₊)^(1/k) → M (using M ≥ 1)
    -- Choose k large: it suffices to show ⌈M^k⌉₊^(1/k) ≤ M + ε for some k.
    -- Since M ≥ 1, ⌈M^k⌉₊ ≤ M^k + 1. So ⌈M^k⌉₊^(1/k) ≤ (M^k + 1)^(1/k).
    -- (M^k + 1)^(1/k) = M * (1 + M^(-k))^(1/k) → M as k → ∞ (since M ≥ 1 so M^(-k) → 0).
    -- Alternative simpler: for large k, ⌈M^k⌉₊ ≤ (M+ε/2)^k (by taking log:
    --    log ⌈M^k⌉₊ ≤ k log M + o(k), so log⌈..⌉/k → log M < log(M+ε/2)).
    -- We use this: show there exists k with (⌈M^k⌉₊ : ℝ)^(1/k) ≤ M + ε.
    -- Since M ≥ 1 and k ≥ 1, we have M^k ≥ 1, so ⌈M^k⌉₊ ≤ M^k + 1 ≤ 2·M^k.
    -- Therefore (⌈M^k⌉₊)^(1/k) ≤ (2·M^k)^(1/k) = 2^(1/k) · M.
    -- Since 2^(1/k) → 1, eventually 2^(1/k) · M ≤ M + ε, i.e., 2^(1/k) ≤ 1 + ε/M.
    have hεM_pos : 0 < ε / M := div_pos hε hM_pos
    have h_two_lim : Tendsto (fun k : ℕ => (2 : ℝ) ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
      have hcont : ContinuousAt (fun x : ℝ => (2 : ℝ)^x) 0 :=
        Real.continuousAt_const_rpow (by norm_num : (2 : ℝ) ≠ 0)
      have h_inv : Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have h := hcont.tendsto.comp h_inv
      simp only [Real.rpow_zero] at h
      exact h
    have h_eventually : ∀ᶠ k : ℕ in atTop,
        (2 : ℝ) ^ (1 / (k : ℝ)) ≤ 1 + ε / M := by
      have : ∀ᶠ k : ℕ in atTop, (2 : ℝ) ^ (1 / (k : ℝ)) ∈ Set.Iio (1 + ε / M) := by
        apply h_two_lim.eventually
        exact Iio_mem_nhds (by linarith)
      filter_upwards [this] with k hk
      exact le_of_lt hk
    obtain ⟨k, hk, hk_bound⟩ : ∃ k : ℕ, 1 ≤ k ∧ (2 : ℝ) ^ (1 / (k : ℝ)) ≤ 1 + ε / M := by
      obtain ⟨k, hk⟩ := (h_eventually.and (Filter.eventually_ge_atTop 1)).exists
      exact ⟨k, hk.2, hk.1⟩
    have h_asymp_k_bound : (asymptotic_rank P a) ^ k ≤ (⌈M^k⌉₊ : ℝ) :=
      h_asymp_pow_bound k hk
    -- Want: asymptotic_rank P a ≤ M + ε, i.e., (asymptotic_rank P a)^1 ≤ M + ε.
    -- From (asymptotic_rank)^k ≤ ⌈M^k⌉₊, taking k-th root:
    -- asymptotic_rank ≤ ⌈M^k⌉₊^(1/k) ≤ M + ε.
    have hk_cast_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k from hk)
    have hk_cast_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_cast_pos
    have h_inv_nonneg : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
    have h_asymp_pow_nonneg : 0 ≤ (asymptotic_rank P a) ^ k :=
      pow_nonneg h_asymp_nonneg k
    have h_rpow_le : ((asymptotic_rank P a) ^ k) ^ (1/(k : ℝ)) ≤ (⌈M^k⌉₊ : ℝ)^(1/(k : ℝ)) :=
      Real.rpow_le_rpow h_asymp_pow_nonneg h_asymp_k_bound h_inv_nonneg
    have h_lhs_eq : ((asymptotic_rank P a) ^ k) ^ (1/(k : ℝ)) = asymptotic_rank P a := by
      rw [← Real.rpow_natCast (asymptotic_rank P a) k, ← Real.rpow_mul h_asymp_nonneg,
          mul_one_div_cancel hk_cast_ne, Real.rpow_one]
    -- Now bound (⌈M^k⌉₊)^(1/k) ≤ (2·M^k)^(1/k) = 2^(1/k) · M ≤ (1 + ε/M) · M = M + ε
    have hMk_pos : 0 < M^k := pow_pos hM_pos k
    have hMk_nonneg : 0 ≤ M^k := le_of_lt hMk_pos
    have hMk_ge_one : 1 ≤ M^k := one_le_pow₀ hM_ge_one
    have h_ceil_bound : (⌈M^k⌉₊ : ℝ) ≤ 2 * M^k := by
      have h1 : (⌈M^k⌉₊ : ℝ) ≤ M^k + 1 := by
        have := Nat.ceil_lt_add_one (le_of_lt hMk_pos)
        linarith
      linarith
    have h_2Mk_nonneg : (0 : ℝ) ≤ 2 * M^k := by linarith
    have h_ceil_nonneg : (0 : ℝ) ≤ (⌈M^k⌉₊ : ℝ) := Nat.cast_nonneg _
    have h_ceil_rpow_le : (⌈M^k⌉₊ : ℝ)^(1/(k : ℝ)) ≤ (2 * M^k)^(1/(k : ℝ)) :=
      Real.rpow_le_rpow h_ceil_nonneg h_ceil_bound h_inv_nonneg
    have h_2Mk_rpow : (2 * M^k)^(1/(k : ℝ)) = (2 : ℝ)^(1/(k : ℝ)) * M := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hMk_nonneg]
      congr 1
      rw [← Real.rpow_natCast M k, ← Real.rpow_mul hM_nonneg,
          mul_one_div_cancel hk_cast_ne, Real.rpow_one]
    have h_prod_le : (2 : ℝ)^(1/(k : ℝ)) * M ≤ (1 + ε/M) * M :=
      mul_le_mul_of_nonneg_right hk_bound hM_nonneg
    have h_arith : (1 + ε/M) * M = M + ε := by
      field_simp
    linarith [h_rpow_le, h_lhs_eq, h_ceil_rpow_le, h_2Mk_rpow, h_prod_le, h_arith]
  · -- Forward direction: ⨆ ϕ, ϕ a ≤ asymptotic_rank P a
    apply ciSup_le
    intro ϕ
    exact spectrum_apply_le_asymptotic_rank P ϕ a

end StrassenPreorder
