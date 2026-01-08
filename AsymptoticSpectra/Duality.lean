import AsymptoticSpectra.Structures
import AsymptoticSpectra.Spectrum
import AsymptoticSpectra.Rank
import AsymptoticSpectra.AsymptoticClosure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

universe u

noncomputable section

open Filter Topology

variable {R : Type u} [CommSemiring R] (P : StrassenPreorder R)

/-- The asymptotic spectrum is always non-empty. -/
instance (P : StrassenPreorder R) : Nonempty (AsymptoticSpectrum R P) := sorry

namespace StrassenPreorder

/-- The Duality Theorem (Part 1): the asymptotic rank is the maximum of evaluations over the spectrum. -/
theorem asymptotic_rank_eq_max_spectrum (a : R) :
  asymptotic_rank P a = ⨆ (ϕ : AsymptoticSpectrum R P), ϕ a := sorry

/-- Weak Duality: if a ≤ b in the asymptotic closure, then ϕ(a) ≤ ϕ(b) for all ϕ in the spectrum. -/
theorem asymptotic_le_imp_spectrum_le {a b : R}
  (hle_closure : AsymptoticLe P a b) :
  ∀ ϕ : AsymptoticSpectrum R P, ϕ a ≤ ϕ b := by
  intro ϕ
  obtain ⟨f, hf, hle⟩ := hle_closure
  have h_ϕ_nonneg_b : 0 ≤ ϕ b := by
    have := ϕ.monotone' (all_nonneg P b)
    simpa using this
  apply le_of_forall_pos_le_add
  intro ε hε
  let ε' := ε / (ϕ b + 1)
  have hε' : 0 < ε' := div_pos hε (by linarith)
  specialize hf ε' hε'
  -- f n ≤ (1 + ε')^n eventually
  have h_filter := hf.and (eventually_gt_atTop 0)
  obtain ⟨N, hN⟩ := h_filter.exists
  have h_hle := hle N
  have h_ϕ_hle := ϕ.monotone' h_hle
  simp at h_ϕ_hle
  have h_bound : (ϕ a)^N ≤ (1 + ε')^N * (ϕ b)^N := by
    apply h_ϕ_hle.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg h_ϕ_nonneg_b N)
    rw [← Real.rpow_natCast]
    exact hN.1
  rw [← mul_pow] at h_bound
  have hN_pos : 0 < N := hN.2
  have h_bound_nonneg : 0 ≤ (1 + ε') * ϕ b := by
    apply mul_nonneg
    · linarith
    · exact h_ϕ_nonneg_b
  have h_ϕ_a_le : ϕ a ≤ (1 + ε') * ϕ b := by
    apply le_of_pow_le_pow_left₀ hN_pos.ne' h_bound_nonneg h_bound
  have : ϕ a ≤ ϕ b + ε' * ϕ b := by
    rw [add_mul, one_mul] at h_ϕ_a_le
    exact h_ϕ_a_le
  apply this.trans
  have h_div : ϕ b / (ϕ b + 1) ≤ 1 := by
    rw [div_le_one (add_pos_of_nonneg_of_pos h_ϕ_nonneg_b _root_.zero_lt_one)]
    linarith
  gcongr
  calc (ε / (ϕ b + 1)) * ϕ b = ε * (ϕ b / (ϕ b + 1)) := by ring
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left h_div (le_of_lt hε)
    _ = ε := mul_one ε

/-- Strong Duality: if ϕ(a) ≤ ϕ(b) for all ϕ in the spectrum, then a ≤ b in the asymptotic closure. -/
theorem spectrum_le_imp_asymptotic_le (a b : R) :
  (∀ ϕ : AsymptoticSpectrum R P, ϕ a ≤ ϕ b) → AsymptoticLe P a b := sorry

theorem asymptotic_le_iff_spectrum_le (a b : R) :
  AsymptoticLe P a b ↔ ∀ ϕ : AsymptoticSpectrum R P, ϕ a ≤ ϕ b :=
  ⟨asymptotic_le_imp_spectrum_le P, spectrum_le_imp_asymptotic_le P a b⟩

end StrassenPreorder
