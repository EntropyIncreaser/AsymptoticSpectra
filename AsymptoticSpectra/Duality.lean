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
instance (P : StrassenPreorder R) : Nonempty (AsymptoticSpectrum R P) := by
  obtain ⟨Q, hP_le_Q, hQ_max⟩ := StrassenPreorder.total_extension P
  have hQ_props := (StrassenPreorder.isMaximal_iff_isTotal_isClosed Q).mp hQ_max
  let E : MaxExtension R P := ⟨Q, hP_le_Q, hQ_props.1, hQ_props.2⟩
  exact ⟨(asymptoticSpectrumEquivMaxExtensions P).symm E⟩

namespace StrassenPreorder

/-- The Duality Theorem (Part 1): the asymptotic rank is the maximum of evaluations over the spectrum. -/
theorem asymptotic_rank_eq_max_spectrum (a : R) :
  asymptotic_rank P a = ⨆ (ϕ : AsymptoticSpectrum R P), ϕ a := sorry

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

end StrassenPreorder
