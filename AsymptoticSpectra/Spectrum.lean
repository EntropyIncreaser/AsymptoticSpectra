import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import AsymptoticSpectra.Structures
import AsymptoticSpectra.Rank
import AsymptoticSpectra.AsymptoticClosure

universe u

noncomputable section

open Classical Set Filter Topology

/-- A point in the asymptotic spectrum is a monotone semiring homomorphism to ℝ. -/
structure AsymptoticSpectrumPoint (R : Type u) [CommSemiring R] (P : StrassenPreorder R) extends R →+* ℝ where
  monotone' : ∀ {a b : R}, P.le a b → toRingHom a ≤ toRingHom b

namespace StrassenPreorder

/-- For a total Strassen preorder, the fractional rank defines a point in the asymptotic spectrum. -/
def rho_asymptoticSpectrumPoint {R : Type u} [CommSemiring R] (P : StrassenPreorder R)
    (total : P.IsTotal) : AsymptoticSpectrumPoint R P where
  toRingHom := P.rho_toRingHom total
  monotone' := by
    intro a b h
    exact P.rho_monotone h

end StrassenPreorder

/-- The asymptotic spectrum is the set of monotone semiring homomorphisms to ℝ. -/
abbrev AsymptoticSpectrum (R : Type u) [CommSemiring R] (P : StrassenPreorder R) : Type u :=
  AsymptoticSpectrumPoint R P

/-- The type of maximal extensions of a Strassen preorder P.
    A Strassen preorder is maximal if and only if it is total and closed. -/
abbrev MaxExtension (R : Type u) [CommSemiring R] (P : StrassenPreorder R) : Type u :=
  { Q : StrassenPreorder R // P ≤ Q ∧ Q.IsTotal ∧ Q.IsClosed }

variable {R : Type u} [CommSemiring R]

instance (P : StrassenPreorder R) : FunLike (AsymptoticSpectrumPoint R P) R ℝ where
  coe f := f.toRingHom.toFun
  coe_injective' f g h := by
    obtain ⟨f_hom, f_mono⟩ := f
    obtain ⟨g_hom, g_mono⟩ := g
    congr
    exact DFunLike.coe_injective h

instance (P : StrassenPreorder R) : RingHomClass (AsymptoticSpectrumPoint R P) R ℝ where
  map_add f := f.toRingHom.map_add'
  map_mul f := f.toRingHom.map_mul'
  map_zero f := f.toRingHom.map_zero'
  map_one f := f.toRingHom.map_one'

/-- The topology on the asymptotic spectrum is the topology of pointwise convergence. -/
instance (P : StrassenPreorder R) : TopologicalSpace (AsymptoticSpectrumPoint R P) :=
  TopologicalSpace.induced (fun f => (f : R → ℝ)) Pi.topologicalSpace

namespace AsymptoticSpectrumPoint

@[ext]
theorem ext {P : StrassenPreorder R} (ϕ ψ : AsymptoticSpectrumPoint R P) (h : ∀ a, ϕ a = ψ a) : ϕ = ψ :=
  DFunLike.ext ϕ ψ h

/-- Restrict a spectrum point from a larger preorder Q to a smaller preorder P. -/
def restrict {P Q : StrassenPreorder R} (h : P ≤ Q) (ϕ : AsymptoticSpectrumPoint R Q) :
    AsymptoticSpectrumPoint R P where
  toRingHom := ϕ.toRingHom
  monotone' := fun hab => ϕ.monotone' (h _ _ hab)

/-- Any point in the asymptotic spectrum defines a Strassen preorder. -/
def toStrassenPreorder {R : Type u} [CommSemiring R] {P : StrassenPreorder R}
    (ϕ : AsymptoticSpectrumPoint R P) : StrassenPreorder R where
  le a b := ϕ a ≤ ϕ b
  le_refl a := le_refl _
  le_trans a b c hab hbc := le_trans hab hbc
  add_right a b hab c := by
    rw [map_add, map_add]
    linarith
  mul_right a b hab c := by
    rw [map_mul, map_mul]
    have h0c : 0 ≤ ϕ c := by
      rw [← map_zero (ϕ.toRingHom)]
      apply ϕ.monotone'
      exact P.all_nonneg c
    nlinarith
  nat_order_embedding n m := by
    rw [map_natCast, map_natCast]
    exact Nat.cast_le
  lower_archimedean a := by
    cases P.lower_archimedean a with
    | inl h => left; simp [h]
    | inr h => right; simpa using ϕ.monotone' h
  upper_archimedean a := by
    obtain ⟨n, h⟩ := P.upper_archimedean a
    use n
    simpa using ϕ.monotone' h

/-- The preorder defined by a spectrum point is total. -/
theorem toStrassenPreorder_isTotal {R : Type u} [CommSemiring R] {P : StrassenPreorder R}
    (ϕ : AsymptoticSpectrumPoint R P) : ϕ.toStrassenPreorder.IsTotal :=
  fun a b => le_total (ϕ a) (ϕ b)

/-- The preorder defined by a spectrum point is closed. -/
theorem toStrassenPreorder_isClosed {R : Type u} [CommSemiring R] {P : StrassenPreorder R}
    (ϕ : AsymptoticSpectrumPoint R P) : ϕ.toStrassenPreorder.IsClosed := by
  intro a b h
  dsimp [toStrassenPreorder]
  obtain ⟨f, hf, hle⟩ := h
  dsimp [toStrassenPreorder] at hle
  have h_phi_le : ∀ n, (ϕ a)^n ≤ f n * (ϕ b)^n := by
    intro n
    specialize hle n
    rw [map_pow, map_mul, map_natCast, map_pow] at hle
    exact_mod_cast hle
  by_cases hb : 0 < ϕ b
  · apply le_of_forall_pos_le_add
    intro δ hδ
    let ε := δ / ϕ b
    have hε : 0 < ε := div_pos hδ hb
    have h_subexp := hf ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp h_subexp
    let n := N + 1
    specialize h_phi_le n
    specialize hN n (Nat.le_add_right N 1)
    have h_pow_pos : 0 < (ϕ b)^n := pow_pos hb n
    have h_ratio : (ϕ a / ϕ b)^n ≤ (f n : ℝ) := by
      rw [div_pow, div_le_iff₀ h_pow_pos]
      exact_mod_cast h_phi_le
    have h_final : (ϕ a / ϕ b)^n ≤ (1 + ε)^n := h_ratio.trans (by exact_mod_cast hN)
    have h_base : ϕ a / ϕ b ≤ 1 + ε := by
      have h_n_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos N)
      rw [← Real.rpow_le_rpow_iff _ (by linarith) h_n_pos]
      · simp only [Real.rpow_natCast]
        exact h_final
      · apply div_nonneg
        · rw [← map_zero (ϕ.toRingHom)]
          apply ϕ.monotone' (P.all_nonneg a)
        · linarith
    rw [div_le_iff₀ hb] at h_base
    calc ϕ a ≤ (1 + ε) * ϕ b := h_base
      _ = ϕ b + ε * ϕ b := by ring
      _ = ϕ b + δ := by rw [div_mul_cancel₀ _ (ne_of_gt hb)]
  · have hb0 : ϕ b = 0 := by
      have : 0 ≤ ϕ b := by
        rw [← map_zero (ϕ.toRingHom)]
        apply ϕ.monotone' (P.all_nonneg b)
      linarith
    rw [hb0] at h_phi_le
    specialize h_phi_le 1
    rw [hb0]
    simp only [pow_one, mul_zero] at h_phi_le
    have h_phi_a_pos : 0 ≤ ϕ a := by
      rw [← map_zero (ϕ.toRingHom)]
      apply ϕ.monotone' (P.all_nonneg a)
    linarith

/-- The preorder defined by a spectrum point extends the original preorder P. -/
theorem toStrassenPreorder_le {R : Type u} [CommSemiring R] {P : StrassenPreorder R}
    (ϕ : AsymptoticSpectrumPoint R P) (a b : R) (h : P.le a b) :
    ϕ.toStrassenPreorder.le a b :=
  ϕ.monotone' h

/-- The fractional rank of the preorder induced by ϕ is ϕ itself. -/
theorem rho_of_toStrassenPreorder {R : Type u} [CommSemiring R] {P : StrassenPreorder R}
    (ϕ : AsymptoticSpectrumPoint R P) (a : R) :
    ϕ.toStrassenPreorder.rho a = ϕ a := by
  let Q := ϕ.toStrassenPreorder
  apply le_antisymm
  · apply le_of_forall_gt
    intro v hv
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hv
    have : Q.rho a ≤ (q : ℝ) := by
      apply csInf_le (Q.rho_set_bddBelow a)
      have h_phi_pos : 0 ≤ ϕ a := by rw [← map_zero (ϕ.toRingHom)]; apply ϕ.monotone'; exact P.all_nonneg a
      have hq_pos : 0 < (q : ℝ) := lt_of_le_of_lt h_phi_pos hq1
      have h_q_num_pos : 0 ≤ q.num := by
        apply Rat.num_nonneg.mpr
        exact_mod_cast hq_pos.le
      let n := q.num.toNat
      let m := q.den
      refine ⟨n, m, q.pos, ?_, ?_⟩
      · dsimp [Q, toStrassenPreorder]
        rw [map_mul, map_natCast, map_natCast]
        have hq_val : (q : ℝ) = (n : ℝ) / (m : ℝ) := by
          rw [Rat.cast_def q]
          congr
          exact (Int.toNat_of_nonneg h_q_num_pos).symm
        have h_den_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr q.pos
        have hq' : ϕ a < (n : ℝ) / (m : ℝ) := by rwa [← hq_val]
        rw [lt_div_iff₀ h_den_pos] at hq'
        nlinarith
      · rw [Rat.cast_def q]
        congr
        exact (Int.toNat_of_nonneg h_q_num_pos).symm
    exact lt_of_le_of_lt this hq2
  · apply le_csInf (Q.rho_set_nonempty a)
    rintro x ⟨n, m, hm, h, rfl⟩
    dsimp [Q, toStrassenPreorder] at h
    rw [map_mul, map_natCast, map_natCast] at h
    have h_m_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    rw [le_div_iff₀ h_m_pos, mul_comm]
    exact h

end AsymptoticSpectrumPoint

/-- Map from a spectrum point to its corresponding maximal extension. -/
def spectrumToMaxExtension {P : StrassenPreorder R} (ϕ : AsymptoticSpectrumPoint R P) :
    MaxExtension R P :=
  ⟨ϕ.toStrassenPreorder, ⟨ϕ.toStrassenPreorder_le, ϕ.toStrassenPreorder_isTotal, ϕ.toStrassenPreorder_isClosed⟩⟩

/-- Map from a maximal extension to its corresponding spectrum point. -/
def maxExtensionToSpectrum {P : StrassenPreorder R} (E : MaxExtension R P) :
    AsymptoticSpectrumPoint R P :=
  let ϕ_E := E.val.rho_asymptoticSpectrumPoint E.property.2.1
  AsymptoticSpectrumPoint.restrict E.property.1 ϕ_E

/-- spectrumToMaxExtension is the left inverse of maxExtensionToSpectrum. -/
theorem spectrum_left_inverse {P : StrassenPreorder R} (ϕ : AsymptoticSpectrumPoint R P) :
    maxExtensionToSpectrum (spectrumToMaxExtension ϕ) = ϕ := by
  ext a
  dsimp [maxExtensionToSpectrum, spectrumToMaxExtension, AsymptoticSpectrumPoint.restrict, StrassenPreorder.rho_asymptoticSpectrumPoint]
  apply AsymptoticSpectrumPoint.rho_of_toStrassenPreorder

/-- spectrumToMaxExtension is the right inverse of maxExtensionToSpectrum. -/
theorem spectrum_right_inverse {P : StrassenPreorder R} (E : MaxExtension R P) :
    spectrumToMaxExtension (maxExtensionToSpectrum E) = E := by
  apply Subtype.ext
  ext a b
  dsimp [spectrumToMaxExtension, maxExtensionToSpectrum, AsymptoticSpectrumPoint.restrict, AsymptoticSpectrumPoint.toStrassenPreorder,
    StrassenPreorder.rho_asymptoticSpectrumPoint, AsymptoticSpectrumPoint.toRingHom,
    StrassenPreorder.rho_toRingHom]
  change (E.val.rho a ≤ E.val.rho b ↔ E.val.le a b)
  rw [StrassenPreorder.rho_reflects_le E.val E.property.2.1 E.property.2.2]

/-- The asymptotic spectrum of P is in bijection with the maximal extensions of P. -/
noncomputable def asymptoticSpectrumEquivMaxExtensions (P : StrassenPreorder R) :
    AsymptoticSpectrumPoint R P ≃ MaxExtension R P where
  toFun := spectrumToMaxExtension
  invFun := maxExtensionToSpectrum
  left_inv := spectrum_left_inverse
  right_inv := spectrum_right_inverse

theorem continuous_eval {R : Type u} [CommSemiring R] (P : StrassenPreorder R) (a : R) :
  Continuous (fun (ϕ : AsymptoticSpectrumPoint R P) => ϕ a) :=
  continuous_pi_iff.mp continuous_induced_dom a

/-- The asymptotic spectrum is a compact Hausdorff space. -/
instance (P : StrassenPreorder R) : CompactSpace (AsymptoticSpectrum R P) := sorry

instance (P : StrassenPreorder R) : T2Space (AsymptoticSpectrum R P) := sorry
