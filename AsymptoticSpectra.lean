import Mathlib.Data.Nat.Cast.Order.Basic
-- import Mathlib.Algebra.GroupPower.Order
import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Order.Monotone.Basic
import AsymptoticSpectra.Submultiplicative
import AsymptoticSpectra.Structures
import AsymptoticSpectra.AsymptoticClosure

universe u

noncomputable section

open Classical Set Filter Topology

/-- A point in the asymptotic spectrum is a monotone semiring homomorphism to ℝ. -/
structure AsymptoticSpectrumPoint (R : Type u) [CommSemiring R] (P : StrassenPreorder R) extends R →+* ℝ where
  monotone' : ∀ {a b : R}, P.le a b → toRingHom a ≤ toRingHom b

/-- The asymptotic spectrum is the set of monotone semiring homomorphisms to ℝ. -/
abbrev AsymptoticSpectrum (R : Type u) [CommSemiring R] (P : StrassenPreorder R) : Type u :=
  AsymptoticSpectrumPoint R P

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

theorem continuous_eval (P : StrassenPreorder R) (a : R) :
  Continuous (fun (ϕ : AsymptoticSpectrumPoint R P) => ϕ a) :=
  continuous_pi_iff.mp continuous_induced_dom a

/-- The asymptotic spectrum is a compact Hausdorff space. -/
instance (P : StrassenPreorder R) : CompactSpace (AsymptoticSpectrum R P) := sorry

instance (P : StrassenPreorder R) : T2Space (AsymptoticSpectrum R P) := sorry

namespace StrassenPreorder

/-- The rank of an element is the smallest natural number n such that a ≤ n. -/
def rank (P : StrassenPreorder R) (a : R) : ℕ := Nat.find (P.upper_archimedean a)

theorem rank_monotone (P : StrassenPreorder R) (a b : R) : P.le a b → rank P a ≤ rank P b := by
  letI := P.toPreorder
  intro h
  apply Nat.find_min'
  exact P.le_trans _ _ _ h (Nat.find_spec (P.upper_archimedean b))

theorem rank_submultiplicative (P : StrassenPreorder R) (a : R) (b : R) : rank P (a * b) ≤ rank P a * rank P b := by
  letI := P.toPreorder
  apply Nat.find_min'
  show P.le (a * b) ↑(rank P a * rank P b)
  rw [Nat.cast_mul]
  have h1 := Nat.find_spec (P.upper_archimedean a)
  have h2 := Nat.find_spec (P.upper_archimedean b)
  apply P.le_trans (a * b) (rank P a * b) (↑(rank P a) * ↑(rank P b))
  · exact P.mul_right a (rank P a) h1 b
  · rw [mul_comm (rank P a : R), mul_comm (rank P a : R)]
    exact P.mul_right b (rank P b) h2 (rank P a)

theorem rank_one (P : StrassenPreorder R) : rank P 1 = 1 := by
  letI := P.toPreorder
  apply le_antisymm
  · apply Nat.find_min'
    convert P.le_refl (1 : R)
    simp
  · have h_pos_nle : ¬ P.le 1 0 := by
      rw [← Nat.cast_one, ← Nat.cast_zero, P.nat_order_embedding]
      exact Nat.not_succ_le_zero 0
    have : rank P 1 ≠ 0 := by
      intro h_rank
      have h_spec := Nat.find_spec (P.upper_archimedean (1 : R))
      dsimp [rank] at h_rank
      rw [h_rank] at h_spec
      simp at h_spec
      exact h_pos_nle h_spec
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero this)

theorem rank_pow_submultiplicative (P : StrassenPreorder R) (a : R) : IsSubmultiplicative (fun n => (rank P (a ^ n) : ℝ)) := by
  intro m n
  dsimp
  rw [pow_add]
  norm_cast
  apply rank_submultiplicative

theorem rank_pow_ge_one (P : StrassenPreorder R) (a : R) (ha : a ≠ 0) (n : ℕ) : 1 ≤ (rank P (a ^ n) : ℝ) := by
  letI := P.toPreorder
  norm_cast
  cases P.lower_archimedean a with
  | inl h => contradiction
  | inr h =>
    have h' : P.le 1 (a ^ n) := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, mul_comm]
        exact P.le_trans 1 a (a * a ^ n) h (by rw [mul_comm a]; simpa using P.mul_right 1 (a ^ n) ih a)
    have h_rank := rank_monotone P 1 (a ^ n) h'
    rw [rank_one P] at h_rank
    exact h_rank

/-- The asymptotic rank is the limit of the normalized rank of high powers. -/
def asymptotic_rank (P : StrassenPreorder R) (a : R) : ℝ :=
  if a = 0 then 0 else IsSubmultiplicative.lim (rank_pow_submultiplicative P a)

theorem tends_to_asymptotic_rank (P : StrassenPreorder R) (a : R) (ha : a ≠ 0) :
  Tendsto (fun n : ℕ => (rank P (a ^ n) : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 (asymptotic_rank P a)) := by
  unfold asymptotic_rank
  simp [ha]
  have := IsSubmultiplicative.tends_to_lim (rank_pow_submultiplicative P a) (rank_pow_ge_one P a ha)
  convert this using 1
  ext n
  simp

end StrassenPreorder
