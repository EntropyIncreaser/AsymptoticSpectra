import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import AsymptoticSpectra.Structures
import AsymptoticSpectra.Submultiplicative

universe u

noncomputable section

open Classical Filter Topology

variable {R : Type u} [CommSemiring R]

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
  apply P.le_trans (a * b) (↑(rank P a) * b) (↑(rank P a) * ↑(rank P b))
  · exact P.mul_right a (↑(rank P a)) h1 b
  · rw [mul_comm (rank P a : R), mul_comm (rank P a : R)]
    exact P.mul_right b (↑(rank P b)) h2 (↑(rank P a))

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

theorem rank_pow_submultiplicative_base (P : StrassenPreorder R) (a : R) : IsSubmultiplicative (fun n => (rank P (a ^ n) : ℝ)) := by
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
        have h_mul := P.mul_right 1 a h (a ^ n)
        rw [one_mul] at h_mul
        exact P.le_trans 1 (a ^ n) (a * a ^ n) ih h_mul
    have h_rank := rank_monotone P 1 (a ^ n) h'
    rw [rank_one P] at h_rank
    exact h_rank

/-- The asymptotic rank is the limit of the normalized rank of high powers. -/
def asymptotic_rank (P : StrassenPreorder R) (a : R) : ℝ :=
  if a = 0 then 0 else IsSubmultiplicative.lim (rank_pow_submultiplicative_base P a)

theorem tends_to_asymptotic_rank (P : StrassenPreorder R) (a : R) (ha : a ≠ 0) :
  Tendsto (fun n : ℕ => (rank P (a ^ n) : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 (asymptotic_rank P a)) := by
  unfold asymptotic_rank
  simp [ha]
  have := IsSubmultiplicative.tends_to_lim (rank_pow_submultiplicative_base P a) (rank_pow_ge_one P a ha)
  convert this using 1
  ext n
  simp

theorem exists_nat_mul_le (P : StrassenPreorder R) (a b : R) (hb : b ≠ 0) :
    ∃ n : ℕ, P.le a (n * b) := by
  rcases P.lower_archimedean b with h | h_le_b
  · contradiction
  obtain ⟨n, hn⟩ := P.upper_archimedean a
  use n
  apply P.le_trans _ (n : R) _ hn
  rw [mul_comm]
  simpa using P.mul_right 1 b h_le_b n

/-- The relative rank of a with respect to b. Defined only when b ≠ 0. -/
def relative_rank (P : StrassenPreorder R) (a b : R) (hb : b ≠ 0) : ℕ :=
  Nat.find (exists_nat_mul_le P a b hb)

theorem relative_rank_spec (P : StrassenPreorder R) (a b : R) (hb : b ≠ 0) :
    P.le a (relative_rank P a b hb * b) := by
  unfold relative_rank
  exact Nat.find_spec (exists_nat_mul_le P a b hb)

theorem relative_rank_le_of_le (P : StrassenPreorder R) {a b : R} {k : ℕ} (hb : b ≠ 0)
    (h : P.le a (k * b)) : relative_rank P a b hb ≤ k := by
  unfold relative_rank
  apply Nat.find_min'
  exact h

theorem relative_rank_mono_left (P : StrassenPreorder R) {a1 a2 b : R} (hb : b ≠ 0)
    (h : P.le a1 a2) : relative_rank P a1 b hb ≤ relative_rank P a2 b hb := by
  apply relative_rank_le_of_le P hb
  apply P.le_trans _ a2 _ h (relative_rank_spec P a2 b hb)

theorem relative_rank_anti_right (P : StrassenPreorder R) {a b1 b2 : R} (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0)
    (h : P.le b1 b2) : relative_rank P a b2 hb2 ≤ relative_rank P a b1 hb1 := by
  apply relative_rank_le_of_le P hb2
  apply P.le_trans _ _ _ (relative_rank_spec P a b1 hb1)
  have : P.le ((relative_rank P a b1 hb1 : R) * b1) ((relative_rank P a b1 hb1 : R) * b2) := by
       rw [mul_comm, mul_comm _ b2]
       apply P.mul_right b1 b2 h
  exact this

theorem relative_rank_submultiplicative (P : StrassenPreorder R) (a1 a2 b1 b2 : R)
    (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0) :
    relative_rank P (a1 * a2) (b1 * b2) (StrassenPreorder.mul_ne_zero P hb1 hb2) ≤ relative_rank P a1 b1 hb1 * relative_rank P a2 b2 hb2 := by
  apply relative_rank_le_of_le P (StrassenPreorder.mul_ne_zero P hb1 hb2)
  rw [Nat.cast_mul]
  let r1 := relative_rank P a1 b1 hb1
  let r2 := relative_rank P a2 b2 hb2
  have h1 := relative_rank_spec P a1 b1 hb1
  have h2 := relative_rank_spec P a2 b2 hb2
  letI := P.toPreorder
  apply P.le_trans (a1 * a2) (↑r1 * b1 * a2) (↑r1 * ↑r2 * (b1 * b2))
  · exact P.mul_right a1 (↑r1 * b1) h1 a2
  · have h_mul := P.mul_right a2 (↑r2 * b2) h2 (↑r1 * b1)
    have h_eq1 : (↑r1 * b1 * a2 : R) = a2 * (↑r1 * b1) := by ring
    have h_eq2 : (↑r1 * ↑r2 * (b1 * b2) : R) = (↑r2 * b2) * (↑r1 * b1) := by ring
    rw [h_eq1, h_eq2]
    exact h_mul

theorem rank_eq_relative_rank (P : StrassenPreorder R) (a : R) (h1 : (1 : R) ≠ 0) :
    rank P a = relative_rank P a 1 h1 := by
  unfold rank relative_rank
  congr
  simp only [mul_one]

theorem relative_rank_pow_submultiplicative (P : StrassenPreorder R) (a b : R) (hb : b ≠ 0) :
    IsSubmultiplicative (fun n => (relative_rank P (a ^ n) (b ^ n) (StrassenPreorder.pow_ne_zero P n hb) : ℝ)) := by
  intro m n
  dsimp
  norm_cast
  have h_bm : b ^ m ≠ 0 := StrassenPreorder.pow_ne_zero P m hb
  have h_bn : b ^ n ≠ 0 := StrassenPreorder.pow_ne_zero P n hb
  have h_sub := relative_rank_submultiplicative P (a^m) (a^n) (b^m) (b^n) h_bm h_bn
  convert h_sub using 2 <;> rw [pow_add]

end StrassenPreorder
