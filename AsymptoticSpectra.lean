import Mathlib.Analysis.SpecialFunctions.Pow.Real
import AsymptoticSpectra.Submultiplicative

noncomputable section

open Classical Set Filter Topology

class StrassenOrderedCommSemiring (α : Type u) extends OrderedCommSemiring α, CharZero α where
  lower_archimedean : ∀ a : α, a = 0 ∨ 1 ≤ a
  upper_archimedean : ∀ a : α, ∃ n : ℕ, a ≤ n

variable [StrassenOrderedCommSemiring R]

namespace StrassenOrderedCommSemiring

theorem all_nonneg (a : R) : 0 ≤ a := by {
  cases lower_archimedean a with
  | inl h => rw [h]
  | inr h => exact le_trans zero_le_one h
}

def rank (a : R) : ℕ := Nat.find (StrassenOrderedCommSemiring.upper_archimedean a)

theorem rank.monotone (a b : R) : a ≤ b → rank a ≤ rank b := by {
  intro h
  apply Nat.find_min'
  exact le_trans h (Nat.find_spec (upper_archimedean b))
}

theorem rank.submultiplicative (a b : R) : rank (a * b) ≤ rank a * rank b := by {
  apply Nat.find_min'
  rw [Nat.cast_mul]
  exact mul_le_mul (Nat.find_spec (upper_archimedean a)) (Nat.find_spec (upper_archimedean b)) (all_nonneg b) (all_nonneg ↑(rank a))
}

theorem rank.one : rank (1 : R) = 1 := by {
  apply le_antisymm
  · apply Nat.find_min'
    simp
  · have h_pos : (1 : R) > 0 := by norm_cast
    have : rank (1 : R) ≠ 0 := by {
      intro h
      have h_spec := Nat.find_spec (upper_archimedean (1 : R))
      dsimp [rank] at h
      rw [h] at h_spec
      simp at h_spec
      exact not_le_of_gt h_pos h_spec
    }
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero this)
}

theorem rank_pow_submultiplicative (a : R) : IsSubmultiplicative (fun n => (rank (a ^ n) : ℝ)) := by {
  intro m n
  dsimp
  rw [pow_add]
  norm_cast
  apply rank.submultiplicative
}

theorem rank_pow_ge_one (a : R) (ha : a ≠ 0) (n : ℕ) : 1 ≤ (rank (a ^ n) : ℝ) := by {
  norm_cast
  cases lower_archimedean a with
  | inl h => contradiction
  | inr h => {
    have h' : 1 ≤ a ^ n := by {
      rw [← one_pow n]
      apply pow_le_pow_of_le_left (all_nonneg 1) h
    }
    have : rank 1 ≤ rank (a ^ n) := rank.monotone 1 (a ^ n) h'
    rw [rank.one] at this
    exact this
  }
}

def asymptotic_rank (a : R) : ℝ :=
  if _h : a = 0 then 0 else (IsSubmultiplicative.lim (rank_pow_submultiplicative a))

theorem tends_to_asymptotic_rank (a : R) (ha : a ≠ 0) :
  Tendsto (fun n : ℕ => (rank (a ^ n) : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 (asymptotic_rank a)) := by {
  unfold asymptotic_rank
  simp [ha]
  convert IsSubmultiplicative.tends_to_lim (rank_pow_submultiplicative a) (rank_pow_ge_one a ha) using 1
  ext n
  simp
}

end StrassenOrderedCommSemiring
