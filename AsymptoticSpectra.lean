import Mathlib.Data.Nat.Cast.Order

noncomputable section

open Classical

class StrassenOrderedCommSemiring (α : Type u) extends OrderedCommSemiring α, CharZero α where
  lower_archimedean : ∀ a : α, a = 0 ∨ 1 ≤ a
  upper_archimedean : ∀ a : α, ∃ n : ℕ, a ≤ n

variable [StrassenOrderedCommSemiring R]

example (a b c d : R) : a ≤ b → c ≤ d → a + c ≤ b + d := add_le_add
example {m n : ℕ} : (m : R) ≤ n ↔ m ≤ n := Nat.cast_le
example : ℕ ↪o R := Nat.castOrderEmbedding

namespace StrassenOrderedCommSemiring

theorem all_nonneg (a : R) : 0 ≤ a := by {
  cases (lower_archimedean a)
  case inl h => { rw [h] }
  case inr h => { exact le_trans zero_le_one h }
}

def rank (a : R) : ℕ := Nat.find (StrassenOrderedCommSemiring.upper_archimedean a)

theorem rank.monotone (a b : R) : a ≤ b → rank a ≤ rank b := by {
  intro h
  let n := rank b
  have h' : b ≤ n := Nat.find_spec (upper_archimedean b)
  apply Nat.find_min'
  exact le_trans h h'
}

theorem rank.subadditive (a b : R) : rank (a + b) ≤ rank a + rank b := by {
  let n := rank a
  let m := rank b
  have h₁ : a ≤ n := Nat.find_spec (upper_archimedean a)
  have h₂ : b ≤ m := Nat.find_spec (upper_archimedean b)
  apply Nat.find_min'
  simp
  exact add_le_add h₁ h₂
}

theorem rank.submultiplicative (a b : R) : rank (a * b) ≤ rank a * rank b := by {
  let n := rank a
  let m := rank b
  have h₁ : a ≤ n := Nat.find_spec (upper_archimedean a)
  have h₂ : b ≤ m := Nat.find_spec (upper_archimedean b)
  apply Nat.find_min'
  simp
  exact mul_le_mul h₁ h₂ (all_nonneg b) (all_nonneg ↑n)
}
