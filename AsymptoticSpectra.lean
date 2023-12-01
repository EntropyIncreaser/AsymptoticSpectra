import Mathlib.Algebra.Ring.Defs
import Mathlib.Init.Order.Defs
import Mathlib.Init.Data.Nat.Lemmas

noncomputable section

open Classical

class PreorderCommSemiring (α : Type u) extends CommSemiring α, Preorder α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b
  zero_le_one : (0 : α) ≤ 1

class StrassenPreorderCommSemiring (α : Type u) extends PreorderCommSemiring α where
  embed_nat : ∀ n m : ℕ, n ≤ m ↔ (n : α) ≤ m
  lower_archimedean : ∀ a : α, a = 0 ∨ 1 ≤ a
  upper_archimedean : ∀ a : α, ∃ n : ℕ, a ≤ n

variable [StrassenPreorderCommSemiring R]

lemma StrassenPreorderCommSemiring.add_le_add (a b c d : R) : (h₁ : a ≤ b) → (h₂ : c ≤ d) → a + c ≤ b + d := sorry

lemma StrassenPreorderCommSemiring.mul_le_mul (a b c d : R) : (h₁ : a ≤ b) → (h₂ : c ≤ d) → a * c ≤ b * d := sorry

namespace StrassenPreorderCommSemiring

def rank (a : R) : ℕ := Nat.find (StrassenPreorderCommSemiring.upper_archimedean a)

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
  exact add_le_add _ _ _ _ h₁ h₂
}

theorem rank.submultiplicative (a b : R) : rank (a * b) ≤ rank a * rank b := by {
  let n := rank a
  let m := rank b
  have h₁ : a ≤ n := Nat.find_spec (upper_archimedean a)
  have h₂ : b ≤ m := Nat.find_spec (upper_archimedean b)
  sorry
}
