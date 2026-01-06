import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.CharZero.Defs

universe u

/-- Bundled Strassen preorder on a commutative semiring. -/
structure StrassenPreorder (α : Type u) [CommSemiring α] extends Preorder α where
  add_right : ∀ a b, le a b → ∀ c, le (a + c) (b + c)
  mul_right : ∀ a b, le a b → ∀ c, le (a * c) (b * c)
  nat_order_embedding : ∀ n m : ℕ, le (n : α) (m : α) ↔ n ≤ m
  lower_archimedean : ∀ a : α, a = 0 ∨ le 1 a
  upper_archimedean : ∀ a : α, ∃ n : ℕ, le a (n : α)

namespace StrassenPreorder

variable {α : Type u} [CommSemiring α]

instance : PartialOrder (StrassenPreorder α) where
  le P Q := ∀ a b, P.le a b → Q.le a b
  le_refl P a b h := h
  le_trans P Q R hPQ hQR a b h := hQR _ _ (hPQ _ _ h)
  le_antisymm P Q hPQ hQP := by
    cases P; cases Q
    congr
    · ext a b
      exact ⟨hPQ a b, hQP a b⟩

variable (P : StrassenPreorder α)

theorem zero_le_one : P.le 0 1 := by
  rw [← Nat.cast_zero, ← Nat.cast_one, P.nat_order_embedding]
  exact Nat.le_succ 0

theorem zero_lt_one : P.le 0 1 ∧ ¬ P.le 1 0 := by
  constructor
  · exact P.zero_le_one
  · rw [← Nat.cast_one, ← Nat.cast_zero, P.nat_order_embedding]
    exact Nat.not_succ_le_zero 0

theorem all_nonneg (a : α) : P.le 0 a := by
  cases P.lower_archimedean a with
  | inl h => rw [h]; exact P.le_refl 0
  | inr h =>
    exact P.le_trans 0 1 a P.zero_le_one h

/-- Create a local Strassen context by activating the instances. -/
def activate (P : StrassenPreorder α) (f : [Preorder α] → [CovariantClass α α (· + ·) (· ≤ ·)] → [PosMulMono α] → [MulPosMono α] → β) : β :=
  letI : Preorder α := P.toPreorder
  letI : CovariantClass α α (· + ·) (· ≤ ·) := ⟨fun a _ _ bc ↦ by
    rw [add_comm a, add_comm a]
    exact P.add_right _ _ bc a⟩
  letI : PosMulMono α := ⟨fun x _ _ h ↦ by
    rw [mul_comm x.1, mul_comm x.1]
    exact P.mul_right _ _ h x.1⟩
  letI : MulPosMono α := ⟨fun x _ _ h ↦ P.mul_right _ _ h x.1⟩
  f

instance (P : StrassenPreorder α) : CharZero α where
  cast_injective := by
    intro n m h
    have h1 : P.le (n : α) (m : α) := by rw [h]; exact P.le_refl _
    have h2 : P.le (m : α) (n : α) := by rw [h]; exact P.le_refl _
    rw [P.nat_order_embedding] at h1 h2
    exact Nat.le_antisymm h1 h2

end StrassenPreorder
