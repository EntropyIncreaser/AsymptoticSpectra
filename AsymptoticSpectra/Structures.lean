import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.Ext

universe u

/-- Intermediate preorder on a commutative semiring with add_right and mul_right axioms. -/
structure SemiringPreorder (α : Type u) [CommSemiring α] extends Preorder α where
  add_right : ∀ a b, le a b → ∀ c, le (a + c) (b + c)
  mul_right : ∀ a b, le a b → ∀ c, le (a * c) (b * c)

/-- Bundled Strassen preorder on a commutative semiring. -/
structure StrassenPreorder (α : Type u) [CommSemiring α] extends SemiringPreorder α where
  nat_order_embedding : ∀ n m : ℕ, le (n : α) (m : α) ↔ n ≤ m
  lower_archimedean : ∀ a : α, a = 0 ∨ le 1 a
  upper_archimedean : ∀ a : α, ∃ n : ℕ, le a (n : α)

namespace SemiringPreorder

variable {α : Type u} [CommSemiring α]

instance : PartialOrder (SemiringPreorder α) where
  le P Q := ∀ a b, P.le a b → Q.le a b
  le_refl P a b h := h
  le_trans P Q R hPQ hQR a b h := hQR _ _ (hPQ _ _ h)
  le_antisymm P Q hPQ hQP := by
    cases P; cases Q
    congr
    · ext a b
      exact ⟨hPQ a b, hQP a b⟩

end SemiringPreorder

namespace StrassenPreorder

variable {α : Type u} [CommSemiring α]

instance : PartialOrder (StrassenPreorder α) where
  le P Q := (P.toSemiringPreorder ≤ Q.toSemiringPreorder)
  le_refl P := le_refl _
  le_trans P Q R := le_trans
  le_antisymm P Q hPQ hQP := by
    have h : P.toSemiringPreorder = Q.toSemiringPreorder := le_antisymm hPQ hQP
    cases P; cases Q
    congr

@[ext]
theorem ext {P Q : StrassenPreorder α} (h : ∀ a b, P.le a b ↔ Q.le a b) : P = Q :=
  le_antisymm (fun a b => (h a b).mp) (fun a b => (h a b).mpr)

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
  letI : PosMulMono α := ⟨fun x _ _ _ h ↦ by
    rw [mul_comm x, mul_comm x]
    exact P.mul_right _ _ h x⟩
  letI : MulPosMono α := ⟨fun x _ _ _ h ↦ P.mul_right _ _ h x⟩
  f

theorem instCharZero (P : StrassenPreorder α) : CharZero α where
  cast_injective := by
    intro n m h
    have h1 : P.le (n : α) (m : α) := by rw [h]; exact P.le_refl _
    have h2 : P.le (m : α) (n : α) := by rw [h]; exact P.le_refl _
    rw [P.nat_order_embedding] at h1 h2
    exact Nat.le_antisymm h1 h2

/-- A Strassen preorder automatically implies NoZeroDivisors. -/
theorem toNoZeroDivisors (P : StrassenPreorder α) : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    by_cases ha : a = 0; · left; exact ha
    by_cases hb : b = 0; · right; exact hb
    exfalso
    letI := P.toPreorder
    cases P.lower_archimedean a with
    | inl ha' => exact ha ha'
    | inr ha' =>
      cases P.lower_archimedean b with
      | inl hb' => exact hb hb'
      | inr hb' =>
        have h1 : P.le (1 : α) (a * b) := by
          apply P.le_trans (1 : α) a (a * b)
          · exact ha'
          · rw [mul_comm]
            simpa [mul_comm] using P.mul_right 1 b hb' a
        rw [h] at h1
        have h_zero : ¬ P.le 1 0 := by
          rw [← Nat.cast_one, ← Nat.cast_zero, P.nat_order_embedding]
          exact Nat.not_succ_le_zero 0
        exact h_zero h1

theorem mul_ne_zero (P : StrassenPreorder α) {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  letI := P.toNoZeroDivisors
  _root_.mul_ne_zero ha hb

theorem pow_ne_zero (P : StrassenPreorder α) (n : ℕ) {a : α} (ha : a ≠ 0) : a ^ n ≠ 0 :=
  letI := P.toNoZeroDivisors
  _root_.pow_ne_zero n ha

/-- A Strassen preorder is total if for any a, b, either a ≤ b or b ≤ a. -/
def IsTotal (P : StrassenPreorder α) : Prop :=
  ∀ a b : α, P.le a b ∨ P.le b a

end StrassenPreorder
