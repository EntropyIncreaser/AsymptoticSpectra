import AsymptoticSpectra.Structures
import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.GroupPower.Order

universe u

noncomputable section

open Filter Topology

variable {R : Type u} [CommSemiring R]

/-- A function f : ℕ → ℕ has subexponential growth if for every ε > 0,
  f n is eventually bounded by (1 + ε)^n. -/
def IsSubexponential (f : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, (f n : ℝ) ≤ (1 + ε) ^ (n : ℝ)

lemma IsSubexponential.const_one : IsSubexponential (fun _ => 1) := by
  intro ε hε
  apply eventually_atTop.mpr
  use 0
  intro n _
  simp
  apply one_le_pow_of_one_le
  linarith

lemma IsSubexponential.mul {f g : ℕ → ℕ} (hf : IsSubexponential f) (hg : IsSubexponential g) :
    IsSubexponential (fun n => f n * g n) := by
  intro ε hε
  let η := Real.sqrt (1 + ε) - 1
  have hη : 0 < η := by
    apply sub_pos.mpr
    rw [Real.lt_sqrt (by linarith)]
    simp [hε]
  specialize hf η hη
  specialize hg η hη
  filter_upwards [hf, hg] with n hfn hgn
  have h_prod : ((f n * g n : ℕ) : ℝ) = (f n : ℝ) * (g n : ℝ) := by norm_cast
  rw [h_prod]
  have h_bound : (f n : ℝ) * (g n : ℝ) ≤ (1 + η) ^ (n : ℝ) * (1 + η) ^ (n : ℝ) :=
    mul_le_mul hfn hgn (Nat.cast_nonneg _) (Real.rpow_nonneg_of_nonneg (by linarith) _)
  apply h_bound.trans
  rw [← Real.mul_rpow (by linarith) (by linarith)]
  have h_sqrt : (1 + η) * (1 + η) = 1 + ε := by
    simp [η]
    have : 0 ≤ 1 + ε := by linarith
    rw [Real.mul_self_sqrt this]
  rw [h_sqrt]

/-- The asymptotic preorder on R with respect to a Strassen preorder P. -/
def AsymptoticLe (P : StrassenPreorder R) (a b : R) : Prop :=
  ∃ f : ℕ → ℕ, IsSubexponential f ∧ ∀ n, P.le (a ^ n) ((f n : R) * b ^ n)

lemma AsymptoticLe.refl (P : StrassenPreorder R) (a : R) : AsymptoticLe P a a :=
  ⟨fun _ => 1, IsSubexponential.const_one, fun n => by
    rw [Nat.cast_one, one_mul]
    exact P.le_refl _⟩

lemma AsymptoticLe.trans (P : StrassenPreorder R) {a b c : R} (hab : AsymptoticLe P a b) (hbc : AsymptoticLe P b c) : AsymptoticLe P a c := by
  obtain ⟨f, hf, hfab⟩ := hab
  obtain ⟨g, hg, hgbc⟩ := hbc
  use fun n => f n * g n
  constructor
  · exact IsSubexponential.mul hf hg
  · intro n
    have h1 := hfab n
    have h2 := hgbc n
    -- a^n ≤ f n * b^n
    -- b^n ≤ g n * c^n
    -- f n * b^n ≤ f n * (g n * c^n)
    have h3 := P.mul_right _ _ h2 (f n : R)
    rw [mul_comm, mul_comm ((g n : R) * c^n)] at h3
    have h4 : P.le (a ^ n) (↑(f n) * (↑(g n) * c ^ n)) := P.le_trans _ _ _ h1 h3
    rw [← mul_assoc, ← Nat.cast_mul] at h4
    exact h4

namespace StrassenPreorder

variable {R : Type u} [CommSemiring R]

/-- The asymptotic closure of a Strassen preorder P. -/
def asymptoticClosure (P : StrassenPreorder R) : StrassenPreorder R where
  le := AsymptoticLe P
  le_refl := AsymptoticLe.refl P
  le_trans _ _ _ := AsymptoticLe.trans P
  add_right := sorry
  mul_right := sorry
  nat_order_embedding := sorry
  lower_archimedean := sorry
  upper_archimedean := sorry

end StrassenPreorder
