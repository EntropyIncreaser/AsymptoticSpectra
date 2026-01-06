import AsymptoticSpectra.Structures
import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.GroupPower.Order
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast

universe u

noncomputable section

open Filter Topology Finset BigOperators

variable {R : Type u} [CommSemiring R]

/-- A function f : ℕ → ℕ has subexponential growth if for every ε > 0,
  f n is eventually bounded by (1 + ε)^n. -/
def IsSubexponential (f : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, (f n : ℝ) ≤ (1 + ε) ^ (n : ℝ)

lemma isSubexponential_iff_exists_constant {f : ℕ → ℕ} :
    IsSubexponential f ↔ ∀ ε > 0, ∃ C : ℝ, ∀ n, (f n : ℝ) ≤ C * (1 + ε) ^ (n : ℝ) := by
  constructor
  · intro h ε hε
    specialize h (ε/2) (half_pos hε)
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    let S := (Finset.range N).image (fun n => (f n : ℝ) / (1 + ε) ^ (n : ℝ))
    let C := max (1 : ℝ) (if hS : S.Nonempty then S.max' hS else 0)
    use C
    intro n
    by_cases hn : n < N
    · have hS : S.Nonempty := ⟨_, Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩⟩
      have h_mem : (f n : ℝ) / (1 + ε) ^ (n : ℝ) ∈ S := Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩
      have : (f n : ℝ) / (1 + ε) ^ (n : ℝ) ≤ C := by
        apply le_max_of_le_right
        rw [dif_pos hS]
        exact S.le_max' _ h_mem
      have h_pos : 0 < (1 + ε) ^ (n : ℝ) := Real.rpow_pos_of_pos (by linarith) _
      exact (div_le_iff h_pos).mp this
    · have h_ge : n ≥ N := not_lt.mp hn
      specialize hN n h_ge
      apply hN.trans
      have h1 : 0 ≤ 1 + ε / 2 := by linarith
      have h2 : 1 + ε / 2 ≤ 1 + ε := by linarith
      apply (Real.rpow_le_rpow h1 h2 (Nat.cast_nonneg n)).trans
      apply le_mul_of_one_le_left (Real.rpow_nonneg_of_nonneg (by linarith) _) (le_max_left _ _)
  · intro h ε hε
    have h_lt : (1 + ε / 2) < (1 + ε) := by linarith
    specialize h (ε / 2) (half_pos hε)
    obtain ⟨C, hC⟩ := h
    have h_ratio : (1 + ε / 2) / (1 + ε) < 1 := (div_lt_one (by linarith)).mpr h_lt
    have h_ratio_pos : 0 ≤ (1 + ε / 2) / (1 + ε) := by
      apply div_nonneg <;> linarith
    have h_lim : Tendsto (fun n : ℕ => C * ((1 + ε / 2) / (1 + ε)) ^ n) atTop (𝓝 0) := by
      rw [← mul_zero C]
      apply Tendsto.const_mul
      apply _root_.tendsto_pow_atTop_nhds_0_of_lt_1 h_ratio_pos h_ratio
    specialize h_lim (eventually_le_nhds (zero_lt_one' ℝ))
    filter_upwards [h_lim] with n hn
    specialize hC n
    apply hC.trans
    have h_pos : 0 < (1 + ε) ^ (n : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have h_le : C * ((1 + ε / 2) / (1 + ε)) ^ n ≤ 1 := hn
    have := mul_le_mul_of_nonneg_right h_le (le_of_lt h_pos)
    rw [← Real.rpow_nat_cast, Real.div_rpow (by linarith) (by linarith),
        mul_assoc, div_mul_cancel _ (ne_of_gt h_pos), one_mul] at this
    exact this

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

lemma IsSubexponential.sup_prefix {f : ℕ → ℕ} (hf : IsSubexponential f) :
    IsSubexponential (fun n => (range (n + 1)).sup f) := by
  rw [isSubexponential_iff_exists_constant] at hf ⊢
  intro ε hε
  obtain ⟨C, hC⟩ := hf ε hε
  let C' := max C 0
  use C'
  intro n
  obtain ⟨k, hk, h_sup⟩ := (range (n + 1)).exists_mem_eq_sup (nonempty_range_iff.mpr (Nat.succ_ne_zero n)) f
  rw [h_sup]
  apply (hC k).trans
  apply (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg_of_nonneg (by linarith) _)).trans
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le
    · linarith
    · simp at hk; exact_mod_cast (Nat.lt_succ_iff.mp hk)
  · exact le_max_right _ _

/-- The asymptotic preorder on R with respect to a Strassen preorder P. -/
def AsymptoticLe (P : StrassenPreorder R) (a b : R) : Prop :=
  ∃ f : ℕ → ℕ, IsSubexponential f ∧ ∀ n, P.le (a ^ n) ((f n : R) * b ^ n)

lemma AsymptoticLe.refl (P : StrassenPreorder R) (a : R) : AsymptoticLe P a a :=
  ⟨fun _ => 1, IsSubexponential.const_one, fun n => by
    rw [Nat.cast_one, one_mul]
    exact P.le_refl _⟩

lemma AsymptoticLe.of_le (P : StrassenPreorder R) {a b : R} (h : P.le a b) : AsymptoticLe P a b :=
  ⟨fun _ => 1, IsSubexponential.const_one, fun n => by
    rw [Nat.cast_one, one_mul]
    induction n with
    | zero =>
      rw [pow_zero, pow_zero]
      exact P.le_refl _
    | succ n ih =>
      rw [pow_succ', pow_succ']
      have h1 := P.mul_right _ _ ih a
      have h2 := P.mul_right _ _ h (b ^ n)
      rw [mul_comm b (b ^ n), mul_comm a (b ^ n)] at h2
      exact P.le_trans _ _ _ h1 h2⟩

lemma AsymptoticLe.trans (P : StrassenPreorder R) {a b c : R} (hab : AsymptoticLe P a b) (hbc : AsymptoticLe P b c) : AsymptoticLe P a c := by
  obtain ⟨f, hf, hfab⟩ := hab
  obtain ⟨g, hg, hgbc⟩ := hbc
  use fun n => f n * g n
  constructor
  · exact IsSubexponential.mul hf hg
  · intro n
    have h1 := hfab n
    have h2 := hgbc n
    have h3 := P.mul_right _ _ h2 (f n : R)
    rw [mul_comm, mul_comm ((g n : R) * c^n)] at h3
    have h4 : P.le (a ^ n) (↑(f n) * (↑(g n) * c ^ n)) := P.le_trans _ _ _ h1 h3
    rw [← mul_assoc, ← Nat.cast_mul] at h4
    exact h4

lemma AsymptoticLe.nat_order_embedding (P : StrassenPreorder R) (n m : ℕ) :
    AsymptoticLe P (n : R) (m : R) ↔ n ≤ m := by
  constructor
  · intro ⟨f, hf, hle⟩
    have h_nat : ∀ k, n ^ k ≤ f k * m ^ k := by
      intro k
      specialize hle k
      rw [← Nat.cast_pow, ← Nat.cast_pow] at hle
      rw [← Nat.cast_mul] at hle
      rw [P.nat_order_embedding] at hle
      exact hle
    by_cases hm : m = 0
    · subst hm
      specialize h_nat 1
      simp at h_nat
      exact Nat.le_of_eq h_nat
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    by_contra h_gt
    push_neg at h_gt
    let δ : ℝ := (n : ℝ) / (m : ℝ) - 1
    have hδ : 0 < δ := by
      rw [sub_pos]
      apply (one_lt_div (by exact_mod_cast hm_pos)).mpr
      exact_mod_cast h_gt
    specialize hf (δ / 2) (half_pos hδ)
    have h_contra : ∀ᶠ k : ℕ in atTop, (1 + δ) ^ (k : ℝ) ≤ (1 + δ / 2) ^ (k : ℝ) := by
      filter_upwards [hf] with k hk
      specialize h_nat k
      have h_nat_real : (n : ℝ) ^ (k : ℝ) ≤ (f k : ℝ) * (m : ℝ) ^ (k : ℝ) := by
        rw [Real.rpow_nat_cast, Real.rpow_nat_cast]
        exact_mod_cast h_nat
      have h_pow_pos : 0 < (m : ℝ) ^ (k : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hm_pos) _
      rw [← div_le_iff h_pow_pos] at h_nat_real
      rw [← Real.div_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg m)] at h_nat_real
      have : (n : ℝ) / (m : ℝ) = 1 + δ := by
        simp [δ]
      rw [this] at h_nat_real
      exact h_nat_real.trans hk
    obtain ⟨N, hN_f⟩ := eventually_atTop.mp h_contra
    let k := max N 1
    specialize hN_f k (le_max_left _ _)
    have h1 : 0 ≤ 1 + δ / 2 := by
      rw [← add_zero (0 : ℝ)]
      apply add_le_add
      · norm_num
      · exact (half_pos hδ).le
    have h2 : 1 + δ / 2 < 1 + δ := by
      apply add_lt_add_left
      exact half_lt_self hδ
    have h_pos : 0 < (k : ℝ) := by
      apply lt_of_lt_of_le (zero_lt_one' ℝ)
      exact_mod_cast (Nat.le_max_right N 1)
    have h_lt := Real.rpow_lt_rpow h1 h2 h_pos
    exact hN_f.not_lt h_lt
  · intro h
    use fun _ => 1
    refine ⟨IsSubexponential.const_one, fun k => ?_⟩
    rw [Nat.cast_one, one_mul]
    rw [← Nat.cast_pow, ← Nat.cast_pow, P.nat_order_embedding]
    exact Nat.pow_le_pow_of_le_left h k

lemma sum_le_sum_P {s : Finset ℕ} {f g : ℕ → R} (P : StrassenPreorder R)
    (h : ∀ i ∈ s, P.le (f i) (g i)) : P.le (∑ i in s, f i) (∑ i in s, g i) := by
  revert h
  refine Finset.induction (p := fun s => (∀ i ∈ s, P.le (f i) (g i)) → P.le (∑ i in s, f i) (∑ i in s, g i)) ?_ ?_ s
  · intro _; simp; exact P.le_refl _
  · intro a s has ih h_all
    rw [sum_insert has, sum_insert has]
    apply P.le_trans _ (f a + ∑ i in s, g i)
    · rw [add_comm (f a), add_comm (f a)]
      apply P.add_right _ _ (ih (fun i hi => h_all i (mem_insert_of_mem hi))) (f a)
    · apply P.add_right (f a) (g a) (h_all a (mem_insert_self a s)) (∑ i in s, g i)

namespace StrassenPreorder

variable {R : Type u} [CommSemiring R]

/-- The asymptotic closure of a Strassen preorder P. -/
def asymptoticClosure (P : StrassenPreorder R) : StrassenPreorder R where
  le := AsymptoticLe P
  le_refl := AsymptoticLe.refl P
  le_trans _ _ _ := AsymptoticLe.trans P
  add_right a b hab c := by
    obtain ⟨f, hf, hle⟩ := hab
    let F := fun n => (range (n + 1)).sup f
    use F
    constructor
    · exact hf.sup_prefix
    · intro n
      rw [add_pow a c n, add_pow b c n]
      rw [Finset.mul_sum]
      apply sum_le_sum_P P
      intro i hi
      simp at hi
      have h_f_le : f i ≤ F n := Finset.le_sup (mem_range.mpr hi)
      have h_f_cast : P.le (f i : R) (F n : R) := (P.nat_order_embedding (f i) (F n)).mpr h_f_le
      have h_ai_bi := hle i
      have h1 := P.mul_right _ _ h_ai_bi (c^(n-i))
      have h2 := P.mul_right _ _ h_f_cast (b^i * c^(n-i))
      have h3 := P.le_trans _ _ _ h1 (by rw [mul_assoc]; exact h2)
      apply P.le_trans _ ((↑(F n) * (b ^ i * c ^ (n - i))) * ↑(Nat.choose n i))
      · exact P.mul_right _ _ h3 ↑(Nat.choose n i)
      · rw [mul_assoc]; exact P.le_refl _
  mul_right a b hab c := by
    obtain ⟨f, hf, hle⟩ := hab
    use f
    refine ⟨hf, fun n => ?_⟩
    rw [mul_pow, mul_pow]
    have := P.mul_right (a ^ n) (↑(f n) * b ^ n) (hle n) (c ^ n)
    rw [mul_assoc] at this
    exact this
  nat_order_embedding := AsymptoticLe.nat_order_embedding P
  lower_archimedean a := by
    cases P.lower_archimedean a with
    | inl h => left; exact h
    | inr h => right; exact AsymptoticLe.of_le P h
  upper_archimedean a := by
    obtain ⟨n, h⟩ := P.upper_archimedean a
    use n
    exact AsymptoticLe.of_le P h

end StrassenPreorder
