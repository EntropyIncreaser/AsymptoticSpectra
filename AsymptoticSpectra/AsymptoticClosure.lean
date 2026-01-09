import AsymptoticSpectra.Structures
import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Order.Zorn
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecificLimits.Normed
import AsymptoticSpectra.Submultiplicative
import AsymptoticSpectra.Rank

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
      exact (div_le_iff₀ h_pos).mp this
    · have h_ge : n ≥ N := not_lt.mp hn
      specialize hN n h_ge
      apply hN.trans
      have h1 : 0 ≤ 1 + ε / 2 := by linarith
      have h2 : 1 + ε / 2 ≤ 1 + ε := by linarith
      apply (Real.rpow_le_rpow h1 h2 (Nat.cast_nonneg n)).trans
      apply le_mul_of_one_le_left (Real.rpow_nonneg (by linarith) _) (le_max_left _ _)
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
      apply tendsto_pow_atTop_nhds_zero_of_lt_one h_ratio_pos h_ratio
    specialize h_lim (eventually_le_nhds (zero_lt_one' ℝ))
    filter_upwards [h_lim] with n hn
    specialize hC n
    apply hC.trans
    have h_pos : 0 < (1 + ε) ^ (n : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have h_le : C * ((1 + ε / 2) / (1 + ε)) ^ n ≤ 1 := hn
    have := mul_le_mul_of_nonneg_right h_le (le_of_lt h_pos)
    rw [← Real.rpow_natCast, Real.div_rpow (by linarith) (by linarith),
        mul_assoc, div_mul_cancel₀ _ (ne_of_gt h_pos), one_mul] at this
    exact this

lemma IsSubexponential.const (k : ℕ) : IsSubexponential (fun _ => k) := by
  rw [isSubexponential_iff_exists_constant]
  intro ε hε
  use k
  intro n
  rw [Real.rpow_natCast]
  have h_base : 1 ≤ 1 + ε := by linarith
  have h_pow : 1 ≤ (1 + ε) ^ n := one_le_pow₀ h_base
  have := mul_le_mul_of_nonneg_left h_pow (Nat.cast_nonneg k)
  simpa using this

lemma IsSubexponential.const_one : IsSubexponential (fun _ => 1) := IsSubexponential.const 1

lemma IsSubexponential.linear : IsSubexponential (fun n => n + 1) := by
  rw [isSubexponential_iff_exists_constant]
  intro ε hε
  let C := max 1 (1/ε)
  use C
  intro n
  rw [Real.rpow_natCast]
  have h_bern : 1 + (n : ℝ) * ε ≤ (1 + ε) ^ n := one_add_mul_le_pow (by linarith) n
  have hC : 1 ≤ C := le_max_left _ _
  have hCeps : 1 ≤ C * ε := by
    rw [← div_mul_cancel₀ 1 (ne_of_gt hε)]
    exact mul_le_mul_of_nonneg_right (le_max_right 1 (1/ε)) (le_of_lt hε)
  calc
    ((n + 1 : ℕ) : ℝ) = n + 1 := by simp
    _ = n * 1 + 1 := by ring
    _ ≤ n * (C * ε) + C := add_le_add (mul_le_mul_of_nonneg_left hCeps (Nat.cast_nonneg n)) hC
    _ = C * (1 + n * ε) := by ring
    _ ≤ C * (1 + ε) ^ n := mul_le_mul_of_nonneg_left h_bern (by linarith [hC])

lemma IsSubexponential.mul {f g : ℕ → ℕ} (hf : IsSubexponential f) (hg : IsSubexponential g) :
    IsSubexponential (fun n => f n * g n) := by
  intro ε hε
  let η := Real.sqrt (1 + ε) - 1
  have hη : 0 < η := by
    dsimp [η]
    rw [sub_pos]
    apply Real.lt_sqrt_of_sq_lt
    linarith
  specialize hf η hη
  specialize hg η hη
  filter_upwards [hf, hg] with n hfn hgn
  have h_prod : ((f n * g n : ℕ) : ℝ) = (f n : ℝ) * (g n : ℝ) := by norm_cast
  rw [h_prod]
  have h_bound : (f n : ℝ) * (g n : ℝ) ≤ (1 + η) ^ (n : ℝ) * (1 + η) ^ (n : ℝ) :=
    mul_le_mul hfn hgn (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith) _)
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
  apply (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)).trans
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le
    · linarith
    · simp at hk; exact_mod_cast hk
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
      rw [pow_succ, pow_succ]
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
        rw [Real.rpow_natCast, Real.rpow_natCast]
        exact_mod_cast h_nat
      have h_pow_pos : 0 < (m : ℝ) ^ (k : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hm_pos) _
      rw [← div_le_iff₀ h_pow_pos] at h_nat_real
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
      linarith
    have h_pos : 0 < (k : ℝ) := by
      apply lt_of_lt_of_le (zero_lt_one' ℝ)
      exact_mod_cast (Nat.le_max_right N 1)
    have h_lt := Real.rpow_lt_rpow h1 h2 h_pos
    exact not_lt_of_ge hN_f h_lt
  · intro h
    use fun _ => 1
    constructor
    · exact IsSubexponential.const_one
    · intro k
      rw [Nat.cast_one, one_mul]
      rw [← Nat.cast_pow, ← Nat.cast_pow, P.nat_order_embedding]
      exact Nat.pow_le_pow_left h k

lemma sum_le_sum_P {s : Finset ℕ} {f g : ℕ → R} (P : StrassenPreorder R)
    (h : ∀ i ∈ s, P.le (f i) (g i)) : P.le (Finset.sum s f) (Finset.sum s g) := by
  revert h
  refine Finset.induction_on s (fun _ => P.le_refl _) fun a s has ih h => by
    rw [sum_insert has, sum_insert has]
    have ih' : P.le (Finset.sum s f) (Finset.sum s g) := ih (fun i hi => h i (mem_insert_of_mem hi))
    apply P.le_trans (f a + Finset.sum s f) (f a + Finset.sum s g)
    · rw [add_comm (f a), add_comm (f a)]
      apply P.add_right _ _ ih' (f a)
    · apply P.add_right (f a) (g a) (h a (mem_insert_self a s)) (Finset.sum s g)

namespace StrassenPreorder

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
      have h_f_le : f i ≤ F n := Finset.le_sup (mem_range.mpr (Nat.lt_succ_of_le hi))
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

theorem le_asymptoticClosure (P : StrassenPreorder R) : P ≤ P.asymptoticClosure :=
  fun _ _ h => AsymptoticLe.of_le P h

/-- Closedness of a Strassen preorder: absorption of the asymptotic closure. -/
def IsClosed (P : StrassenPreorder R) : Prop :=
  AsymptoticLe P ≤ P.le

/-- Fixed-point definition of closedness: the asymptotic closure does not add any new relations. -/
def IsClosedFixedPoint (P : StrassenPreorder R) : Prop :=
  P.asymptoticClosure ≤ P

theorem isClosed_iff_fixedPoint (P : StrassenPreorder R) :
    P.IsClosed ↔ P.IsClosedFixedPoint :=
  Iff.rfl

lemma asymptoticLe_iff_relative_rank_subexponential {P : StrassenPreorder R} {a b : R} (hb : b ≠ 0) :
    AsymptoticLe P a b ↔ IsSubexponential (fun n => relative_rank P (a ^ n) (b ^ n) (StrassenPreorder.pow_ne_zero P n hb)) := by
  constructor
  · rintro ⟨f, hf, hle⟩
    intro ε hε
    specialize hf ε hε
    filter_upwards [hf] with n hn
    have h_le_f_nat : relative_rank P (a ^ n) (b ^ n) (StrassenPreorder.pow_ne_zero P n hb) ≤ f n := by
       apply relative_rank_le_of_le P (StrassenPreorder.pow_ne_zero P n hb)
       exact hle n
    have h_le_f : (relative_rank P (a ^ n) (b ^ n) (StrassenPreorder.pow_ne_zero P n hb) : ℝ) ≤ (f n : ℝ) := by exact_mod_cast h_le_f_nat
    exact h_le_f.trans hn
  · intro h
    use fun n => relative_rank P (a ^ n) (b ^ n) (StrassenPreorder.pow_ne_zero P n hb)
    constructor
    · exact h
    · intro n
      exact relative_rank_spec P (a ^ n) (b ^ n) (StrassenPreorder.pow_ne_zero P n hb)

lemma relative_rank_scale_le (P : StrassenPreorder R) (a b : R) (k : ℕ) (hb : b ≠ 0) (hk : (k : R) ≠ 0) :
    relative_rank P a b hb ≤ k * relative_rank P a (k * b) (StrassenPreorder.mul_ne_zero P hk hb) := by
  letI := P.instCharZero
  apply relative_rank_le_of_le P hb
  let r := relative_rank P a (k * b) (StrassenPreorder.mul_ne_zero P hk hb)
  have h := relative_rank_spec P a (k * b) (StrassenPreorder.mul_ne_zero P hk hb)
  -- a ≤ r * (k * b) = r * k * b
  convert h using 1
  -- Goal: r * (k * b) = r * k * b
  push_cast
  ring

/-- The asymptotic closure of a Strassen preorder is always closed. -/
theorem asymptoticClosure_isClosed (P : StrassenPreorder R) :
    P.asymptoticClosure.IsClosed := by
  intro a b h
  dsimp [StrassenPreorder.asymptoticClosure] at *
  letI := P.toNoZeroDivisors
  letI := P.instCharZero
  by_cases hb : b = 0
  · subst hb
    obtain ⟨f, hf, hle⟩ := h
    specialize hle 1
    simp only [pow_one, mul_zero] at hle
    exact hle
  · rw [asymptoticLe_iff_relative_rank_subexponential hb]
    let hb_pow : ∀ n, b ^ n ≠ 0 := fun n => StrassenPreorder.pow_ne_zero P n hb
    obtain ⟨f, hf, hle⟩ := h
    let f' := fun n => max 1 (f n)
    have hf'_ge_1 : ∀ n, 1 ≤ f' n := fun n => le_max_left _ _
    have hf'_pos : ∀ n, 0 < f' n := fun n => Nat.lt_of_succ_le (hf'_ge_1 n)
    have hf'_subexp : IsSubexponential f' := by
      rw [isSubexponential_iff_exists_constant] at hf ⊢
      intro ε hε
      obtain ⟨C, hC⟩ := hf ε hε
      use max 1 C
      intro n
      specialize hC n
      dsimp [f']
      rw [Nat.cast_max]
      apply max_le
      · trans ((1+ε)^(n:ℝ))
        · simp only [Nat.cast_one]
          refine Real.one_le_rpow (le_add_of_nonneg_right (le_of_lt hε)) (Nat.cast_nonneg n)
        · apply le_mul_of_one_le_left (Real.rpow_nonneg (by linarith [hε]) _)
          exact le_max_left 1 C
      · apply (hC).trans
        apply mul_le_mul_of_nonneg_right (le_max_right 1 C) (Real.rpow_nonneg (by linarith) _)

    have h_le_f' : ∀ n, AsymptoticLe P (a^n) (f' n * b^n) := by
      intro n
      apply AsymptoticLe.trans P (hle n)
      apply AsymptoticLe.of_le
      apply P.mul_right _ _ _ (b^n)
      dsimp [f']
      apply (P.nat_order_embedding _ _).mpr (le_max_right 1 (f n))

    let ψ (n : ℕ) := fun m => relative_rank P ((a^n)^m) ((f' n * b^n)^m) (StrassenPreorder.pow_ne_zero P m (StrassenPreorder.mul_ne_zero P (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hf'_pos n))) (hb_pow n)))

    have h_psi_subexp : ∀ n, IsSubexponential (ψ n) := by
      intro n
      rw [← asymptoticLe_iff_relative_rank_subexponential]
      exact h_le_f' n
      exact StrassenPreorder.mul_ne_zero P (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hf'_pos n))) (hb_pow n)

    rw [isSubexponential_iff_exists_constant]
    intro ε hε

    -- Limit 1: f' n bounds
    have h1 : ∀ᶠ n in atTop, (f' n : ℝ) ^ (1 / (n : ℝ)) < 1 + ε/2 := by
      have : ∀ᶠ n in atTop, (f' n : ℝ) ≤ (1 + ε/4) ^ (n : ℝ) := hf'_subexp (ε/4) (by linarith)
      filter_upwards [this, eventually_gt_atTop 0] with n hn h_pos
      rw [← Real.rpow_lt_rpow_iff (z := (n : ℝ)) (by apply Real.rpow_nonneg; exact_mod_cast (hf'_pos n).le) (by linarith) (by exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_of_gt h_pos))]
      rw [← Real.rpow_mul (by exact_mod_cast (hf'_pos n).le)]
      rw [div_mul_cancel₀ 1 (by have := Nat.ne_of_gt h_pos; exact_mod_cast this)]
      rw [Real.rpow_one]
      apply lt_of_le_of_lt hn
      apply Real.rpow_lt_rpow (by linarith) (by linarith) (by exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_of_gt h_pos))

    -- Limit 2: Powers
    have h2 : ∀ᶠ (n : ℕ) in atTop, (1 + ε/2) ^ (1 + 1 / (n : ℝ)) < 1 + ε := by
       have h_base : Tendsto (fun _ : ℕ => 1 + ε / 2) atTop (𝓝 (1 + ε / 2)) := tendsto_const_nhds
       have h_exp : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
          convert Tendsto.const_add 1 (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
          simp only [add_zero]
       have h_lim := Tendsto.rpow h_base h_exp (Or.inl (ne_of_gt (by linarith [hε] : 0 < 1 + ε / 2)))
       simp only [Real.rpow_one] at h_lim
       exact h_lim.eventually_lt (tendsto_const_nhds (x := 1+ε)) (by linarith)

    obtain ⟨n, hn_prop⟩ := (h1.and (h2.and (eventually_gt_atTop (0 : ℕ)))).exists
    rcases hn_prop with ⟨h_fn_root, h_n_large_enough, hn_pos⟩

    obtain ⟨C_psi, h_psi⟩ := isSubexponential_iff_exists_constant.mp (h_psi_subexp n) (ε/2) (half_pos hε)

    let S_r := (Finset.range n).image (fun r => relative_rank P (a^r) (b^r) (hb_pow r))
    let C_r := S_r.max' (by use relative_rank P (a^0) (b^0) (hb_pow 0); apply mem_image_of_mem; simp [hn_pos])

    use C_psi * (max 1 C_r)
    intro k
    let q := k / n
    let r := k % n

    let φ (m : ℕ) := relative_rank P (a^m) (b^m) (hb_pow m)

    have h_sub : φ k ≤ φ (n*q) * φ r := by
      dsimp [φ]
      convert relative_rank_submultiplicative P (a^(n*q)) (a^r) (b^(n*q)) (b^r) (hb_pow (n*q)) (hb_pow r)
      · rw [← pow_add, Nat.div_add_mod]
      · rw [← pow_add, Nat.div_add_mod]

    have h_mult : φ (n*q) ≤ (f' n)^q * ψ n q := by
      let X := (a^n)^q
      let Y := (b^n)^q
      let K := (f' n)^q
      have hK : (K:R) ≠ 0 := by
         rw [Nat.cast_ne_zero]
         exact Nat.ne_of_gt (Nat.pow_pos (hf'_pos n))
      let hY_ne : b^(n*q) ≠ 0 := hb_pow (n*q)
      have h_rw_a : a^(n*q) = X := by rw [pow_mul]
      have h_rw_b : b^(n*q) = Y := by rw [pow_mul]

      have hY_ne' : Y ≠ 0 := by rw [← h_rw_b]; exact hY_ne

      have h_lhs : φ (n*q) = relative_rank P X Y hY_ne' := by
        dsimp [φ, X, Y]
        simp only [pow_mul]

      have h_rhs_eq : (f' n)^q * ψ n q = K * relative_rank P X (↑K * Y) (mul_ne_zero P hK hY_ne') := by
        dsimp [ψ, K, X, Y]
        simp only [mul_pow, Nat.cast_pow]

      rw [h_lhs, h_rhs_eq]
      exact relative_rank_scale_le P X Y K hY_ne' hK



    have h_phi_r : (φ r : ℝ) ≤ max 1 C_r := by
      have hr : r < n := Nat.mod_lt k hn_pos
      have h_mem : φ r ∈ S_r := Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, rfl⟩
      exact_mod_cast le_trans (Finset.le_max' S_r _ h_mem) (le_max_right 1 C_r)

    have h_C_nonneg : 0 ≤ C_psi := by
      have := h_psi 0
      simp only [Nat.cast_zero, Real.rpow_zero, mul_one] at this
      exact le_trans (Nat.cast_nonneg _) this

    calc (φ k : ℝ) ≤ (φ (n*q) : ℝ) * (φ r : ℝ) := by exact_mod_cast h_sub
      _ ≤ ((f' n)^q * ψ n q) * (max 1 C_r) := by
          apply mul_le_mul _ h_phi_r (by exact_mod_cast Nat.zero_le _) (by exact_mod_cast Nat.zero_le _)
          exact_mod_cast h_mult
      _ ≤ ((f' n)^q * (C_psi * (1+ε/2)^q)) * (max 1 C_r) := by
          apply mul_le_mul_of_nonneg_right _ (by exact_mod_cast Nat.zero_le _)
          apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast Nat.zero_le _)
          rw [← Real.rpow_natCast]
          exact h_psi q
      _ = (C_psi * max 1 C_r) * ((f' n : ℝ) * (1+ε/2))^q := by
          simp only [mul_pow, mul_assoc, mul_comm, mul_left_comm]
      _ ≤ (C_psi * max 1 C_r) * ((1+ε/2)^n * (1+ε/2))^q := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg h_C_nonneg (by exact_mod_cast Nat.zero_le (max 1 C_r)))
          have h_le : (f' n : ℝ) ≤ (1+ε/2)^n := by
              rw [← Real.rpow_natCast]
              have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
              have h_f_nonneg : (0 : ℝ) ≤ f' n := by exact_mod_cast (hf'_pos n).le
              calc
                (f' n : ℝ) = ((f' n : ℝ) ^ (1 / (n : ℝ))) ^ (n : ℝ) := by
                  rw [← Real.rpow_mul h_f_nonneg, one_div, inv_mul_cancel₀ h_n_pos.ne', Real.rpow_one]
                _ ≤ (1 + ε / 2) ^ (n : ℝ) := by
                  apply Real.rpow_le_rpow
                  · apply Real.rpow_nonneg; exact h_f_nonneg
                  · exact h_fn_root.le
                  · exact h_n_pos.le
          have h_base_nonneg : 0 ≤ (f' n : ℝ) * (1 + ε / 2) :=
              mul_nonneg (by exact_mod_cast (hf'_pos n).le) (by linarith)
          exact pow_le_pow_left₀ h_base_nonneg (mul_le_mul_of_nonneg_right h_le (by linarith)) q
      _ = (C_psi * max 1 C_r) * (1+ε/2)^(n*q + q) := by
          simp only [mul_pow, ← pow_mul, ← pow_add]
      _ ≤ (C_psi * max 1 C_r) * (1+ε)^(k:ℝ) := by
          have h_calc : (1+ε/2)^(n*q + q) ≤ (1+ε)^k := calc
            (1+ε/2)^(n*q + q) = (1+ε/2)^((n+1)*q) := by congr 1; rw [add_mul, one_mul]
            _ = (1+ε/2)^((↑((n+1)*q)) : ℝ) := by rw [Real.rpow_natCast]
            _ ≤ (1+ε/2)^(k * (1 + 1 / (n : ℝ))) := by
                apply Real.rpow_le_rpow_of_exponent_le (by linarith)
                have h1 : (n:ℝ) * q ≤ k := by
                  rw [← Nat.cast_mul]
                  exact_mod_cast Nat.mul_div_le k n
                have h2 : (q:ℝ) ≤ k / n := by
                  rw [le_div_iff₀ (by exact_mod_cast hn_pos)]
                  rw [mul_comm]
                  exact_mod_cast Nat.mul_div_le k n
                rw [Nat.cast_mul, Nat.cast_add_one, add_mul, one_mul, mul_one_add, mul_one_div]
                exact add_le_add h1 h2
            _ = ((1+ε/2)^(1+1/(n:ℝ)))^k := by
                rw [mul_comm, Real.rpow_mul (by linarith), Real.rpow_natCast]
            _ ≤ (1+ε)^k := by
                have h_base_le : (1 + ε / 2) ^ (1 + 1 / (n : ℝ)) ≤ 1 + ε := h_n_large_enough.le
                apply pow_le_pow_left₀ (by apply Real.rpow_nonneg; linarith) h_base_le k
          rw [← Real.rpow_natCast (1+ε) k] at h_calc
          apply mul_le_mul_of_nonneg_left h_calc
          apply mul_nonneg h_C_nonneg
          exact_mod_cast Nat.zero_le (max 1 C_r)

def IsMaximal (P : StrassenPreorder R) : Prop :=
  ∀ Q : StrassenPreorder R, P ≤ Q → Q = P

/-- A maximal Strassen preorder is closed. -/
theorem IsMaximal.IsClosed {P : StrassenPreorder R} (hP : P.IsMaximal) : P.IsClosed := by
  let Q := P.asymptoticClosure
  have hPQ : P ≤ Q := P.le_asymptoticClosure
  have hQP : Q = P := hP Q hPQ
  rw [← hQP]
  exact P.asymptoticClosure_isClosed

/-- Multiplicative cancellation: if ac ≤ bc and c ≠ 0, then a ≤ b in a closed Strassen preorder. -/
theorem multiplicative_cancellation (P : StrassenPreorder R) (hP : P.IsClosed) {a b c : R} (hc : c ≠ 0)
    (h : P.le (a * c) (b * c)) : P.le a b := by
  letI := P.toNoZeroDivisors
  apply hP
  rcases P.lower_archimedean c with hc0 | h1c
  · contradiction
  obtain ⟨k, hk⟩ := P.upper_archimedean c
  use fun _ => k
  constructor
  · exact IsSubexponential.const k
  · intro n
    have h_pow : P.le (a ^ n * c) (b ^ n * c) := by
      induction n with
      | zero =>
        simp only [pow_zero, one_mul]
        exact P.le_refl _
      | succ n ih =>
        rw [pow_succ, pow_succ]
        apply P.le_trans _ (a ^ n * b * c)
        · have h' := P.mul_right _ _ h (a ^ n)
          convert h' using 1 <;> ring
        · have h' := P.mul_right _ _ ih b
          convert h' using 1 <;> ring
    apply P.le_trans (a ^ n) (a ^ n * c)
    · have h' := P.mul_right 1 c h1c (a ^ n)
      convert h' using 1 <;> ring
    · apply P.le_trans _ (b ^ n * c)
      · exact h_pow
      · have h' := P.mul_right c k hk (b ^ n)
        (convert h' using 1; ring)

theorem gap_property (P : StrassenPreorder R) (hP : P.IsClosed) {a b : R} (h_not_ab : ¬ P.le a b) (c : R) :
    ∃ m : ℕ, 0 < m ∧ ¬ P.le ((m : R) * a) ((m : R) * b + c) := by
  letI := P.toNoZeroDivisors
  letI := P.instCharZero
  by_contra h_all
  push_neg at h_all
  cases P.lower_archimedean b with
  | inl hb0 =>
    -- Case b = 0
    subst hb0
    obtain ⟨kc, hkc⟩ := P.upper_archimedean c
    cases P.lower_archimedean a with
    | inl ha0 =>
      subst ha0; exact h_not_ab (P.le_refl _)
    | inr h1a =>
      let m := kc + 1
      specialize h_all m (Nat.succ_pos _)
      simp only [mul_zero, zero_add] at h_all
      have h1 : P.le (m : R) (m * a : R) := by
        simpa [mul_comm] using P.mul_right 1 a h1a (m : R)
      have h2 : P.le (m * a : R) (kc : R) := P.le_trans _ _ _ h_all hkc
      have h_m_le_kc : P.le (m : R) (kc : R) := P.le_trans _ _ _ h1 h2
      rw [P.nat_order_embedding] at h_m_le_kc
      exact Nat.not_succ_le_self _ h_m_le_kc
  | inr h1b =>
    -- Case b != 0, 1 <= b
    obtain ⟨kc, hkc⟩ := P.upper_archimedean c
    cases kc with
    | zero =>
      -- Case k = 0, so c ≤ 0
      simp only [Nat.cast_zero] at hkc
      specialize h_all 1 Nat.one_pos
      simp only [Nat.cast_one, one_mul] at h_all
      have : P.le a b := by
        apply P.le_trans _ (b + c) _ h_all
        rw [← add_zero b]
        have h_add := P.add_right c 0 hkc b
        simpa [add_comm] using h_add
      exact h_not_ab this
    | succ kc' =>
      let k := kc' + 1
      have hk_pos : 0 < k := Nat.succ_pos _
      have h_ckb : P.le c ((k : R) * b) := by
        apply P.le_trans c (k : R) _ hkc
        rw [mul_comm]
        have := P.mul_right 1 b h1b k
        (convert this using 1; ring)
      have h_ma_mbk : ∀ m : ℕ, P.le ((m : R) * a) ((m + k : R) * b) := by
        intro m
        specialize h_all m
        by_cases hm0 : m = 0
        · subst hm0; simp
          apply P.le_trans 0 c
          · exact P.all_nonneg c
          · convert h_ckb using 1
        · specialize h_all (Nat.pos_of_ne_zero hm0)
          apply P.le_trans _ ((m : R) * b + c)
          · exact h_all
          · apply P.le_trans _ ((m : R) * b + (k : R) * b)
            · have := P.add_right c ((k : R) * b) h_ckb ((m : R) * b)
              convert this using 1 <;> ring
            · (convert P.le_refl ((m : R) * b + (k : R) * b) using 1; ring)
      have h_na_nb1 : ∀ n : ℕ, P.le ((n : R) * a) ((n + 1 : R) * b) := by
        intro n
        let m := n * k
        have h1 := h_ma_mbk m
        have h2 : (m + k : ℕ) = (n + 1) * k := by rw [Nat.add_mul, one_mul];
        have h1' : P.le (((n : R) * a) * (k : R)) (((n + 1 : R) * b) * (k : R)) := by
          have : (n : R) * a * (k : R) = (m : R) * a := by
            simp only [m, Nat.cast_mul]
            ring
          have this₂ : (n + 1 : R) * b * (k : R) = (m + k : R) * b := by
             have : ((n + 1) * k : R) = (m + k : R) := by exact_mod_cast h2.symm
             rw [← this]
             ring
          rw [this, this₂]
          exact h1
        apply multiplicative_cancellation P hP _ h1'
        exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk_pos)
      have h_pow : ∀ n : ℕ, P.le (a ^ n) ((n + 1 : ℕ) * b ^ n) := by
        intro n
        induction n with
        | zero =>
          simp only [pow_zero, zero_add, Nat.cast_one, one_mul]
          exact P.le_refl 1
        | succ n ih =>
          rw [Nat.cast_succ] at ih
          -- ih : a^n ≤ (↑n + 1) * b^n

          have h_scale : P.le ((↑n + 1 : R) * a) ((↑n + 2 : R) * b) := by
            have := h_na_nb1 (n+1)
            rw [Nat.cast_succ] at this
            (convert this using 2; ring)

          rw [pow_succ a, pow_succ b]

          -- step1 : a^n * a ≤ ((↑n + 1) * b^n) * a
          have step1 : P.le (a^n * a) ((↑n + 1 : R) * b^n * a) := P.mul_right _ _ ih a

          -- rearrange RHS of step1 to match LHS of step2
          have step1_rw : ((↑n + 1 : R) * b^n) * a = (↑n + 1 : R) * a * b^n := by ring
          rw [step1_rw] at step1

          -- step2 : (↑n + 1) * a * b^n ≤ ((↑n + 2) * b) * b^n
          have step2 : P.le ((↑n + 1 : R) * a * b^n) ((↑n + 2 : R) * b * b^n) := P.mul_right _ _ h_scale (b^n)

          apply P.le_trans _ _ _ step1
          convert step2 using 1
          push_cast
          ring
      have h_asymp : AsymptoticLe P a b := ⟨fun n => n + 1, IsSubexponential.linear, fun n => by
        simpa using h_pow n⟩
      exact h_not_ab (hP a b h_asymp)


/-- Additive cancellation: if a + c ≤ b + c, then a ≤ b in a closed Strassen preorder. -/
theorem additive_cancellation (P : StrassenPreorder R) (hP : P.IsClosed) {a b c : R}
    (h : P.le (a + c) (b + c)) : P.le a b := by
  by_contra h_not_le
  obtain ⟨m, _, hm_not_le⟩ := gap_property P hP h_not_le c
  apply hm_not_le
  have h_ind : ∀ n : ℕ, P.le (n * a) (n * b + c) := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, zero_add]
      exact P.all_nonneg c
    | succ n ih =>
      simp only [Nat.cast_succ, add_mul, one_mul]
      apply P.le_trans _ ((↑n * b + c) + a)
      · exact P.add_right _ _ ih a
      apply P.le_trans _ ((a + c) + ↑n * b)
      · convert P.le_refl _ using 1; ring
      apply P.le_trans _ ((b + c) + ↑n * b)
      · exact P.add_right _ _ h _
      · convert P.le_refl _ using 1; ring
  exact h_ind m

/-- The Strassen preorder obtained by extending P to force b ≤ a.
    This construction yields a StrassenPreorder provided a ≤ b is not true in P. -/
def extensionBy (P : StrassenPreorder R) (hP : P.IsClosed) {a b : R} (h_not_le : ¬ P.le a b) : StrassenPreorder R where
  le x y := ∃ s : R, P.le (x + s * a) (y + s * b)
  le_refl x := ⟨0, by simp⟩
  le_trans x y z := by
    rintro ⟨s1, h1⟩ ⟨s2, h2⟩
    use s1 + s2
    letI := P.toNoZeroDivisors
    letI := P.instCharZero
    apply additive_cancellation P hP (c := y)
    have h1' := P.add_right _ _ h1 (y + s2 * a)
    have h2' := P.add_right _ _ h2 (y + s1 * b)
    rw [add_comm (y + s2 * a), add_comm (z + s2 * b)] at h2'
    have h_sum := P.le_trans _ _ _ h1' h2'
    convert h_sum using 1 <;> ring
  add_right x y hxy c := by
    obtain ⟨s, h⟩ := hxy
    use s
    have h' := P.add_right _ _ h c
    convert h' using 1 <;> ring
  mul_right x y hxy c := by
    obtain ⟨s, h⟩ := hxy
    use s * c
    have h' := P.mul_right _ _ h c
    convert h' using 1 <;> ring
  nat_order_embedding n m := by
    constructor
    · rintro ⟨s, h⟩
      by_cases hnm : n ≤ m
      · exact hnm
      · exfalso
        letI := P.instCharZero
        letI := P.toNoZeroDivisors
        have h_gt : m < n := Nat.lt_of_not_ge hnm
        let k := n - m
        have hk : 1 ≤ k := Nat.one_le_of_lt (Nat.sub_pos_of_lt h_gt)
        have h_k_rw : (n : R) = (m : R) + (k : R) := by
          norm_cast
          rw [Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt h_gt)]
        rw [h_k_rw, add_assoc, add_comm (k : R)] at h
        have h' : P.le ((s * a + (k : R)) + (m : R)) (s * b + (m : R)) := by
           rw [add_comm, add_comm (s * b)]
           exact h
        have h'' : P.le (s * a + (k : R)) (s * b) := additive_cancellation P hP h'
        have h''' : P.le (s * a + 1) (s * b) := by
          apply P.le_trans _ (s * a + (k : R))
          · have h_1_k : P.le (1 : R) (k : R) := by
              rw [← Nat.cast_one]
              exact (P.nat_order_embedding 1 k).mpr hk
            convert P.add_right 1 (k : R) h_1_k (s * a) using 1 <;> ring
          · exact h''
        have hs : s ≠ 0 := by
          intro hs
          subst hs
          simp at h'''
          rw [← Nat.cast_one, ← Nat.cast_zero, P.nat_order_embedding] at h'''
          exact Nat.not_succ_le_zero 0 h'''
        have h_sa_sb : P.le (s * a) (s * b) := by
          apply P.le_trans (s * a) (s * a + 1) (s * b)
          · convert P.add_right 0 1 P.zero_le_one (s * a) using 1 <;> ring
          · exact h'''
        rw [mul_comm s a, mul_comm s b] at h_sa_sb
        have h_ab_P := multiplicative_cancellation P hP hs h_sa_sb
        exact h_not_le h_ab_P
    · intro hnm
      use 0
      simp
      rw [P.nat_order_embedding]
      exact hnm
  lower_archimedean x := by
    cases P.lower_archimedean x with
    | inl h => left; exact h
    | inr h => right; use 0; simp; exact h
  upper_archimedean x := by
    obtain ⟨n, h⟩ := P.upper_archimedean x
    use n, 0
    simp; exact h

/-- One-step extension lemma: If a ≤ b is not true in a closed Strassen preorder P,
    there exists an extension Q where b ≤ a and a ≤ b is still not true. -/
theorem one_step_extension (P : StrassenPreorder R) (hP : P.IsClosed) {a b : R}
    (h_not_le : ¬ P.le a b) :
    ∃ Q : StrassenPreorder R, P ≤ Q ∧ Q.le b a ∧ ¬ Q.le a b := by
  let Q := extensionBy P hP h_not_le
  use Q
  constructor
  · intro x y h; use 0; simp; exact h
  constructor
  · use 1; simp; rw [add_comm]; exact P.le_refl _
  · rintro ⟨s, hs⟩
    letI := P.toNoZeroDivisors
    letI := P.instCharZero
    have h_final : P.le (a * (1 + s)) (b * (1 + s)) := by
      rw [mul_add, mul_one, mul_add, mul_one, mul_comm a s, mul_comm b s]
      exact hs
    have h_ne : 1 + s ≠ 0 := by
      intro h_zero
      have h1 : P.le 1 (1 + s) := by
        convert P.add_right 0 s (P.all_nonneg s) 1 using 1 <;> ring
      rw [h_zero] at h1
      rw [← Nat.cast_one, ← Nat.cast_zero, P.nat_order_embedding] at h1
      exact Nat.not_succ_le_zero 0 h1
    have h_le_P := multiplicative_cancellation P hP h_ne h_final
    exact h_not_le h_le_P

/-- The union of a chain of Strassen preorders is a Strassen preorder. -/
def chain_ub {R : Type u} [CommSemiring R] (c : Set (StrassenPreorder R))
    (hc : IsChain (· ≤ ·) c) (h_nonempty : c.Nonempty) : StrassenPreorder R where
  le x y := ∃ P ∈ c, P.le x y
  le_refl x := by
    obtain ⟨P, hP⟩ := h_nonempty
    exact ⟨P, hP, P.le_refl x⟩
  le_trans x y z := by
    rintro ⟨P1, hP1, h1⟩ ⟨P2, hP2, h2⟩
    cases hc.total hP1 hP2 with
    | inl h => exact ⟨P2, hP2, P2.le_trans _ _ _ (h _ _ h1) h2⟩
    | inr h => exact ⟨P1, hP1, P1.le_trans _ _ _ h1 (h _ _ h2)⟩
  add_right x y hxy c' := by
    obtain ⟨P, hP, h⟩ := hxy
    exact ⟨P, hP, P.add_right x y h c'⟩
  mul_right x y hxy c' := by
    obtain ⟨s, hP, h⟩ := hxy
    exact ⟨s, hP, s.mul_right x y h c'⟩
  nat_order_embedding n m := by
    constructor
    · rintro ⟨P, hP, h⟩
      exact (P.nat_order_embedding n m).mp h
    · intro h
      obtain ⟨P, hP⟩ := h_nonempty
      exact ⟨P, hP, (P.nat_order_embedding n m).mpr h⟩
  lower_archimedean a := by
    obtain ⟨P, hP⟩ := h_nonempty
    cases P.lower_archimedean a with
    | inl h => left; exact h
    | inr h => right; exact ⟨P, hP, h⟩
  upper_archimedean a := by
    obtain ⟨P, hP⟩ := h_nonempty
    obtain ⟨n, h⟩ := P.upper_archimedean a
    exact ⟨n, P, hP, h⟩

/-- Total extension lemma: Every Strassen preorder can be extended to a maximal one. -/
theorem total_extension (P : StrassenPreorder R) :
    ∃ Q : StrassenPreorder R, P ≤ Q ∧ Q.IsMaximal := by
  let S := {Q : StrassenPreorder R | P ≤ Q}
  have h_zorn : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ S, ∀ a ∈ c, a ≤ ub := by
    intro c hc_sub hc_chain P₀ hP₀
    let ub := chain_ub c hc_chain ⟨P₀, hP₀⟩
    use ub
    constructor
    · -- Prove P ≤ ub
      intro x y hxy
      exact ⟨P₀, hP₀, hc_sub hP₀ x y hxy⟩
    · -- Prove ub is upper bound
      intro Q' hQ' x y hxy
      exact ⟨Q', hQ', hxy⟩
  obtain ⟨Q, hPQ, hQ_max⟩ := zorn_le_nonempty₀ S h_zorn P (le_refl P)
  use Q
  constructor
  · exact hPQ
  · intro Q' hQQ'
    have hPQ' : Q' ∈ S := le_trans hPQ hQQ'
    exact le_antisymm (hQ_max.2 hPQ' hQQ') hQQ'

/-- A maximal Strassen preorder is total. -/
theorem IsMaximal.IsTotal {P : StrassenPreorder R} (hP : P.IsMaximal) : P.IsTotal := by
  let Q := P.asymptoticClosure
  have hPQ : P ≤ Q := P.le_asymptoticClosure
  have hQP : Q = P := hP Q hPQ
  rw [← hQP]
  intro a b
  by_contra h_not
  push_neg at h_not
  rcases h_not with ⟨h_not_ab, h_not_ba⟩
  -- Use one_step_extension to get a larger preorder where b ≤ a.
  -- This requires the preorder to be closed, which we have for Q.
  have hQ_closed : Q.IsClosed := P.asymptoticClosure_isClosed
  obtain ⟨Q1, hQQ1, hQ1_ba, hQ1_not_ab⟩ := one_step_extension Q hQ_closed h_not_ab
  -- Extend Q1 to a maximal one using total_extension.
  obtain ⟨Q2, hQ1Q2, hQ2_max⟩ := Q1.total_extension
  -- Since P is maximal and P = Q ≤ Q1 ≤ Q2, we must have P = Q2.
  have hPQ2 : P ≤ Q2 := le_trans hPQ (le_trans hQQ1 hQ1Q2)
  have hPQ2_eq : Q2 = P := hP Q2 hPQ2
  -- But Q1.le b a implies Q2.le b a, so Q.le b a.
  have hQ2_ba : Q2.le b a := hQ1Q2 b a hQ1_ba
  have hQ2_eq_Q : Q2 = Q := hPQ2_eq.trans hQP.symm
  rw [hQ2_eq_Q] at hQ2_ba
  exact h_not_ba hQ2_ba

/-- Every closed Strassen preorder is the intersection of all maximal Strassen preorders extending it. -/
theorem closed_strassen_preorder_eq_intersection_maximal (P : StrassenPreorder R) (hP : P.IsClosed) :
    ∀ x y : R, P.le x y ↔ ∀ Q : StrassenPreorder R, P ≤ Q → Q.IsMaximal → Q.le x y := by
  intro x y
  constructor
  · intro h Q hPQ _
    exact hPQ x y h
  · intro h
    by_contra h_not
    -- Use gap property to find n such that ¬ P.le (nx) (ny + 1)
    obtain ⟨n, hn_pos, h_gap⟩ := P.gap_property hP h_not 1
    let a := (n : R) * x
    let b := (n : R) * y + 1
    -- Extend P to Q1 forced by b ≤ a
    let Q1 := extensionBy P hP h_gap
    have hPQ1 : P ≤ Q1 := by
      intro u v huv; use 0; simp; exact huv
    have hQ1_ba : Q1.le b a := by
      use 1; simp [a, b]; rw [add_comm, add_comm ((n : R) * y)]
      exact P.le_refl _
    -- Extend Q1 to maximal Q
    obtain ⟨Q, hQ1Q, hQ_max⟩ := Q1.total_extension
    have hPQ : P ≤ Q := le_trans hPQ1 hQ1Q
    have hQ_le := h Q hPQ hQ_max
    -- In Q, we have ny + 1 ≤ nx (from Q1) and nx ≤ ny (from x ≤ y in Q)
    have hQ_ba : Q.le b a := hQ1Q b a hQ1_ba
    have hQ_xy : Q.le a ((n : R) * y) := by
      dsimp [a]
      have : ∀ (n : ℕ) (x y : R), Q.le x y → Q.le ((n : R) * x) ((n : R) * y) := by
        intro n' x' y' h'
        induction n' with
        | zero => simp
        | succ n' ih =>
          rw [Nat.cast_succ, add_mul, add_mul]
          apply Q.le_trans _ (↑n' * y' + x')
          · (convert Q.add_right (↑n' * x') (↑n' * y') ih x' using 1; ring)
          · convert Q.add_right x' y' h' (↑n' * y') using 1 <;> ring
      exact this n x y hQ_le
    have hQ_bad : Q.le b ((n : R) * y) := Q.le_trans _ _ _ hQ_ba hQ_xy
    -- This implies 1 ≤ 0 in Q
    dsimp [b] at hQ_bad
    have hQ_closed := hQ_max.IsClosed
    have hQ_one_zero : Q.le 1 0 := by
      have h_cancel : Q.le (1 + (n : R) * y) (0 + (n : R) * y) := by
        convert hQ_bad using 1 <;> ring
      exact additive_cancellation Q hQ_closed h_cancel
    rw [← Nat.cast_one, ← Nat.cast_zero, Q.nat_order_embedding] at hQ_one_zero
    exact Nat.not_succ_le_zero 0 hQ_one_zero

/-- A Strassen preorder P is maximal if and only if it is total and closed. -/
theorem isMaximal_iff_isTotal_isClosed (P : StrassenPreorder R) :
    P.IsMaximal ↔ P.IsTotal ∧ P.IsClosed := by
  constructor
  · intro h
    exact ⟨h.IsTotal, h.IsClosed⟩
  · rintro ⟨h_total, h_closed⟩ Q hPQ
    refine _root_.le_antisymm ?_ hPQ
    intro x y hQ
    by_contra h_not
    obtain ⟨n, hn_pos, h_gap⟩ := P.gap_property h_closed h_not 1
    have h_total_not := (h_total ((n:R)*x) ((n:R)*y + 1)).resolve_left h_gap
    have hQ_xy : Q.le ((n:R)*x) ((n:R)*y) := by
       have : ∀ (n' : ℕ) (x' y' : R), Q.le x' y' → Q.le ((n' : R) * x') ((n' : R) * y') := by
         intro n' x' y' h'
         induction n' with
         | zero => simp
         | succ n' ih =>
           rw [Nat.cast_succ, add_mul, add_mul]
           apply Q.le_trans _ (↑n' * y' + x')
           · (convert Q.add_right (↑n' * x') (↑n' * y') ih x' using 1; ring)
           · convert Q.add_right x' y' h' (↑n' * y') using 1 <;> ring
       exact this n x y hQ
    have hQ_bad : Q.le ((n:R)*y + 1) ((n:R)*y) := Q.le_trans _ _ _ (hPQ _ _ h_total_not) hQ_xy
    obtain ⟨Q_max, hQQ_max, hQ_max_maximal⟩ := total_extension Q
    have hQ_max_bad : Q_max.le ((n:R)*y + 1) ((n:R)*y) := hQQ_max _ _ hQ_bad
    have hQ_max_one_zero : Q_max.le 1 0 := by
      have h_cancel : Q_max.le (1 + (n : R) * y) (0 + (n : R) * y) := by
        convert hQ_max_bad using 1 <;> ring
      exact additive_cancellation Q_max (IsMaximal.IsClosed hQ_max_maximal) h_cancel
    rw [← Nat.cast_one, ← Nat.cast_zero, Q_max.nat_order_embedding] at hQ_max_one_zero
    exact Nat.not_succ_le_zero 0 hQ_max_one_zero

/-- If P ≤ Q and Q is closed, then the asymptotic closure of P is also contained in Q. -/
lemma asymptoticClosure_le_of_isClosed {P Q : StrassenPreorder R} (h : P ≤ Q) (hQ : Q.IsClosed) :
    asymptoticClosure P ≤ Q := by
  intro a b hab
  obtain ⟨f, hf, hle⟩ := hab
  apply hQ
  use f, hf
  intro n
  exact h _ _ (hle n)

/-- The asymptotic closure of P is the intersection of all total and closed extensions of P. -/
theorem asymptoticClosure_eq_intersection_total_closed (P : StrassenPreorder R) (x y : R) :
    (asymptoticClosure P).le x y ↔ ∀ Q : StrassenPreorder R, P ≤ Q → Q.IsTotal → Q.IsClosed → Q.le x y := by
  let P_star := asymptoticClosure P
  rw [closed_strassen_preorder_eq_intersection_maximal P_star (asymptoticClosure_isClosed P)]
  constructor
  · intro h Q hPQ h_total h_closed
    apply h Q
    · exact asymptoticClosure_le_of_isClosed hPQ h_closed
    · rw [isMaximal_iff_isTotal_isClosed]
      exact ⟨h_total, h_closed⟩
  · intro h Q hP_star_Q h_max
    have h_total_closed : Q.IsTotal ∧ Q.IsClosed := (isMaximal_iff_isTotal_isClosed Q).mp h_max
    apply h Q (le_trans (le_asymptoticClosure P) hP_star_Q) h_total_closed.1 h_total_closed.2

end StrassenPreorder
