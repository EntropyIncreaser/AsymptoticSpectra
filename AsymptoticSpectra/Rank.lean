import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import AsymptoticSpectra.Structures
import AsymptoticSpectra.Submultiplicative
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic

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

/-- The set of rational upper bounds for fractional rank. -/
def rho_set (P : StrassenPreorder R) (a : R) : Set ℝ :=
  { q : ℝ | ∃ (n m : ℕ), 0 < m ∧ P.le (m * a) n ∧ q = (n : ℝ) / m }

/-- The set of rational lower bounds for fractional subrank. -/
def kappa_set (P : StrassenPreorder R) (a : R) : Set ℝ :=
  { q : ℝ | ∃ (n m : ℕ), 0 < m ∧ P.le n (m * a) ∧ q = (n : ℝ) / m }

/-- The fractional rank of an element. -/
def rho (P : StrassenPreorder R) (a : R) : ℝ := sInf (P.rho_set a)

/-- The fractional subrank of an element. -/
def kappa (P : StrassenPreorder R) (a : R) : ℝ := sSup (P.kappa_set a)

lemma rho_set_nonempty (P : StrassenPreorder R) (a : R) : (P.rho_set a).Nonempty := by
  obtain ⟨n, hn⟩ := P.upper_archimedean a
  refine ⟨(n : ℝ), n, 1, Nat.zero_lt_one, ?_, by simp⟩
  simpa using hn

lemma rho_set_bddBelow (P : StrassenPreorder R) (a : R) : BddBelow (P.rho_set a) := by
  use 0
  rintro q ⟨n, m, hm, _, rfl⟩
  apply div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)

lemma kappa_set_nonempty (P : StrassenPreorder R) (a : R) : (P.kappa_set a).Nonempty := by
  refine ⟨0, 0, 1, Nat.zero_lt_one, ?_, by simp⟩
  simp; exact P.all_nonneg a

lemma kappa_set_bddAbove (P : StrassenPreorder R) (a : R) : BddAbove (P.kappa_set a) := by
  obtain ⟨K, hK⟩ := P.upper_archimedean a
  use K
  rintro q ⟨n, m, hm, h, rfl⟩
  rw [div_le_iff₀ (Nat.cast_pos.mpr hm)]
  norm_cast
  have h_ma_mK : P.le ((m : R) * a) ((m : R) * (K : R)) := by
    rw [mul_comm, mul_comm (m : R) (K : R)]
    apply P.mul_right a (K : R) hK (m : R)
  rw [mul_comm K m]
  apply (P.nat_order_embedding n (m * K)).mp
  rw [Nat.cast_mul]
  exact P.le_trans _ _ _ h h_ma_mK

lemma sInf_add_sInf_le {S1 S2 S3 : Set ℝ} (h1 : S1.Nonempty) (h2 : S2.Nonempty)
    (H : ∀ x ∈ S1, ∀ y ∈ S2, sInf S3 ≤ x + y) : sInf S3 ≤ sInf S1 + sInf S2 := by
  have h_y : ∀ y ∈ S2, sInf S3 - y ≤ sInf S1 := by
    intro y hy
    apply le_csInf h1
    intro x hx
    linarith [H x hx y hy]
  have h_x : sInf S3 - sInf S1 ≤ sInf S2 := by
    apply le_csInf h2
    intro y hy
    linarith [h_y y hy]
  linarith

lemma sInf_mul_sInf_le {S1 S2 S3 : Set ℝ} (h1 : S1.Nonempty) (hb1 : BddBelow S1) (pos1 : ∀ x ∈ S1, 0 ≤ x)
    (h2 : S2.Nonempty) (pos2 : ∀ x ∈ S2, 0 ≤ x)
    (H : ∀ x ∈ S1, ∀ y ∈ S2, sInf S3 ≤ x * y) : sInf S3 ≤ sInf S1 * sInf S2 := by
  have h_inf1 : 0 ≤ sInf S1 := le_csInf h1 pos1
  by_cases h01 : sInf S1 = 0
  · rw [h01, zero_mul]
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨y, hy⟩ := h2
    have h_nonneg_y : 0 ≤ y := pos2 y hy
    by_cases hy0 : y = 0
    · obtain ⟨x, hx⟩ := h1
      have := H x hx y hy
      rw [hy0, mul_zero] at this
      linarith
    · have : sInf S1 < sInf S1 + ε / y := lt_add_of_pos_right _ (div_pos hε (lt_of_le_of_ne h_nonneg_y (Ne.symm hy0)))
      obtain ⟨x, hx, hx_lt⟩ := (csInf_lt_iff hb1 h1).mp this
      calc sInf S3 ≤ x * y := H x hx y hy
        _ ≤ (sInf S1 + ε / y) * y := mul_le_mul_of_nonneg_right hx_lt.le h_nonneg_y
        _ = ε := by field_simp [hy0]; rw [h01]; ring
        _ ≤ 0 + ε := by simp
  · have h1_pos : 0 < sInf S1 := lt_of_le_of_ne h_inf1 (Ne.symm h01)
    have h_bound : ∀ y ∈ S2, sInf S3 ≤ y * sInf S1 := by
      intro y hy
      by_cases hy0 : y = 0
      · rw [hy0, zero_mul]; obtain ⟨x, hx⟩ := h1; have := H x hx y hy; rwa [hy0, mul_zero] at this
      · have : 0 < y := lt_of_le_of_ne (pos2 y hy) (Ne.symm hy0)
        rw [mul_comm y]
        apply (div_le_iff₀ this).mp
        apply le_csInf h1
        intro x hx
        apply (div_le_iff₀ this).mpr
        exact H x hx y hy
    have : ∀ y ∈ S2, sInf S3 / sInf S1 ≤ y := by
      intro y hy
      exact (div_le_iff₀ h1_pos).mpr (h_bound y hy)
    have : sInf S3 / sInf S1 ≤ sInf S2 := le_csInf h2 this
    rw [mul_comm]
    exact (div_le_iff₀ h1_pos).mp this

lemma csSup_add_le_csSup {S1 S2 S3 : Set ℝ} (h1 : S1.Nonempty) (h2 : S2.Nonempty)
    (H : ∀ x ∈ S1, ∀ y ∈ S2, x + y ≤ sSup S3) : sSup S1 + sSup S2 ≤ sSup S3 := by
  have h_y : ∀ y ∈ S2, sSup S1 ≤ sSup S3 - y := by
    intro y hy
    apply csSup_le h1
    intro x hx
    linarith [H x hx y hy]
  have h_x : sSup S2 ≤ sSup S3 - sSup S1 := by
    apply csSup_le h2
    intro y hy
    linarith [h_y y hy]
  linarith

lemma csSup_mul_le_csSup {S1 S2 S3 : Set ℝ} (h1 : S1.Nonempty) (hb1 : BddAbove S1) (pos1 : ∀ x ∈ S1, 0 ≤ x)
    (h2 : S2.Nonempty) (pos2 : ∀ x ∈ S2, 0 ≤ x)
    (H : ∀ x ∈ S1, ∀ y ∈ S2, x * y ≤ sSup S3) : sSup S1 * sSup S2 ≤ sSup S3 := by
  have h_nonneg_sup1 : 0 ≤ sSup S1 := (pos1 h1.some h1.some_mem).trans (le_csSup hb1 h1.some_mem)
  by_cases h01 : sSup S1 = 0
  · rw [h01, zero_mul]
    obtain ⟨x, hx⟩ := h1
    obtain ⟨y, hy⟩ := h2
    have : 0 ≤ x * y := mul_nonneg (pos1 x hx) (pos2 y hy)
    exact this.trans (H x hx y hy)
  · have h1_pos : 0 < sSup S1 := lt_of_le_of_ne h_nonneg_sup1 (Ne.symm h01)
    have h_bound : ∀ y ∈ S2, y * sSup S1 ≤ sSup S3 := by
        intro y hy
        by_cases hy0 : y = 0
        · rw [hy0, zero_mul]; obtain ⟨x, hx⟩ := h1; have := H x hx y hy; rwa [hy0, mul_zero] at this
        · have hy_pos : 0 < y := lt_of_le_of_ne (pos2 y hy) (Ne.symm hy0)
          rw [mul_comm y]
          apply (le_div_iff₀ hy_pos).mp
          apply csSup_le h1
          intro x hx
          apply (le_div_iff₀ hy_pos).mpr
          exact H x hx y hy
    have : ∀ y ∈ S2, y ≤ sSup S3 / sSup S1 := by
      intro y hy
      exact (le_div_iff₀ h1_pos).mpr (h_bound y hy)
    have : sSup S2 ≤ sSup S3 / sSup S1 := csSup_le h2 this
    rw [mul_comm]
    exact (le_div_iff₀ h1_pos).mp this

theorem rho_monotone (P : StrassenPreorder R) {a b : R} (h : P.le a b) : P.rho a ≤ P.rho b := by
  apply le_csInf (P.rho_set_nonempty b)
  rintro q ⟨n, m, hm, hb, rfl⟩
  apply csInf_le (P.rho_set_bddBelow a)
  refine ⟨n, m, hm, ?_, rfl⟩
  have h_ma_mb : P.le ((m : R) * a) ((m : R) * b) := by
    rw [mul_comm, mul_comm (m : R) b]
    apply P.mul_right a b h (m : R)
  exact P.le_trans _ _ _ h_ma_mb hb

theorem rho_nat_cast (P : StrassenPreorder R) (n : ℕ) : P.rho n = n := by
  apply le_antisymm
  · apply csInf_le (P.rho_set_bddBelow n)
    refine ⟨n, 1, Nat.zero_lt_one, ?_, by simp⟩
    simp only [Nat.cast_one, one_mul, P.le_refl]
  · apply le_csInf (P.rho_set_nonempty n)
    rintro q ⟨k, m, hm, h, rfl⟩
    rw [le_div_iff₀ (Nat.cast_pos.mpr hm)]
    norm_cast at h
    rw [Nat.mul_comm] at h
    norm_cast
    exact (P.nat_order_embedding _ _).mp h

theorem rho_add_le (P : StrassenPreorder R) (a b : R) : P.rho (a + b) ≤ P.rho a + P.rho b := by
  apply sInf_add_sInf_le (P.rho_set_nonempty a) (P.rho_set_nonempty b)
  rintro q1 ⟨n1, m1, hm1, ha, rfl⟩ q2 ⟨n2, m2, hm2, hb, rfl⟩
  apply csInf_le (P.rho_set_bddBelow _)
  refine ⟨m2 * n1 + m1 * n2, m1 * m2, Nat.mul_pos hm1 hm2, ?_, ?_⟩
  · have h_eq1 : (↑(m1 * m2) * (a + b) : R) = (↑m1 * a) * ↑m2 + (↑m2 * b) * ↑m1 := by push_cast; ring
    rw [h_eq1]
    have hA : P.le (↑m1 * a * ↑m2) (↑n1 * ↑m2) := by
      apply P.mul_right (↑m1 * a) (↑n1) ha
    have hB : P.le (↑m2 * b * ↑m1) ((n2 : R) * m1) := by
      apply P.mul_right
      exact hb
    letI := P.toPreorder
    calc
      P.le ((↑m1 * a) * ↑m2 + (↑m2 * b) * ↑m1) (↑n1 * ↑m2 + (↑m2 * b) * ↑m1) := by
        apply P.add_right; exact hA
      _ ≤ ↑n1 * ↑m2 + (n2 : R) * m1 := by
        have h_comm : ↑n1 * ↑m2 + ↑m2 * b * ↑m1 = ↑m2 * b * ↑m1 + ↑n1 * ↑m2 := by ring
        have h_comm2 : ↑n1 * ↑m2 + (n2 : R) * m1 = (n2 : R) * m1 + ↑n1 * ↑m2 := by ring
        rw [h_comm, h_comm2]
        apply P.add_right; exact hB
      _ ≤ ↑(m2 * n1 + m1 * n2) := by
        apply le_of_eq; push_cast; ring
  · push_cast; field_simp; try ring

theorem rho_mul_le (P : StrassenPreorder R) (a b : R) : P.rho (a * b) ≤ P.rho a * P.rho b := by
  let Sa := P.rho_set a
  let Sb := P.rho_set b
  have posa : ∀ q ∈ Sa, 0 ≤ q := by rintro q ⟨n, m, hm, h, rfl⟩; apply div_nonneg <;> exact Nat.cast_nonneg _
  have posb : ∀ q ∈ Sb, 0 ≤ q := by rintro q ⟨n, m, hm, h, rfl⟩; apply div_nonneg <;> exact Nat.cast_nonneg _
  apply sInf_mul_sInf_le (P.rho_set_nonempty a) (P.rho_set_bddBelow a) posa (P.rho_set_nonempty b) posb
  rintro q1 ⟨n1, m1, hm1, ha, rfl⟩ q2 ⟨n2, m2, hm2, hb, rfl⟩
  apply csInf_le (P.rho_set_bddBelow _)
  refine ⟨n1 * n2, m1 * m2, Nat.mul_pos hm1 hm2, ?_, ?_⟩
  · letI := P.toPreorder
    have h_eq : ↑(m1 * m2) * (a * b) = (↑m1 * a) * (↑m2 * b) := by push_cast; ring
    rw [h_eq]
    calc
      P.le ((↑m1 * a) * (↑m2 * b)) (↑n1 * (↑m2 * b)) := by
        exact P.mul_right (↑m1 * a) (↑n1) ha (↑m2 * b)
      _ ≤ ↑n1 * ↑n2 := by
        have h_swap : ↑n1 * (↑m2 * b) = (↑m2 * b) * ↑n1 := by ring
        rw [h_swap]
        have h_main : P.le ((↑m2 * b) * ↑n1) (↑n2 * ↑n1) := P.mul_right (↑m2 * b) (↑n2) hb (↑n1)
        have h_comm_res : (↑n2 : R) * ↑n1 = ↑n1 * ↑n2 := by ring
        rw [← h_comm_res]
        exact h_main
      _ ≤ ↑(n1 * n2) := by
        apply le_of_eq; push_cast; rfl
  · push_cast; field_simp; try ring

theorem kappa_monotone (P : StrassenPreorder R) {a b : R} (h : P.le a b) : P.kappa a ≤ P.kappa b := by
  apply csSup_le (P.kappa_set_nonempty a)
  rintro q ⟨n, m, hm, ha, rfl⟩
  apply le_csSup (P.kappa_set_bddAbove b)
  refine ⟨n, m, hm, ?_, rfl⟩
  have h_ma : P.le ((m : R) * a) ((m : R) * b) := by
    rw [mul_comm, mul_comm (m : R) b]
    apply P.mul_right a b h (m : R)
  exact P.le_trans _ _ _ ha h_ma

theorem kappa_nat_cast (P : StrassenPreorder R) (n : ℕ) : P.kappa n = n := by
  apply le_antisymm
  · apply csSup_le (P.kappa_set_nonempty n)
    rintro q ⟨k, m, hm, h, rfl⟩
    rw [div_le_iff₀ (Nat.cast_pos.mpr hm)]
    norm_cast at h
    rw [Nat.mul_comm] at h
    norm_cast
    exact (P.nat_order_embedding _ _).mp h
  · apply le_csSup (P.kappa_set_bddAbove n)
    refine ⟨n, 1, Nat.zero_lt_one, ?_, by simp⟩
    simp only [Nat.cast_one, one_mul, P.le_refl]

theorem kappa_add_ge (P : StrassenPreorder R) (a b : R) : P.kappa a + P.kappa b ≤ P.kappa (a + b) := by
  apply csSup_add_le_csSup (P.kappa_set_nonempty a) (P.kappa_set_nonempty b)
  rintro q1 ⟨n1, m1, hm1, ha, rfl⟩ q2 ⟨n2, m2, hm2, hb, rfl⟩
  apply le_csSup (P.kappa_set_bddAbove _)
  refine ⟨m2 * n1 + m1 * n2, m1 * m2, Nat.mul_pos hm1 hm2, ?_, ?_⟩
  · have h_eq1 : (↑(m1 * m2) * (a + b) : R) = (↑m1 * a) * ↑m2 + (↑m2 * b) * ↑m1 := by push_cast; ring
    rw [h_eq1]
    push_cast
    letI := P.toPreorder
    have hA : (↑m2 : R) * ↑n1 ≤ ↑m1 * a * ↑m2 := by
      have h1 : (↑m2 : R) * ↑n1 = ↑n1 * ↑m2 := by ring
      have h2 : ↑m1 * a * ↑m2 = (↑m1 * a) * ↑m2 := by ring
      rw [h1, h2]
      apply P.mul_right; exact ha
    have hB : (↑m1 : R) * ↑n2 ≤ ↑m2 * b * ↑m1 := by
      have h1 : (↑m1 : R) * ↑n2 = ↑n2 * ↑m1 := by ring
      have h2 : ↑m2 * b * ↑m1 = (↑m2 * b) * ↑m1 := by ring
      rw [h1, h2]
      apply P.mul_right; exact hb
    calc
      P.le (↑m2 * ↑n1 + ↑m1 * ↑n2) (↑m1 * a * ↑m2 + ↑m1 * ↑n2) := by
        apply P.add_right; exact hA
      _ ≤ ↑m1 * a * ↑m2 + ↑m2 * b * ↑m1 := by
        rw [add_comm, add_comm (↑m1 * a * ↑m2)]
        apply P.add_right; exact hB
  · push_cast; field_simp; try ring

theorem kappa_mul_ge (P : StrassenPreorder R) (a b : R) : P.kappa a * P.kappa b ≤ P.kappa (a * b) := by
  let Sa := P.kappa_set a
  let Sb := P.kappa_set b
  have posa : ∀ q ∈ Sa, 0 ≤ q := by rintro q ⟨n, m, hm, h, rfl⟩; apply div_nonneg <;> exact Nat.cast_nonneg _
  have posb : ∀ q ∈ Sb, 0 ≤ q := by rintro q ⟨n, m, hm, h, rfl⟩; apply div_nonneg <;> exact Nat.cast_nonneg _
  apply csSup_mul_le_csSup (P.kappa_set_nonempty a) (P.kappa_set_bddAbove a) posa (P.kappa_set_nonempty b) posb
  rintro q1 ⟨n1, m1, hm1, ha, rfl⟩ q2 ⟨n2, m2, hm2, hb, rfl⟩
  apply le_csSup (P.kappa_set_bddAbove _)
  refine ⟨n1 * n2, m1 * m2, Nat.mul_pos hm1 hm2, ?_, ?_⟩
  · letI := P.toPreorder
    push_cast
    calc
      P.le (↑n1 * ↑n2) (↑m1 * a * ↑n2) := by
        apply P.mul_right; exact ha
      _ ≤ ((↑m2 * b) * (↑m1 * a)) := by
        have h_comm : ↑m1 * a * ↑n2 = ↑n2 * (↑m1 * a) := by ring
        rw [h_comm]
        apply P.mul_right; exact hb
      _ ≤ (↑m1 * ↑m2 * (a * b)) := by
        apply le_of_eq; ring
  · push_cast; field_simp; try ring

theorem kappa_le_rho (P : StrassenPreorder R) (a : R) : P.kappa a ≤ P.rho a := by
  apply csSup_le (P.kappa_set_nonempty a)
  rintro qk ⟨nk, mk, hmk, hk, rfl⟩
  apply le_csInf (P.rho_set_nonempty a)
  rintro qr ⟨nr, mr, hmr, hr, rfl⟩
  have hmk_pos : 0 < (mk : ℝ) := Nat.cast_pos.mpr hmk
  have hmr_pos : 0 < (mr : ℝ) := Nat.cast_pos.mpr hmr
  rw [div_le_div_iff₀ hmk_pos hmr_pos]
  norm_cast
  letI := P.toPreorder
  -- Goal: nk * mr ≤ mk * nr
  have h1 : P.le (↑nk * ↑mr) (↑mk * a * ↑mr) := P.mul_right ↑nk (↑mk * a) hk ↑mr
  have h2 : P.le (↑mk * (↑mr * a)) (↑mk * ↑nr) := by
    apply P.le_trans _ ((↑mr * a) * ↑mk)
    · apply le_of_eq; ring
    · apply P.le_trans _ (↑nr * ↑mk)
      · exact P.mul_right (↑mr * a) ↑nr hr ↑mk
      · apply le_of_eq; ring
  have h_goal : P.le (↑nk * ↑mr) (↑mk * ↑nr) := by
    have h_eq : (↑mk : R) * a * ↑mr = ↑mk * (↑mr * a) := by ring
    rw [h_eq] at h1
    exact P.le_trans _ _ _ h1 h2
  rw [← Nat.cast_mul, ← Nat.cast_mul, P.nat_order_embedding] at h_goal
  rw [Nat.mul_comm nr mk]
  exact h_goal

theorem rho_eq_kappa_of_total (P : StrassenPreorder R) (total : P.IsTotal) (a : R) :
    P.rho a = P.kappa a := by
  apply le_antisymm
  · -- rho a ≤ kappa a
    by_contra h
    have h_lt : P.kappa a < P.rho a := not_le.mp h
    obtain ⟨q, hq_kappa, hq_rho⟩ := exists_rat_btwn h_lt
    let n := q.num.natAbs
    let m := q.den
    have hm : 0 < m := q.den_pos
    have hq_pos : 0 ≤ q := by
      have h0 : 0 ≤ P.kappa a := by
        apply le_csSup (P.kappa_set_bddAbove a)
        refine ⟨0, 1, Nat.zero_lt_one, ?_, by simp⟩
        simpa using P.all_nonneg a
      exact Rat.cast_nonneg.mp (h0.trans hq_kappa.le)
    have hq_eq : (q : ℝ) = (n : ℝ) / m := by
      rw [Rat.cast_def]
      field_simp [hm.ne', q.den_pos.ne']
      norm_cast
      have : q.num = (n : ℤ) := (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq_pos)).symm
      rw [this, Int.mul_comm]
      rfl
    have h_rho_imp : P.le (↑m * a) ↑n → False := by
      intro h_le
      have mem : (n : ℝ) / m ∈ P.rho_set a := ⟨n, m, hm, h_le, rfl⟩
      have : P.rho a ≤ (n : ℝ) / m := csInf_le (P.rho_set_bddBelow a) mem
      rw [← hq_eq] at this
      linarith
    have h_kappa_imp : P.le ↑n (↑m * a) → False := by
      intro h_le
      have mem : (n : ℝ) / m ∈ P.kappa_set a := ⟨n, m, hm, h_le, rfl⟩
      have : (n : ℝ) / m ≤ P.kappa a := le_csSup (P.kappa_set_bddAbove a) mem
      rw [← hq_eq] at this
      linarith
    -- Totality contradiction
    cases total (↑m * a) ↑n with
    | inl h_tot => exact h_rho_imp h_tot
    | inr h_tot => exact h_kappa_imp h_tot
  · exact P.kappa_le_rho a

theorem rho_add (P : StrassenPreorder R) (total : P.IsTotal) (a b : R) :
    P.rho (a + b) = P.rho a + P.rho b := by
  apply le_antisymm
  · exact P.rho_add_le a b
  · rw [P.rho_eq_kappa_of_total total a, P.rho_eq_kappa_of_total total b, P.rho_eq_kappa_of_total total (a + b)]
    exact P.kappa_add_ge a b

theorem rho_mul (P : StrassenPreorder R) (total : P.IsTotal) (a b : R) :
    P.rho (a * b) = P.rho a * P.rho b := by
  apply le_antisymm
  · exact P.rho_mul_le a b
  · rw [P.rho_eq_kappa_of_total total a, P.rho_eq_kappa_of_total total b, P.rho_eq_kappa_of_total total (a * b)]
    exact P.kappa_mul_ge a b

theorem rho_zero (P : StrassenPreorder R) : P.rho 0 = 0 := by
  rw [← Nat.cast_zero, P.rho_nat_cast]
  simp

theorem rho_one (P : StrassenPreorder R) : P.rho 1 = 1 := by
  rw [← Nat.cast_one, P.rho_nat_cast]
  simp

/-- The fractional rank as a ring homomorphism for total preorders. -/
def rho_toRingHom (P : StrassenPreorder R) (total : P.IsTotal) : R →+* ℝ where
  toFun := P.rho
  map_one' := P.rho_one
  map_mul' := P.rho_mul total
  map_zero' := P.rho_zero
  map_add' := P.rho_add total

end StrassenPreorder
