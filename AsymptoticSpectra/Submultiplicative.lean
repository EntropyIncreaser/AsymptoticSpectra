import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Subadditive
noncomputable section
open Set Filter Topology

/-- A sequence u : ℕ → ℝ is submultiplicative if u(m + n) ≤ u(m) * u(n) for all m, n. -/
def IsSubmultiplicative (u : ℕ → ℝ) : Prop :=
  ∀ m n, u (m + n) ≤ u m * u n

namespace IsSubmultiplicative

variable {u : ℕ → ℝ} (h : IsSubmultiplicative u) (h1 : ∀ n, 1 ≤ u n)

/-- The limit guaranteed by Fekete's Lemma for submultiplicative sequences. -/
def lim (_h : IsSubmultiplicative u) :=
  sInf ((fun n : ℕ => (u n) ^ (1 / (n : ℝ))) '' Ici 1)

/-- Fekete's Lemma for submultiplicative sequences: the normalized sequence tends to its infimum. -/
theorem tends_to_lim :
  Tendsto (fun n => (u n) ^ (1 / (n : ℝ))) atTop (𝓝 h.lim) := by
  have pos_u : ∀ n, 0 < u n := fun n => zero_lt_one.trans_le (h1 n)

  let v : ℕ → ℝ := fun n => Real.log (u n)
  have hv : Subadditive v := by
    intro m n
    dsimp [v]
    rw [← Real.log_mul (pos_u m).ne' (pos_u n).ne']
    apply (Real.log_le_log (pos_u (m + n)) (mul_pos (pos_u m) (pos_u n))).mpr
    exact h m n
  have hbdd : BddBelow (range fun n => v n / n) := by
    use 0
    rintro _ ⟨n, rfl⟩
    rw [div_nonneg_iff]
    left
    constructor
    · apply Real.log_nonneg
      exact h1 n
    · exact Nat.cast_nonneg n

  have hlim : Tendsto (fun n => v n / n) atTop (𝓝 hv.lim) :=
    Subadditive.tendsto_lim hv hbdd

  -- Exponentiate
  have hexp : Tendsto (fun n => Real.exp (v n / n)) atTop (𝓝 (Real.exp hv.lim)) :=
    hlim.exp

  have eq_exp : ∀ n, n ≠ 0 → Real.exp (v n / n) = (u n) ^ (1 / (n : ℝ)) := by
    intro n _hn
    rw [div_eq_mul_one_div, Real.exp_mul, Real.exp_log (pos_u n)]

  have : Tendsto (fun n => (u n) ^ (1 / (n : ℝ))) atTop (𝓝 (Real.exp hv.lim)) := by
    refine hexp.congr' (eventually_atTop.2 ⟨1, ?_⟩)
    intro n hn
    rw [eq_exp n (ne_of_gt (Nat.succ_le_iff.mp hn))]

  convert this
  -- Proof that h.lim = exp hv.lim
  dsimp [lim]
  unfold Subadditive.lim

  set S_log := (fun n : ℕ => v n / (n : ℝ)) '' Ici 1
  set S_u := (fun n : ℕ => (u n) ^ (1 / (n : ℝ))) '' Ici 1

  have h_sets : S_u = Real.exp '' S_log := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      use v n / (n : ℝ)
      constructor
      · exact ⟨n, hn, rfl⟩
      · rw [eq_exp n (ne_of_gt (zero_lt_one.trans_le hn))]
    · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
      use n, hn
      rw [eq_exp n (ne_of_gt (zero_lt_one.trans_le hn))]

  rw [h_sets]
  -- Target: sInf (Real.exp '' S_log) = Real.exp (sInf S_log)
  exact (Monotone.map_csInf_of_continuousAt Real.continuous_exp.continuousAt Real.exp_monotone
    (Set.Nonempty.image _ ⟨1, mem_Ici.mpr (le_refl 1)⟩) (hbdd.mono (image_subset_range _ _))).symm
