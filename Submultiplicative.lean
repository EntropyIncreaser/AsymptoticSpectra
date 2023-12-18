import Mathlib.Topology.Instances.Real
import Mathlib.Order.Filter.Archimedean
import Mathlib.Data.Real.NNReal

noncomputable section

open Set Filter Topology

def Submultiplicative (u : ℕ → NNReal) : Prop :=
  ∀ m n, u (m * n) ≤ u m * u n

namespace Submultiplicative

variable {u : ℕ → NNReal} (h : Submultiplicative u)

def lim (_h : Submultiplicative u) :=
  sInf ((fun n : ℕ => (u n) ^ (1 / n)) '' Ici 1)

theorem Submultiplicative.tends_to_lim :
  Tendsto (fun n => (u n) ^ (1 / n)) atTop (𝓝 h.lim) := by
  sorry
