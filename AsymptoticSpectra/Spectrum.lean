import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import AsymptoticSpectra.Structures

universe u

noncomputable section

open Classical Set Filter Topology

/-- A point in the asymptotic spectrum is a monotone semiring homomorphism to ℝ. -/
structure AsymptoticSpectrumPoint (R : Type u) [CommSemiring R] (P : StrassenPreorder R) extends R →+* ℝ where
  monotone' : ∀ {a b : R}, P.le a b → toRingHom a ≤ toRingHom b

/-- The asymptotic spectrum is the set of monotone semiring homomorphisms to ℝ. -/
abbrev AsymptoticSpectrum (R : Type u) [CommSemiring R] (P : StrassenPreorder R) : Type u :=
  AsymptoticSpectrumPoint R P

variable {R : Type u} [CommSemiring R]

instance (P : StrassenPreorder R) : FunLike (AsymptoticSpectrumPoint R P) R ℝ where
  coe f := f.toRingHom.toFun
  coe_injective' f g h := by
    obtain ⟨f_hom, f_mono⟩ := f
    obtain ⟨g_hom, g_mono⟩ := g
    congr
    exact DFunLike.coe_injective h

instance (P : StrassenPreorder R) : RingHomClass (AsymptoticSpectrumPoint R P) R ℝ where
  map_add f := f.toRingHom.map_add'
  map_mul f := f.toRingHom.map_mul'
  map_zero f := f.toRingHom.map_zero'
  map_one f := f.toRingHom.map_one'

/-- The topology on the asymptotic spectrum is the topology of pointwise convergence. -/
instance (P : StrassenPreorder R) : TopologicalSpace (AsymptoticSpectrumPoint R P) :=
  TopologicalSpace.induced (fun f => (f : R → ℝ)) Pi.topologicalSpace

theorem continuous_eval {R : Type u} [CommSemiring R] (P : StrassenPreorder R) (a : R) :
  Continuous (fun (ϕ : AsymptoticSpectrumPoint R P) => ϕ a) :=
  continuous_pi_iff.mp continuous_induced_dom a

/-- The asymptotic spectrum is a compact Hausdorff space. -/
instance (P : StrassenPreorder R) : CompactSpace (AsymptoticSpectrum R P) := sorry

instance (P : StrassenPreorder R) : T2Space (AsymptoticSpectrum R P) := sorry
