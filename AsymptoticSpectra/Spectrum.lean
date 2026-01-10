import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import AsymptoticSpectra.Structures
import AsymptoticSpectra.Rank
import AsymptoticSpectra.AsymptoticClosure

universe u

noncomputable section

open Classical Set Filter Topology

structure SemiringSpectrumPoint (R : Type u) [CommSemiring R] (P : SemiringPreorder R) extends R →+* ℝ where
  monotone' : ∀ {a b : R}, P.le a b → toRingHom a ≤ toRingHom b

/-- A point in the asymptotic spectrum is a monotone semiring homomorphism to ℝ. -/
abbrev AsymptoticSpectrumPoint (R : Type u) [CommSemiring R] (P : StrassenPreorder R) :=
  SemiringSpectrumPoint R (P.toSemiringPreorder)

namespace StrassenPreorder

/-- For a total Strassen preorder, the fractional rank defines a point in the asymptotic spectrum. -/
def rho_asymptoticSpectrumPoint {R : Type u} [CommSemiring R] (P : StrassenPreorder R)
    (total : P.IsTotal) : AsymptoticSpectrumPoint R P where
  toRingHom := P.rho_toRingHom total
  monotone' := by
    intro a b h
    exact P.rho_monotone h

end StrassenPreorder

/-- The asymptotic spectrum is the set of monotone semiring homomorphisms to ℝ. -/
abbrev AsymptoticSpectrum (R : Type u) [CommSemiring R] (P : StrassenPreorder R) : Type u :=
  AsymptoticSpectrumPoint R P

/-- The type of maximal extensions of a Strassen preorder P.
    A Strassen preorder is maximal if and only if it is total and closed. -/
abbrev MaxExtension (R : Type u) [CommSemiring R] (P : StrassenPreorder R) : Type u :=
  { Q : StrassenPreorder R // P ≤ Q ∧ Q.IsTotal ∧ Q.IsClosed }

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

/-- The product space of intervals [0, rank P a] that contains the asymptotic spectrum. -/
def SpectrumBox (P : StrassenPreorder R) : Type u :=
  ∀ a : R, ↥(Set.Icc (0 : ℝ) (P.rank a : ℝ))

instance (P : StrassenPreorder R) : TopologicalSpace (SpectrumBox P) :=
  Pi.topologicalSpace

instance (P : StrassenPreorder R) : CompactSpace (SpectrumBox P) :=
  Pi.compactSpace

/-- The natural map from spectrum points to the compact box. -/
def toBox {P : StrassenPreorder R} (ϕ : AsymptoticSpectrumPoint R P) : SpectrumBox P :=
  fun a => ⟨ϕ a, by
    constructor
    · have h0 : P.le 0 a := P.zero_le a
      have := ϕ.monotone' h0
      rw [map_zero (ϕ.toRingHom)] at this
      exact this
    · have hr := Nat.find_spec (P.upper_archimedean a)
      have := ϕ.monotone' hr
      rw [map_natCast] at this
      exact this⟩

/-- The topology on the asymptotic spectrum is the topology of pointwise convergence. -/
instance (P : StrassenPreorder R) : TopologicalSpace (AsymptoticSpectrumPoint R P) :=
  TopologicalSpace.induced (fun f => (f : R → ℝ)) Pi.topologicalSpace

namespace AsymptoticSpectrumPoint

@[ext]
theorem ext {P : StrassenPreorder R} (ϕ ψ : AsymptoticSpectrumPoint R P) (h : ∀ a, ϕ a = ψ a) : ϕ = ψ :=
  DFunLike.ext ϕ ψ h

/-- Restrict a spectrum point from a larger preorder Q to a smaller preorder P. -/
def restrict {P Q : StrassenPreorder R} (h : P ≤ Q) (ϕ : AsymptoticSpectrumPoint R Q) :
    AsymptoticSpectrumPoint R P where
  toRingHom := ϕ.toRingHom
  monotone' := fun hab => ϕ.monotone' (h _ _ hab)

/-- Any point in the asymptotic spectrum defines a Strassen preorder. -/
def toStrassenPreorder {R : Type u} [CommSemiring R] {P : StrassenPreorder R}
    (ϕ : AsymptoticSpectrumPoint R P) : StrassenPreorder R where
  le a b := ϕ a ≤ ϕ b
  le_refl a := le_refl _
  le_trans a b c hab hbc := le_trans hab hbc
  add_right a b hab c := by
    rw [map_add, map_add]
    linarith
  mul_right a b hab c := by
    rw [map_mul, map_mul]
    have h0c : 0 ≤ ϕ c := by
      rw [← map_zero (ϕ.toRingHom)]
      apply ϕ.monotone'
      exact P.zero_le c
    nlinarith
  zero_le a := ϕ.monotone' (P.zero_le a)
  nat_order_embedding n m := by
    rw [map_natCast, map_natCast]
    exact Nat.cast_le
  lower_archimedean a := by
    cases P.lower_archimedean a with
    | inl h => left; simp [h]
    | inr h => right; simpa using ϕ.monotone' h
  upper_archimedean a := by
    obtain ⟨n, h⟩ := P.upper_archimedean a
    use n
    simpa using ϕ.monotone' h

/-- The preorder defined by a spectrum point is total. -/
theorem toStrassenPreorder_isTotal {R : Type u} [CommSemiring R] {P : StrassenPreorder R}
    (ϕ : AsymptoticSpectrumPoint R P) : ϕ.toStrassenPreorder.IsTotal :=
  fun a b => le_total (ϕ a) (ϕ b)

/-- The preorder defined by a spectrum point is closed. -/
theorem toStrassenPreorder_isClosed {R : Type u} [CommSemiring R] {P : StrassenPreorder R}
    (ϕ : AsymptoticSpectrumPoint R P) : ϕ.toStrassenPreorder.IsClosed := by
  intro a b h
  dsimp [toStrassenPreorder]
  obtain ⟨f, hf, hle⟩ := h
  dsimp [toStrassenPreorder] at hle
  have h_phi_le : ∀ n, (ϕ a)^n ≤ f n * (ϕ b)^n := by
    intro n
    specialize hle n
    rw [map_pow, map_mul, map_natCast, map_pow] at hle
    exact_mod_cast hle
  by_cases hb : 0 < ϕ b
  · apply le_of_forall_pos_le_add
    intro δ hδ
    let ε := δ / ϕ b
    have hε : 0 < ε := div_pos hδ hb
    have h_subexp := hf ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp h_subexp
    let n := N + 1
    specialize h_phi_le n
    specialize hN n (Nat.le_add_right N 1)
    have h_pow_pos : 0 < (ϕ b)^n := pow_pos hb n
    have h_ratio : (ϕ a / ϕ b)^n ≤ (f n : ℝ) := by
      rw [div_pow, div_le_iff₀ h_pow_pos]
      exact_mod_cast h_phi_le
    have h_final : (ϕ a / ϕ b)^n ≤ (1 + ε)^n := h_ratio.trans (by exact_mod_cast hN)
    have h_base : ϕ a / ϕ b ≤ 1 + ε := by
      have h_n_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos N)
      rw [← Real.rpow_le_rpow_iff _ (by linarith) h_n_pos]
      · simp only [Real.rpow_natCast]
        exact h_final
      · apply div_nonneg
        · rw [← map_zero (ϕ.toRingHom)]
          apply ϕ.monotone' (P.zero_le a)
        · linarith
    rw [div_le_iff₀ hb] at h_base
    calc ϕ a ≤ (1 + ε) * ϕ b := h_base
      _ = ϕ b + ε * ϕ b := by ring
      _ = ϕ b + δ := by rw [div_mul_cancel₀ _ (ne_of_gt hb)]
  · have hb0 : ϕ b = 0 := by
      have : 0 ≤ ϕ b := by
        rw [← map_zero (ϕ.toRingHom)]
        apply ϕ.monotone' (P.zero_le b)
      linarith
    rw [hb0] at h_phi_le
    specialize h_phi_le 1
    rw [hb0]
    simp only [pow_one, mul_zero] at h_phi_le
    have h_phi_a_pos : 0 ≤ ϕ a := by
      rw [← map_zero (ϕ.toRingHom)]
      apply ϕ.monotone' (P.zero_le a)
    linarith

/-- The preorder defined by a spectrum point extends the original preorder P. -/
theorem toStrassenPreorder_le {R : Type u} [CommSemiring R] {P : StrassenPreorder R}
    (ϕ : AsymptoticSpectrumPoint R P) (a b : R) (h : P.le a b) :
    ϕ.toStrassenPreorder.le a b :=
  ϕ.monotone' h

/-- The fractional rank of the preorder induced by ϕ is ϕ itself. -/
theorem rho_of_toStrassenPreorder {R : Type u} [CommSemiring R] {P : StrassenPreorder R}
    (ϕ : AsymptoticSpectrumPoint R P) (a : R) :
    ϕ.toStrassenPreorder.rho a = ϕ a := by
  let Q := ϕ.toStrassenPreorder
  apply le_antisymm
  · apply le_of_forall_gt
    intro v hv
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hv
    have : Q.rho a ≤ (q : ℝ) := by
      apply csInf_le (Q.rho_set_bddBelow a)
      have h_phi_pos : 0 ≤ ϕ a := by rw [← map_zero (ϕ.toRingHom)]; apply ϕ.monotone'; exact P.zero_le a
      have hq_pos : 0 < (q : ℝ) := lt_of_le_of_lt h_phi_pos hq1
      have h_q_num_pos : 0 ≤ q.num := by
        apply Rat.num_nonneg.mpr
        exact_mod_cast hq_pos.le
      let n := q.num.toNat
      let m := q.den
      refine ⟨n, m, q.pos, ?_, ?_⟩
      · dsimp [Q, toStrassenPreorder]
        rw [map_mul, map_natCast, map_natCast]
        have hq_val : (q : ℝ) = (n : ℝ) / (m : ℝ) := by
          rw [Rat.cast_def q]
          congr
          exact (Int.toNat_of_nonneg h_q_num_pos).symm
        have h_den_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr q.pos
        have hq' : ϕ a < (n : ℝ) / (m : ℝ) := by rwa [← hq_val]
        rw [lt_div_iff₀ h_den_pos] at hq'
        nlinarith
      · rw [Rat.cast_def q]
        congr
        exact (Int.toNat_of_nonneg h_q_num_pos).symm
    exact lt_of_le_of_lt this hq2
  · apply le_csInf (Q.rho_set_nonempty a)
    rintro x ⟨n, m, hm, h, rfl⟩
    dsimp [Q, toStrassenPreorder] at h
    rw [map_mul, map_natCast, map_natCast] at h
    have h_m_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    rw [le_div_iff₀ h_m_pos, mul_comm]
    exact h

end AsymptoticSpectrumPoint

/-- Map from a spectrum point to its corresponding maximal extension. -/
def spectrumToMaxExtension {P : StrassenPreorder R} (ϕ : AsymptoticSpectrumPoint R P) :
    MaxExtension R P :=
  ⟨ϕ.toStrassenPreorder, ⟨ϕ.toStrassenPreorder_le, ϕ.toStrassenPreorder_isTotal, ϕ.toStrassenPreorder_isClosed⟩⟩

/-- Map from a maximal extension to its corresponding spectrum point. -/
def maxExtensionToSpectrum {P : StrassenPreorder R} (E : MaxExtension R P) :
    AsymptoticSpectrumPoint R P :=
  let ϕ_E := E.val.rho_asymptoticSpectrumPoint E.property.2.1
  AsymptoticSpectrumPoint.restrict E.property.1 ϕ_E

/-- spectrumToMaxExtension is the left inverse of maxExtensionToSpectrum. -/
theorem spectrum_left_inverse {P : StrassenPreorder R} (ϕ : AsymptoticSpectrumPoint R P) :
    maxExtensionToSpectrum (spectrumToMaxExtension ϕ) = ϕ := by
  ext a
  dsimp [maxExtensionToSpectrum, spectrumToMaxExtension, AsymptoticSpectrumPoint.restrict, StrassenPreorder.rho_asymptoticSpectrumPoint]
  apply AsymptoticSpectrumPoint.rho_of_toStrassenPreorder

/-- spectrumToMaxExtension is the right inverse of maxExtensionToSpectrum. -/
theorem spectrum_right_inverse {P : StrassenPreorder R} (E : MaxExtension R P) :
    spectrumToMaxExtension (maxExtensionToSpectrum E) = E := by
  apply Subtype.ext
  ext a b
  dsimp [spectrumToMaxExtension, maxExtensionToSpectrum, AsymptoticSpectrumPoint.restrict, AsymptoticSpectrumPoint.toStrassenPreorder,
    StrassenPreorder.rho_asymptoticSpectrumPoint, SemiringSpectrumPoint.toRingHom,
    StrassenPreorder.rho_toRingHom]
  change (E.val.rho a ≤ E.val.rho b ↔ E.val.le a b)
  rw [StrassenPreorder.rho_reflects_le E.val E.property.2.1 E.property.2.2]

/-- The asymptotic spectrum of P is in bijection with the maximal extensions of P. -/
noncomputable def asymptoticSpectrumEquivMaxExtensions (P : StrassenPreorder R) :
    AsymptoticSpectrumPoint R P ≃ MaxExtension R P where
  toFun := spectrumToMaxExtension
  invFun := maxExtensionToSpectrum
  left_inv := spectrum_left_inverse
  right_inv := spectrum_right_inverse

theorem continuous_eval {R : Type u} [CommSemiring R] (P : StrassenPreorder R) (a : R) :
  Continuous (fun (ϕ : AsymptoticSpectrumPoint R P) => ϕ a) :=
  continuous_pi_iff.mp continuous_induced_dom a

/-- The map to the bounding box is continuous. -/
theorem continuous_toBox {P : StrassenPreorder R} :
    Continuous (toBox (P := P)) := by
  apply continuous_pi
  intro a
  apply Continuous.subtype_mk
  apply continuous_eval P a

/-- The map to the bounding box is an embedding. -/
theorem embedding_toBox {P : StrassenPreorder R} :
    IsEmbedding (toBox (P := P)) := {
  eq_induced := by
    let coe : SpectrumBox P → (R → ℝ) := fun f a => f a
    have h_ind : instTopologicalSpaceSpectrumBox P = TopologicalSpace.induced coe Pi.topologicalSpace := by
      simp only [instTopologicalSpaceSpectrumBox, Pi.topologicalSpace, induced_iInf, induced_compose]
      congr; funext a
      have : IsEmbedding (Subtype.val : Set.Icc (0:ℝ) (P.rank a) → ℝ) := IsEmbedding.subtypeVal
      rw [this.eq_induced]
      simp only [induced_compose]
      rfl
    change _ = TopologicalSpace.induced toBox (instTopologicalSpaceSpectrumBox P)
    rw [h_ind, induced_compose]
    rfl
  injective := fun ϕ ψ h => by
    ext a
    have := congr_fun h a
    rw [Subtype.ext_iff] at this
    exact this
}

/-- The range of the map to the bounding box is closed. -/
theorem isClosed_range_toBox {P : StrassenPreorder R} :
    IsClosed (Set.range (toBox (P := P))) := by
  let f_val (a : R) : SpectrumBox P → ℝ := fun f => (f a : ℝ)
  have h_val (a : R) : Continuous (f_val a) :=
    (continuous_apply a).subtype_val

  let S_add := {f : SpectrumBox P | ∀ a b, f_val (a + b) f = f_val a f + f_val b f}
  let S_mul := {f : SpectrumBox P | ∀ a b, f_val (a * b) f = f_val a f * f_val b f}
  let S_zero := {f : SpectrumBox P | f_val 0 f = 0}
  let S_one := {f : SpectrumBox P | f_val 1 f = 1}
  let S_mono := {f : SpectrumBox P | ∀ a b, P.le a b → f_val a f ≤ f_val b f}

  have h_cl : IsClosed (S_add ∩ S_mul ∩ S_zero ∩ S_one ∩ S_mono) := by
    repeat' apply IsClosed.inter
    · simp only [S_add, setOf_forall]
      exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq (h_val _) ((h_val _).add (h_val _))
    · simp only [S_mul, setOf_forall]
      exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq (h_val _) ((h_val _).mul (h_val _))
    · exact isClosed_eq (h_val 0) continuous_const
    · exact isClosed_eq (h_val 1) continuous_const
    · simp only [S_mono, setOf_forall]
      exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => isClosed_le (h_val _) (h_val _)

  have h_eq : Set.range (toBox (P := P)) = S_add ∩ S_mul ∩ S_zero ∩ S_one ∩ S_mono := by
    ext f
    constructor
    · rintro ⟨ϕ, rfl⟩
      simp only [Set.mem_inter_iff, S_add, S_mul, S_zero, S_one, S_mono, mem_setOf_eq]
      exact ⟨⟨⟨⟨fun a b => map_add ϕ a b, fun a b => map_mul ϕ a b⟩, map_zero ϕ⟩, map_one ϕ⟩, fun a b hab => ϕ.monotone' hab⟩
    · intro h
      rcases h with ⟨⟨⟨⟨h_add, h_mul⟩, h_zero⟩, h_one⟩, h_mono⟩
      let ϕ_hom : R →+* ℝ := {
        toFun := fun a => f_val a f
        map_add' := h_add
        map_mul' := h_mul
        map_zero' := h_zero
        map_one' := h_one
      }
      let ϕ : AsymptoticSpectrumPoint R P := {
        toRingHom := ϕ_hom
        monotone' := fun {a b} hab => h_mono a b hab
      }
      use ϕ
      apply funext
      intro a
      apply Subtype.ext
      rfl

  rw [h_eq]
  exact h_cl

instance (P : StrassenPreorder R) : T2Space (SpectrumBox P) :=
  Pi.t2Space

/-- The asymptotic spectrum is a compact space. -/
instance (P : StrassenPreorder R) : CompactSpace (AsymptoticSpectrumPoint R P) :=
  ⟨by
    rw [embedding_toBox.isCompact_iff, Set.image_univ]
    exact IsClosed.isCompact isClosed_range_toBox⟩

instance (P : StrassenPreorder R) : T2Space (AsymptoticSpectrumPoint R P) :=
  T2Space.of_injective_continuous embedding_toBox.injective continuous_toBox

theorem spectrumPoint_implies_nat_order_embedding {P : SemiringPreorder R} (ϕ : SemiringSpectrumPoint R P) :
    ∀ n m : ℕ, P.le (n : R) (m : R) ↔ n ≤ m := by
  intro n m
  constructor
  · intro h
    apply Nat.cast_le (α := ℝ).mp
    rw [← map_natCast ϕ.toRingHom, ← map_natCast ϕ.toRingHom]
    exact ϕ.monotone' h
  · intro h
    obtain ⟨k, rfl⟩ := Nat.le.dest h
    rw [Nat.cast_add]
    nth_rewrite 1 [← add_zero (n : R)]
    rw [add_comm (n : R) 0, add_comm (n : R) (k : R)]
    apply P.add_right
    exact P.zero_le _
