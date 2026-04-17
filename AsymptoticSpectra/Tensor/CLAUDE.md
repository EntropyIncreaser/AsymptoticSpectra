# AsymptoticSpectra/Tensor/ — Subdirectory Overview

This subdirectory develops the **tensor-product semiring** used as the primary example of a `StrassenPreorder`. The underlying semiring consists of isomorphism classes of order-`d` tensors over a field `K`, with direct sum as addition and tensor contraction (via the interchange map) as multiplication.

## Files

### `Tensor.lean`
- Defines `TensorObj K d`: a concrete order-`d` tensor as a `d`-tuple of vector spaces `V₁, …, V_d` together with an element of `⨂ V_i`.
- Defines `TensorIso` (componentwise linear equivalence) and the quotient `Tensor K d` (isomorphism classes).
- Defines **addition** (direct sum of ambient spaces) and **multiplication** (tensor contraction via `interchangeMap`) on `TensorObj`, and proves they descend to the quotient.
- Constructs `interchangeMap : (⨂ V_i) ⊗ (⨂ W_i) →ₗ ⨂ (V_i ⊗ W_i)` and proves functoriality and naturality.
- Provides the zero and unit tensor objects, making `Tensor K d` a commutative semiring.

### `BaseChange.lean`
- Defines `TensorObj.baseChange L X`: extension of scalars from `K` to a field extension `L`, acting componentwise on each `V_i`.
- Proves `baseChange` preserves addition, multiplication, zero, and one up to isomorphism.
- Constructs the **base-change ring homomorphism** `Tensor K d →+* Tensor L d`.
- Key lemma: `baseChange_interchange` — base-change commutes with the interchange map.

### `Flattening.lean`
- Defines `Split (Fin d)`: a partition of the `d` indices into two non-empty blocks `S` and `Sᶜ`.
- Defines `flatteningMap σ X`: the linear map `⨂_{i∈S} V_i ⊗ ⨂_{i∈Sᶜ} V_i → Hom(⨂_{i∈S} V_i*, ⨂_{i∈Sᶜ} V_i)` (the flattening of `X` along split `σ`).
- Defines `flatteningRank σ X` as the rank of `flatteningMap σ X`, and proves it is invariant under `TensorIso`.
- Proves **additivity** `flatteningRank σ (X + Y) = flatteningRank σ X + flatteningRank σ Y` and **multiplicativity** `flatteningRank σ (X * Y) = flatteningRank σ X * flatteningRank σ Y`.
- Constructs `FlatteningRankPoint σ`: a `SemiringSpectrumPoint` for `Tensor K d`, used to supply the `nat_order_embedding` required by `StrassenPreorder`.

### `Restriction.lean`
- Defines `TensorObj.Restrict X Y`: `X` restricts to `Y` if there exist linear maps `f_i : Y.V_i → X.V_i` such that `(⨂ f_i)(Y.t) = X.t`; defines `Tensor.Restrict` on the quotient.
- Proves `Restrict` is a preorder (reflexivity, transitivity) and respects isomorphism.
- Establishes that `flatteningRank` is monotone under restriction.
- Proves `tensor_le_natCast_iff`: `⟦X⟧ ≤ (r : Tensor K d)` iff `X.t` is a sum of `r` pure tensors.
- Constructs the `StrassenPreorder` instance on `Tensor K d` (no remaining `sorry`).

### `Degeneration.lean`
- Defines `TensorObj.PolyFamily X Y`: a finite-support family of `K`-linear maps `A_i^{(j)} : Y.V_i →ₗ X.V_i` per mode `i`, representing a `K[T]`-linear map under the scalar-family encoding.
- Defines `TensorObj.DegeneratesOfOrder X Y h`: `X` is a degeneration of `Y` at order `h`, meaning there exists a `PolyFamily` whose `T^k` coefficients vanish for `k < h` and whose `T^h` coefficient equals `X.t`.
- Proves closure properties: `refl`, `add_right`, `mul_right`, `mul` (orders add), `trans` (orders compose as `(h₁+1)(h₂+1)-1`), and compatibility with restriction (`of_restrict_left/right`).
- Lifts to `Tensor K d` as `Tensor.Degenerates`; proves `Restrict.degenerates` (restriction implies degeneration at order 0) and `Degenerates.asymptoticLe` (degeneration implies asymptotic restriction, via subexponential multiplier `(nh+1)^d`).
- Constructs `Tensor.strassenPreorderOfDegenerates`: a `StrassenPreorder` on `Tensor K d` with `le := Degenerates`, and proves `asymptoticClosure_degenerates_eq`: degeneration and restriction have the same asymptotic closure. No remaining `sorry`.

### `Permutation.lean`
- Defines `TensorObj.permuteSpaces σ X`: permutes the mode spaces of `X` by `σ ∈ Sₐ`, with mode `i` getting `X.V (σ.symm i)` and tensor element permuted via `PiTensorProduct.reindex K X.V σ`.
- Proves `permuteSpaces` respects `TensorObj.Restrict` and direct sums, hence descends to `Tensor.permuteSpaces : Tensor K d → Tensor K d` (a ring homomorphism, with `mul` and `one` still `sorry`).
- Constructs `AsymptoticSpectrumPoint.perm φ σ`: the permuted spectrum point `φ^σ(x) = φ(permuteSpaces σ x)`, still a spectrum point (monotonicity `sorry`).
- Key lemma: `TensorObj.permuteSpaces_add_restrict` — reindexing commutes with `inl`/`inr` via `PiTensorProduct.map_reindex`.

### `MatrixMult.lean`
- Defines `MMObj n m p : TensorObj K 3` and `MM n m p : Tensor K 3`; proves `MM_mul`, `MM_pow`, `MM_le_of_le`, `MM_le_mul`, `one_le_MM`, `MM_ne_zero`.
- Defines `θ₁, θ₂, θ₃ : AsymptoticSpectrumPoint → ℝ` as `log φ(MM 2 1 1) / log 2` etc.; proves `θᵢ ∈ [0,1]` (under `RefinesCanonical P`) and `MM_eval`: `φ(MM n m p) = n^θ₁ · m^θ₂ · p^θ₃`.
- Defines `specMM : Set (ℝ × ℝ × ℝ)` as the image of the spectrum under `φ ↦ (θ₁, θ₂, θ₃)`; proves `specMM ⊆ [0,1]³` and `specMM` is compact. Defines `cyclicPerm`/`transpPerm` and proves `MM_permuteSpaces_cyclic/transp`, `θ_perm_cyclic/transp`, `specMM_perm`.
- Defines `matMulExp : ℝ` intrinsically as `iInf n, log (rank P_can (MM n n n)) / log n`; proves the canonical normalization `matMulExp_eq_log_AR_222`: `ω = log_2 AR(MM 2 2 2)`, and the duality characterization `matMulExp_eq_sup_specMM`: `ω = ⨆_φ (θ₁+θ₂+θ₃)(φ)` (modulo the upstream Duality `sorry`).
- Proves `jensen_S3_convex` (3-cyclic Jensen averaging) and the **asymptotic sum inequality** `asymptotic_sum_inequality`: `AR(⊕ᵢ MM(nᵢ,mᵢ,pᵢ)) ≤ r` implies `∑ᵢ (nᵢ·mᵢ·pᵢ)^{ω/3} ≤ r`. No remaining `sorry` in this file (only the Duality black-box is upstream).

---

## Maintenance instructions

When you add or significantly modify a `.lean` file in this directory:
1. Update the relevant entry in this file (or add a new entry if it is a new file).
2. Keep each file's description to **at most 5 bullet points**.
3. Focus on mathematical content: what structures are defined, what key theorems are proved.
4. Do not describe proof techniques or implementation details unless they are mathematically significant.
5. If a file has significant `sorry`s, note which theorems are still incomplete.
