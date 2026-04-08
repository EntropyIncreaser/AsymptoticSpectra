# AsymptoticSpectra — Project Overview

This project formalizes the theory of **asymptotic spectra** (Strassen 1988) in Lean 4 / Mathlib. The central object is the asymptotic spectrum of a semiring equipped with a Strassen preorder: a compact space of monotone semiring homomorphisms to ℝ that characterizes the asymptotic preorder via a duality theorem.

## Top-level files

### `AsymptoticSpectra.lean`
Root import file. Re-exports all modules; serves as the single entry point for the library.

### `AsymptoticSpectra/Structures.lean`
- Defines `SemiringPreorder`: a preorder on a commutative semiring compatible with addition and multiplication.
- Defines `StrassenPreorder`: extends `SemiringPreorder` with archimedean bounds and a natural-number order embedding.
- Proves basic consequences: `CharZero`, `NoZeroDivisors`, totality, extensionality.
- Provides `activate` to locally install a `StrassenPreorder` as typeclass instances.

### `AsymptoticSpectra/Submultiplicative.lean`
- Defines `IsSubmultiplicative` for sequences `ℕ → ℝ`.
- States and proves **Fekete's Lemma**: a submultiplicative sequence bounded below by 1 converges to its infimum under normalization.

### `AsymptoticSpectra/AsymptoticClosure.lean`
- Defines `AsymptoticLe P a b`: `a` asymptotically precedes `b` (there exist subexponential multipliers making `a^n ≤ c_n · b^n`).
- Defines `StrassenPreorder.asymptoticClosure P` and proves it is itself a `StrassenPreorder`.
- Develops the theory of **closed** Strassen preorders: multiplicative/additive cancellation, gap property, one-step and total extension lemmas.
- Proves the characterization: a closed preorder equals the intersection of all total closed preorders extending it (Zorn argument).

### `AsymptoticSpectra/Rank.lean`
- Defines integer `rank` and `subrank` of an element in a Strassen preorder.
- Proves sub/super-additivity and sub/super-multiplicativity of rank and subrank.
- Defines **fractional rank** `rho` and **fractional subrank** `kappa` as real-valued limits via submultiplicativity.
- Shows `rho` is additive and multiplicative for total preorders, and constructs `rho_toRingHom`.

### `AsymptoticSpectra/Spectrum.lean`
- Defines `AsymptoticSpectrumPoint`: a monotone semiring homomorphism `R →+* ℝ` that is non-decreasing on `P`.
- Defines `AsymptoticSpectrum P` and proves it is **compact** (embeds into a product of closed intervals).
- Establishes bijection between spectrum points and maximal extensions of `P`.
- Shows evaluation maps are continuous.

### `AsymptoticSpectra/Duality.lean`
- Proves the **Duality Theorem** (two parts):
  1. `asymptotic_rank a = max { ϕ(a) | ϕ ∈ AsymptoticSpectrum P }`.
  2. `a ≤_asymp b ↔ ∀ ϕ ∈ AsymptoticSpectrum P, ϕ(a) ≤ ϕ(b)`.

## Subdirectory `AsymptoticSpectra/Tensor/`

See [`AsymptoticSpectra/Tensor/CLAUDE.md`](AsymptoticSpectra/Tensor/CLAUDE.md).

---

## Maintenance instructions

When you add or significantly modify a `.lean` file in this directory:
1. Update the relevant entry in this file (or add a new entry if it is a new file).
2. Keep each file's description to **at most 5 bullet points**.
3. Focus on mathematical content: what structures are defined, what key theorems are proved.
4. Do not describe proof techniques or implementation details unless they are mathematically significant.
5. If a subdirectory is added, create a `CLAUDE.md` inside it and add a pointer here.
