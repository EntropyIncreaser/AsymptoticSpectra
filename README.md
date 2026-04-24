# Prism

This is a (toy) project to formalize the theory of asymptotic spectra, a theory developed by Volker Strassen. This framework of this project is based on the survey [Asymptotic Spectra: Theory, Applications and Extensions](https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf) by Avi Wigderson and Jeroen Zuiddam.

## Project structure

The library lives under `AsymptoticSpectra/`. Top-level files develop the abstract
theory over an arbitrary commutative semiring equipped with a `StrassenPreorder`;
the subdirectory `AsymptoticSpectra/Tensor/` specializes the theory to the
semiring of order-`d` tensors over a field and derives quantitative consequences
for matrix multiplication.

### Abstract theory (top level)

- [`Structures.lean`](AsymptoticSpectra/Structures.lean) — `SemiringPreorder`
  and `StrassenPreorder`: preorders on a commutative semiring with
  archimedean bounds and a natural-number order embedding.
- [`Submultiplicative.lean`](AsymptoticSpectra/Submultiplicative.lean) —
  **Fekete's lemma** for submultiplicative sequences.
- [`AsymptoticClosure.lean`](AsymptoticSpectra/AsymptoticClosure.lean) —
  `AsymptoticLe`, the asymptotic closure of a Strassen preorder, and the
  characterization of closed preorders as intersections of maximal total closed
  extensions (Zorn).
- [`Rank.lean`](AsymptoticSpectra/Rank.lean) — integer `rank`/`subrank`,
  fractional rank `rho` and subrank `kappa`, and the asymptotic rank
  `asymptotic_rank`.
- [`Spectrum.lean`](AsymptoticSpectra/Spectrum.lean) — the
  `AsymptoticSpectrum`: monotone ring homomorphisms `R →+* ℝ`; compactness and
  the bijection with maximal extensions.
- **[`Duality.lean`](AsymptoticSpectra/Duality.lean) — the Duality Theorem.**
  - `asymptotic_rank_eq_max_spectrum`: `asymptotic_rank a = ⨆_ϕ ϕ(a)`.
  - `asymptotic_le_iff_spectrum_le`: `a ≤_asymp b ↔ ∀ϕ, ϕ(a) ≤ ϕ(b)`.

### Tensor semiring (`AsymptoticSpectra/Tensor/`)

See [`AsymptoticSpectra/Tensor/CLAUDE.md`](AsymptoticSpectra/Tensor/CLAUDE.md)
for the full file-by-file overview.

- [`Tensor.lean`](AsymptoticSpectra/Tensor/Tensor.lean),
  [`BaseChange.lean`](AsymptoticSpectra/Tensor/BaseChange.lean) — the
  commutative semiring `Tensor K d` of isomorphism classes of order-`d`
  tensors, with direct sum and tensor contraction.
- [`Flattening.lean`](AsymptoticSpectra/Tensor/Flattening.lean) —
  flattening rank; a first family of spectrum points.
- **[`Restriction.lean`](AsymptoticSpectra/Tensor/Restriction.lean) — the
  Strassen preorder on tensors.** Constructs the `StrassenPreorder` instance
  on `Tensor K d` via tensor restriction.
- [`Degeneration.lean`](AsymptoticSpectra/Tensor/Degeneration.lean) — border
  rank / degeneration; `asymptoticClosure_degenerates_eq`.
- [`Permutation.lean`](AsymptoticSpectra/Tensor/Permutation.lean) — mode
  permutations acting on `Tensor K d` and on spectrum points.
- [`Schonhage.lean`](AsymptoticSpectra/Tensor/Schonhage.lean),
  **[`MatrixMult.lean`](AsymptoticSpectra/Tensor/MatrixMult.lean) — bounds on
  the matrix multiplication exponent ω.**
  - `schonhage_direct_sum`: Schönhage's direct sum construction,
    `MM(n,1,m) ⊕ MM(1,(n-1)(m-1),1)` has border rank `≤ nm+1`.
  - `asymptotic_sum_inequality`: the key consequence of duality, bounding
    `∑ᵢ (nᵢmᵢpᵢ)^{ω/3}` by the asymptotic rank of a direct sum.
  - `matMulExp_lt`: **ω < 51/20 = 2.55**, derived by plugging `n = m = 4`
    into Schönhage's construction.
  - `matMulExp_eq_sup_specMM`: the duality characterization
    `ω = ⨆_ϕ (θ₁+θ₂+θ₃)(ϕ)` over spectrum points.

The project is `sorry`-free.

## Statistics

Approximate counts (lines include blank lines and comments; "defs" covers
`def`/`abbrev`/`instance`, "thms" covers `theorem`/`lemma`):

| File | Lines | Defs | Thms |
|---|---:|---:|---:|
| `Structures.lean` | 116 | 4 | 6 |
| `Submultiplicative.lean` | 78 | 2 | 1 |
| `AsymptoticClosure.lean` | 1063 | 8 | 28 |
| `Rank.lean` | 650 | 11 | 44 |
| `Spectrum.lean` | 392 | 19 | 12 |
| `Duality.lean` | 366 | 1 | 8 |
| `Tensor/Tensor.lean` | 1187 | 34 | 50 |
| `Tensor/BaseChange.lean` | 602 | 11 | 30 |
| `Tensor/Flattening.lean` | 2268 | 21 | 47 |
| `Tensor/Restriction.lean` | 584 | 5 | 12 |
| `Tensor/Degeneration.lean` | 1240 | 11 | 53 |
| `Tensor/Permutation.lean` | 285 | 3 | 11 |
| `Tensor/Schonhage.lean` | 654 | 13 | 19 |
| `Tensor/MatrixMult.lean` | 1956 | 18 | 45 |
| **Total** | **~11 400** | **161** | **366** |

## Building

Compile the project:

```bash
lake build
```

Build documentation (requires `doc-gen4`):

```bash
lake build AsymptoticSpectra:docs
```
