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
`def`/`abbrev`/`instance`, "thms" covers `theorem`/`lemma`; the rightmost
column is the average number of source lines per theorem in that file —
a rough proxy for "how hard, on average, the proofs are"):

| File | Lines | Defs | Thms | Lines / Thm |
|---|---:|---:|---:|---:|
| `Structures.lean` | 116 | 4 | 6 | 19.3 |
| `Submultiplicative.lean` | 78 | 2 | 1 | 78.0 |
| `AsymptoticClosure.lean` | 1063 | 8 | 28 | 38.0 |
| `Rank.lean` | 650 | 11 | 44 | 14.8 |
| `Spectrum.lean` | 392 | 19 | 12 | 32.7 |
| `Duality.lean` | 366 | 1 | 8 | 45.8 |
| `Tensor/Tensor.lean` | 1187 | 34 | 50 | 23.7 |
| `Tensor/BaseChange.lean` | 602 | 11 | 30 | 20.1 |
| `Tensor/Flattening.lean` | 2268 | 21 | 47 | 48.3 |
| `Tensor/Restriction.lean` | 584 | 5 | 12 | 48.7 |
| `Tensor/Degeneration.lean` | 1240 | 11 | 53 | 23.4 |
| `Tensor/Permutation.lean` | 285 | 3 | 11 | 25.9 |
| `Tensor/Schonhage.lean` | 654 | 13 | 19 | 34.4 |
| `Tensor/MatrixMult.lean` | 1956 | 18 | 45 | 43.5 |
| **Total** | **~11 400** | **161** | **366** | **31.1** |

### Mathematical-domain breakdown

Each declaration is assigned to **one** of three categories. Source of truth:
[`classification.csv`](classification.csv) (one row per declaration); regenerate
with `bash scripts/classify_decls.sh | python3 scripts/apply_classification.py > classification.csv`
and aggregate with `bash scripts/totals.sh classification.csv`.

The categories are:

- **A — Analysis.** Real limits, `Tendsto`, `liminf`/`limsup`, Fekete-style
  submultiplicativity, convexity, `rpow`, ceilings, the entire asymptotic family
  (`AsymptoticLe`, `asymptoticClosure`, `asymptotic_rank`, `rho`, `kappa`),
  the Duality theorem, the matMulExp duality characterization, Jensen, etc.
- **B — Semiring abstract algebra.** The algebraic core of `SemiringPreorder` /
  `StrassenPreorder` (compatibility axioms, `CharZero`, `NoZeroDivisors`,
  totality), integer `rank`/`subrank` and their algebraic inequalities,
  `AsymptoticSpectrumPoint` as a ring hom, the spectrum-point ↔ maximal-extension
  bijection, Zorn-based total extension construction, `rho_toRingHom`.
- **C — Multilinear algebra / tensors.** Everything tensor-specific:
  `TensorObj`, `TensorIso`, the semiring on `Tensor K d`, base change,
  flattening rank, restriction, degeneration, permutation, Schönhage's
  polynomial-family construction, `MMObj`/`MM` and their algebraic identities.

Counts (line counts measure **declaration spans only**, excluding imports,
top-level docstrings, namespace headers, and other inter-declaration filler):

| Category | # decls | # thms | # defs | Lines | % of decl-LOC | Lines / Thm |
|---|---:|---:|---:|---:|---:|---:|
| A — Analysis | 134 | 103 | 31 | 3 285 | 30.9% | 31.9 |
| B — Semiring algebra | 52 | 31 | 21 | 451 | 4.2% | 14.5 |
| C — Multilinear / tensors | 341 | 232 | 109 | 6 900 | 64.9% | 29.7 |
| **Total** | **527** | **366** | **161** | **10 636** | **100.0%** | **29.1** |

Per-file split, sorted by total declaration-LOC (`A B C` columns are LOC; the
final column is the file's total declaration-LOC divided by its theorem count):

| File | A | B | C | Total | Lines / Thm |
|---|---:|---:|---:|---:|---:|
| [`Tensor/Flattening.lean`](AsymptoticSpectra/Tensor/Flattening.lean) | 0 | 0 | 2 174 | 2 174 | 46.3 |
| [`Tensor/MatrixMult.lean`](AsymptoticSpectra/Tensor/MatrixMult.lean) | 1 254 | 0 | 621 | 1 875 | 41.7 |
| [`Tensor/Degeneration.lean`](AsymptoticSpectra/Tensor/Degeneration.lean) | 0 | 0 | 1 137 | 1 137 | 21.5 |
| [`Tensor/Tensor.lean`](AsymptoticSpectra/Tensor/Tensor.lean) | 0 | 0 | 1 070 | 1 070 | 21.4 |
| [`AsymptoticClosure.lean`](AsymptoticSpectra/AsymptoticClosure.lean) | 1 001 | 0 | 0 | 1 001 | 35.8 |
| [`Tensor/Schonhage.lean`](AsymptoticSpectra/Tensor/Schonhage.lean) | 70 | 0 | 532 | 602 | 31.7 |
| [`Rank.lean`](AsymptoticSpectra/Rank.lean) | 389 | 186 | 0 | 575 | 13.1 |
| [`Tensor/BaseChange.lean`](AsymptoticSpectra/Tensor/BaseChange.lean) | 0 | 0 | 567 | 567 | 18.9 |
| [`Tensor/Restriction.lean`](AsymptoticSpectra/Tensor/Restriction.lean) | 0 | 0 | 551 | 551 | 45.9 |
| [`Duality.lean`](AsymptoticSpectra/Duality.lean) | 344 | 0 | 0 | 344 | 43.0 |
| [`Spectrum.lean`](AsymptoticSpectra/Spectrum.lean) | 159 | 179 | 0 | 338 | 28.2 |
| [`Tensor/Permutation.lean`](AsymptoticSpectra/Tensor/Permutation.lean) | 0 | 0 | 248 | 248 | 22.5 |
| [`Structures.lean`](AsymptoticSpectra/Structures.lean) | 0 | 86 | 0 | 86 | 14.3 |
| [`Submultiplicative.lean`](AsymptoticSpectra/Submultiplicative.lean) | 68 | 0 | 0 | 68 | 68.0 |

The roughly 65/30/5 split reflects the project's flavor: more than half of the
work is tensor multilinear algebra (`Tensor/*`); about a third is real-valued
analysis (the asymptotic-rank machinery, the duality theorem, and the
matrix-multiplication exponent); and a small but load-bearing core (`451`
lines) is pure abstract-algebraic preorder theory. Every theorem in
[`Duality.lean`](AsymptoticSpectra/Duality.lean) is classified as analysis
because the duality proof itself goes through real limits and `rpow` even
though its statement is structural.

## Building

Compile the project:

```bash
lake build
```

Build documentation (requires `doc-gen4`):

```bash
lake build AsymptoticSpectra:docs
```

## Dependency graphs ([lean-graph](https://github.com/patrik-cihal/lean-graph))

The repo ships a preconfigured
[`DependencyExtractor.lean`](DependencyExtractor.lean) that imports
`AsymptoticSpectra` and exposes the main theorems as graph roots. To render
the dependency graph of any theorem:

1. Ensure the project is built: `lake build`.
2. Open [`DependencyExtractor.lean`](DependencyExtractor.lean) and **uncomment**
   one of the `#eval` lines at the bottom (templates are provided for
   `asymptotic_rank_eq_max_spectrum`, `matMulExp_lt`, `schonhage_direct_sum`,
   etc.).
3. Run the extractor to emit a JSON file:
   ```bash
   lake env lean DependencyExtractor.lean
   ```
4. Drag the resulting `<theorem-name>.json` into the hosted viewer at
   [patrik-cihal.github.io/lean-graph](https://patrik-cihal.github.io/lean-graph/),
   or install and run the CLI locally:
   ```bash
   cargo install --git https://github.com/patrik-cihal/lean-graph
   lean-graph
   ```

The `*.json` outputs at the project root are git-ignored.
