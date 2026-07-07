# Hypothesis Frontier

Date: 2026-07-07

## Main Branch Status

- Lean `sorry`: 0 intended.
- Project-local `axiom`: 0 intended.
- Hard analytic inputs: carried only as explicit fields of structures in `Lean2dYangMills/Interfaces.lean`.

## Closed facts on `main` through PR #42

Current audited base commit: PR #42 at `main` commit `6e1fef6`.

PR #29 was a digest/status refresh after PR #28; it did not add or rename Lean
theorems.

PR #34 was a digest/status refresh after PR #33; it did not add or rename Lean
theorems.

PR #35 was a digest/status refresh after PR #34; it did not add or rename Lean
theorems.

PR #40 was a digest/status refresh after PR #37; it did not add or rename Lean
theorems.

PR #41 was a digest/status refresh after PR #40; it did not add or rename Lean
theorems.

PR #42 was a digest/status refresh after PR #41; it did not add or rename Lean
theorems.

Witten zeta layer (`WittenZetaSU2.lean`) — milestone M4 convergence closed:

- `su2WittenZetaData`: SU(2) dimensions `1, 2, 3, ...` with terms `(n+1)^(-s)`.
- `summable_su2WittenZetaTerm`: convergence for `1 < Re s`.
- `su2WittenZetaPackage`: `WittenZetaPackage` instantiated with
  `zeta := riemannZeta`, BOTH hypothesis fields discharged — the first fully
  unconditional package instance of this repository.
- `su2_wittenZetaSeries_eq_riemannZeta`: **the Witten zeta function of SU(2)
  IS the Riemann zeta function** on the convergence half-plane.
- `su2ZeroAreaSurfaceModel`, `su2ZeroArea_partition_eq_wittenZetaSeries`,
  `su2ZeroArea_wittenZetaSeries_converges` (PR #26 consumer check for the
  public `wittenZeta_converges` wrapper),
  `su2ZeroArea_surfacePartitionSeries_summable` (consumer check for the
  public `surfacePartitionFunction_summable` wrapper), and
  `su2ZeroArea_partition_eq_riemannZeta`: zero-area genus-g partition
  functions are consumed through the public M4 surface wrapper; the public
  `wittenZeta_converges` wrapper supplies convergence at the genus argument
  `2g-2`; the public surface summability wrapper exposes the same package
  field; and the same series is identified with `zeta(2g-2)` (the partition
  function is DEFINED as the series in this topological-limit model — a
  declared consumer test).

Convergence engine (`ConvergenceEngine.lean`) — the M0 analytic engine:

- `summable_pow_mul_exp_neg`: `(n+1)^k exp(-t n)` summable for `t > 0`.
- `summable_pow_mul_exp_neg_casimir`: the Casimir-decay variant
  `(n+1)^k exp(-t n(n+2)/4)`.
- `summable_su2_dim_sq_exp_neg_casimir`: the `k = 2` specialization
  `((n+1)^2) exp(-t n(n+2)/4)`, useful after a future Weyl bound reduces
  SU(2) heat-kernel terms to dimension-square Casimir decay. This does not
  construct the SU(2) heat kernel or character table.

Consumer test (`TrivialModel.lean`):

- `trivialHeatKernelPackage`: `HeatKernelCharacterPackage` with EVERY field
  a theorem; its semigroup proposition is the honest convolution law,
  stated and proved (`trivialHeatKernelPackage_semigroup`).
- `trivialHeatKernelCharacterSeries_converges`: consumer check that the public
  `heatKernel_character_series_converges` wrapper applies to the trivial
  model's character series.
- `trivialHeatKernelCharacterSeries_eq_one`: consumer check that the public
  `heatKernel_character_series_eq` wrapper reduces the trivial model's
  character series to `1`.
- `trivialHeatKernel_conj_invariant`: consumer check that the public
  `heatKernel_conj_invariant` wrapper applies to the trivial heat kernel.
- `trivialExactAreaLawPackage`: `ExactAreaLawPackage` for a one-loop,
  zero-area model with EVERY field discharged; the public M2 wrapper is
  exercised by `trivialSimpleLoop_areaLaw_exact`.
- `trivialSimpleLoop_stringTension_nonnegative`: consumer check that the
  public `simpleLoop_stringTension_nonnegative` wrapper applies to the
  trivial exact-area-law package.
- `trivialSimpleLoop_area_nonnegative`: consumer check that the explicit
  `ExactAreaLawPackage.area_nonnegative` field is available through the public
  `simpleLoop_area_nonnegative` wrapper for the trivial exact-area-law package.
- `trivialSimpleLoop_wilsonExpectation_zero_area`: consumer check that the
  public `simpleLoop_wilsonExpectation_zero_area` wrapper combines an exact
  area-law package with an explicit zero-area hypothesis to reduce the Wilson
  expectation to `1`.
- `trivialAreaLawValue_zero_area`: consumer check that the public
  `areaLawValue_zero_area` API lemma reduces the trivial model's area-law
  value to `1`.

Area-law API normalization (`Interfaces.lean`):

- `areaLawValue_zero_area`: definitional lemma proving `areaLawValue T C = 1`
  from the explicit hypothesis `T.area C = 0`. It is only public-interface
  glue and does not discharge `ExactAreaLawPackage.*`.
- `simpleLoop_area_nonnegative`: public-interface glue projecting the explicit
  `ExactAreaLawPackage.area_nonnegative` field. It does not discharge an
  `ExactAreaLawPackage` for any nontrivial model.
- `simpleLoop_wilsonExpectation_zero_area`: conditional public-interface glue
  combining an already supplied `ExactAreaLawPackage` with an explicit
  zero-area hypothesis. It does not supply the package or prove a physical
  area law.

## Explicit Hypothesis Packages (unchanged, still open for real models)

- `HeatKernelCharacterPackage.*` for SU(2): summability, tsum equality,
  conjugation invariance, semigroup law.
- `MigdalSelfSimilarityPackage.self_similarity`.
- `ExactAreaLawPackage.*`.
- `ContinuumLimitPackage.convergence`.
- `WittenZetaSurfacePackage` at positive area (the zero-area model above
  does not close the analytic M4).

## Frontier obligations (branch `frontier/M0-su2`, statement-first, sorried)

`Frontier/SU2Character.lean`:

- `su2CharacterChebyshev` (DEFINED today via `Polynomial.Chebyshev.U` at
  half the trace) and `su2CharacterTable` with Casimir `n(n+2)/4`.
- `su2CharacterChebyshev_one` (`U_n(1) = n+1`).
- `abs_su2CharacterChebyshev_le` (Weyl bound; spectral input: SU(2)
  eigenvalues on the unit circle, `|tr g| <= 2`).
- `summable_su2HeatKernelTerm` (route: Weyl bound + the Casimir engine
  already proved on main).
- `exists_su2HeatKernelPackage`.

## Distance To Goal

M4's convergence layer is closed and identifies the Riemann bridge
unconditionally. M0 now has its convergence engine, the dimension-square
Casimir specialization, and its character DEFINITION; what remains for M0 is
the Weyl bound (one spectral fact about SU(2)) plus orthogonality for the
semigroup. M1 (Migdal), M2 (area law), M3 (continuum) remain open as before.

Any branch that introduces `sorry` must be named `frontier/*` and must
update this file with exact theorem names and remaining assumptions.
