# Hypothesis Frontier

Date: 2026-07-03

## Main Branch Status

- Lean `sorry`: 0 intended.
- Project-local `axiom`: 0 intended.
- Hard analytic inputs: carried only as explicit fields of structures in `Lean2dYangMills/Interfaces.lean`.

## Explicit Hypothesis Packages

The following fields are not proofs supplied by this repository. They are honest interfaces for future proofs or imported results:

- `HeatKernelCharacterPackage.heatKernel_summable`: convergence of the compact-group heat-kernel character expansion.
- `HeatKernelCharacterPackage.heatKernel_eq_tsum`: equality between the supplied heat kernel and the character series.
- `HeatKernelCharacterPackage.heatKernel_conj_invariant`: conjugation invariance of the supplied heat kernel.
- `HeatKernelCharacterPackage.heatKernel_semigroup`: heat-kernel convolution semigroup law, recorded as an explicit proposition.
- `MigdalSelfSimilarityPackage.self_similarity`: invariance of finite-lattice expectations under plaquette subdivision.
- `ExactAreaLawPackage.wilson_eq_areaLaw`: exact simple-loop Wilson expectation area law with an explicit string tension.
- `ExactAreaLawPackage.area_nonnegative`: nonnegativity of the loop area input.
- `ExactAreaLawPackage.stringTension_nonnegative`: nonnegativity of the supplied string tension.
- `ContinuumLimitPackage.convergence`: lattice-to-continuum convergence statement.
- `WittenZetaPackage.zeta_summable`: convergence of the Witten zeta series in the supplied half-plane.
- `WittenZetaPackage.zeta_eq_tsum`: equality between the supplied zeta function and the representation-dimension series.
- `WittenZetaSurfacePackage.partition_summable`: convergence of the surface partition series.
- `WittenZetaSurfacePackage.partition_eq_zeta`: appearance of the Witten zeta series in surface partition functions.

## Distance To Goal

This repo currently provides a stable, compilable contract. It does not yet close M0-M4 mathematically.

- M0 needs the shared Peter-Weyl/character/Haar layer, including concrete `SU(2)` irreps and Casimir eigenvalues.
- M1 needs a finite lattice heat-kernel convolution formalization and Migdal subdivision proof.
- M2 needs a formal Wilson-loop expectation computation for simple planar loops.
- M3 needs statements-first continuum limit formalization following Driver/Levy/Sengupta.
- M4 needs Witten-zeta convergence and the representation-sum partition-function theorem.

Any branch that introduces `sorry` must be named `frontier/*` and must update this file with exact theorem names and remaining assumptions.
