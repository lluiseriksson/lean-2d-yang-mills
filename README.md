# lean-2d-yang-mills

Lean 4 + Mathlib satellite for the THE-ERIKSSON-PROGRAMME 2D Yang-Mills sandbox.

This repository is about the exactly soluble two-dimensional model: heat-kernel lattice Yang-Mills, Migdal subdivision self-similarity, exact Wilson loop area law for simple planar loops, continuum-limit statements, and the Witten zeta/partition-function bridge.

What this is:

- A small, buildable interface layer for 2D Yang-Mills statements.
- A place to make every hard analytic input explicit as a hypothesis.
- A benchmark for the parent repository's lattice-to-continuum and area-law pipeline.

What this is not:

- It is not a proof of the four-dimensional Yang-Mills mass gap.
- It is not a construction of continuum 4D Yang-Mills.
- It is not a replacement for the Balaban/Kotecky-Preiss frontier in the parent repo.
- It does not claim Peter-Weyl, compact Lie heat-kernel convergence, or Levy/Sengupta continuum limits unless those inputs are supplied explicitly.

## Build

The toolchain and Mathlib commit are copied from the parent repository:

- Lean toolchain: `leanprover/lean4:v4.29.0-rc6`
- Mathlib commit: `07642720480157414db592fa85b626dafb71355b`

```bash
lake build
```

## Discipline

`main` is intended to stay free of `sorry` and project-local axioms. Frontier work may live on `frontier/*` branches, with every open statement mirrored in `HYPOTHESIS_FRONTIER.md`.

The current `main` interface is conditional: theorem statements project explicit fields from structures such as `HeatKernelCharacterPackage`, `MigdalSelfSimilarityPackage`, and `ExactAreaLawPackage`. This keeps the import surface stable without pretending the analytic theorems are already formalized.

The concrete SU(2) character layer is no longer conditional: `main` proves
the Chebyshev character formula at the identity, the sharp Weyl bound
`|chi_n(g)| <= n+1`, class-function invariance, and pointwise convergence of
the heat-kernel character series for every positive heat time. The same
Casimir majorant now proves uniform convergence on all of SU(2) and continuity
of the resulting series. It also proves
the exact Chebyshev-U orthogonality integral with the SU(2) Weyl angle weight.
Identifying that angle measure with the class pushforward of Mathlib's SU(2)
Haar measure, and then proving the full convolution law, remain the live M0
frontier.

The repository now constructs that normalized Haar probability measure
internally (including compactness and topological-group instances) and proves
that every odd Chebyshev character has zero Haar mean. Explicit translation
symmetries also give `E|g₀₀|²=1/2`, `E(Re g₀₀)²=1/4`, `∫χ₁²=1`, and the first
even selector `∫χ₂=0`. The full Weyl pushforward formula and all-order even
sector remain open.

## Public Interface

The parent repo should import only the contract module:

```lean
import Interfaces
```

The stable signatures are listed in `INTERFACES.md`, re-exported by `Interfaces.lean`, and implemented in `Lean2dYangMills/Interfaces.lean`.
