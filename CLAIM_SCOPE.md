# Claim Scope: Two Distinct Wilson-Loop Area Laws

This file is authoritative for the novelty and priority boundary of the
`lean-2d-yang-mills` manuscript.

| Work | Regime | Mechanism | Result |
| --- | --- | --- | --- |
| Previous area-law paper | Strong coupling, `SU(N_c)`, finite lattices | Cluster expansion, Kotecky--Preiss convergence, Penrose/rooted-tree bounds | Volume-uniform inequality `|<W_C>| <= prefactor * exp(-tau A(C))` with positive tension in an explicit window |
| Current candidate | Exactly soluble two-dimensional `SU(2)` Yang--Mills | Weyl integration, heat-kernel character convolution, edge integration, Migdal subdivision | Exact identity `E[W_j(C)] = exp(-C_2(j) Area(C))` for simple planar loops |

The distinction is substantive:

- perturbative strong-coupling inequality versus exact identity;
- an explicit strong-coupling window versus the admissible area-time domain of
  the exact two-dimensional heat kernel;
- cluster control versus convolution and subdivision consistency.

The previous theorem is prior work and must be cited.  The archived
`lean-rooted-tree-polymer-expansion` repository is a reusable artifact for the
rooted-tree/polymer combinatorics of that cluster-expansion result.  It does not
supply model-specific Yang--Mills activity estimates, a continuum construction,
or a conceptual dependency of the heat-kernel/Migdal mechanism.

## Intended title

**Exact Two-Dimensional SU(2) Yang--Mills in Lean: Weyl Integration,
Heat-Kernel Convolution, Migdal Invariance, and the Exact Simple-Loop Area Law**

## Novelty wording

The manuscript may state the end-to-end priority claim only after a final,
systematic literature and formalization-repository review. It must never claim
to be the first machine-checked Wilson-loop area law simpliciter.

## Architectural rule

The previous strong-coupling theorem does not instantiate
`ExactAreaLawPackage`. A nontrivial instance must be built internally from the
concrete two-dimensional heat-kernel convolution law, lattice edge integration,
Migdal subdivision invariance, and the resulting simple-loop expectation.
