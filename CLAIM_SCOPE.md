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

## Current finite-cellulation endpoint

The current formal object is an oriented finite combinatorial disk
cellulation: it stores finite vertices, edges, paired half-edges, source and
target incidence, cyclic face successors, one exterior face, the disk Euler
relation, and positive bounded-face areas. Its dual graph is derived from the
half-edge incidences.

For every such cellulation with connected dual graph, the development proves:

- existence of a labelled binary gauge-fixing/elimination schedule;
- validity of each merge against an actual dual edge;
- exact reduction of every valid schedule to the heat kernel at total area;
- independence of the chosen valid schedule;
- a schedule-free `ExactAreaLawPackage` and the exact simple-loop Casimir law.

No acyclicity hypothesis is imposed on the dual graph. This closes finite
choice-independent reduction of the explicitly defined post-gauge-fixed
amplitude, including schedules supported on dual graphs with cycles.

The first nontrivial product-Haar bridge is also closed for the concrete
three-spoke disk whose face dual is the three-cycle.  Starting from three
original edge variables, the formalization proves that
`(x,y,z) |-> (x,x^-1*y,x^-1*z)` preserves triple normalized Haar, that the
density loses the pure-gauge coordinate, and that the unreduced integral is
the heat kernel at total area.  This is not yet a theorem for every finite
cellulation.

The product-Haar gauge step itself is now uniform in arbitrary finite valence:
for every finite type `I`, the diagonal action and the triangular change on
`SU2 × (I -> SU2)` are measure preserving, and every diagonally invariant
density admits exact identity-slice integration.  What is not yet proved is the
composition of these local steps along a spanning tree of an arbitrary
`SU2FiniteDiskCellulation`, together with the induced formula for every face
holonomy.  Nor does the development identify the abstract combinatorial
disks with isotopy classes of piecewise-smooth planar embeddings, treat
nonsimple/intersecting Wilson loops, or construct a continuum measure.
