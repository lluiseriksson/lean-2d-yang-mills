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

The product-Haar bridge is now uniform for the full original edge space.  For
every primal-connected finite disk cellulation, a construction-ordered rooted
spanning tree selects exactly `V-1` distinct physical edges.  The formalization
constructs the literal measurable equivalence

`SU2^Edge ≃ SU2^(V-{root}) × SU2^(Edge-Tree)`

(with the non-root vertices represented by their construction indices), proves
that it preserves normalized product Haar, reconstructs the rooted vertex
potentials, and proves that the transformed configuration sets every tree edge
to `1` while retaining precisely the gauge-fixed chord coordinates.

`SU2EdgeConnectedDiskCellulation` records the additional physical
well-formedness that every bounded face has one finite, once-around boundary
enumeration.  For this object, all facial holonomies are defined simultaneously
on the original edge variables and are proved to transform by conjugation at
their respective boundary basepoints.  Consequently the complete heat-kernel
density factors through the chord coordinates, and
`unreducedEdgeIntegral_eq_chordGaugeFixedIntegral` proves equality of the full
`SU2^Edge` Haar integral with the gauge-fixed chord integral, with no residual
gauge-volume factor.

This closes the edge-model/gauge-reduction gap.  The development still does not
identify the fully boundary-integrated chord scalar with the
boundary-dependent schedule amplitude.  Those objects cannot be equated as
currently typed: the first integrates every exterior edge, whereas the second
retains an exterior holonomy.  The correct remaining statement requires a
boundary-conditioned original-edge integral and a pointwise proof that it is
the schedule amplitude.  The development also does not identify abstract
combinatorial disks with isotopy classes of piecewise-smooth planar embeddings,
treat nonsimple/intersecting Wilson loops, or construct a continuum measure.
