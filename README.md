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

## Publication claim boundary

The Eriksson programme already contains a distinct machine-checked Wilson-loop
area-law theorem: a volume-uniform strong-coupling bound for finite-lattice
`SU(N_c)` gauge theory, proved with a formalized cluster expansion and a
Kotecky--Preiss criterion.  That theorem establishes an exponentially decaying
*inequality* in an explicit strong-coupling window.  It does not establish the
exact two-dimensional heat-kernel identity pursued here.

The nontrivial target of this repository is instead the exact `SU(2)` chain

```text
Haar/canonical measure = Weyl integration -> character convolution
  -> Migdal subdivision invariance -> exact simple-loop identity.
```

Accordingly, the earlier strong-coupling theorem must not be used to instantiate
`ExactAreaLawPackage`: the regimes, hypotheses, mechanisms, and conclusions do
not match.  A nontrivial instance must be derived internally from the concrete
two-dimensional heat-kernel and Migdal construction.  See `CLAIM_SCOPE.md` and
`paper/claim-boundary.tex` for the comparison and manuscript-ready wording.

## Build

The toolchain and Mathlib commit are copied from the parent repository:

- Lean toolchain: `leanprover/lean4:v4.29.0-rc6`
- Mathlib commit: `07642720480157414db592fa85b626dafb71355b`

```bash
lake build
```

## Discipline

`main` is intended to stay free of `sorry` and project-local axioms. Frontier work may live on `frontier/*` branches, with every open statement mirrored in `HYPOTHESIS_FRONTIER.md`.

The generic public interfaces remain available, but the concrete `SU(2)` chain
is no longer conditional.  The development proves the Haar/spherical measure
bridge, the all-order orbital law, translated character convolution, the
infinite heat-kernel semigroup, a two-face Migdal edge integration, and the
exact all-label simple-loop coefficient without projecting those conclusions
from a hypothesis package.

`SU2FiniteCellulation.lean` now separates the geometric input from the binary
evaluator.  Its finite oriented disk object stores vertices, edges, paired
half-edges, source/target incidence, cyclic face successors, the disk Euler
relation, and positive bounded-face areas.  The dual graph is derived from
these incidences.  Every connected dual graph admits a valid elimination
schedule; every valid schedule reduces to the heat kernel at total area; and
any two schedules give exactly the same reduced amplitude.  A public
`SU2ConnectedDiskCellulation` contains no schedule choice and supplies a
nontrivial `ExactAreaLawPackage`, the exact Casimir law, and normalization.

No acyclicity condition is imposed on the dual graph.  For cyclic duals, the
development now also closes the first genuine unreduced example: a three-face
disk with a three-cycle dual and three original spoke-edge variables.  An
explicit triangular measurable equivalence preserves triple product Haar,
removes the interior gauge coordinate, and proves that the unreduced integral
is exactly the reduced two-coordinate amplitude and hence the heat kernel at
summed area.

`SU2FiniteGaugeFixing.lean` makes the local measure-theoretic part uniform in the
valence.  For every finite type `I`, simultaneous left gauge action on
`SU2 × (I -> SU2)` and the triangular map
`(x,y) |-> (x, fun i => x^-1 * y i)` preserve the literal normalized product
Haar measure.  Any diagonally gauge-invariant density can therefore be
integrated by setting the anchor coordinate to the identity.

`SU2RootedTreeGaugeFixing.lean` now closes the global vertex-coordinate layer.
Every finite connected simple graph admits a construction-ordered rooted
spanning tree.  For a disk cellulation with connected primal graph, the chosen
tree is certified by actual half-edge incidences, and one measurable
equivalence replaces all vertex variables by the root variable and the ordered
parent--child increments.  The map and its inverse are explicit, its coordinate
formulas are theorems, and it preserves the literal `Measure.pi` product Haar
probability.

`SU2GlobalEdgeGaugeFixing.lean` closes the stronger edge-model layer.  It
selects `V-1` distinct physical tree edges, partitions every original edge
configuration into oriented tree increments and complementary chords, and
constructs the explicit measurable equivalence
`SU(2)^E ≃ SU(2)^{V\setminus\{r\}} × SU(2)^{E\setminus T}`.  The equivalence
preserves literal normalized product Haar.  Reconstructed vertex potentials
set all tree edges to the identity, every facial holonomy transforms by its
basepoint conjugation, the full heat-kernel density loses every tree/gauge
coordinate, and the unreduced edge integral equals the chord integral exactly.
This integral includes the exterior edge variables and is a scalar; it is not
the boundary-dependent schedule amplitude.  The next physical bridge is a
boundary-conditioned original-edge integral, followed by comparison with
embedded planar isotopy classes and continuum constructions.  Release and
commit authentication details are recorded in `RELEASE_PROVENANCE.md`.

## Public Interface

The parent repo should import only the contract module:

```lean
import Interfaces
```

The stable signatures are listed in `INTERFACES.md`, re-exported by `Interfaces.lean`, and implemented in `Lean2dYangMills/Interfaces.lean`.
