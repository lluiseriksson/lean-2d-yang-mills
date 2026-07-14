# Release provenance

The authoritative mathematical snapshot audited by the manuscript is

`a1fbea97cbe673d383dbb4bc5e2a2fb70dbf190a`.

At that snapshot:

- `Lean2dYangMills.lean` imports the universal tree--cotree closure, the
  conditioned original-edge model, and the audit module;
- `Lean2dYangMills/AuditMigdalClosure.lean` contains 167 `#print axioms`
  commands;
- the project contains no `sorry`, `admit`, or project-local `axiom`;
- the audited endpoints depend only on `propext`, `Classical.choice`, and
  `Quot.sound`;
- the universal existence endpoint is
  `SU2BoundaryDiskCellulation.nonempty_physicalBoundaryEliminationChart`;
- the terminal conditioned-edge endpoint is
  `SU2BoundaryDiskCellulation.conditionedEdgeModelAmplitude_eq_heatKernel`.

The resulting formal chain is unconditional on auxiliary chart data for every
certified finite physical disk cellulation:

```text
conditioned original-edge integral
  = gauge-fixed chord integral
  = physical elimination amplitude
  = heat kernel at total face area and retained exterior holonomy.
```

The release archive carries a complete Git bundle in addition to the exported
source tree. The bundle makes both the mathematical checkpoint and the
editorial release independently inspectable away from GitHub. Verify it with:

```text
git bundle verify repository.bundle
git clone repository.bundle verified-repository
git -C verified-repository checkout agent/su2-boundary-conditioned-bridge
```

The exported manuscript and PDFs belong to the editorial commit at the bundle's
`HEAD`; the mathematical proof snapshot cited in the manuscript is its parent
checkpoint named above. The remaining frontier is geometric and topological:
comparison with planar isotopy classes, nonsimple or intersecting Wilson loops,
higher-topology surfaces, and continuum constructions. No conditioned
edge-model obligation is left unresolved.
