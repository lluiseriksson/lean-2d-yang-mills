# Release provenance

The authoritative Lean snapshot audited by the manuscript is

`52e0e6f54e40a891c9dc092f730daba26f100bcd`.

At that snapshot:

- `Lean2dYangMills.lean` imports the global edge model and the audit module;
- `Lean2dYangMills/AuditMigdalClosure.lean` contains 52 `#print axioms`
  commands;
- the project contains no `sorry`, `admit`, or project-local `axiom`;
- the global edge endpoint is
  `SU2EdgeConnectedDiskCellulation.unreducedEdgeIntegral_eq_chordGaugeFixedIntegral`.

The release archive carries a Git bundle in addition to an exported source
tree.  The bundle makes the named commit object independently inspectable even
when the archive is opened away from GitHub.  Verify it with:

```text
git bundle verify lean-2d-yang-mills.bundle
git clone lean-2d-yang-mills.bundle verified-repository
git -C verified-repository checkout 52e0e6f54e40a891c9dc092f730daba26f100bcd
```

The manuscript distinguishes the fully boundary-integrated original-edge
scalar from the boundary-dependent schedule amplitude.  The remaining
pointwise bridge must first define a boundary-conditioned edge integral; no
equality between those differently typed objects is claimed in this release.
