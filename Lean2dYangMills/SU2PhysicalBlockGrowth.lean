import Lean2dYangMills.SU2PhysicalBlockMigdal

/-!
# One certified growth step of the global physical elimination

The construction-ordered dual tree adjoins one new face at a time.  Assuming
the parent face already belongs to the aggregate block and the selected edge
has not been eliminated, completeness supplies the parent dart automatically.
The reverse dart belongs to the new singleton face.  This module packages the
resulting splice and proves preservation of the full block/Migdal invariant.
-/

noncomputable section

namespace Lean2dYangMills

open MeasureTheory

namespace SU2EdgeConnectedDiskCellulation.CyclicFaceMerge

variable {P : SU2EdgeConnectedDiskCellulation}
  {parent child : P.connected.cellulation.Face}
  (M : SU2EdgeConnectedDiskCellulation.CyclicFaceMerge P parent child)
  {eliminated : Set P.connected.cellulation.Edge}

/-- Completeness of an aggregate block exposes the physical dart connecting
its parent face to the new child face. -/
theorem dart_mem_block
    (B : P.PhysicalWordBlock eliminated)
    (hparent : parent ∈ B.faces) (hlive : M.selectedEdge ∉ eliminated) :
    M.dart ∈ B.word := by
  apply B.complete M.dart
  · exact ⟨parent, hparent, P.mem_faceDartWord_of_face parent M.dart M.dart_face⟩
  · exact hlive

/-- The reverse selected dart occurs in the singleton word of the newly
attached child face. -/
theorem reverse_mem_singleton :
    P.connected.cellulation.reverse M.dart ∈
      (SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singletonAt eliminated child).word := by
  exact P.mem_faceDartWord_of_face child
    (P.connected.cellulation.reverse M.dart) M.reverse_face

/-- Extend an aggregate block by its next construction-ordered leaf. -/
def grow
    (B : P.PhysicalWordBlock eliminated)
    (hparent : parent ∈ B.faces) (hlive : M.selectedEdge ∉ eliminated) :
    P.PhysicalWordBlock (insert M.selectedEdge eliminated) :=
  SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.merge B
    (SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singletonAt eliminated child)
    (M.dart_mem_block B hparent hlive) M.reverse_mem_singleton

@[simp] theorem grow_faces
    (B : P.PhysicalWordBlock eliminated)
    (hparent : parent ∈ B.faces) (hlive : M.selectedEdge ∉ eliminated) :
    (M.grow B hparent hlive).faces = insert child B.faces := by
  change B.faces ∪ {child} = insert child B.faces
  ext f
  simp

/-- The new face is disjoint from the aggregate block precisely when it has
not appeared at an earlier construction stage. -/
theorem faces_disjoint_singleton
    (B : P.PhysicalWordBlock eliminated) (hchild : child ∉ B.faces) :
    Disjoint B.faces
      (SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singletonAt eliminated child).faces := by
  simpa [SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singletonAt] using
    (Finset.disjoint_singleton_right.mpr hchild)

/-- Duplicate-freeness is preserved by a certified leaf-attachment step. -/
theorem grow_nodup
    (B : P.PhysicalWordBlock eliminated)
    (hparent : parent ∈ B.faces) (hlive : M.selectedEdge ∉ eliminated)
    (hchild : child ∉ B.faces) (hnodup : B.word.Nodup) :
    (M.grow B hparent hlive).word.Nodup := by
  exact SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.nodup_merge B
    (SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singletonAt eliminated child)
    (M.dart_mem_block B hparent hlive) M.reverse_mem_singleton
    (faces_disjoint_singleton B hchild) hnodup
    (P.faceDartWord_nodup child)

/-- A growth step adds exactly the area of its new child face. -/
theorem grow_area
    (B : P.PhysicalWordBlock eliminated)
    (hparent : parent ∈ B.faces) (hlive : M.selectedEdge ∉ eliminated)
    (hchild : child ∉ B.faces) :
    (M.grow B hparent hlive).area =
      B.area + P.connected.cellulation.faceArea child := by
  unfold grow
  rw [SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.area_merge_of_disjoint
    B (SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singletonAt eliminated child)
    (M.dart_mem_block B hparent hlive) M.reverse_mem_singleton
    (faces_disjoint_singleton B hchild)]
  simp [SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.area,
    SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singletonAt]

/-- **One complete global-induction step.**  Integrating the selected physical
coordinate attaches the new face to the aggregate heat-kernel block. -/
theorem integrate_grow
    (B : P.PhysicalWordBlock eliminated)
    (hparent : parent ∈ B.faces) (hlive : M.selectedEdge ∉ eliminated)
    (hchild : child ∉ B.faces) (harea : 0 < B.area)
    (hnodup : B.word.Nodup)
    (r : {e : P.connected.cellulation.Edge // e ≠ M.selectedEdge} -> SU2) :
    (∫ x : SU2,
      su2HeatKernel B.area
          (P.connected.cellulation.evalDartWord
            (P.connected.cellulation.edgeInsert M.selectedEdge r x) B.word) *
        su2HeatKernel (P.connected.cellulation.faceArea child)
          (P.connected.cellulation.evalDartWord
            (P.connected.cellulation.edgeInsert M.selectedEdge r x)
    (SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singletonAt eliminated child).word)
      ∂su2HaarProb) =
      su2HeatKernel (M.grow B hparent hlive).area
        (P.connected.cellulation.evalDartWord
          (P.connected.cellulation.edgeInsert M.selectedEdge r 1)
          (M.grow B hparent hlive).word) := by
  have h := SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.integrate_merge_of_nodup B
    (SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singletonAt eliminated child)
    (M.dart_mem_block B hparent hlive) M.reverse_mem_singleton
    (faces_disjoint_singleton B hchild) harea
    (by
      simp [SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.area,
        SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singletonAt,
        P.connected.cellulation.faceArea_pos child])
    hnodup (P.faceDartWord_nodup child) r
  simpa [grow, SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.area,
    SU2EdgeConnectedDiskCellulation.PhysicalWordBlock.singletonAt] using h

end SU2EdgeConnectedDiskCellulation.CyclicFaceMerge

end Lean2dYangMills
