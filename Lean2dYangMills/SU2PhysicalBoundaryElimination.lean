import Lean2dYangMills.SU2BoundaryConditionedGaugeFixing
import Lean2dYangMills.SU2TreeCotreeConnectivity

/-!
# Compatibility of boundary gauge coordinates with physical elimination

The adaptive boundary chart leaves exactly `F - 1` internal chord variables.
The dual rooted elimination tree selects exactly `F - 1` distinct physical
internal edges.  This module identifies the two finite types once the primal
tree is certified to avoid those selected dual-tree edges.
-/

noncomputable section

namespace Lean2dYangMills

open MeasureTheory

namespace SU2DualRootedEliminationTree

variable {P : SU2BoundaryDiskCellulation}
  (T : SU2DualRootedEliminationTree
    P.toSU2EdgeConnectedDiskCellulation)

/-- A physical edge separating two bounded faces cannot be an edge of the
certified exterior cycle. -/
theorem selectedEdge_ne_exteriorEdge
    (i : Fin T.n) (k : Fin P.exteriorBoundaryLength) :
    T.selectedEdge i ≠
      P.connected.cellulation.edgeOfHalfEdge
        ((P.connected.cellulation.next ^ (k : Nat))
          P.exteriorBoundaryStart) := by
  intro hedge
  let C := P.connected.cellulation
  let M := T.merge i
  let hExt : C.HalfEdge :=
    (C.next ^ (k : Nat)) P.exteriorBoundaryStart
  have hext : C.face hExt = none := by
    dsimp [hExt]
    rw [C.face_next_pow]
    exact P.exteriorBoundaryStart_face
  rcases C.eq_or_eq_reverse_of_edgeOfHalfEdge_eq hedge with hsame | hrev
  · have hf := M.dart_face
    rw [hsame, hext] at hf
    simpa using hf
  · have hr := congrArg C.reverse hrev
    rw [C.reverse_involutive hExt] at hr
    have hf := M.reverse_face
    rw [hr, hext] at hf
    simpa using hf

end SU2DualRootedEliminationTree

/-- A primal adaptive boundary chart and a dual physical elimination tree
are compatible when every physical edge selected for Migdal elimination is a
chord of the primal tree.  Boundary exclusion is automatic and proved above. -/
structure SU2PhysicalBoundaryEliminationChart
    (P : SU2BoundaryDiskCellulation) where
  boundary : P.AdaptiveBoundaryGaugeChart
  elimination : SU2DualRootedEliminationTree
    P.toSU2EdgeConnectedDiskCellulation
  selected_not_tree : ∀ i : Fin elimination.n,
    elimination.selectedEdge i ∉ Set.range boundary.tree.treeEdge

namespace SU2PhysicalBoundaryEliminationChart

variable {P : SU2BoundaryDiskCellulation}
  (D : SU2PhysicalBoundaryEliminationChart P)

abbrev OtherChord := D.boundary.OtherChord

local instance edgeDecidableEq :
    DecidableEq P.connected.cellulation.Edge := Classical.decEq _

local instance chordEdgeDecidableEq :
    DecidableEq D.boundary.ChordEdge := Classical.decEq _

/-- Every dual-tree step is one of the internal chord coordinates retained by
the adaptive boundary chart. -/
def stepChord (i : Fin D.elimination.n) : D.OtherChord := by
  let c : D.boundary.ChordEdge :=
    ⟨D.elimination.selectedEdge i, D.selected_not_tree i⟩
  refine ⟨c, ?_⟩
  intro h
  have hedge : D.elimination.selectedEdge i = D.boundary.anchorEdge :=
    congrArg Subtype.val h
  exact D.elimination.selectedEdge_ne_exteriorEdge i
    D.boundary.anchorIndex (by
      simpa [SU2BoundaryDiskCellulation.AdaptiveBoundaryGaugeChart.anchorEdge,
        SU2BoundaryDiskCellulation.AdaptiveBoundaryGaugeChart.anchorDart]
        using hedge)

theorem stepChord_injective : Function.Injective D.stepChord := by
  intro i j hij
  apply D.elimination.selectedEdge_injective
  exact congrArg (fun e : D.OtherChord => e.1.1) hij

theorem card_step_eq_card_otherChord :
    Fintype.card (Fin D.elimination.n) =
      Fintype.card D.OtherChord := by
  change Fintype.card (Fin D.elimination.n) =
    Fintype.card D.boundary.OtherChord
  calc
    Fintype.card (Fin D.elimination.n) = D.elimination.n :=
      Fintype.card_fin _
    _ = Fintype.card P.connected.cellulation.Face - 1 :=
      D.elimination.card_step
    _ = Fintype.card D.boundary.OtherChord :=
      D.boundary.card_otherChord_eq_card_face_sub_one.symm

theorem stepChord_bijective : Function.Bijective D.stepChord := by
  exact (Fintype.bijective_iff_injective_and_card D.stepChord).mpr
    ⟨D.stepChord_injective, D.card_step_eq_card_otherChord⟩

/-- The physical elimination steps and the internal conditioned chord
variables are literally equivalent finite coordinate types. -/
def stepChordEquiv : Fin D.elimination.n ≃ D.OtherChord :=
  Equiv.ofBijective D.stepChord D.stepChord_bijective

@[simp]
theorem stepChordEquiv_apply (i : Fin D.elimination.n) :
    D.stepChordEquiv i = D.stepChord i := rfl

/-- Reindex the `F - 1` conditioned internal chord coordinates by the
construction order of the physical elimination tree. -/
def internalCoordinateEquiv :
    (D.OtherChord -> SU2) ≃ᵐ (Fin D.elimination.n -> SU2) :=
  su2VertexRelabelEquiv (stepChordEquiv D).symm

theorem internalCoordinateEquiv_measurePreserving :
    MeasurePreserving D.internalCoordinateEquiv
      (su2FiniteProductHaar D.OtherChord)
      (su2FiniteProductHaar (Fin D.elimination.n)) :=
  su2VertexRelabel_measurePreserving (stepChordEquiv D).symm

@[simp]
theorem internalCoordinateEquiv_apply
    (r : D.OtherChord -> SU2) (i : Fin D.elimination.n) :
    D.internalCoordinateEquiv r i = r (D.stepChord i) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (e := (stepChordEquiv D).symm)
    (β := fun _ : Fin D.elimination.n => SU2)
    r (stepChordEquiv D i)
  change (MeasurableEquiv.piCongrLeft
    (fun _ : Fin D.elimination.n => SU2) (stepChordEquiv D).symm) r i =
      r (D.stepChord i)
  rw [← stepChordEquiv_apply D i]
  simpa only [Equiv.symm_apply_apply] using h

end SU2PhysicalBoundaryEliminationChart

namespace SU2BoundaryDiskCellulation.AdaptiveBoundaryGaugeChart

variable {P : SU2BoundaryDiskCellulation}
  (B : P.AdaptiveBoundaryGaugeChart)

/-- Dual adjacency witnessed specifically by an internal chord retained by
the adaptive boundary chart. -/
def internalChordDualAdj
    (f g : P.connected.cellulation.Face) : Prop :=
  f ≠ g ∧ ∃ h : P.connected.cellulation.HalfEdge,
    P.connected.cellulation.face h = some f ∧
    P.connected.cellulation.face (P.connected.cellulation.reverse h) = some g ∧
    P.connected.cellulation.edgeOfHalfEdge h ∉ Set.range B.tree.treeEdge ∧
    P.connected.cellulation.edgeOfHalfEdge h ≠ B.anchorEdge

theorem internalChordDualAdj_symm {f g : P.connected.cellulation.Face} :
    B.internalChordDualAdj f g -> B.internalChordDualAdj g f := by
  rintro ⟨hfg, h, hhf, hhg, htree, hanchor⟩
  refine ⟨hfg.symm, P.connected.cellulation.reverse h, hhg, ?_, ?_, ?_⟩
  · simpa [P.connected.cellulation.reverse_involutive h] using hhf
  · simpa using htree
  · simpa using hanchor

def internalChordDualGraph :
    SimpleGraph P.connected.cellulation.Face where
  Adj := B.internalChordDualAdj
  symm := fun _ _ => B.internalChordDualAdj_symm
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- One internal-chord dual adjacency supplies a cyclic physical merge whose
selected edge is certified to remain outside the primal tree. -/
theorem exists_internalChordCyclicFaceMerge
    {f g : P.connected.cellulation.Face}
    (hfg : B.internalChordDualAdj f g) :
    ∃ M : SU2EdgeConnectedDiskCellulation.CyclicFaceMerge
        P.toSU2EdgeConnectedDiskCellulation f g,
      P.connected.cellulation.edgeOfHalfEdge M.dart ∉
        Set.range B.tree.treeEdge := by
  rcases hfg with ⟨_, h, hhf, hhg, htree, _⟩
  obtain ⟨fb, fa, hfw⟩ :=
    P.toSU2EdgeConnectedDiskCellulation.exists_faceDartWord_split f h hhf
  obtain ⟨gb, ga, hgw⟩ :=
    P.toSU2EdgeConnectedDiskCellulation.exists_faceDartWord_split g
      (P.connected.cellulation.reverse h) hhg
  exact ⟨⟨h, hhf, hhg, fb, fa, hfw, gb, ga, hgw⟩, htree⟩

/-- Connectivity of the dual graph carried by internal chords is a local
sufficient criterion for constructing a fully compatible physical
boundary-elimination chart.  The unconditional theorem below later produces
such a chart directly for every certified physical disk. -/
theorem nonempty_physicalBoundaryEliminationChart_of_connected
    (hconn : B.internalChordDualGraph.Connected) :
    Nonempty (SU2PhysicalBoundaryEliminationChart P) := by
  classical
  letI : DecidableRel B.internalChordDualGraph.Adj := Classical.decRel _
  obtain ⟨n, order, faceOrder, hvalid⟩ :=
    SU2RootedTreeOrder.exists_validForGraph_of_connected
      B.internalChordDualGraph hconn
  let hadj : ∀ i : Fin n,
      B.internalChordDualAdj
        (faceOrder (order.parentIndex i))
        (faceOrder (Fin.succ i)) := fun i =>
    hvalid _ (order.parentIndex_pair_mem_parentPairs i)
  let hm : ∀ i : Fin n,
      ∃ M : SU2EdgeConnectedDiskCellulation.CyclicFaceMerge
          P.toSU2EdgeConnectedDiskCellulation
            (faceOrder (order.parentIndex i))
            (faceOrder (Fin.succ i)),
        P.connected.cellulation.edgeOfHalfEdge M.dart ∉
          Set.range B.tree.treeEdge := fun i =>
    B.exists_internalChordCyclicFaceMerge (hadj i)
  let merges : ∀ i : Fin n,
      SU2EdgeConnectedDiskCellulation.CyclicFaceMerge
        P.toSU2EdgeConnectedDiskCellulation
          (faceOrder (order.parentIndex i))
          (faceOrder (Fin.succ i)) := fun i => Classical.choose (hm i)
  let T : SU2DualRootedEliminationTree
      P.toSU2EdgeConnectedDiskCellulation :=
    ⟨n, faceOrder, order,
      fun i => ⟨(hadj i).1, Classical.choose (hadj i).2,
        (Classical.choose_spec (hadj i).2).1,
        (Classical.choose_spec (hadj i).2).2.1⟩,
      merges⟩
  refine ⟨⟨B, T, fun i => ?_⟩⟩
  change P.connected.cellulation.edgeOfHalfEdge (merges i).dart ∉
    Set.range B.tree.treeEdge
  exact Classical.choose_spec (hm i)

end SU2BoundaryDiskCellulation.AdaptiveBoundaryGaugeChart

namespace SU2BoundaryDiskCellulation

/-- **Universal tree--cotree existence.** Every certified physical disk
cellulation admits a primal boundary gauge chart whose retained internal
chords contain a complete physical dual elimination tree.  No compatibility
or connectedness hypothesis is supplied by the caller. -/
theorem nonempty_physicalBoundaryEliminationChart
    (P : SU2BoundaryDiskCellulation) :
    Nonempty (SU2PhysicalBoundaryEliminationChart P) := by
  obtain ⟨T⟩ :=
    P.toSU2EdgeConnectedDiskCellulation.nonempty_dualRootedEliminationTree
  have hconn := T.primalGraphAvoiding_selectedEdgeRange_connected
  obtain ⟨S, hS⟩ :=
    P.connected.cellulation.exists_rootedSpanningTree_avoiding_of_connected
      (Set.range T.selectedEdge) hconn
  obtain ⟨k, hk⟩ := P.exists_exterior_edge_not_tree S
  let B : P.AdaptiveBoundaryGaugeChart := ⟨S, k, hk⟩
  refine ⟨⟨B, T, fun i hi => ?_⟩⟩
  rcases hi with ⟨j, hj⟩
  apply hS j
  exact ⟨i, hj.symm⟩

end SU2BoundaryDiskCellulation

end Lean2dYangMills
