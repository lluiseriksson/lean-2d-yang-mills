import Lean2dYangMills.SU2CyclicEdgeElimination
import Lean2dYangMills.SU2RootedTreeGaugeFixing

/-!
# A physical elimination tree in the face dual graph

This module turns connectedness of the bounded-face dual graph into exactly
`F - 1` concrete physical edge choices.  Each parent--child adjacency is
realized by a `CyclicFaceMerge`, and the selected physical edges are proved
pairwise distinct.  This is the first global combinatorial invariant needed
to iterate the local Migdal move without reusing an integration variable.
-/

noncomputable section

namespace Lean2dYangMills

/-- A construction-ordered spanning tree of the bounded-face dual graph,
with every abstract parent--child adjacency retained as physical cellulation
data. -/
structure SU2DualRootedEliminationTree
    (P : SU2EdgeConnectedDiskCellulation) where
  n : Nat
  faceOrder : Fin (n + 1) ≃ P.connected.cellulation.Face
  order : SU2RootedTreeOrder n
  parent_adj : ∀ i : Fin n,
    P.connected.cellulation.dualAdj
      (faceOrder (order.parentIndex i))
      (faceOrder (Fin.succ i))
  parent_merge : ∀ i : Fin n,
    SU2EdgeConnectedDiskCellulation.CyclicFaceMerge P
      (faceOrder (order.parentIndex i))
      (faceOrder (Fin.succ i))

namespace SU2EdgeConnectedDiskCellulation

/-- Dual connectedness supplies a construction-ordered physical elimination
tree on all bounded faces. -/
theorem nonempty_dualRootedEliminationTree
    (P : SU2EdgeConnectedDiskCellulation) :
    Nonempty (SU2DualRootedEliminationTree P) := by
  classical
  letI : DecidableRel P.connected.cellulation.dualGraph.Adj :=
    Classical.decRel _
  obtain ⟨n, tree, faceOrder, hvalid⟩ :=
    SU2RootedTreeOrder.exists_validForGraph_of_connected
      P.connected.cellulation.dualGraph P.connected.dual_connected
  let hadj : ∀ i : Fin n,
      P.connected.cellulation.dualAdj
        (faceOrder (tree.parentIndex i))
        (faceOrder (Fin.succ i)) := fun i =>
    hvalid _ (tree.parentIndex_pair_mem_parentPairs i)
  exact ⟨⟨n, faceOrder, tree, hadj, fun i =>
    Classical.choice (P.exists_cyclicFaceMerge_of_dualAdj (hadj i))⟩⟩

end SU2EdgeConnectedDiskCellulation

namespace SU2DualRootedEliminationTree

variable {P : SU2EdgeConnectedDiskCellulation}
  (T : SU2DualRootedEliminationTree P)

/-- The physical cyclic-word witness attached to one dual-tree edge. -/
def merge (i : Fin T.n) :
    SU2EdgeConnectedDiskCellulation.CyclicFaceMerge P
      (T.faceOrder (T.order.parentIndex i))
      (T.faceOrder (Fin.succ i)) :=
  T.parent_merge i

/-- The actual original edge coordinate eliminated at one dual-tree step. -/
def selectedEdge (i : Fin T.n) : P.connected.cellulation.Edge :=
  P.connected.cellulation.edgeOfHalfEdge (T.merge i).dart

/-- The construction has one non-root step for every bounded face except the
root face. -/
theorem card_step : T.n =
    Fintype.card P.connected.cellulation.Face - 1 := by
  have hcard : T.n + 1 =
      Fintype.card P.connected.cellulation.Face := by
    simpa using Fintype.card_congr T.faceOrder
  omega

/-- **No global reuse.** Distinct dual-tree steps select distinct original
physical edges.  A same-orientation collision identifies the two children;
an opposite-orientation collision would make each child the other's strict
ancestor, contradicting construction order. -/
theorem selectedEdge_injective : Function.Injective T.selectedEdge := by
  intro i j hij
  let C := P.connected.cellulation
  let Mi := T.merge i
  let Mj := T.merge j
  rcases C.eq_or_eq_reverse_of_edgeOfHalfEdge_eq hij with hsame | hrev
  · have hchild :
        T.faceOrder (Fin.succ i) = T.faceOrder (Fin.succ j) := by
      apply Option.some.inj
      calc
        some (T.faceOrder (Fin.succ i)) =
            C.face (C.reverse Mi.dart) := Mi.reverse_face.symm
        _ = C.face (C.reverse Mj.dart) := by rw [hsame]
        _ = some (T.faceOrder (Fin.succ j)) := Mj.reverse_face
    exact Fin.succ_injective _ (T.faceOrder.injective hchild)
  · have hparentChild :
        T.order.parentIndex i = Fin.succ j := by
      apply T.faceOrder.injective
      apply Option.some.inj
      calc
        some (T.faceOrder (T.order.parentIndex i)) =
            C.face Mi.dart := Mi.dart_face.symm
        _ = C.face (C.reverse Mj.dart) := by rw [hrev]
        _ = some (T.faceOrder (Fin.succ j)) := Mj.reverse_face
    have hchildParent :
        Fin.succ i = T.order.parentIndex j := by
      apply T.faceOrder.injective
      apply Option.some.inj
      calc
        some (T.faceOrder (Fin.succ i)) =
            C.face (C.reverse Mi.dart) := Mi.reverse_face.symm
        _ = C.face Mj.dart := by
          have hr := congrArg C.reverse hrev
          rw [C.reverse_involutive Mj.dart] at hr
          rw [hr]
        _ = some (T.faceOrder (T.order.parentIndex j)) := Mj.dart_face
    have hi := T.order.parentIndex_lt_child i
    have hj := T.order.parentIndex_lt_child j
    rw [hparentChild] at hi
    rw [← hchildParent] at hj
    exact (Nat.lt_asymm hi hj).elim

/-- The selected physical edge type is literally equivalent to the `F - 1`
construction steps. -/
def selectedEdgeEquivRange :
    Fin T.n ≃ Set.range T.selectedEdge :=
  Equiv.ofInjective T.selectedEdge T.selectedEdge_injective

noncomputable instance selectedEdgeRangeFintype :
    Fintype (Set.range T.selectedEdge) := Fintype.ofFinite _

theorem card_selectedEdgeRange :
    Fintype.card (Set.range T.selectedEdge) =
      Fintype.card P.connected.cellulation.Face - 1 := by
  classical
  calc
    Fintype.card (Set.range T.selectedEdge) = Fintype.card (Fin T.n) :=
      Fintype.card_congr T.selectedEdgeEquivRange.symm
    _ = T.n := Fintype.card_fin T.n
    _ = Fintype.card P.connected.cellulation.Face - 1 :=
      SU2DualRootedEliminationTree.card_step T

end SU2DualRootedEliminationTree

end Lean2dYangMills
