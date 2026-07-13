import Lean2dYangMills.SU2FiniteGaugeFixing
import Lean2dYangMills.SU2FiniteCellulation

/-!
# Global product-Haar gauge coordinates on a rooted construction tree

A value `SU2RootedTreeOrder n` describes a rooted tree with `n+1` vertices in
an order obtained by adjoining one new leaf at a time.  At a growth step, the
parent is a vertex already present in the smaller tree.

The module constructs one measurable equivalence on `Fin (n+1) -> SU2`.  Its
zeroth coordinate is the root variable and every later coordinate is the
relative group element from its parent to that vertex.  The equivalence is a
recursive composition of finite product splittings and Haar-preserving skew
products.  The final theorem proves preservation of the literal `Measure.pi`
product Haar measure in every finite dimension.

For a primal-connected `SU2FiniteDiskCellulation`, the module additionally
constructs a certified spanning-tree order and transports the equivalence to
the literal cellulation vertex type.  The remaining step is the induced
equivalence on the full edge configuration and the simultaneous formula for
all face holonomies.
-/

noncomputable section

namespace Lean2dYangMills

open MeasureTheory

/-- A rooted tree with `n+1` vertices, built by adjoining one leaf at a time.
The `parent` of the new leaf is a vertex of the already constructed tree. -/
inductive SU2RootedTreeOrder : Nat -> Type
  | root : SU2RootedTreeOrder 0
  | grow {n : Nat} (tree : SU2RootedTreeOrder n)
      (parent : Fin (n + 1)) : SU2RootedTreeOrder (n + 1)

/-- Product Haar on the vertex variables of an ordered rooted tree. -/
def su2RootedTreeVertexHaar (n : Nat) : Measure (Fin (n + 1) -> SU2) :=
  su2FiniteProductHaar (Fin (n + 1))

instance instIsProbabilityMeasureSU2RootedTreeVertexHaar (n : Nat) :
    IsProbabilityMeasure (su2RootedTreeVertexHaar n) := by
  unfold su2RootedTreeVertexHaar
  infer_instance

/-- Split the last coordinate from a finite SU(2) configuration. -/
def su2SplitLastEquiv (n : Nat) :
    (Fin (n + 1) -> SU2) ≃ᵐ (SU2 × (Fin n -> SU2)) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => SU2) (Fin.last n)

/-- One triangular tree-growth step.  The old configuration is unchanged and
the new vertex variable is replaced by its increment from `parent`. -/
def su2AttachLeafGaugeFixEquiv {n : Nat} (parent : Fin (n + 1)) :
    ((Fin (n + 1) -> SU2) × SU2) ≃ᵐ
      ((Fin (n + 1) -> SU2) × SU2) where
  toEquiv :=
    { toFun := fun p => (p.1, (p.1 parent)⁻¹ * p.2)
      invFun := fun p => (p.1, p.1 parent * p.2)
      left_inv := by
        rintro ⟨x, y⟩
        simp
      right_inv := by
        rintro ⟨x, y⟩
        simp }
  measurable_toFun := by
    exact measurable_fst.prodMk <| continuous_mul.measurable2
      (measurable_inv.comp <| (measurable_pi_apply parent).comp measurable_fst)
      measurable_snd
  measurable_invFun := by
    exact measurable_fst.prodMk <| continuous_mul.measurable2
      ((measurable_pi_apply parent).comp measurable_fst) measurable_snd

/-- The leaf-attachment shear preserves old-product-Haar times new-edge Haar. -/
theorem su2AttachLeafGaugeFix_measurePreserving {n : Nat}
    (parent : Fin (n + 1)) :
    MeasurePreserving (su2AttachLeafGaugeFixEquiv parent)
      ((su2RootedTreeVertexHaar n).prod su2HaarProb)
      ((su2RootedTreeVertexHaar n).prod su2HaarProb) := by
  have hmeas : Measurable (Function.uncurry
      (fun x : Fin (n + 1) -> SU2 => fun y : SU2 => (x parent)⁻¹ * y)) := by
    exact continuous_mul.measurable2
      (measurable_inv.comp <| (measurable_pi_apply parent).comp measurable_fst)
      measurable_snd
  have h := (MeasurePreserving.id (su2RootedTreeVertexHaar n)).skew_product
    (μc := su2HaarProb) (μd := su2HaarProb)
    (g := fun x : Fin (n + 1) -> SU2 => fun y : SU2 => (x parent)⁻¹ * y)
    hmeas (ae_of_all _ fun x =>
      (measurePreserving_mul_left su2HaarProb (x parent)⁻¹).map_eq)
  simpa [su2AttachLeafGaugeFixEquiv] using h

namespace SU2RootedTreeOrder

/-- Parent--child pairs, embedded in the final vertex index type. -/
def parentPairs : {n : Nat} -> SU2RootedTreeOrder n ->
    List (Fin (n + 1) × Fin (n + 1))
  | 0, .root => []
  | n + 1, .grow tree parent =>
      tree.parentPairs.map
        (fun p => (Fin.castSucc p.1, Fin.castSucc p.2)) ++
      [(Fin.castSucc parent, Fin.last (n + 1))]

/-- A construction order realizes a finite simple graph when every recorded
parent--child pair is an actual graph edge. -/
def ValidForGraph {V : Type} {n : Nat} (G : SimpleGraph V)
    (tree : SU2RootedTreeOrder n) (vertexOrder : Fin (n + 1) ≃ V) : Prop :=
  ∀ p ∈ tree.parentPairs,
    G.Adj (vertexOrder p.1) (vertexOrder p.2)

/-- Every finite connected simple graph admits a construction-ordered rooted
spanning tree. -/
theorem exists_validForGraph_of_connected {V : Type}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) :
    ∃ n, ∃ tree : SU2RootedTreeOrder n,
      ∃ vertexOrder : Fin (n + 1) ≃ V,
        ValidForGraph G tree vertexOrder := by
  classical
  let P : ∀ (α : Type) [Fintype α], Prop := fun α _ =>
    ∀ (_ : DecidableEq α) (H : SimpleGraph α) (_ : DecidableRel H.Adj),
      H.Connected ->
        ∃ n, ∃ tree : SU2RootedTreeOrder n,
          ∃ vertexOrder : Fin (n + 1) ≃ α,
            ValidForGraph H tree vertexOrder
  have hPV : P V := Fintype.induction_subsingleton_or_nontrivial (P := P) V (by
    intro α inst hsub
    intro _ H _ hH
    letI : Nonempty α := hH.nonempty
    letI : Unique α :=
      { default := Classical.choice inferInstance
        uniq := fun a => hsub.elim a (Classical.choice inferInstance) }
    let vertexOrder : Fin 1 ≃ α := Equiv.ofUnique _ _
    exact ⟨0, .root, vertexOrder, by simp [ValidForGraph, parentPairs]⟩) (by
    intro α inst hnontrivial ih
    intro _ H _ hH
    obtain ⟨v, hconn⟩ :=
      hH.exists_connected_induce_compl_singleton_of_finite_nontrivial
    let β := ↥({v}ᶜ : Set α)
    have hcard : Fintype.card β < Fintype.card α := by
      exact Fintype.card_subtype_lt (x := v) (by simp)
    let H' : SimpleGraph β := H.induce ({v}ᶜ : Set α)
    obtain ⟨n, tree, vertexOrder, hvalid⟩ :=
      ih β hcard inferInstance H' inferInstance hconn
    obtain ⟨u, hvu⟩ := hH.preconnected.exists_adj_of_nontrivial v
    have huv_ne : u ≠ v := hvu.ne.symm
    let u' : β := ⟨u, by simp [huv_ne]⟩
    let parent : Fin (n + 1) := vertexOrder.symm u'
    let fullOrder : Fin (n + 2) ≃ α :=
      (finSuccEquivLast (n := n + 1)).trans
        ((Equiv.optionCongr vertexOrder).trans (Equiv.optionSubtypeNe v))
    refine ⟨n + 1, .grow tree parent, fullOrder, ?_⟩
    intro p hp
    simp only [parentPairs, List.mem_append, List.mem_map,
      List.mem_singleton] at hp
    rcases hp with ⟨q, hq, rfl⟩ | rfl
    · have hqAdj := hvalid q hq
      simpa [fullOrder] using hqAdj
    · simpa [fullOrder, parent, u'] using hvu.symm)
  exact hPV inferInstance G inferInstance hG

/-- The global rooted-tree coordinate equivalence.  It is a single map on all
vertex variables, recursively assembled from the local leaf shears. -/
def coordinateEquiv : {n : Nat} -> SU2RootedTreeOrder n ->
    (Fin (n + 1) -> SU2) ≃ᵐ (Fin (n + 1) -> SU2)
  | 0, .root => MeasurableEquiv.refl _
  | n + 1, .grow tree parent =>
      let split := su2SplitLastEquiv (n + 1)
      split.trans MeasurableEquiv.prodComm |>.trans
        (su2AttachLeafGaugeFixEquiv parent) |>.trans
        (MeasurableEquiv.prodCongr tree.coordinateEquiv
          (MeasurableEquiv.refl SU2)) |>.trans
        MeasurableEquiv.prodComm |>.trans split.symm

@[simp]
theorem coordinateEquiv_root_apply (x : Fin 1 -> SU2) :
    (coordinateEquiv .root) x = x := rfl

@[simp]
theorem coordinateEquiv_grow_apply_last {n : Nat}
    (tree : SU2RootedTreeOrder n) (parent : Fin (n + 1))
    (x : Fin (n + 2) -> SU2) :
    (coordinateEquiv (.grow tree parent) x) (Fin.last (n + 1)) =
      (x (Fin.castSucc parent))⁻¹ * x (Fin.last (n + 1)) := by
  simp [coordinateEquiv, su2SplitLastEquiv, su2AttachLeafGaugeFixEquiv,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr, Fin.init_def]

@[simp]
theorem coordinateEquiv_grow_apply_castSucc {n : Nat}
    (tree : SU2RootedTreeOrder n) (parent : Fin (n + 1))
    (x : Fin (n + 2) -> SU2) (i : Fin (n + 1)) :
    (coordinateEquiv (.grow tree parent) x) (Fin.castSucc i) =
      coordinateEquiv tree (fun j => x (Fin.castSucc j)) i := by
  simp [coordinateEquiv, su2SplitLastEquiv, su2AttachLeafGaugeFixEquiv,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr, Fin.init_def]

/-- The recursive global rooted-tree coordinate map preserves product Haar in
every finite dimension. -/
theorem coordinateEquiv_measurePreserving : {n : Nat} ->
    (tree : SU2RootedTreeOrder n) ->
    MeasurePreserving tree.coordinateEquiv
      (su2RootedTreeVertexHaar n) (su2RootedTreeVertexHaar n)
  | 0, .root => MeasurePreserving.id _
  | n + 1, .grow tree parent => by
      let split := su2SplitLastEquiv (n + 1)
      have hsplit : MeasurePreserving split
          (su2RootedTreeVertexHaar (n + 1))
          (su2HaarProb.prod (su2RootedTreeVertexHaar n)) := by
        change MeasurePreserving
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => SU2)
            (Fin.last (n + 1)))
          (Measure.pi (fun _ : Fin (n + 2) => su2HaarProb))
          (su2HaarProb.prod
            (Measure.pi (fun _ : Fin (n + 1) => su2HaarProb)))
        exact measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 2) => su2HaarProb) (Fin.last (n + 1))
      have hswap₁ : MeasurePreserving Prod.swap
          (su2HaarProb.prod (su2RootedTreeVertexHaar n))
          ((su2RootedTreeVertexHaar n).prod su2HaarProb) :=
        Measure.measurePreserving_swap
      have hleaf := su2AttachLeafGaugeFix_measurePreserving parent
      have hold : MeasurePreserving tree.coordinateEquiv
          (su2RootedTreeVertexHaar n) (su2RootedTreeVertexHaar n) :=
        coordinateEquiv_measurePreserving tree
      have hprod : MeasurePreserving
          (Prod.map tree.coordinateEquiv (id : SU2 -> SU2))
          ((su2RootedTreeVertexHaar n).prod su2HaarProb)
          ((su2RootedTreeVertexHaar n).prod su2HaarProb) :=
        hold.prod (MeasurePreserving.id su2HaarProb)
      have hswap₂ : MeasurePreserving Prod.swap
          ((su2RootedTreeVertexHaar n).prod su2HaarProb)
          (su2HaarProb.prod (su2RootedTreeVertexHaar n)) :=
        Measure.measurePreserving_swap
      have hsplitInv : MeasurePreserving split.symm
          (su2HaarProb.prod (su2RootedTreeVertexHaar n))
          (su2RootedTreeVertexHaar (n + 1)) :=
        MeasurePreserving.symm split hsplit
      have hcomp := hsplitInv.comp <| hswap₂.comp <| hprod.comp <|
        hleaf.comp <| hswap₁.comp hsplit
      simpa [coordinateEquiv, split, Function.comp_def,
        MeasurableEquiv.prodComm, MeasurableEquiv.prodCongr] using hcomp

end SU2RootedTreeOrder

/-- Relabel a finite SU(2) configuration along an equivalence of its index
types. -/
def su2VertexRelabelEquiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) : (ι -> SU2) ≃ᵐ (κ -> SU2) :=
  MeasurableEquiv.piCongrLeft (fun _ : κ => SU2) e

/-- A relabelling of finitely many coordinates preserves their literal
product Haar measure. -/
theorem su2VertexRelabel_measurePreserving {ι κ : Type}
    [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    MeasurePreserving (su2VertexRelabelEquiv e)
      (su2FiniteProductHaar ι) (su2FiniteProductHaar κ) := by
  simpa [su2VertexRelabelEquiv, su2FiniteProductHaar] using
    (measurePreserving_piCongrLeft
      (fun _ : κ => su2HaarProb) e)

namespace SU2FiniteDiskCellulation

/-- Adjacency in the primal one-skeleton, witnessed by an oriented
half-edge.  Symmetry follows by reversing the witness. -/
def primalAdj (C : SU2FiniteDiskCellulation) (v w : C.Vertex) : Prop :=
  v ≠ w ∧ ∃ h : C.HalfEdge, C.source h = v ∧ C.target h = w

theorem primalAdj_symm (C : SU2FiniteDiskCellulation) {v w : C.Vertex} :
    C.primalAdj v w -> C.primalAdj w v := by
  rintro ⟨hvw, h, hsv, htw⟩
  refine ⟨Ne.symm hvw, C.reverse h, ?_, ?_⟩
  · simpa [target] using htw
  · simpa [target, C.reverse_involutive h] using hsv

/-- The primal simple graph derived from the half-edge incidence data. -/
def primalGraph (C : SU2FiniteDiskCellulation) : SimpleGraph C.Vertex where
  Adj := C.primalAdj
  symm := by
    intro v w
    exact C.primalAdj_symm
  loopless := ⟨by
    intro v hv
    exact hv.1 rfl⟩

/-- A construction-ordered spanning tree certificate inside the primal
one-skeleton of a finite disk cellulation.  The vertex equivalence supplies
coverage and uniqueness; `parent_edges` proves that every growth edge is a
genuine cellulation edge. -/
structure RootedSpanningTree (C : SU2FiniteDiskCellulation) where
  n : Nat
  vertexOrder : Fin (n + 1) ≃ C.Vertex
  order : SU2RootedTreeOrder n
  parent_edges : ∀ p ∈ order.parentPairs,
    C.primalAdj (vertexOrder p.1) (vertexOrder p.2)

/-- Primal connectedness is precisely the extra geometric hypothesis needed
to construct a certified rooted spanning tree from the present cellulation
record. -/
theorem exists_rootedSpanningTree_of_primal_connected
    (C : SU2FiniteDiskCellulation) (hC : C.primalGraph.Connected) :
    Nonempty C.RootedSpanningTree := by
  classical
  letI : DecidableRel C.primalGraph.Adj := Classical.decRel _
  obtain ⟨n, tree, vertexOrder, hvalid⟩ :=
    SU2RootedTreeOrder.exists_validForGraph_of_connected C.primalGraph hC
  exact ⟨{
    n := n
    vertexOrder := vertexOrder
    order := tree
    parent_edges := hvalid }⟩

/-- Global rooted-tree coordinates on the vertex variables of a finite disk
cellulation.  `vertexOrder` labels every cellulation vertex by the construction
order; the incidence condition saying that each parent--child pair is an edge
of the cellulation is intentionally a separate combinatorial certificate. -/
def rootedTreeVertexCoordinateEquiv (C : SU2FiniteDiskCellulation) {n : Nat}
    (vertexOrder : Fin (n + 1) ≃ C.Vertex)
    (tree : SU2RootedTreeOrder n) :
    (C.Vertex -> SU2) ≃ᵐ (C.Vertex -> SU2) :=
  let relabel := su2VertexRelabelEquiv vertexOrder
  relabel.symm.trans (tree.coordinateEquiv.trans relabel)

/-- The single global rooted-tree change of all cellulation vertex variables
preserves the product of normalized Haar probabilities. -/
theorem rootedTreeVertexCoordinateEquiv_measurePreserving
    (C : SU2FiniteDiskCellulation) {n : Nat}
    (vertexOrder : Fin (n + 1) ≃ C.Vertex)
    (tree : SU2RootedTreeOrder n) :
    MeasurePreserving (C.rootedTreeVertexCoordinateEquiv vertexOrder tree)
      (su2FiniteProductHaar C.Vertex) (su2FiniteProductHaar C.Vertex) := by
  let relabel := su2VertexRelabelEquiv vertexOrder
  have hrelabel : MeasurePreserving relabel
      (su2RootedTreeVertexHaar n) (su2FiniteProductHaar C.Vertex) := by
    simpa [relabel, su2RootedTreeVertexHaar] using
      (su2VertexRelabel_measurePreserving vertexOrder)
  have hrelabelInv : MeasurePreserving relabel.symm
      (su2FiniteProductHaar C.Vertex) (su2RootedTreeVertexHaar n) :=
    MeasurePreserving.symm relabel hrelabel
  have htree := tree.coordinateEquiv_measurePreserving
  have hcomp := hrelabel.comp (htree.comp hrelabelInv)
  simpa [rootedTreeVertexCoordinateEquiv, relabel, Function.comp_def] using hcomp

/-- The global vertex-coordinate map attached to a certified spanning tree of
the cellulation. -/
def RootedSpanningTree.vertexCoordinateEquiv
    {C : SU2FiniteDiskCellulation} (T : C.RootedSpanningTree) :
    (C.Vertex -> SU2) ≃ᵐ (C.Vertex -> SU2) :=
  C.rootedTreeVertexCoordinateEquiv T.vertexOrder T.order

/-- A certified primal spanning tree therefore gives one global
measure-preserving coordinate transformation on all cellulation vertices. -/
theorem RootedSpanningTree.vertexCoordinateEquiv_measurePreserving
    {C : SU2FiniteDiskCellulation} (T : C.RootedSpanningTree) :
    MeasurePreserving T.vertexCoordinateEquiv
      (su2FiniteProductHaar C.Vertex) (su2FiniteProductHaar C.Vertex) := by
  exact C.rootedTreeVertexCoordinateEquiv_measurePreserving
    T.vertexOrder T.order

/-- Every primal-connected finite disk cellulation admits a single global
root-plus-tree-increments coordinate equivalence preserving vertex product
Haar.  The theorem chooses the certified spanning tree internally. -/
theorem exists_rootedTreeVertexCoordinateEquiv_measurePreserving
    (C : SU2FiniteDiskCellulation) (hC : C.primalGraph.Connected) :
    ∃ Φ : (C.Vertex -> SU2) ≃ᵐ (C.Vertex -> SU2),
      MeasurePreserving Φ
        (su2FiniteProductHaar C.Vertex) (su2FiniteProductHaar C.Vertex) := by
  obtain ⟨T⟩ := C.exists_rootedSpanningTree_of_primal_connected hC
  exact ⟨T.vertexCoordinateEquiv,
    T.vertexCoordinateEquiv_measurePreserving⟩

@[simp]
theorem rootedTreeVertexCoordinateEquiv_grow_apply_new
    (C : SU2FiniteDiskCellulation) {n : Nat}
    (vertexOrder : Fin (n + 2) ≃ C.Vertex)
    (tree : SU2RootedTreeOrder n) (parent : Fin (n + 1))
    (x : C.Vertex -> SU2) :
    C.rootedTreeVertexCoordinateEquiv vertexOrder (.grow tree parent) x
        (vertexOrder (Fin.last (n + 1))) =
      (x (vertexOrder (Fin.castSucc parent)))⁻¹ *
        x (vertexOrder (Fin.last (n + 1))) := by
  simp [rootedTreeVertexCoordinateEquiv, su2VertexRelabelEquiv,
    MeasurableEquiv.piCongrLeft]

end SU2FiniteDiskCellulation

end Lean2dYangMills
