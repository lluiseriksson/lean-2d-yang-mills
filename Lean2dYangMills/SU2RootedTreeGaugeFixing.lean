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

/-- The parent of the non-root vertex `i.succ`.  The construction order makes
this parent strictly older than the child; that triangularity is what later
prevents two tree steps from selecting the same physical edge. -/
def parentIndex : {n : Nat} -> (tree : SU2RootedTreeOrder n) ->
    Fin n -> Fin (n + 1)
  | 0, .root => Fin.elim0
  | n + 1, .grow tree parent => fun i =>
      Fin.lastCases (Fin.castSucc parent)
        (fun j => Fin.castSucc (tree.parentIndex j)) i

theorem parentIndex_lt_child : {n : Nat} ->
    (tree : SU2RootedTreeOrder n) -> (i : Fin n) ->
      (tree.parentIndex i).val < (Fin.succ i).val
  | 0, .root, i => Fin.elim0 i
  | n + 1, .grow tree parent, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [parentIndex] using parent.isLt
      · simpa [parentIndex] using tree.parentIndex_lt_child j

/-- Every parent selected by `parentIndex` is one of the certified
parent--child pairs stored by the construction tree. -/
theorem parentIndex_pair_mem_parentPairs : {n : Nat} ->
    (tree : SU2RootedTreeOrder n) -> (i : Fin n) ->
      (tree.parentIndex i, Fin.succ i) ∈ tree.parentPairs
  | 0, .root, i => Fin.elim0 i
  | n + 1, .grow tree parent, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [parentIndex, parentPairs]
      · have hj := tree.parentIndex_pair_mem_parentPairs j
        simp only [parentIndex, Fin.lastCases_castSucc, parentPairs,
          List.mem_append, List.mem_map, List.mem_singleton]
        left
        refine ⟨(tree.parentIndex j, Fin.succ j), hj, ?_⟩
        ext <;> rfl

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

/-- At every non-root vertex, the global coordinate map is exactly the
parent-to-child increment. -/
theorem coordinateEquiv_apply_succ : {n : Nat} ->
    (tree : SU2RootedTreeOrder n) -> (x : Fin (n + 1) -> SU2) ->
      (i : Fin n) ->
        tree.coordinateEquiv x (Fin.succ i) =
          (x (tree.parentIndex i))⁻¹ * x (Fin.succ i)
  | 0, .root, _, i => Fin.elim0 i
  | n + 1, .grow tree parent, x, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [parentIndex] using
          coordinateEquiv_grow_apply_last tree parent x
      · have hidx : Fin.succ (Fin.castSucc j) =
            Fin.castSucc (Fin.succ j) := by ext; rfl
        rw [hidx]
        rw [coordinateEquiv_grow_apply_castSucc]
        simpa [parentIndex] using
          tree.coordinateEquiv_apply_succ
            (fun k => x (Fin.castSucc k)) j

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
coverage and uniqueness.  The physical parent dart is stored explicitly;
this matters when parallel physical edges join the same pair of vertices,
because later tree--cotree arguments must retain the selected edge itself,
not merely the existence of some edge with the same endpoints. -/
structure RootedSpanningTree (C : SU2FiniteDiskCellulation) where
  n : Nat
  vertexOrder : Fin (n + 1) ≃ C.Vertex
  order : SU2RootedTreeOrder n
  treeDart : Fin n -> C.HalfEdge
  treeDart_source_cert : ∀ i,
    C.source (treeDart i) = vertexOrder (order.parentIndex i)
  treeDart_target_cert : ∀ i,
    C.target (treeDart i) = vertexOrder (Fin.succ i)

/-- The physical edge underlying an oriented half-edge. -/
def edgeOfHalfEdge (C : SU2FiniteDiskCellulation) (h : C.HalfEdge) : C.Edge :=
  (C.edgeDarts.symm h).1

/-- The orientation bit of a half-edge in the cellulation's chosen edge
coordinates. -/
def halfEdgeSide (C : SU2FiniteDiskCellulation) (h : C.HalfEdge) : Bool :=
  (C.edgeDarts.symm h).2

@[simp]
theorem edgeDarts_edgeOfHalfEdge_halfEdgeSide
    (C : SU2FiniteDiskCellulation) (h : C.HalfEdge) :
    C.edgeDarts (C.edgeOfHalfEdge h, C.halfEdgeSide h) = h := by
  exact C.edgeDarts.apply_symm_apply h

@[simp]
theorem edgeOfHalfEdge_reverse (C : SU2FiniteDiskCellulation)
    (h : C.HalfEdge) :
    C.edgeOfHalfEdge (C.reverse h) = C.edgeOfHalfEdge h := by
  rcases hp : C.edgeDarts.symm h with ⟨e, b⟩
  have hh : h = C.edgeDarts (e, b) := by
    rw [← hp]
    exact (C.edgeDarts.apply_symm_apply h).symm
  subst h
  simp [edgeOfHalfEdge, C.reverse_edgeDarts]

/-- Primal adjacency witnessed by a physical edge outside a prescribed
forbidden set.  Unlike deleting an edge of a `SimpleGraph`, this definition
retains parallel allowed edges when one parallel physical edge is forbidden. -/
def primalAdjAvoiding (C : SU2FiniteDiskCellulation)
    (forbidden : Set C.Edge) (v w : C.Vertex) : Prop :=
  v ≠ w ∧ ∃ h : C.HalfEdge,
    C.source h = v ∧ C.target h = w ∧
      C.edgeOfHalfEdge h ∉ forbidden

theorem primalAdjAvoiding_symm (C : SU2FiniteDiskCellulation)
    (forbidden : Set C.Edge) {v w : C.Vertex} :
    C.primalAdjAvoiding forbidden v w ->
      C.primalAdjAvoiding forbidden w v := by
  rintro ⟨hvw, h, hsv, htv, hedge⟩
  refine ⟨hvw.symm, C.reverse h, ?_, ?_, ?_⟩
  · exact htv
  · simpa [target, C.reverse_involutive h] using hsv
  · simpa using hedge

/-- The simple primal graph obtained after forbidding physical edges. -/
def primalGraphAvoiding (C : SU2FiniteDiskCellulation)
    (forbidden : Set C.Edge) : SimpleGraph C.Vertex where
  Adj := C.primalAdjAvoiding forbidden
  symm := by
    intro v w
    exact C.primalAdjAvoiding_symm forbidden
  loopless := ⟨by
    intro v hv
    exact hv.1 rfl⟩

theorem primalGraphAvoiding_mono (C : SU2FiniteDiskCellulation)
    {s t : Set C.Edge} (hst : s ⊆ t) :
    C.primalGraphAvoiding t ≤ C.primalGraphAvoiding s := by
  intro v w hvw
  rcases hvw with ⟨hne, h, hs, ht, hedge⟩
  exact ⟨hne, h, hs, ht, fun he => hedge (hst he)⟩

theorem primalGraphAvoiding_le_primalGraph
    (C : SU2FiniteDiskCellulation) (forbidden : Set C.Edge) :
    C.primalGraphAvoiding forbidden ≤ C.primalGraph := by
  intro v w hvw
  rcases hvw with ⟨hne, h, hs, ht, _⟩
  exact ⟨hne, h, hs, ht⟩

/-- Consecutive allowed darts along a face orbit give primal reachability in
the physical-edge-deleted graph.  This is the local path lemma used to replace
one dual-tree edge by the rest of the newly attached face boundary. -/
theorem reachable_next_pow_of_forall_not_mem
    (C : SU2FiniteDiskCellulation) (forbidden : Set C.Edge)
    (h : C.HalfEdge) (n : Nat)
    (hallowed : ∀ k < n,
      C.edgeOfHalfEdge ((C.next ^ k) h) ∉ forbidden) :
    (C.primalGraphAvoiding forbidden).Reachable
      (C.source h) (C.source ((C.next ^ n) h)) := by
  induction n with
  | zero => exact .rfl
  | succ n ih =>
      have hprefix := ih (fun k hk => hallowed k (Nat.lt_succ_of_lt hk))
      have hedge : C.edgeOfHalfEdge ((C.next ^ n) h) ∉ forbidden :=
        hallowed n (Nat.lt_succ_self n)
      have htarget :
          C.target ((C.next ^ n) h) =
            C.source ((C.next ^ (n + 1)) h) := by
        simpa [pow_succ'] using
          (C.next_source ((C.next ^ n) h)).symm
      have hstep :
          (C.primalGraphAvoiding forbidden).Reachable
            (C.source ((C.next ^ n) h))
            (C.source ((C.next ^ (n + 1)) h)) := by
        by_cases heq : C.source ((C.next ^ n) h) =
            C.source ((C.next ^ (n + 1)) h)
        · simpa [heq]
        · apply SimpleGraph.Adj.reachable
          exact ⟨heq, (C.next ^ n) h, rfl, htarget, hedge⟩
      exact hprefix.trans hstep

/-- If every edge of one graph can be replaced by a reachable path in a
second graph, reachability in the first graph lifts to the second. -/
theorem reachable_of_reachable_of_adj_reachable
    {V : Type} {G H : SimpleGraph V}
    (hadj : ∀ {v w}, G.Adj v w -> H.Reachable v w)
    {v w : V} (hvw : G.Reachable v w) : H.Reachable v w := by
  obtain ⟨p⟩ := hvw
  induction p with
  | nil => exact .rfl
  | cons h p ih => exact (hadj h).trans ih

/-- Removing one additional physical edge preserves primal connectedness when
both orientations of that edge can be bypassed in the smaller graph. -/
theorem primalGraphAvoiding_insert_connected
    (C : SU2FiniteDiskCellulation) (forbidden : Set C.Edge) (e : C.Edge)
    (hconn : (C.primalGraphAvoiding forbidden).Connected)
    (hbypass : ∀ h : C.HalfEdge, C.edgeOfHalfEdge h = e ->
      (C.primalGraphAvoiding (Set.insert e forbidden)).Reachable
        (C.source h) (C.target h)) :
    (C.primalGraphAvoiding (Set.insert e forbidden)).Connected := by
  letI : Nonempty C.Vertex := hconn.nonempty
  refine ⟨?_⟩
  intro v w
  apply reachable_of_reachable_of_adj_reachable (G :=
    C.primalGraphAvoiding forbidden) (H :=
    C.primalGraphAvoiding (Set.insert e forbidden)) ?_ (hconn v w)
  intro a b hab
  rcases hab with ⟨hne, h, hs, ht, hedge⟩
  by_cases he : C.edgeOfHalfEdge h = e
  · simpa [hs, ht] using hbypass h he
  · apply SimpleGraph.Adj.reachable
    exact ⟨hne, h, hs, ht, by
      intro hin
      rcases Set.mem_insert_iff.mp hin with heq | hmem
      · exact he heq
      · exact hedge hmem⟩

/-- Two oriented half-edges over the same physical edge are either equal or
reverse to one another. -/
theorem eq_or_eq_reverse_of_edgeOfHalfEdge_eq
    (C : SU2FiniteDiskCellulation) {h k : C.HalfEdge}
    (hedge : C.edgeOfHalfEdge h = C.edgeOfHalfEdge k) :
    h = k ∨ h = C.reverse k := by
  rcases hp : C.edgeDarts.symm h with ⟨e, b⟩
  rcases hq : C.edgeDarts.symm k with ⟨f, c⟩
  have hh : h = C.edgeDarts (e, b) := by
    rw [← hp]
    exact (C.edgeDarts.apply_symm_apply h).symm
  have hk : k = C.edgeDarts (f, c) := by
    rw [← hq]
    exact (C.edgeDarts.apply_symm_apply k).symm
  have hef : e = f := by
    simpa [edgeOfHalfEdge, hp, hq] using hedge
  subst f
  subst h
  subst k
  cases b <;> cases c
  · exact Or.inl rfl
  · exact Or.inr (by simp [C.reverse_edgeDarts])
  · exact Or.inr (by simp [C.reverse_edgeDarts])
  · exact Or.inl rfl

/-- The certified primal adjacency attached to a non-root construction
vertex. -/
theorem RootedSpanningTree.parentAdj
    {C : SU2FiniteDiskCellulation} (T : C.RootedSpanningTree) (i : Fin T.n) :
    C.primalAdj
      (T.vertexOrder (T.order.parentIndex i))
      (T.vertexOrder (Fin.succ i)) := by
  refine ⟨?_, T.treeDart i, T.treeDart_source_cert i,
    T.treeDart_target_cert i⟩
  intro h
  have hp := T.order.parentIndex_lt_child i
  exact (Nat.ne_of_lt hp) (Fin.ext_iff.mp (T.vertexOrder.injective h))

@[simp]
theorem RootedSpanningTree.treeDart_source
    {C : SU2FiniteDiskCellulation} (T : C.RootedSpanningTree) (i : Fin T.n) :
    C.source (T.treeDart i) =
      T.vertexOrder (T.order.parentIndex i) :=
  T.treeDart_source_cert i

@[simp]
theorem RootedSpanningTree.treeDart_target
    {C : SU2FiniteDiskCellulation} (T : C.RootedSpanningTree) (i : Fin T.n) :
    C.target (T.treeDart i) = T.vertexOrder (Fin.succ i) :=
  T.treeDart_target_cert i

/-- The physical tree edge selected at a non-root construction vertex. -/
def RootedSpanningTree.treeEdge
    {C : SU2FiniteDiskCellulation} (T : C.RootedSpanningTree) (i : Fin T.n) :
    C.Edge :=
  C.edgeOfHalfEdge (T.treeDart i)

/-- Distinct non-root vertices select distinct physical tree edges.  The key
point is that a reversed collision would force a strict cycle in the
construction order. -/
theorem RootedSpanningTree.treeEdge_injective
    {C : SU2FiniteDiskCellulation} (T : C.RootedSpanningTree) :
    Function.Injective T.treeEdge := by
  intro i j hij
  rcases C.eq_or_eq_reverse_of_edgeOfHalfEdge_eq hij with hsame | hrev
  · have ht := congrArg C.target hsame
    rw [T.treeDart_target, T.treeDart_target] at ht
    exact Fin.succ_injective _ (T.vertexOrder.injective ht)
  · have hparentChild : T.order.parentIndex i = Fin.succ j := by
      apply T.vertexOrder.injective
      calc
        T.vertexOrder (T.order.parentIndex i) = C.source (T.treeDart i) := by
          simp
        _ = C.source (C.reverse (T.treeDart j)) := by rw [hrev]
        _ = C.target (T.treeDart j) := rfl
        _ = T.vertexOrder (Fin.succ j) := by simp
    have hchildParent : Fin.succ i = T.order.parentIndex j := by
      apply T.vertexOrder.injective
      calc
        T.vertexOrder (Fin.succ i) = C.target (T.treeDart i) := by simp
        _ = C.target (C.reverse (T.treeDart j)) := by rw [hrev]
        _ = C.source (T.treeDart j) := by
          exact congrArg C.source (C.reverse_involutive (T.treeDart j))
        _ = T.vertexOrder (T.order.parentIndex j) := by simp
    have hi := T.order.parentIndex_lt_child i
    have hj := T.order.parentIndex_lt_child j
    rw [hparentChild] at hi
    rw [← hchildParent] at hj
    exact (Nat.lt_asymm hi hj).elim

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
  let hadj : ∀ i : Fin n,
      C.primalAdj
        (vertexOrder (tree.parentIndex i))
        (vertexOrder (Fin.succ i)) := fun i =>
    hvalid _ (tree.parentIndex_pair_mem_parentPairs i)
  exact ⟨{
    n := n
    vertexOrder := vertexOrder
    order := tree
    treeDart := fun i => Classical.choose (hadj i).2
    treeDart_source_cert := fun i => (Classical.choose_spec (hadj i).2).1
    treeDart_target_cert := fun i => (Classical.choose_spec (hadj i).2).2 }⟩

/-- Connectedness after removing a set of physical edges supplies a rooted
spanning tree whose *stored physical darts* all avoid that set.  The explicit
dart field prevents an unrelated parallel edge from being re-selected by
classical choice downstream. -/
theorem exists_rootedSpanningTree_avoiding_of_connected
    (C : SU2FiniteDiskCellulation) (forbidden : Set C.Edge)
    (hC : (C.primalGraphAvoiding forbidden).Connected) :
    ∃ T : C.RootedSpanningTree,
      ∀ i : Fin T.n, T.treeEdge i ∉ forbidden := by
  classical
  letI : DecidableRel (C.primalGraphAvoiding forbidden).Adj :=
    Classical.decRel _
  obtain ⟨n, tree, vertexOrder, hvalid⟩ :=
    SU2RootedTreeOrder.exists_validForGraph_of_connected
      (C.primalGraphAvoiding forbidden) hC
  let hadj : ∀ i : Fin n,
      C.primalAdjAvoiding forbidden
        (vertexOrder (tree.parentIndex i))
        (vertexOrder (Fin.succ i)) := fun i =>
    hvalid _ (tree.parentIndex_pair_mem_parentPairs i)
  let T : C.RootedSpanningTree := {
    n := n
    vertexOrder := vertexOrder
    order := tree
    treeDart := fun i => Classical.choose (hadj i).2
    treeDart_source_cert := fun i => (Classical.choose_spec (hadj i).2).1
    treeDart_target_cert := fun i => (Classical.choose_spec (hadj i).2).2.1 }
  refine ⟨T, fun i => ?_⟩
  change C.edgeOfHalfEdge (Classical.choose (hadj i).2) ∉ forbidden
  exact (Classical.choose_spec (hadj i).2).2.2

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
