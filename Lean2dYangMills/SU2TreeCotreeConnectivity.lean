import Lean2dYangMills.SU2BoundaryConditionedGaugeFixing
import Lean2dYangMills.SU2PhysicalEliminationTree

/-!
# Tree--cotree connectivity for physical disk cellulations

This module supplies the geometric bridge missing from the conditioned edge
model.  A facial dart word is first treated as an explicitly typed primal
path.  Splitting the closed word at one dart and rotating the remaining
fragments gives a bypass of the corresponding physical edge.  These bypasses
will be used in construction order to delete the dual-tree edges while
preserving primal connectedness.
-/

noncomputable section

namespace Lean2dYangMills

namespace SU2FiniteDiskCellulation

/-- A list of oriented physical darts whose endpoints concatenate. -/
inductive DartPath (C : SU2FiniteDiskCellulation) :
    C.Vertex -> List C.HalfEdge -> C.Vertex -> Prop
  | nil (v : C.Vertex) : DartPath C v [] v
  | cons (h : C.HalfEdge) {w : List C.HalfEdge} {v : C.Vertex}
      (tail : DartPath C (C.target h) w v) :
      DartPath C (C.source h) (h :: w) v

namespace DartPath

variable {C : SU2FiniteDiskCellulation}

theorem append {u v w : C.Vertex} {xs ys : List C.HalfEdge}
    (p : C.DartPath u xs v) (q : C.DartPath v ys w) :
    C.DartPath u (xs ++ ys) w := by
  induction p with
  | nil => simpa using q
  | cons h tail ih =>
      simpa using DartPath.cons h (ih q)

/-- A physical dart path using only allowed edges gives reachability in the
corresponding edge-deleted primal graph.  Loop darts are harmless and are
contracted to reflexive reachability. -/
theorem reachable {u v : C.Vertex} {w : List C.HalfEdge}
    {forbidden : Set C.Edge} (p : C.DartPath u w v)
    (hallowed : ∀ h ∈ w, C.edgeOfHalfEdge h ∉ forbidden) :
    (C.primalGraphAvoiding forbidden).Reachable u v := by
  induction p with
  | nil => exact .rfl
  | @cons h w v tail ih =>
      have htail : ∀ k : C.HalfEdge, k ∈ w ->
          C.edgeOfHalfEdge k ∉ forbidden := by
        intro k hk
        exact hallowed k (by simp [hk])
      have hrest := ih htail
      by_cases heq : C.source h = C.target h
      · simpa [heq] using hrest
      · have hadj : (C.primalGraphAvoiding forbidden).Adj
            (C.source h) (C.target h) :=
          ⟨heq, h, rfl, rfl, hallowed h (by simp)⟩
        exact hadj.reachable.trans hrest

/-- Splitting a closed dart path at one distinguished dart recovers the two
typed fragments on either side of that dart. -/
theorem split_middle {u v : C.Vertex} {before after : List C.HalfEdge}
    {d : C.HalfEdge}
    (p : C.DartPath u (before ++ d :: after) v) :
    ∃ _ : C.DartPath u before (C.source d),
      C.DartPath (C.target d) after v := by
  induction before generalizing u with
  | nil =>
      cases p with
      | cons _ tail => exact ⟨DartPath.nil _, tail⟩
  | cons h before ih =>
      cases p with
      | cons _ tail =>
          obtain ⟨pb, pa⟩ := ih tail
          exact ⟨DartPath.cons h pb, pa⟩

/-- Removing one dart from a closed typed word and rotating the two remaining
fragments gives a path from its target back to its source. -/
theorem rotate_around {u : C.Vertex} {before after : List C.HalfEdge}
    {d : C.HalfEdge}
    (p : C.DartPath u (before ++ d :: after) u) :
    C.DartPath (C.target d) (after ++ before) (C.source d) := by
  obtain ⟨pb, pa⟩ := p.split_middle
  exact pa.append pb

end DartPath

/-- Expose the last dart of a finite successor orbit. -/
theorem dartWord_succ (C : SU2FiniteDiskCellulation)
    (h : C.HalfEdge) (n : Nat) :
    C.dartWord h (n + 1) =
      C.dartWord h n ++ [(C.next ^ n) h] := by
  rw [dartWord, List.ofFn_succ']
  simp only [Fin.val_castSucc, List.concat_eq_append]
  change C.dartWord h n ++ [(C.next ^ n) h] =
    C.dartWord h n ++ [(C.next ^ n) h]
  rfl

/-- The literal `next`-orbit word is a typed path between its expected
endpoints. -/
theorem dartPath_dartWord (C : SU2FiniteDiskCellulation)
    (h : C.HalfEdge) (n : Nat) :
    C.DartPath (C.source h) (C.dartWord h n)
      (C.source ((C.next ^ n) h)) := by
  induction n with
  | zero => exact DartPath.nil _
  | succ n ih =>
      have htarget : C.target ((C.next ^ n) h) =
          C.source ((C.next ^ (n + 1)) h) := by
        simpa [pow_succ'] using
          (C.next_source ((C.next ^ n) h)).symm
      have plast : C.DartPath (C.source ((C.next ^ n) h))
          [(C.next ^ n) h] (C.source ((C.next ^ (n + 1)) h)) := by
        rw [← htarget]
        exact DartPath.cons _ (DartPath.nil _)
      rw [C.dartWord_succ h n]
      exact ih.append plast

end SU2FiniteDiskCellulation

namespace SU2EdgeConnectedDiskCellulation

/-- Every certified once-around facial word is a closed typed primal path. -/
theorem dartPath_faceDartWord (P : SU2EdgeConnectedDiskCellulation)
    (f : P.connected.cellulation.Face) :
    P.connected.cellulation.DartPath
      (P.connected.cellulation.source (P.faceBoundaryStart f))
      (P.faceDartWord f)
      (P.connected.cellulation.source (P.faceBoundaryStart f)) := by
  have h := P.connected.cellulation.dartPath_dartWord
    (P.faceBoundaryStart f) (P.faceBoundaryLength f)
  simpa [faceDartWord, P.faceBoundary_closed f] using h

/-- The rest of a facial cycle bypasses a distinguished dart in every primal
graph that retains all other physical edges in the word. -/
theorem reachable_bypass_of_faceDartWord_split
    (P : SU2EdgeConnectedDiskCellulation)
    (f : P.connected.cellulation.Face)
    (d : P.connected.cellulation.HalfEdge)
    (before after : List P.connected.cellulation.HalfEdge)
    (hsplit : P.faceDartWord f = before ++ d :: after)
    (forbidden : Set P.connected.cellulation.Edge)
    (hallowed : ∀ h ∈ after ++ before,
      P.connected.cellulation.edgeOfHalfEdge h ∉ forbidden) :
    (P.connected.cellulation.primalGraphAvoiding forbidden).Reachable
      (P.connected.cellulation.target d)
      (P.connected.cellulation.source d) := by
  have hclosed := P.dartPath_faceDartWord f
  rw [hsplit] at hclosed
  exact (hclosed.rotate_around).reachable hallowed

end SU2EdgeConnectedDiskCellulation

namespace SU2DualRootedEliminationTree

variable {P : SU2EdgeConnectedDiskCellulation}
  (T : SU2DualRootedEliminationTree P)

/-- Physical dual-tree edges whose construction index is strictly below
`k`.  The definition for arbitrary naturals makes induction independent of
dependent `Fin` casts. -/
def selectedBefore (k : Nat) : Set P.connected.cellulation.Edge :=
  {e | ∃ i : Fin T.n, (i : Nat) < k ∧ T.selectedEdge i = e}

@[simp]
theorem selectedBefore_zero : T.selectedBefore 0 = ∅ := by
  ext e
  simp [selectedBefore]

theorem selectedBefore_succ (i : Fin T.n) :
    T.selectedBefore ((i : Nat) + 1) =
      Set.insert (T.selectedEdge i) (T.selectedBefore (i : Nat)) := by
  ext e
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases hji : j = i
    · subst j
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨j, by omega, rfl⟩
  · intro he
    rcases Set.mem_insert_iff.mp he with rfl | he
    · exact ⟨i, by omega, rfl⟩
    · rcases he with ⟨j, hj, rfl⟩
      exact ⟨j, by omega, rfl⟩

theorem selectedBefore_n :
    T.selectedBefore T.n = Set.range T.selectedEdge := by
  ext e
  constructor
  · rintro ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩

/-- The non-selected fragments of the newly adjoined face contain no physical
edge selected at an earlier construction step. -/
theorem second_fragments_avoid_selectedBefore (i : Fin T.n) :
    ∀ k ∈ (T.merge i).secondAfter ++ (T.merge i).secondBefore,
      P.connected.cellulation.edgeOfHalfEdge k ∉
        T.selectedBefore (i : Nat) := by
  intro k hk hmem
  rcases hmem with ⟨j, hji, hedge⟩
  let Mi := T.merge i
  let Mj := T.merge j
  have hkmem : k ∈
      P.faceDartWord (T.faceOrder (Fin.succ i)) := by
    rw [Mi.second_word]
    simp only [List.mem_append, List.mem_cons]
    rcases List.mem_append.mp hk with hka | hkb
    · exact Or.inr (Or.inr hka)
    · exact Or.inl hkb
  have hkface := P.face_of_mem_faceDartWord
    (T.faceOrder (Fin.succ i)) k hkmem
  have hedge' :
      P.connected.cellulation.edgeOfHalfEdge k =
        P.connected.cellulation.edgeOfHalfEdge Mj.dart := by
    simpa [SU2DualRootedEliminationTree.selectedEdge, Mj] using hedge.symm
  rcases P.connected.cellulation.eq_or_eq_reverse_of_edgeOfHalfEdge_eq
      hedge' with hsame | hrev
  · rw [hsame, Mj.dart_face] at hkface
    have hidx : T.order.parentIndex j = Fin.succ i :=
      T.faceOrder.injective (Option.some.inj hkface)
    have hval : (T.order.parentIndex j : Nat) = (i : Nat) + 1 := by
      simpa using congrArg Fin.val hidx
    have hp : (T.order.parentIndex j : Nat) < (j : Nat) + 1 := by
      simpa using T.order.parentIndex_lt_child j
    omega
  · rw [hrev, Mj.reverse_face] at hkface
    have hidx : Fin.succ j = Fin.succ i :=
      T.faceOrder.injective (Option.some.inj hkface)
    have hjiEq : j = i := Fin.succ_injective _ hidx
    exact (Nat.ne_of_lt hji) (congrArg Fin.val hjiEq)

/-- The rotated remainder of the child face avoids both the current physical
dual-tree edge and every earlier selected edge. -/
theorem second_fragments_avoid_selectedThrough (i : Fin T.n) :
    ∀ k ∈ (T.merge i).secondAfter ++ (T.merge i).secondBefore,
      P.connected.cellulation.edgeOfHalfEdge k ∉
        Set.insert (T.selectedEdge i) (T.selectedBefore (i : Nat)) := by
  intro k hk hmem
  rcases Set.mem_insert_iff.mp hmem with hcurrent | hbefore
  · exact (T.merge i).second_fragments_avoid_edge (T.parent_adj i).1
      k (by
        rcases List.mem_append.mp hk with hka | hkb
        · exact List.mem_append_right _ hka
        · exact List.mem_append_left _ hkb) hcurrent
  · exact T.second_fragments_avoid_selectedBefore i k hk hbefore

/-- The remainder of the newly adjoined face bypasses the current dual-tree
edge after every edge through the current construction step is forbidden. -/
theorem selectedEdge_bypass (i : Fin T.n) :
    (P.connected.cellulation.primalGraphAvoiding
      (Set.insert (T.selectedEdge i) (T.selectedBefore (i : Nat)))).Reachable
        (P.connected.cellulation.source (T.merge i).dart)
        (P.connected.cellulation.target (T.merge i).dart) := by
  have h := P.reachable_bypass_of_faceDartWord_split
    (T.faceOrder (Fin.succ i))
    (P.connected.cellulation.reverse (T.merge i).dart)
    (T.merge i).secondBefore (T.merge i).secondAfter
    (T.merge i).second_word
    (Set.insert (T.selectedEdge i) (T.selectedBefore (i : Nat)))
    (T.second_fragments_avoid_selectedThrough i)
  change (P.connected.cellulation.primalGraphAvoiding
      (Set.insert (T.selectedEdge i) (T.selectedBefore (i : Nat)))).Reachable
    (P.connected.cellulation.source
      (P.connected.cellulation.reverse
        (P.connected.cellulation.reverse (T.merge i).dart)))
    (P.connected.cellulation.source
      (P.connected.cellulation.reverse (T.merge i).dart)) at h
  change (P.connected.cellulation.primalGraphAvoiding
      (Set.insert (T.selectedEdge i) (T.selectedBefore (i : Nat)))).Reachable
    (P.connected.cellulation.source (T.merge i).dart)
    (P.connected.cellulation.source
      (P.connected.cellulation.reverse (T.merge i).dart))
  rw [P.connected.cellulation.reverse_involutive] at h
  exact h

/-- The bypass is orientation-independent for every dart over the selected
physical edge. -/
theorem selectedEdge_orientation_bypass (i : Fin T.n)
    (h : P.connected.cellulation.HalfEdge)
    (hedge : P.connected.cellulation.edgeOfHalfEdge h = T.selectedEdge i) :
    (P.connected.cellulation.primalGraphAvoiding
      (Set.insert (T.selectedEdge i) (T.selectedBefore (i : Nat)))).Reachable
        (P.connected.cellulation.source h)
        (P.connected.cellulation.target h) := by
  have hedge' : P.connected.cellulation.edgeOfHalfEdge h =
      P.connected.cellulation.edgeOfHalfEdge (T.merge i).dart := by
    simpa [SU2DualRootedEliminationTree.selectedEdge] using hedge
  rcases P.connected.cellulation.eq_or_eq_reverse_of_edgeOfHalfEdge_eq
      hedge' with hsame | hrev
  · subst h
    exact T.selectedEdge_bypass i
  · subst h
    rw [SU2FiniteDiskCellulation.target,
      P.connected.cellulation.reverse_involutive]
    exact (T.selectedEdge_bypass i).symm

/-- Deleting the first `k` physical edges of the dual construction tree never
disconnects the primal one-skeleton. -/
theorem primalGraphAvoiding_selectedBefore_connected
    (k : Nat) (hk : k ≤ T.n) :
    (P.connected.cellulation.primalGraphAvoiding
      (T.selectedBefore k)).Connected := by
  induction k with
  | zero =>
      apply P.primal_connected.mono
      intro v w hvw
      rcases hvw with ⟨hne, h, hs, ht⟩
      exact ⟨hne, h, hs, ht, by simp [selectedBefore]⟩
  | succ k ih =>
      have hklt : k < T.n := by omega
      let i : Fin T.n := ⟨k, hklt⟩
      have hprev := ih (by omega)
      have hset : T.selectedBefore (k + 1) =
          Set.insert (T.selectedEdge i) (T.selectedBefore k) := by
        simpa [i] using T.selectedBefore_succ i
      rw [hset]
      apply P.connected.cellulation.primalGraphAvoiding_insert_connected
        (T.selectedBefore k) (T.selectedEdge i) hprev
      intro h hedge
      simpa [i] using T.selectedEdge_orientation_bypass i h hedge

/-- The complete physical dual-tree range has connected primal complement. -/
theorem primalGraphAvoiding_selectedEdgeRange_connected :
    (P.connected.cellulation.primalGraphAvoiding
      (Set.range T.selectedEdge)).Connected := by
  rw [← T.selectedBefore_n]
  exact T.primalGraphAvoiding_selectedBefore_connected T.n le_rfl

end SU2DualRootedEliminationTree

end Lean2dYangMills
