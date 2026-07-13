import Lean2dYangMills.SU2PlanarReduction
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Independent finite cellulations and elimination schedules

This module separates finite combinatorial cellulation data from the binary
syntax used to evaluate iterated Migdal integrals.  A cellulation carries finite
vertices, edges, half-edges, faces, edge reversal, oriented face-boundary
successor, the disk Euler relation, and positive face areas.  Its dual graph is
derived from the two faces incident to an internal edge.

An elimination schedule is a separately defined labelled binary tree.  Its
validity requires that it enumerate every face exactly once and that every
binary merge cross an actual dual adjacency.  Any valid schedule reduces to
the heat kernel at the total cellulation area, so the resulting amplitude is
independent of the valid schedule chosen.

For every connected finite dual graph, a valid schedule is constructed by
finite induction.  The public connected-cellulation amplitude hides that
choice and is proved equal to the result of every other valid schedule.
-/

noncomputable section

namespace Lean2dYangMills

open MeasureTheory

/-- A finite oriented combinatorial disk cellulation, independent of any
elimination tree.  `face h = none` denotes the exterior face. -/
structure SU2FiniteDiskCellulation where
  Face : Type
  Vertex : Type
  Edge : Type
  HalfEdge : Type
  [faceFintype : Fintype Face]
  [faceDecidableEq : DecidableEq Face]
  [vertexFintype : Fintype Vertex]
  [edgeFintype : Fintype Edge]
  [halfEdgeFintype : Fintype HalfEdge]
  [halfEdgeDecidableEq : DecidableEq HalfEdge]
  edgeDarts : Edge × Bool ≃ HalfEdge
  reverse : Equiv.Perm HalfEdge
  reverse_involutive : Function.Involutive reverse
  reverse_ne : ∀ h, reverse h ≠ h
  reverse_edgeDarts : ∀ e b,
    reverse (edgeDarts (e, b)) = edgeDarts (e, !b)
  source : HalfEdge -> Vertex
  face : HalfEdge -> Option Face
  next : Equiv.Perm HalfEdge
  next_source : ∀ h, source (next h) = source (reverse h)
  face_next : ∀ h, face (next h) = face h
  face_cycle : ∀ h k, face h = face k ->
    ∃ n : Nat, (next ^ n) h = k
  faceArea : Face -> Real
  faceArea_pos : ∀ f, 0 < faceArea f
  euler_disk :
    (Fintype.card Vertex : Int) - (Fintype.card Edge : Int) +
      (Fintype.card Face : Int) = 1

attribute [instance]
  SU2FiniteDiskCellulation.faceFintype
  SU2FiniteDiskCellulation.faceDecidableEq
  SU2FiniteDiskCellulation.vertexFintype
  SU2FiniteDiskCellulation.edgeFintype
  SU2FiniteDiskCellulation.halfEdgeFintype
  SU2FiniteDiskCellulation.halfEdgeDecidableEq

namespace SU2FiniteDiskCellulation

/-- Target vertex of an oriented half-edge. -/
def target (C : SU2FiniteDiskCellulation) (h : C.HalfEdge) : C.Vertex :=
  C.source (C.reverse h)

/-- Dual adjacency is witnessed by an internal half-edge whose reverse belongs
to the other face. -/
def dualAdj (C : SU2FiniteDiskCellulation) (f g : C.Face) : Prop :=
  f ≠ g ∧ ∃ h : C.HalfEdge,
    C.face h = some f ∧ C.face (C.reverse h) = some g

theorem dualAdj_symm (C : SU2FiniteDiskCellulation) {f g : C.Face} :
    C.dualAdj f g -> C.dualAdj g f := by
  rintro ⟨hfg, h, hhf, hhg⟩
  refine ⟨Ne.symm hfg, C.reverse h, hhg, ?_⟩
  simpa [C.reverse_involutive h] using hhf

/-- The face-dual simple graph derived from the incidence data. -/
def dualGraph (C : SU2FiniteDiskCellulation) : SimpleGraph C.Face where
  Adj := C.dualAdj
  symm := by
    intro f g
    exact C.dualAdj_symm
  loopless := ⟨by
    intro f h
    exact h.1 rfl⟩

/-- Sum of all bounded-face areas. -/
def totalArea (C : SU2FiniteDiskCellulation) : Real :=
  ∑ f : C.Face, C.faceArea f

theorem totalArea_pos (C : SU2FiniteDiskCellulation) [Nonempty C.Face] :
    0 < C.totalArea := by
  exact Finset.sum_pos' (fun f _ => (C.faceArea_pos f).le)
    ⟨Classical.choice inferInstance, Finset.mem_univ _, C.faceArea_pos _⟩

end SU2FiniteDiskCellulation

/-- A labelled binary schedule for eliminating all bounded faces.  This syntax
is independent of the combinatorial cellulation. -/
inductive SU2FaceEliminationSchedule (F : Type) where
  | leaf (face : F)
  | merge (left right : SU2FaceEliminationSchedule F)

namespace SU2FaceEliminationSchedule

def leafList {F : Type} : SU2FaceEliminationSchedule F -> List F
  | .leaf f => [f]
  | .merge left right => left.leafList ++ right.leafList

/-- Relabel every leaf of a schedule. -/
def map {F F' : Type} (f : F -> F') :
    SU2FaceEliminationSchedule F -> SU2FaceEliminationSchedule F'
  | .leaf x => .leaf (f x)
  | .merge left right => .merge (left.map f) (right.map f)

@[simp] theorem leafList_map {F F' : Type} (f : F -> F')
    (S : SU2FaceEliminationSchedule F) :
    (S.map f).leafList = S.leafList.map f := by
  induction S with
  | leaf => rfl
  | merge left right hleft hright =>
      simp [map, leafList, hleft, hright]

/-- Local schedule validity relative to an arbitrary face-adjacency graph. -/
def locallyValidGraph {F : Type} (G : SimpleGraph F) :
    SU2FaceEliminationSchedule F -> Prop
  | .leaf _ => True
  | .merge left right =>
      left.locallyValidGraph G ∧ right.locallyValidGraph G ∧
        ∃ f ∈ left.leafList, ∃ g ∈ right.leafList,
          G.Adj f g

def locallyValid (C : SU2FiniteDiskCellulation)
    (S : SU2FaceEliminationSchedule C.Face) : Prop :=
  S.locallyValidGraph C.dualGraph

theorem locallyValidGraph_map {F F' : Type}
    {G : SimpleGraph F} {G' : SimpleGraph F'}
    (f : F -> F') (hadj : ∀ {u v}, G.Adj u v -> G'.Adj (f u) (f v))
    {S : SU2FaceEliminationSchedule F} (hS : S.locallyValidGraph G) :
    (S.map f).locallyValidGraph G' := by
  induction S with
  | leaf x => trivial
  | merge left right hleft hright =>
      rcases hS with ⟨hl, hr, u, hu, v, hv, huv⟩
      refine ⟨hleft hl, hright hr, f u, ?_, f v, ?_, hadj huv⟩
      · simpa using List.mem_map_of_mem hu
      · simpa using List.mem_map_of_mem hv

/-- A valid schedule merges only adjacent face blocks and lists every face
exactly once.  The permutation formulation simultaneously supplies coverage
and absence of duplicates. -/
structure ValidFor (C : SU2FiniteDiskCellulation)
    (S : SU2FaceEliminationSchedule C.Face) : Prop where
  locally_valid : S.locallyValid C
  enumerates_faces : S.leafList.Perm Finset.univ.toList

/-- Every finite connected face-adjacency graph admits a binary elimination
schedule.  The proof removes a vertex whose complement remains connected,
recurses on the induced graph, and finally reattaches the removed face across
one genuine adjacency. -/
theorem exists_schedule_of_connected_graph {F : Type}
    [Fintype F] [DecidableEq F] (G : SimpleGraph F)
    [DecidableRel G.Adj] (hG : G.Connected) :
    ∃ S : SU2FaceEliminationSchedule F,
      S.locallyValidGraph G ∧ S.leafList.Perm Finset.univ.toList := by
  classical
  let P : ∀ (α : Type) [Fintype α], Prop := fun α _ =>
    ∀ (_ : DecidableEq α) (H : SimpleGraph α) (_ : DecidableRel H.Adj),
      H.Connected -> ∃ S : SU2FaceEliminationSchedule α,
        S.locallyValidGraph H ∧ S.leafList.Perm Finset.univ.toList
  have hPF : P F := Fintype.induction_subsingleton_or_nontrivial (P := P) F (by
    intro α inst hsub
    intro _ H _ hH
    letI : Nonempty α := hH.nonempty
    let x : α := Classical.choice inferInstance
    refine ⟨.leaf x, trivial, ?_⟩
    have huniv : (Finset.univ : Finset α) = {x} := by
      ext y
      simp [Subsingleton.elim y x]
    rw [huniv]
    simp [leafList]) (by
    intro α inst hnontrivial ih
    intro _ H _ hH
    obtain ⟨v, hconn⟩ :=
      hH.exists_connected_induce_compl_singleton_of_finite_nontrivial
    let β := ↥({v}ᶜ : Set α)
    have hcard : Fintype.card β < Fintype.card α := by
      exact Fintype.card_subtype_lt (x := v) (by simp)
    let H' : SimpleGraph β := H.induce ({v}ᶜ : Set α)
    obtain ⟨S, hSloc, hSperm⟩ := ih β hcard inferInstance H' inferInstance hconn
    let incl : β -> α := Subtype.val
    let S' : SU2FaceEliminationSchedule α := S.map incl
    have hS'loc : S'.locallyValidGraph H := by
      apply locallyValidGraph_map incl (S := S) (G := H')
      · intro u w huw
        exact huw
      · exact hSloc
    obtain ⟨u, hvu⟩ := hH.preconnected.exists_adj_of_nontrivial v
    have huv_ne : u ≠ v := hvu.ne.symm
    let u' : β := ⟨u, by simp [huv_ne]⟩
    have hu_mem : u' ∈ S.leafList := by
      rw [hSperm.mem_iff]
      simp
    have hu_mem' : u ∈ S'.leafList := by
      simpa [S', incl] using List.mem_map_of_mem hu_mem
    refine ⟨.merge S' (.leaf v), ?_, ?_⟩
    · exact ⟨hS'loc, trivial, u, hu_mem', v, by simp [leafList], hvu.symm⟩
    · have hSnodup : S.leafList.Nodup :=
        hSperm.nodup_iff.mpr
          (Finset.nodup_toList (Finset.univ : Finset β))
      have hmapnodup : S'.leafList.Nodup := by
        simpa [S', incl] using hSnodup.map Subtype.val_injective
      have hvnot : v ∉ S'.leafList := by
        intro hv
        have hv' : v ∈ S.leafList.map incl := by
          simpa [S', leafList] using hv
        rcases List.mem_map.mp hv' with ⟨w, -, hwv⟩
        exact w.property hwv
      have hmergeNodup :
          (SU2FaceEliminationSchedule.merge S' (.leaf v)).leafList.Nodup := by
        simpa [leafList] using hmapnodup.append (by simp) (by simpa using hvnot)
      apply (List.perm_ext_iff_of_nodup hmergeNodup
        (Finset.nodup_toList (Finset.univ : Finset α))).2
      · intro x
        simp only [leafList, List.mem_append, List.mem_singleton,
          Finset.mem_toList, Finset.mem_univ, iff_true]
        by_cases hx : x = v
        · exact Or.inr hx
        · left
          let x' : β := ⟨x, by simp [hx]⟩
          have hxmem : x' ∈ S.leafList := by
            rw [hSperm.mem_iff]
            simp
          simpa [S', incl] using List.mem_map_of_mem hxmem)
  exact hPF inferInstance G inferInstance hG

theorem exists_valid_schedule_of_dual_connected
    (C : SU2FiniteDiskCellulation) (hC : C.dualGraph.Connected) :
    ∃ S : SU2FaceEliminationSchedule C.Face, S.ValidFor C := by
  classical
  obtain ⟨S, hlocal, hperm⟩ :=
    exists_schedule_of_connected_graph C.dualGraph hC
  exact ⟨S, hlocal, hperm⟩

/-- Area read from the labelled leaves of a schedule. -/
def scheduledArea (C : SU2FiniteDiskCellulation)
    (S : SU2FaceEliminationSchedule C.Face) : Real :=
  (S.leafList.map C.faceArea).sum

/-- Forget labels and incidence certificates after transferring the positive
area of each scheduled face to the analytic reduction tree. -/
def toFaceTree (C : SU2FiniteDiskCellulation) :
    SU2FaceEliminationSchedule C.Face -> SU2PlanarFaceTree
  | .leaf f => .face (C.faceArea f) (C.faceArea_pos f)
  | .merge left right =>
      .glue (left.toFaceTree C) (right.toFaceTree C)

theorem totalArea_toFaceTree (C : SU2FiniteDiskCellulation)
    (S : SU2FaceEliminationSchedule C.Face) :
    (S.toFaceTree C).totalArea = S.scheduledArea C := by
  induction S with
  | leaf f => simp [toFaceTree, scheduledArea, leafList,
      SU2PlanarFaceTree.totalArea]
  | merge left right hleft hright =>
      simp [toFaceTree, scheduledArea, leafList,
        SU2PlanarFaceTree.totalArea, hleft, hright]

theorem ValidFor.scheduledArea_eq_totalArea
    {C : SU2FiniteDiskCellulation}
    {S : SU2FaceEliminationSchedule C.Face} (hS : S.ValidFor C) :
    S.scheduledArea C = C.totalArea := by
  have hp := hS.enumerates_faces.map C.faceArea
  simpa [scheduledArea, SU2FiniteDiskCellulation.totalArea] using hp.sum_eq

/-- The actual iterated Haar amplitude associated with a valid or invalid
schedule.  Validity is used only to relate the result to the independent
cellulation. -/
def amplitude (C : SU2FiniteDiskCellulation)
    (S : SU2FaceEliminationSchedule C.Face) (a b : SU2) : Complex :=
  su2PlanarCellulationAmplitude (S.toFaceTree C) a b

theorem amplitude_eq_heatKernel_scheduledArea
    (C : SU2FiniteDiskCellulation)
    (S : SU2FaceEliminationSchedule C.Face) (a b : SU2) :
    S.amplitude C a b = su2HeatKernel (S.scheduledArea C) (a * b) := by
  rw [amplitude, su2PlanarCellulationAmplitude_eq_heatKernel,
    totalArea_toFaceTree]

/-- Every valid elimination schedule yields the heat kernel at the independent
cellulation's total area. -/
theorem amplitude_eq_heatKernel_totalArea
    (C : SU2FiniteDiskCellulation)
    (S : SU2FaceEliminationSchedule C.Face) (hS : S.ValidFor C)
    (a b : SU2) :
    S.amplitude C a b = su2HeatKernel C.totalArea (a * b) := by
  rw [amplitude_eq_heatKernel_scheduledArea, hS.scheduledArea_eq_totalArea]

/-- **Schedule independence.** Any two valid edge-elimination schedules for
the same independent cellulation give exactly the same recursively integrated
amplitude. -/
theorem amplitude_eq_of_valid_schedules
    (C : SU2FiniteDiskCellulation)
    (S₁ S₂ : SU2FaceEliminationSchedule C.Face)
    (h₁ : S₁.ValidFor C) (h₂ : S₂.ValidFor C) (a b : SU2) :
    S₁.amplitude C a b = S₂.amplitude C a b := by
  rw [amplitude_eq_heatKernel_totalArea C S₁ h₁,
    amplitude_eq_heatKernel_totalArea C S₂ h₂]

end SU2FaceEliminationSchedule

/-- An independently specified finite disk cellulation together with one
certified elimination schedule.  Other valid schedules are provably
equivalent by `amplitude_eq_of_valid_schedules`. -/
structure SU2ScheduledDiskCellulation where
  cellulation : SU2FiniteDiskCellulation
  schedule : SU2FaceEliminationSchedule cellulation.Face
  schedule_valid : schedule.ValidFor cellulation
  face_nonempty : Nonempty cellulation.Face

namespace SU2ScheduledDiskCellulation

def area (P : SU2ScheduledDiskCellulation) : Real :=
  P.cellulation.totalArea

theorem area_pos (P : SU2ScheduledDiskCellulation) : 0 < P.area := by
  letI : Nonempty P.cellulation.Face := P.face_nonempty
  exact P.cellulation.totalArea_pos

def amplitude (P : SU2ScheduledDiskCellulation) (a b : SU2) : Complex :=
  P.schedule.amplitude P.cellulation a b

theorem amplitude_eq_heatKernel (P : SU2ScheduledDiskCellulation) (a b : SU2) :
    P.amplitude a b = su2HeatKernel P.area (a * b) :=
  P.schedule.amplitude_eq_heatKernel_totalArea P.cellulation
    P.schedule_valid a b

end SU2ScheduledDiskCellulation

/-- Fixed-label simple-loop theory on independently specified scheduled disk
cellulations. -/
def su2ScheduledDiskSimpleLoopTheory (n : Nat) : PlaneSimpleLoopTheory where
  Loop := SU2ScheduledDiskCellulation
  area := SU2ScheduledDiskCellulation.area
  wilsonExpectation := fun P =>
    ∫ g : SU2, su2NormalizedWilsonCharacter n g * P.amplitude 1 g
      ∂su2HaarProb
  stringTension := ((n : Real) * ((n : Real) + 2)) / 4

theorem su2ScheduledDisk_wilsonExpectation_eq_casimir
    (n : Nat) (P : SU2ScheduledDiskCellulation) :
    (su2ScheduledDiskSimpleLoopTheory n).wilsonExpectation P =
      ((Real.exp (-P.area *
        (((n : Real) * ((n : Real) + 2)) / 4)) : Real) : Complex) := by
  change (∫ g : SU2,
      su2NormalizedWilsonCharacter n g * P.amplitude 1 g
        ∂su2HaarProb) = _
  simp_rw [P.amplitude_eq_heatKernel]
  simp only [one_mul, su2HeatKernel]
  exact su2_exact_simpleLoop_areaLaw P.area_pos n

/-- Exact-area-law package for independently specified finite disk
cellulations equipped with any certified valid elimination schedule. -/
def su2ScheduledDiskExactAreaLawPackage (n : Nat) :
    ExactAreaLawPackage (su2ScheduledDiskSimpleLoopTheory n) where
  area_nonnegative := fun P => P.area_pos.le
  stringTension_nonnegative := by
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (by positivity)) (by norm_num)
  wilson_eq_areaLaw := by
    intro P
    rw [su2ScheduledDisk_wilsonExpectation_eq_casimir]
    rw [areaLawValue]
    change ((Real.exp (-P.area *
      (((n : Real) * ((n : Real) + 2)) / 4)) : Real) : Complex) =
        Complex.exp (((-(((n : Real) * ((n : Real) + 2)) / 4) *
          P.area : Real) : Complex))
    rw [← Complex.ofReal_exp]
    congr 2
    ring

theorem su2ScheduledDisk_simpleLoop_areaLaw_exact
    (n : Nat) (P : SU2ScheduledDiskCellulation) :
    (su2ScheduledDiskSimpleLoopTheory n).wilsonExpectation P =
      areaLawValue (su2ScheduledDiskSimpleLoopTheory n) P :=
  simpleLoop_areaLaw_exact (su2ScheduledDiskExactAreaLawPackage n) P

/-! ## Connected cellulations with schedule choice hidden

The public object below contains no elimination tree.  Connectedness of the
independently defined dual graph proves that at least one schedule exists.
Classical choice is used only to define an internal representative; the
amplitude theorem and `amplitude_eq_any_valid_schedule` prove that the answer
does not depend on that choice.  In particular no acyclicity assumption is
made on the dual graph. -/

/-- A finite disk cellulation whose independently defined dual graph is
connected.  Unlike `SU2ScheduledDiskCellulation`, this structure contains no
choice of elimination order. -/
structure SU2ConnectedDiskCellulation where
  cellulation : SU2FiniteDiskCellulation
  dual_connected : cellulation.dualGraph.Connected

namespace SU2ConnectedDiskCellulation

def area (P : SU2ConnectedDiskCellulation) : Real :=
  P.cellulation.totalArea

theorem face_nonempty (P : SU2ConnectedDiskCellulation) :
    Nonempty P.cellulation.Face :=
  P.dual_connected.nonempty

theorem area_pos (P : SU2ConnectedDiskCellulation) : 0 < P.area := by
  letI : Nonempty P.cellulation.Face := P.face_nonempty
  exact P.cellulation.totalArea_pos

/-- An internal witness supplied by connectedness.  It is deliberately not a
field of the public cellulation object. -/
noncomputable def canonicalSchedule (P : SU2ConnectedDiskCellulation) :
    SU2FaceEliminationSchedule P.cellulation.Face :=
  Classical.choose
    (SU2FaceEliminationSchedule.exists_valid_schedule_of_dual_connected
      P.cellulation P.dual_connected)

theorem canonicalSchedule_valid (P : SU2ConnectedDiskCellulation) :
    P.canonicalSchedule.ValidFor P.cellulation :=
  Classical.choose_spec
    (SU2FaceEliminationSchedule.exists_valid_schedule_of_dual_connected
      P.cellulation P.dual_connected)

/-- The cellulation amplitude, defined using an internal schedule whose choice
is observationally irrelevant. -/
noncomputable def amplitude (P : SU2ConnectedDiskCellulation)
    (a b : SU2) : Complex :=
  P.canonicalSchedule.amplitude P.cellulation a b

theorem amplitude_eq_heatKernel (P : SU2ConnectedDiskCellulation)
    (a b : SU2) :
    P.amplitude a b = su2HeatKernel P.area (a * b) :=
  P.canonicalSchedule.amplitude_eq_heatKernel_totalArea P.cellulation
    P.canonicalSchedule_valid a b

/-- Any externally supplied valid gauge-fixing/elimination schedule computes
the same amplitude as the schedule-free public object. -/
theorem amplitude_eq_any_valid_schedule
    (P : SU2ConnectedDiskCellulation)
    (S : SU2FaceEliminationSchedule P.cellulation.Face)
    (hS : S.ValidFor P.cellulation) (a b : SU2) :
    P.amplitude a b = S.amplitude P.cellulation a b := by
  exact SU2FaceEliminationSchedule.amplitude_eq_of_valid_schedules
    P.cellulation P.canonicalSchedule S P.canonicalSchedule_valid hS a b

end SU2ConnectedDiskCellulation

/-- Fixed-label simple-loop theory on connected independently specified disk
cellulations, including cellulations whose dual graph has cycles. -/
noncomputable def su2ConnectedDiskSimpleLoopTheory (n : Nat) :
    PlaneSimpleLoopTheory where
  Loop := SU2ConnectedDiskCellulation
  area := SU2ConnectedDiskCellulation.area
  wilsonExpectation := fun P =>
    ∫ g : SU2, su2NormalizedWilsonCharacter n g * P.amplitude 1 g
      ∂su2HaarProb
  stringTension := ((n : Real) * ((n : Real) + 2)) / 4

theorem su2ConnectedDisk_wilsonExpectation_eq_casimir
    (n : Nat) (P : SU2ConnectedDiskCellulation) :
    (su2ConnectedDiskSimpleLoopTheory n).wilsonExpectation P =
      ((Real.exp (-P.area *
        (((n : Real) * ((n : Real) + 2)) / 4)) : Real) : Complex) := by
  change (∫ g : SU2,
      su2NormalizedWilsonCharacter n g * P.amplitude 1 g
        ∂su2HaarProb) = _
  simp_rw [P.amplitude_eq_heatKernel]
  simp only [one_mul, su2HeatKernel]
  exact su2_exact_simpleLoop_areaLaw P.area_pos n

/-- A nontrivial exact-area-law package whose loop object contains no chosen
elimination schedule. -/
noncomputable def su2ConnectedDiskExactAreaLawPackage (n : Nat) :
    ExactAreaLawPackage (su2ConnectedDiskSimpleLoopTheory n) where
  area_nonnegative := fun P => P.area_pos.le
  stringTension_nonnegative := by
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (by positivity)) (by norm_num)
  wilson_eq_areaLaw := by
    intro P
    rw [su2ConnectedDisk_wilsonExpectation_eq_casimir]
    rw [areaLawValue]
    change ((Real.exp (-P.area *
      (((n : Real) * ((n : Real) + 2)) / 4)) : Real) : Complex) =
        Complex.exp (((-(((n : Real) * ((n : Real) + 2)) / 4) *
          P.area : Real) : Complex))
    rw [← Complex.ofReal_exp]
    congr 2
    ring

theorem su2ConnectedDisk_simpleLoop_areaLaw_exact
    (n : Nat) (P : SU2ConnectedDiskCellulation) :
    (su2ConnectedDiskSimpleLoopTheory n).wilsonExpectation P =
      areaLawValue (su2ConnectedDiskSimpleLoopTheory n) P :=
  simpleLoop_areaLaw_exact (su2ConnectedDiskExactAreaLawPackage n) P

/-- Normalization of the schedule-independent connected-cellulation
functional. -/
theorem integral_su2ConnectedDiskAmplitude_eq_one
    (P : SU2ConnectedDiskCellulation) :
    (∫ g : SU2, P.amplitude 1 g ∂su2HaarProb) = 1 := by
  have h := su2ConnectedDisk_wilsonExpectation_eq_casimir 0 P
  simpa [su2ConnectedDiskSimpleLoopTheory, su2NormalizedWilsonCharacter,
    su2CharacterChebyshev, Polynomial.Chebyshev.U_zero] using h

end Lean2dYangMills
