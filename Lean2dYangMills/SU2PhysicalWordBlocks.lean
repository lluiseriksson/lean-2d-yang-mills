import Lean2dYangMills.SU2PhysicalBlockInvariant

/-!
# Physical word blocks for the global Migdal induction

A physical block remembers a finite set of original faces and one current
cyclic boundary word.  Relative to the global set of already eliminated
physical edges, the word is both complete and sound for those faces.  The
canonical cyclic splice merges two blocks, inserts exactly the selected edge
into the eliminated set, and adds their areas when the face sets are disjoint.
-/

noncomputable section

namespace Lean2dYangMills

namespace SU2EdgeConnectedDiskCellulation

variable (P : SU2EdgeConnectedDiskCellulation)

private abbrev C := P.connected.cellulation

/-- Darts belonging to at least one original face in `faces`. -/
def faceDartSource (faces : Finset P.connected.cellulation.Face) :
    Set P.connected.cellulation.HalfEdge :=
  {h | ∃ f ∈ faces, h ∈ P.faceDartWord f}

theorem faceDartSource_union
    (left right : Finset P.connected.cellulation.Face) :
    P.faceDartSource (left ∪ right) =
      P.faceDartSource left ∪ P.faceDartSource right := by
  ext h
  simp only [faceDartSource, Set.mem_setOf_eq, Finset.mem_union,
    Set.mem_union]
  constructor
  · rintro ⟨f, hf | hf, hh⟩
    · exact Or.inl ⟨f, hf, hh⟩
    · exact Or.inr ⟨f, hf, hh⟩
  · rintro (⟨f, hf, hh⟩ | ⟨f, hf, hh⟩)
    · exact ⟨f, Or.inl hf, hh⟩
    · exact ⟨f, Or.inr hf, hh⟩

theorem faceDartSource_singleton
    (f : P.connected.cellulation.Face) :
    P.faceDartSource {f} = {h | h ∈ P.faceDartWord f} := by
  ext h
  simp [faceDartSource]

/-- A current physical block in the global elimination.  Its word contains
exactly the still-live darts sourced by its original faces, up to multiplicity
and cyclic order, which are handled by the local splice theorem. -/
structure PhysicalWordBlock
    (eliminated : Set P.connected.cellulation.Edge) where
  faces : Finset P.connected.cellulation.Face
  word : List P.connected.cellulation.HalfEdge
  complete : P.connected.cellulation.WordCompleteAwayFrom word
    (P.faceDartSource faces) eliminated
  sound : P.connected.cellulation.WordSound word
    (P.faceDartSource faces)

namespace PhysicalWordBlock

variable {P : SU2EdgeConnectedDiskCellulation}
  {eliminated : Set P.connected.cellulation.Edge}

/-- A singleton face block viewed relative to any global eliminated-edge set.
Completeness only asks for still-live source darts, all of which occur in the
original facial word. -/
def singletonAt (eliminated : Set P.connected.cellulation.Edge)
    (f : P.connected.cellulation.Face) :
    P.PhysicalWordBlock eliminated where
  faces := {f}
  word := P.faceDartWord f
  complete := by
    intro h hsource _
    simpa [P.faceDartSource_singleton f] using hsource
  sound := by
    intro h hh
    simpa [P.faceDartSource_singleton f] using hh

/-- The initial singleton block before any edge has been eliminated. -/
def singleton (f : P.connected.cellulation.Face) :
    P.PhysicalWordBlock ∅ := singletonAt ∅ f

/-- Total physical area carried by a block. -/
def area (B : P.PhysicalWordBlock eliminated) : Real :=
  ∑ f ∈ B.faces, P.connected.cellulation.faceArea f

/-- Merge two current blocks along a selected dart and its reverse. -/
def merge (first second : P.PhysicalWordBlock eliminated)
    {dart : P.connected.cellulation.HalfEdge}
    (hfirst : dart ∈ first.word)
    (hsecond : P.connected.cellulation.reverse dart ∈ second.word) :
    P.PhysicalWordBlock
      (insert (P.connected.cellulation.edgeOfHalfEdge dart) eliminated) where
  faces := first.faces ∪ second.faces
  word := SU2FiniteDiskCellulation.CyclicDartWordMerge.spliceAt hfirst hsecond
  complete := by
    rw [P.faceDartSource_union]
    exact
      SU2FiniteDiskCellulation.CyclicDartWordMerge.wordCompleteAwayFrom_spliceAt
        hfirst hsecond first.complete second.complete
  sound := by
    rw [P.faceDartSource_union]
    exact SU2FiniteDiskCellulation.CyclicDartWordMerge.wordSound_spliceAt
      hfirst hsecond first.sound second.sound

@[simp] theorem merge_faces
    (first second : P.PhysicalWordBlock eliminated)
    {dart : P.connected.cellulation.HalfEdge}
    (hfirst : dart ∈ first.word)
    (hsecond : P.connected.cellulation.reverse dart ∈ second.word) :
    (merge first second hfirst hsecond).faces =
      first.faces ∪ second.faces := rfl

@[simp] theorem merge_word
    (first second : P.PhysicalWordBlock eliminated)
    {dart : P.connected.cellulation.HalfEdge}
    (hfirst : dart ∈ first.word)
    (hsecond : P.connected.cellulation.reverse dart ∈ second.word) :
    (merge first second hfirst hsecond).word =
      SU2FiniteDiskCellulation.CyclicDartWordMerge.spliceAt hfirst hsecond := rfl

/-- Blocks supported on disjoint original face sets have disjoint current
dart words.  This uses soundness and the fact that every dart has one face. -/
theorem word_disjoint_of_faces_disjoint
    (first second : P.PhysicalWordBlock eliminated)
    (hfaces : Disjoint first.faces second.faces) :
    List.Disjoint first.word second.word := by
  rw [List.disjoint_left]
  intro h hhFirst hhSecond
  obtain ⟨f, hf, hhf⟩ := first.sound h hhFirst
  obtain ⟨g, hg, hhg⟩ := second.sound h hhSecond
  have hfaceF := P.face_of_mem_faceDartWord f h hhf
  have hfaceG := P.face_of_mem_faceDartWord g h hhg
  have hfg : f = g := Option.some.inj (hfaceF.symm.trans hfaceG)
  subst g
  exact (Finset.disjoint_left.mp hfaces) hf hg

/-- Disjoint physical blocks add their face areas exactly under a splice. -/
theorem area_merge_of_disjoint
    (first second : P.PhysicalWordBlock eliminated)
    {dart : P.connected.cellulation.HalfEdge}
    (hfirst : dart ∈ first.word)
    (hsecond : P.connected.cellulation.reverse dart ∈ second.word)
    (hdisjoint : Disjoint first.faces second.faces) :
    area (merge first second hfirst hsecond) =
      area first + area second := by
  simp only [area, merge_faces]
  exact Finset.sum_union hdisjoint

end PhysicalWordBlock

end SU2EdgeConnectedDiskCellulation

end Lean2dYangMills
