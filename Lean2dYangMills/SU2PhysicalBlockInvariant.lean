import Lean2dYangMills.SU2PhysicalEliminationIntegral

/-!
# Global word-block invariants for physical Migdal elimination

The global induction needs a compact invariant, not four cyclic fragments at
every node.  A block word is complete when it contains every dart belonging
to its source faces except darts on already eliminated physical edges.  It is
sound when it contains no dart outside that source.  This module proves that
the canonical cyclic splice preserves both properties while adding exactly
the selected physical edge to the eliminated set.
-/

noncomputable section

namespace Lean2dYangMills

namespace SU2FiniteDiskCellulation

variable (C : SU2FiniteDiskCellulation)

/-- Every source dart whose physical edge is still live occurs in `word`. -/
def WordCompleteAwayFrom (word : List C.HalfEdge)
    (source : Set C.HalfEdge) (eliminated : Set C.Edge) : Prop :=
  ∀ h, h ∈ source -> C.edgeOfHalfEdge h ∉ eliminated -> h ∈ word

/-- A word introduces no dart outside the declared source block. -/
def WordSound (word : List C.HalfEdge) (source : Set C.HalfEdge) : Prop :=
  ∀ h, h ∈ word -> h ∈ source

namespace CyclicDartWordMerge

variable {C : SU2FiniteDiskCellulation}
  {dart : C.HalfEdge} {first second : List C.HalfEdge}

/-- Completeness is stable under a physical splice.  The two source blocks
are united and the selected physical edge is added to the eliminated set. -/
theorem wordCompleteAwayFrom_spliceAt
    (hfirst : dart ∈ first) (hsecond : C.reverse dart ∈ second)
    {sourceFirst sourceSecond : Set C.HalfEdge}
    {eliminated : Set C.Edge}
    (hcompleteFirst : C.WordCompleteAwayFrom first sourceFirst eliminated)
    (hcompleteSecond : C.WordCompleteAwayFrom second sourceSecond eliminated) :
    C.WordCompleteAwayFrom (spliceAt hfirst hsecond)
      (sourceFirst ∪ sourceSecond)
      (insert (C.edgeOfHalfEdge dart) eliminated) := by
  intro k hsource hlive
  have hedge : C.edgeOfHalfEdge k ≠ C.edgeOfHalfEdge dart := by
    intro heq
    exact hlive (by simp [heq])
  have hnotEliminated : C.edgeOfHalfEdge k ∉ eliminated := by
    intro hk
    exact hlive (by simp [hk])
  rw [mem_spliceAt_iff_of_edge_ne hfirst hsecond hedge]
  rcases hsource with hsource | hsource
  · exact Or.inl (hcompleteFirst k hsource hnotEliminated)
  · exact Or.inr (hcompleteSecond k hsource hnotEliminated)

/-- Soundness is stable under splicing: every resulting dart came from one
of the two input words and hence from the corresponding source block. -/
theorem wordSound_spliceAt
    (hfirst : dart ∈ first) (hsecond : C.reverse dart ∈ second)
    {sourceFirst sourceSecond : Set C.HalfEdge}
    (hsoundFirst : C.WordSound first sourceFirst)
    (hsoundSecond : C.WordSound second sourceSecond) :
    C.WordSound (spliceAt hfirst hsecond)
      (sourceFirst ∪ sourceSecond) := by
  intro k hk
  have hk' :=
    (ofMem hfirst hsecond).mem_first_or_second_of_mem_mergedWord hk
  rcases hk' with hkfirst | hksecond
  · exact Or.inl (hsoundFirst k hkfirst)
  · exact Or.inr (hsoundSecond k hksecond)

end CyclicDartWordMerge

end SU2FiniteDiskCellulation

end Lean2dYangMills
