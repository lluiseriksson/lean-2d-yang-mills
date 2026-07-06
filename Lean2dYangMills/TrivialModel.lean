import Lean2dYangMills.Interfaces

/-!
# Consumer test: the trivial-group heat-kernel package, fully discharged

The trivial group with one representation label instantiates
`HeatKernelCharacterPackage` with EVERY hypothesis field a theorem, and its
`heatKernel_semigroup` proposition is stated as the genuine finite
convolution law and proved.  This has no physical content; its purpose is
doctrinal: it certifies the M0 interface is instantiable with zero carried
hypotheses, so any future difficulty lies in the mathematics, not in the
contract shape.
-/

noncomputable section

namespace Lean2dYangMills

abbrev TrivialGaugeGroup : Type :=
  PUnit

/-- The trivial character table: one label, dimension one. -/
def trivialCharacterTable : CharacterTable TrivialGaugeGroup where
  Label := Fin 1
  dim := fun _ => 1
  dim_pos := fun _ => Nat.one_pos
  char := fun _ _ => 1
  casimir := fun _ => 0
  heatWeight := fun _ _ => 1

/-- The trivial heat kernel: constantly one. -/
def trivialHeatKernel : Real -> TrivialGaugeGroup -> Complex :=
  fun _ _ => 1

/-- The finite convolution semigroup law of the trivial heat kernel, stated
as the honest proposition (not `True`). -/
def trivialConvolutionLaw : Prop :=
  ∀ (t s : Real) (g : TrivialGaugeGroup),
    (∑ x : TrivialGaugeGroup, trivialHeatKernel t x * trivialHeatKernel s (x⁻¹ * g))
      = trivialHeatKernel (t + s) g

theorem trivialConvolutionLaw_holds : trivialConvolutionLaw := by
  intro t s g
  rw [Fintype.sum_unique]
  simp [trivialHeatKernel]

/-- The trivial heat-kernel package: every field discharged. -/
def trivialHeatKernelPackage : HeatKernelCharacterPackage TrivialGaugeGroup where
  table := trivialCharacterTable
  heatKernel := trivialHeatKernel
  heatKernel_summable := by
    intro t _ g
    haveI : Fintype trivialCharacterTable.Label := by
      unfold trivialCharacterTable
      infer_instance
    exact (hasSum_fintype (heatKernelTerm trivialCharacterTable t g)).summable
  heatKernel_eq_tsum := by
    intro t _ g
    haveI : Fintype trivialCharacterTable.Label := by
      unfold trivialCharacterTable
      infer_instance
    rw [heatKernelCharacterSeries, tsum_fintype]
    simp [trivialHeatKernel, heatKernelTerm, trivialCharacterTable]
  heatKernel_conj_invariant := fun _ _ _ => rfl
  heatKernel_semigroup := trivialConvolutionLaw

/-- The semigroup proposition carried by the trivial package is true. -/
theorem trivialHeatKernelPackage_semigroup :
    heatKernel_semigroup_statement trivialHeatKernelPackage :=
  by
    simpa [heatKernel_semigroup_statement, trivialHeatKernelPackage] using
      trivialConvolutionLaw_holds

/-- Consumer theorem: the public M0 convergence wrapper applies to the
trivial heat-kernel character series. -/
theorem trivialHeatKernelCharacterSeries_converges {t : Real} (ht : 0 < t)
    (g : TrivialGaugeGroup) :
    Summable (heatKernelTerm trivialCharacterTable t g) := by
  simpa [trivialHeatKernelPackage] using
    heatKernel_character_series_converges trivialHeatKernelPackage ht g

/-- Consumer theorem: the public M0 equality wrapper reduces the trivial
heat-kernel character series to `1`. -/
theorem trivialHeatKernelCharacterSeries_eq_one {t : Real} (ht : 0 < t)
    (g : TrivialGaugeGroup) :
    heatKernelCharacterSeries trivialCharacterTable t g = 1 := by
  have h := heatKernel_character_series_eq trivialHeatKernelPackage ht g
  simpa [trivialHeatKernelPackage, trivialHeatKernel] using h.symm

/-- Consumer theorem: the public M0 conjugation-invariance wrapper applies to
the trivial heat kernel. -/
theorem trivialHeatKernel_conj_invariant {t : Real} (ht : 0 < t)
    (x g : TrivialGaugeGroup) :
    trivialHeatKernel t (x * g * x⁻¹) = trivialHeatKernel t g := by
  simpa [trivialHeatKernelPackage] using
    heatKernel_conj_invariant trivialHeatKernelPackage ht x g

/-- The one-loop zero-area planar theory: the Wilson expectation is constantly
one and the string tension is zero.  This is a consumer test for the M2
area-law interface only, not a physical plane-loop construction. -/
def trivialPlaneSimpleLoopTheory : PlaneSimpleLoopTheory where
  Loop := PUnit
  area := fun _ => 0
  wilsonExpectation := fun _ => 1
  stringTension := 0

/-- The trivial exact-area-law package: every field is discharged. -/
def trivialExactAreaLawPackage : ExactAreaLawPackage trivialPlaneSimpleLoopTheory where
  area_nonnegative := by
    intro C
    simp [trivialPlaneSimpleLoopTheory]
  stringTension_nonnegative := by
    simp [trivialPlaneSimpleLoopTheory]
  wilson_eq_areaLaw := by
    intro C
    simp [trivialPlaneSimpleLoopTheory, areaLawValue]

/-- Consumer theorem: in the trivial area-law model, the public M2 wrapper
returns Wilson expectation `1`. -/
theorem trivialSimpleLoop_areaLaw_exact (C : trivialPlaneSimpleLoopTheory.Loop) :
    trivialPlaneSimpleLoopTheory.wilsonExpectation C = 1 := by
  have h := simpleLoop_areaLaw_exact trivialExactAreaLawPackage C
  simpa [trivialExactAreaLawPackage, trivialPlaneSimpleLoopTheory, areaLawValue] using h

/-- Consumer theorem: the public M2 string-tension wrapper returns
nonnegativity for the trivial exact-area-law package. -/
theorem trivialSimpleLoop_stringTension_nonnegative :
    0 <= trivialPlaneSimpleLoopTheory.stringTension := by
  simpa [trivialExactAreaLawPackage, trivialPlaneSimpleLoopTheory] using
    simpleLoop_stringTension_nonnegative trivialExactAreaLawPackage

/-- Consumer theorem: the trivial exact-area-law package also discharges the
explicit nonnegative-area hypothesis for its only loop model. -/
theorem trivialSimpleLoop_area_nonnegative (C : trivialPlaneSimpleLoopTheory.Loop) :
    0 <= trivialPlaneSimpleLoopTheory.area C := by
  simpa [trivialExactAreaLawPackage, trivialPlaneSimpleLoopTheory] using
    trivialExactAreaLawPackage.area_nonnegative C

/-- Consumer theorem: the public zero-area area-law API lemma reduces the
trivial model's area-law value to `1`. -/
theorem trivialAreaLawValue_zero_area (C : trivialPlaneSimpleLoopTheory.Loop) :
    areaLawValue trivialPlaneSimpleLoopTheory C = 1 :=
  areaLawValue_zero_area trivialPlaneSimpleLoopTheory (by simp [trivialPlaneSimpleLoopTheory])

end Lean2dYangMills
