import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Lean2dYangMills.SU2Haar

/-!
# Concrete identification of SU(2) with the unit 3-sphere

An SU(2) matrix is uniquely determined by its first row `(a,b)`, with
`|a|²+|b|²=1`.  This file packages that elementary identification as a Lean
equivalence.  The subsequent measure-theoretic milestone is to upgrade it to
a homeomorphism and identify the pushforward of normalized Haar with the
normalized spherical measure.
-/

noncomputable section

namespace Lean2dYangMills

open Matrix

/-- The concrete complex-coordinate model of the unit 3-sphere. -/
abbrev SU2RowSphere :=
  {z : Complex × Complex // Complex.normSq z.1 + Complex.normSq z.2 = 1}

/-- The ambient real inner-product space used by Mathlib's canonical
spherical measure. -/
abbrev SU2SphereAmbient := WithLp 2 (Complex × Complex)

instance instMeasurableSpaceSU2SphereAmbient :
    MeasurableSpace SU2SphereAmbient := borel _

instance instBorelSpaceSU2SphereAmbient :
    BorelSpace SU2SphereAmbient := ⟨rfl⟩

/-- The same unit 3-sphere, now as Mathlib's metric sphere in the L2 product. -/
abbrev SU2MetricSphere := Metric.sphere (0 : SU2SphereAmbient) 1

theorem norm_toLp_complex_prod_eq_one (z : SU2RowSphere) :
    ‖WithLp.toLp 2 z.1‖ = 1 := by
  have hsquare : ‖WithLp.toLp 2 z.1‖ ^ 2 = (1 : Real) := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖z.1.1‖ ^ 2 + ‖z.1.2‖ ^ 2 = 1
    simpa [Complex.normSq_eq_norm_sq] using z.2
  nlinarith [norm_nonneg (WithLp.toLp 2 z.1)]

/-- Move the coordinate sphere into Mathlib's canonical metric-sphere type. -/
def rowSphereToMetricSphere (z : SU2RowSphere) : SU2MetricSphere :=
  ⟨WithLp.toLp 2 z.1, mem_sphere_zero_iff_norm.2
    (norm_toLp_complex_prod_eq_one z)⟩

/-- Recover complex coordinates from Mathlib's L2 metric sphere. -/
def metricSphereToRowSphere (z : SU2MetricSphere) : SU2RowSphere := by
  refine ⟨WithLp.ofLp z.1, ?_⟩
  have hnorm : ‖z.1‖ = 1 := mem_sphere_zero_iff_norm.1 z.2
  have hsquare := congrArg (fun x : Real => x ^ 2) hnorm
  dsimp at hsquare
  rw [WithLp.prod_norm_sq_eq_of_L2] at hsquare
  change Complex.normSq (WithLp.ofLp z.1).1 +
      Complex.normSq (WithLp.ofLp z.1).2 = 1
  simpa [Complex.normSq_eq_norm_sq] using hsquare

@[simp]
theorem rowSphereToMetricSphere_metricSphereToRowSphere (z : SU2MetricSphere) :
    rowSphereToMetricSphere (metricSphereToRowSphere z) = z := by
  apply Subtype.ext
  rfl

@[simp]
theorem metricSphereToRowSphere_rowSphereToMetricSphere (z : SU2RowSphere) :
    metricSphereToRowSphere (rowSphereToMetricSphere z) = z := by
  apply Subtype.ext
  rfl

/-- Algebraic equivalence with Mathlib's canonical metric sphere. -/
def rowSphereEquivMetricSphere : SU2RowSphere ≃ SU2MetricSphere where
  toFun := rowSphereToMetricSphere
  invFun := metricSphereToRowSphere
  left_inv := metricSphereToRowSphere_rowSphereToMetricSphere
  right_inv := rowSphereToMetricSphere_metricSphereToRowSphere

theorem continuous_rowSphereToMetricSphere :
    Continuous rowSphereToMetricSphere := by
  apply Continuous.subtype_mk
  exact (WithLp.prod_continuous_toLp 2 Complex Complex).comp
    continuous_subtype_val

theorem continuous_metricSphereToRowSphere :
    Continuous metricSphereToRowSphere := by
  apply Continuous.subtype_mk
  exact (WithLp.prod_continuous_ofLp 2 Complex Complex).comp
    continuous_subtype_val

/-- Homeomorphism from the coordinate model to the exact sphere type used by
`Measure.toSphere`. -/
def rowSphereHomeomorphMetricSphere : SU2RowSphere ≃ₜ SU2MetricSphere where
  toEquiv := rowSphereEquivMetricSphere
  continuous_toFun := continuous_rowSphereToMetricSphere
  continuous_invFun := continuous_metricSphereToRowSphere

instance : Nonempty SU2MetricSphere :=
  ⟨rowSphereToMetricSphere ⟨(1, 0), by simp⟩⟩

/-- Mathlib's canonical spherical measure, normalized to a probability. -/
def su2CanonicalSphereProbability :
    MeasureTheory.ProbabilityMeasure SU2MetricSphere :=
  MeasureTheory.FiniteMeasure.normalize
    (⟨(MeasureTheory.volume : MeasureTheory.Measure SU2SphereAmbient).toSphere,
      inferInstance⟩ : MeasureTheory.FiniteMeasure SU2MetricSphere)

/-- The canonical spherical probability pulled back to the complex-coordinate
model.  The live equality target is this measure versus `su2RowSphereHaar`. -/
def su2CanonicalRowSphereMeasure : MeasureTheory.Measure SU2RowSphere :=
  (su2CanonicalSphereProbability : MeasureTheory.Measure SU2MetricSphere).map
    metricSphereToRowSphere

instance : MeasureTheory.IsProbabilityMeasure su2CanonicalRowSphereMeasure := by
  constructor
  rw [su2CanonicalRowSphereMeasure, MeasureTheory.Measure.map_apply
    continuous_metricSphereToRowSphere.measurable MeasurableSet.univ]
  simp

/-- Extract the first row of an SU(2) matrix. -/
def su2ToRowSphere (g : SU2) : SU2RowSphere :=
  ⟨((g : Matrix (Fin 2) (Fin 2) Complex) 0 0,
    (g : Matrix (Fin 2) (Fin 2) Complex) 0 1), su2_normSq_row_zero g⟩

/-- Reconstruct an SU(2) matrix from a unit row `(a,b)`. -/
def rowSphereToSU2 (z : SU2RowSphere) : SU2 := by
  let a : Complex := z.1.1
  let b : Complex := z.1.2
  have hzR : Complex.normSq a + Complex.normSq b = 1 := z.2
  have hzC : a * (starRingEnd Complex) a + b * (starRingEnd Complex) b = 1 := by
    rw [starRingEnd_apply, starRingEnd_apply, Complex.star_def,
      Complex.mul_conj, Complex.mul_conj]
    exact_mod_cast hzR
  refine ⟨!![a, b; -star b, star a], ?_⟩
  rw [mem_specialUnitaryGroup_iff]
  constructor
  · rw [mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.star_eq_conjTranspose] using hzC
    · simp [Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.star_eq_conjTranspose]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.star_eq_conjTranspose]
      ring
    · simpa [Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.star_eq_conjTranspose, add_comm, mul_comm] using hzC
  · simp [Matrix.det_fin_two, Complex.mul_conj]
    exact_mod_cast hzR

@[simp]
theorem su2ToRowSphere_fst (g : SU2) :
    (su2ToRowSphere g).1.1 =
      (g : Matrix (Fin 2) (Fin 2) Complex) 0 0 := rfl

@[simp]
theorem su2ToRowSphere_snd (g : SU2) :
    (su2ToRowSphere g).1.2 =
      (g : Matrix (Fin 2) (Fin 2) Complex) 0 1 := rfl

@[simp]
theorem su2ToRowSphere_rowSphereToSU2 (z : SU2RowSphere) :
    su2ToRowSphere (rowSphereToSU2 z) = z := by
  apply Subtype.ext
  ext <;> rfl

@[simp]
theorem rowSphereToSU2_su2ToRowSphere (g : SU2) :
    rowSphereToSU2 (su2ToRowSphere g) = g := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simp [rowSphereToSU2, su2ToRowSphere]
  · simp [rowSphereToSU2, su2ToRowSphere]
  · simpa [rowSphereToSU2, su2ToRowSphere] using
      (su2_apply_one_zero_eq_neg_conj_apply_zero_one g).symm
  · simpa [rowSphereToSU2, su2ToRowSphere] using
      (su2_apply_one_one_eq_conj_apply_zero_zero g).symm

/-- Algebraic equivalence between concrete SU(2) and the complex unit
3-sphere. -/
def su2EquivRowSphere : SU2 ≃ SU2RowSphere where
  toFun := su2ToRowSphere
  invFun := rowSphereToSU2
  left_inv := rowSphereToSU2_su2ToRowSphere
  right_inv := su2ToRowSphere_rowSphereToSU2

theorem continuous_su2ToRowSphere : Continuous su2ToRowSphere := by
  apply Continuous.subtype_mk
  exact (continuous_su2_entry 0 0).prodMk (continuous_su2_entry 0 1)

theorem continuous_rowSphereToSU2 : Continuous rowSphereToSU2 := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · change Continuous (fun x : SU2RowSphere => x.1.1)
    fun_prop
  · change Continuous (fun x : SU2RowSphere => x.1.2)
    fun_prop
  · change Continuous (fun x : SU2RowSphere => -star x.1.2)
    fun_prop
  · change Continuous (fun x : SU2RowSphere => star x.1.1)
    fun_prop

/-- Topological identification of concrete SU(2) with the complex-coordinate
unit 3-sphere. -/
def su2HomeomorphRowSphere : SU2 ≃ₜ SU2RowSphere where
  toEquiv := su2EquivRowSphere
  continuous_toFun := continuous_su2ToRowSphere
  continuous_invFun := continuous_rowSphereToSU2

/-- Normalized SU(2) Haar transported to the concrete unit 3-sphere. -/
def su2RowSphereHaar : MeasureTheory.Measure SU2RowSphere :=
  su2HaarProb.map su2ToRowSphere

instance : MeasureTheory.IsProbabilityMeasure su2RowSphereHaar := by
  constructor
  rw [su2RowSphereHaar, MeasureTheory.Measure.map_apply
    continuous_su2ToRowSphere.measurable MeasurableSet.univ]
  simp

/-- The concrete SU(2)-to-sphere homeomorphism preserves Haar by definition
of the transported measure. -/
theorem measurePreserving_su2ToRowSphere :
    MeasureTheory.MeasurePreserving su2ToRowSphere su2HaarProb
      su2RowSphereHaar where
  measurable := continuous_su2ToRowSphere.measurable
  map_eq := rfl

theorem measurePreserving_rowSphereToSU2 :
    MeasureTheory.MeasurePreserving rowSphereToSU2 su2RowSphereHaar
      su2HaarProb :=
  MeasureTheory.MeasurePreserving.symm
    su2HomeomorphRowSphere.toMeasurableEquiv
    measurePreserving_su2ToRowSphere

/-- Left SU(2) action transported to the unit-row sphere. -/
def su2RowSphereLeft (h : SU2) (z : SU2RowSphere) : SU2RowSphere :=
  su2ToRowSphere (h * rowSphereToSU2 z)

/-- The transported spherical Haar probability is invariant under the full
left SU(2) action, not merely under the finite rotations used for low moments. -/
theorem measurePreserving_su2RowSphereLeft (h : SU2) :
    MeasureTheory.MeasurePreserving (su2RowSphereLeft h)
      su2RowSphereHaar su2RowSphereHaar := by
  exact measurePreserving_su2ToRowSphere.comp
    ((MeasureTheory.measurePreserving_mul_left su2HaarProb h).comp
      measurePreserving_rowSphereToSU2)

end Lean2dYangMills
