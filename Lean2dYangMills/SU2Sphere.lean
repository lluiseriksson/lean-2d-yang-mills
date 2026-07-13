import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
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

open Matrix Set Function Metric MeasurableSpace
open scoped Pointwise ENNReal NNReal

/-- The open unit cone over a measurable subset of the unit sphere is
measurable in the ambient normed space. -/
theorem measurableSet_unitSphereCone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) :
    MeasurableSet (Ioo (0 : ℝ) 1 •
      ((fun z : sphere (0 : E) 1 => (z : E)) '' s)) := by
  let r : Ioi (0 : ℝ) := ⟨1, mem_Ioi.2 one_pos⟩
  have hpre : MeasurableSet
      (homeomorphUnitSphereProd E ⁻¹' (s ×ˢ Iio r)) :=
    (homeomorphUnitSphereProd E).measurable (hs.prod measurableSet_Iio)
  have himage : MeasurableSet
      ((fun x : {x : E // x ∈ ({0} : Set E)ᶜ} => (x : E)) ''
        (homeomorphUnitSphereProd E ⁻¹' (s ×ˢ Iio r))) :=
    (MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl).measurableSet_image'
      hpre
  have hset :
      ((fun x : {x : E // x ∈ ({0} : Set E)ᶜ} => (x : E)) ''
          (homeomorphUnitSphereProd E ⁻¹' (s ×ˢ Iio r))) =
        Ioo (0 : ℝ) (r : ℝ) •
          ((fun z : sphere (0 : E) 1 => (z : E)) '' s) := by
    rw [← image2_smul, image2_image_right, ← Homeomorph.image_symm, image_image,
      ← image_subtype_val_Ioi_Iio, image2_image_left, image2_swap, ← image_prod]
    rfl
  simpa [r] using hset ▸ himage

/-- Restrict a real-linear isometric equivalence to the unit sphere. -/
def linearIsometryUnitSphereMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃ₗᵢ[ℝ] E) (z : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨L z.1, by
    rw [mem_sphere_zero_iff_norm, L.norm_map]
    exact mem_sphere_zero_iff_norm.1 z.2⟩

theorem continuous_linearIsometryUnitSphereMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃ₗᵢ[ℝ] E) : Continuous (linearIsometryUnitSphereMap L) := by
  apply Continuous.subtype_mk
  exact L.continuous.comp continuous_subtype_val

/-- Any ambient measure preserved by a real-linear isometry induces a
preserved spherical measure under `Measure.toSphere`. -/
theorem measurePreserving_linearIsometryUnitSphereMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : E ≃ₗᵢ[ℝ] E) (μ : MeasureTheory.Measure E)
    (hL : MeasureTheory.MeasurePreserving L μ μ) :
    MeasureTheory.MeasurePreserving (linearIsometryUnitSphereMap L)
      μ.toSphere μ.toSphere := by
  refine ⟨(continuous_linearIsometryUnitSphereMap L).measurable, ?_⟩
  ext s hs
  rw [MeasureTheory.Measure.map_apply
      (continuous_linearIsometryUnitSphereMap L).measurable hs,
    MeasureTheory.Measure.toSphere_apply' _
      (hs.preimage (continuous_linearIsometryUnitSphereMap L).measurable),
    MeasureTheory.Measure.toSphere_apply' _ hs]
  congr 1
  have hcone :
      L ⁻¹' (Ioo (0 : ℝ) 1 •
        ((fun z : sphere (0 : E) 1 => (z : E)) '' s)) =
      Ioo (0 : ℝ) 1 •
        ((fun z : sphere (0 : E) 1 => (z : E)) ''
          (linearIsometryUnitSphereMap L ⁻¹' s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, v, ⟨z, hzs, rfl⟩, hrz⟩
      let y : sphere (0 : E) 1 :=
        ⟨L.symm z.1, by
          rw [mem_sphere_zero_iff_norm, L.symm.norm_map]
          exact mem_sphere_zero_iff_norm.1 z.2⟩
      have hy : y ∈ linearIsometryUnitSphereMap L ⁻¹' s := by
        change linearIsometryUnitSphereMap L y ∈ s
        convert hzs using 1
        apply Subtype.ext
        simp [linearIsometryUnitSphereMap, y]
      refine ⟨r, hr, (y : E), ⟨y, hy, rfl⟩, ?_⟩
      apply L.injective
      simpa [map_smul, y] using hrz
    · rintro ⟨r, hr, v, ⟨z, hzs, rfl⟩, rfl⟩
      change L (r • (z : E)) ∈
        Ioo (0 : ℝ) 1 • ((fun z : sphere (0 : E) 1 => (z : E)) '' s)
      refine ⟨r, hr, (linearIsometryUnitSphereMap L z : E),
        ⟨linearIsometryUnitSphereMap L z, hzs, rfl⟩, ?_⟩
      simp [linearIsometryUnitSphereMap, map_smul]
  rw [← hcone]
  exact hL.measure_preimage
    (measurableSet_unitSphereCone hs).nullMeasurableSet

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

/-- The quaternionic norm identity underlying the real-orthogonal SU(2)
action on `ℂ²`. -/
theorem su2Ambient_normSq_identity (p q a b : Complex) :
    Complex.normSq (p * a - q * star b) +
        Complex.normSq (p * b + q * star a) =
      (Complex.normSq p + Complex.normSq q) *
        (Complex.normSq a + Complex.normSq b) := by
  have hbre : (star b).re = b.re := by simp
  have hbim : (star b).im = -b.im := by simp
  have hare : (star a).re = a.re := by simp
  have haim : (star a).im = -a.im := by simp
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
  rw [hbre, hbim, hare, haim]
  ring

/-- Ambient action induced by left multiplication on SU(2), written in first
row coordinates. -/
def su2AmbientLeftFun (h : SU2) (z : SU2SphereAmbient) : SU2SphereAmbient :=
  let p := (h : Matrix (Fin 2) (Fin 2) Complex) 0 0
  let q := (h : Matrix (Fin 2) (Fin 2) Complex) 0 1
  let a := (WithLp.ofLp z).1
  let b := (WithLp.ofLp z).2
  WithLp.toLp 2 (p * a - q * star b, p * b + q * star a)

/-- The ambient SU(2) action is real-linear. -/
def su2AmbientLeftLinear (h : SU2) :
    SU2SphereAmbient →ₗ[Real] SU2SphereAmbient where
  toFun := su2AmbientLeftFun h
  map_add' x y := by
    apply WithLp.ofLp_injective
    ext <;> simp [su2AmbientLeftFun]
    <;> ring
  map_smul' c x := by
    apply WithLp.ofLp_injective
    ext
    · simp [su2AmbientLeftFun]
      change
        (h : Matrix (Fin 2) (Fin 2) Complex) 0 0 *
              ((c : Complex) * (WithLp.ofLp x).1) -
            (h : Matrix (Fin 2) (Fin 2) Complex) 0 1 *
              ((c : Complex) * star (WithLp.ofLp x).2) =
          (c : Complex) *
            ((h : Matrix (Fin 2) (Fin 2) Complex) 0 0 * (WithLp.ofLp x).1 -
              (h : Matrix (Fin 2) (Fin 2) Complex) 0 1 * star (WithLp.ofLp x).2)
      ring
    · simp [su2AmbientLeftFun]
      rw [mul_smul_comm, mul_smul_comm]

theorem norm_su2AmbientLeftFun (h : SU2) (z : SU2SphereAmbient) :
    ‖su2AmbientLeftFun h z‖ = ‖z‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change
    ‖(h : Matrix (Fin 2) (Fin 2) Complex) 0 0 * (WithLp.ofLp z).1 -
        (h : Matrix (Fin 2) (Fin 2) Complex) 0 1 * star (WithLp.ofLp z).2‖ ^ 2 +
      ‖(h : Matrix (Fin 2) (Fin 2) Complex) 0 0 * (WithLp.ofLp z).2 +
        (h : Matrix (Fin 2) (Fin 2) Complex) 0 1 * star (WithLp.ofLp z).1‖ ^ 2 =
      ‖(WithLp.ofLp z).1‖ ^ 2 + ‖(WithLp.ofLp z).2‖ ^ 2
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  rw [su2Ambient_normSq_identity, su2_normSq_row_zero]
  ring

/-- The induced ambient action as a real-linear isometry. -/
def su2AmbientLeftLinearIsometry (h : SU2) :
    SU2SphereAmbient →ₗᵢ[Real] SU2SphereAmbient :=
  ⟨su2AmbientLeftLinear h, norm_su2AmbientLeftFun h⟩

/-- Finite dimensionality upgrades the ambient isometry to an isometric
equivalence. -/
def su2AmbientLeftLinearIsometryEquiv (h : SU2) :
    SU2SphereAmbient ≃ₗᵢ[Real] SU2SphereAmbient :=
  (su2AmbientLeftLinearIsometry h).toLinearIsometryEquiv rfl

/-- Restriction of the ambient real-linear isometry to the canonical metric
sphere. -/
def su2MetricSphereLeft (h : SU2) (z : SU2MetricSphere) : SU2MetricSphere :=
  ⟨su2AmbientLeftFun h z.1, by
    rw [mem_sphere_zero_iff_norm, norm_su2AmbientLeftFun]
    exact mem_sphere_zero_iff_norm.1 z.2⟩

theorem su2MetricSphereLeft_eq_linearIsometryUnitSphereMap (h : SU2) :
    su2MetricSphereLeft h =
      linearIsometryUnitSphereMap (su2AmbientLeftLinearIsometryEquiv h) := by
  rfl

/-- The unnormalized canonical spherical measure is invariant under the full
ambient SU(2) action. -/
theorem measurePreserving_su2MetricSphereLeft_toSphere (h : SU2) :
    MeasureTheory.MeasurePreserving (su2MetricSphereLeft h)
      (MeasureTheory.volume : MeasureTheory.Measure SU2SphereAmbient).toSphere
      (MeasureTheory.volume : MeasureTheory.Measure SU2SphereAmbient).toSphere := by
  rw [su2MetricSphereLeft_eq_linearIsometryUnitSphereMap]
  exact measurePreserving_linearIsometryUnitSphereMap
    (su2AmbientLeftLinearIsometryEquiv h) MeasureTheory.volume
    (LinearIsometryEquiv.measurePreserving _)

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

/-- Normalization preserves the full SU(2) invariance of the canonical
spherical measure. -/
theorem measurePreserving_su2MetricSphereLeft_canonical (h : SU2) :
    MeasureTheory.MeasurePreserving (su2MetricSphereLeft h)
      (su2CanonicalSphereProbability : MeasureTheory.Measure SU2MetricSphere)
      (su2CanonicalSphereProbability : MeasureTheory.Measure SU2MetricSphere) := by
  refine ⟨(measurePreserving_su2MetricSphereLeft_toSphere h).measurable, ?_⟩
  rw [su2CanonicalSphereProbability, MeasureTheory.FiniteMeasure.normalize]
  split_ifs with hz
  · exfalso
    have hmass : MeasureTheory.FiniteMeasure.mass
        (⟨(MeasureTheory.volume : MeasureTheory.Measure SU2SphereAmbient).toSphere,
          inferInstance⟩ : MeasureTheory.FiniteMeasure SU2MetricSphere) ≠ 0 :=
      (MeasureTheory.FiniteMeasure.mass_nonzero_iff
        (⟨(MeasureTheory.volume : MeasureTheory.Measure SU2SphereAmbient).toSphere,
          inferInstance⟩ : MeasureTheory.FiniteMeasure SU2MetricSphere)).2 (by
            intro hzero
            apply MeasureTheory.Measure.toSphere_ne_zero
              (MeasureTheory.volume : MeasureTheory.Measure SU2SphereAmbient)
            simpa using congrArg
              (fun ν : MeasureTheory.FiniteMeasure SU2MetricSphere =>
                (ν : MeasureTheory.Measure SU2MetricSphere)) hzero)
    exact hmass hz
  · change MeasureTheory.Measure.map (su2MetricSphereLeft h)
        (_ • (MeasureTheory.volume : MeasureTheory.Measure SU2SphereAmbient).toSphere) =
      _ • (MeasureTheory.volume : MeasureTheory.Measure SU2SphereAmbient).toSphere
    rw [MeasureTheory.Measure.map_smul,
      (measurePreserving_su2MetricSphereLeft_toSphere h).map_eq]

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

/-- The coordinate action transported from group multiplication is exactly
the restriction of the ambient real-linear isometry. -/
theorem rowSphereToMetricSphere_su2RowSphereLeft
    (h : SU2) (z : SU2RowSphere) :
    rowSphereToMetricSphere (su2RowSphereLeft h z) =
      su2MetricSphereLeft h (rowSphereToMetricSphere z) := by
  apply Subtype.ext
  apply WithLp.ofLp_injective
  ext
  · simp [rowSphereToMetricSphere, su2MetricSphereLeft, su2AmbientLeftFun,
      su2RowSphereLeft, su2ToRowSphere, rowSphereToSU2, Matrix.mul_apply,
      Fin.sum_univ_two]
    ring
  · simp [rowSphereToMetricSphere, su2MetricSphereLeft, su2AmbientLeftFun,
      su2RowSphereLeft, su2ToRowSphere, rowSphereToSU2, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- The transported spherical Haar probability is invariant under the full
left SU(2) action, not merely under the finite rotations used for low moments. -/
theorem measurePreserving_su2RowSphereLeft (h : SU2) :
    MeasureTheory.MeasurePreserving (su2RowSphereLeft h)
      su2RowSphereHaar su2RowSphereHaar := by
  exact measurePreserving_su2ToRowSphere.comp
    ((MeasureTheory.measurePreserving_mul_left su2HaarProb h).comp
      measurePreserving_rowSphereToSU2)

theorem metricSphereToRowSphere_su2MetricSphereLeft
    (h : SU2) (z : SU2MetricSphere) :
    metricSphereToRowSphere (su2MetricSphereLeft h z) =
      su2RowSphereLeft h (metricSphereToRowSphere z) := by
  apply rowSphereEquivMetricSphere.injective
  change rowSphereToMetricSphere
      (metricSphereToRowSphere (su2MetricSphereLeft h z)) =
    rowSphereToMetricSphere
      (su2RowSphereLeft h (metricSphereToRowSphere z))
  rw [rowSphereToMetricSphere_su2RowSphereLeft]
  simp

theorem continuous_su2RowSphereLeft (h : SU2) :
    Continuous (su2RowSphereLeft h) := by
  exact continuous_su2ToRowSphere.comp
    (continuous_const.mul continuous_rowSphereToSU2)

/-- Pulling the canonical metric-sphere probability into row coordinates is
measure preserving by definition. -/
theorem measurePreserving_metricSphereToRowSphere_canonical :
    MeasureTheory.MeasurePreserving metricSphereToRowSphere
      (su2CanonicalSphereProbability : MeasureTheory.Measure SU2MetricSphere)
      su2CanonicalRowSphereMeasure := by
  exact ⟨continuous_metricSphereToRowSphere.measurable, rfl⟩

/-- The canonical probability in row coordinates is invariant under the
transported left SU(2) action. -/
theorem measurePreserving_su2RowSphereLeft_canonical (h : SU2) :
    MeasureTheory.MeasurePreserving (su2RowSphereLeft h)
      su2CanonicalRowSphereMeasure su2CanonicalRowSphereMeasure := by
  apply measurePreserving_metricSphereToRowSphere_canonical.of_semiconj
    (measurePreserving_su2MetricSphereLeft_canonical h)
  · intro z
    exact metricSphereToRowSphere_su2MetricSphereLeft h z
  · exact (continuous_su2RowSphereLeft h).measurable

/-- Canonical spherical probability transported back to concrete SU(2). -/
def su2CanonicalPullback : MeasureTheory.Measure SU2 :=
  su2CanonicalRowSphereMeasure.map rowSphereToSU2

instance instIsProbabilityMeasureSU2CanonicalPullback :
    MeasureTheory.IsProbabilityMeasure su2CanonicalPullback := by
  constructor
  rw [su2CanonicalPullback, MeasureTheory.Measure.map_apply
    continuous_rowSphereToSU2.measurable MeasurableSet.univ]
  simp

theorem measurePreserving_rowSphereToSU2_canonical :
    MeasureTheory.MeasurePreserving rowSphereToSU2
      su2CanonicalRowSphereMeasure su2CanonicalPullback := by
  exact ⟨continuous_rowSphereToSU2.measurable, rfl⟩

theorem rowSphereToSU2_su2RowSphereLeft
    (h : SU2) (z : SU2RowSphere) :
    rowSphereToSU2 (su2RowSphereLeft h z) = h * rowSphereToSU2 z := by
  simp [su2RowSphereLeft]

theorem measurePreserving_mul_left_su2CanonicalPullback (h : SU2) :
    MeasureTheory.MeasurePreserving (h * ·)
      su2CanonicalPullback su2CanonicalPullback := by
  apply measurePreserving_rowSphereToSU2_canonical.of_semiconj
    (measurePreserving_su2RowSphereLeft_canonical h)
  · intro z
    exact rowSphereToSU2_su2RowSphereLeft h z
  · fun_prop

instance instIsMulLeftInvariantSU2CanonicalPullback :
    su2CanonicalPullback.IsMulLeftInvariant where
  map_mul_left_eq_self h :=
    (measurePreserving_mul_left_su2CanonicalPullback h).map_eq

/-- Uniqueness of normalized Haar identifies the canonical spherical
pullback with the internally constructed SU(2) Haar probability. -/
theorem su2CanonicalPullback_eq_su2HaarProb :
    su2CanonicalPullback = su2HaarProb := by
  letI : su2HaarProb.IsHaarMeasure := by
    unfold su2HaarProb
    infer_instance
  have hscale := MeasureTheory.Measure.isMulInvariant_eq_smul_of_compactSpace
    su2CanonicalPullback su2HaarProb
  have huniv := congrArg
    (fun μ : MeasureTheory.Measure SU2 => μ Set.univ) hscale
  have hc : MeasureTheory.Measure.haarScalarFactor
      su2CanonicalPullback su2HaarProb = 1 := by
    simpa [ENNReal.smul_def] using huniv.symm
  exact hscale.trans (by
    rw [hc]
    exact one_smul NNReal su2HaarProb)

/-- The literal measure bridge: transported normalized Haar equals the
normalized canonical spherical measure on the identical row-sphere type. -/
theorem su2RowSphereHaar_eq_su2CanonicalRowSphereMeasure :
    su2RowSphereHaar = su2CanonicalRowSphereMeasure := by
  have hmap := congrArg (MeasureTheory.Measure.map su2ToRowSphere)
    su2CanonicalPullback_eq_su2HaarProb
  rw [su2CanonicalPullback,
    MeasureTheory.Measure.map_map continuous_su2ToRowSphere.measurable
      continuous_rowSphereToSU2.measurable] at hmap
  rw [show su2ToRowSphere ∘ rowSphereToSU2 = id by
    funext z
    simp, MeasureTheory.Measure.map_id] at hmap
  change su2CanonicalRowSphereMeasure = su2RowSphereHaar at hmap
  exact hmap.symm

end Lean2dYangMills
