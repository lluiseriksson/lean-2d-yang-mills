import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Topology.ContinuousMap.Weierstrass
import Lean2dYangMills.SU2ClassOrthogonality
import Lean2dYangMills.SU2Sphere

/-!
# The SU(2) Weyl pushforward

This file develops the live M0 theorem: the pushforward of normalized SU(2)
Haar by the half-trace coordinate is the normalized semicircle measure.  The
definitions below are concrete; no Weyl formula is carried as a hypothesis.
-/

noncomputable section

open scoped ENNReal Interval Polynomial

namespace Lean2dYangMills

open Matrix Set MeasureTheory intervalIntegral

/-- Multiplication by a complex phase as a real-linear isometric equivalence. -/
def complexPhaseLinearIsometryEquiv (theta : Real) :
    Complex ≃ₗᵢ[Real] Complex where
  toFun z := Complex.exp ((theta : Complex) * Complex.I) * z
  invFun z := Complex.exp ((-theta : Real) * Complex.I) * z
  left_inv z := by
    change Complex.exp ((-theta : Real) * Complex.I) *
      (Complex.exp ((theta : Complex) * Complex.I) * z) = z
    rw [← mul_assoc, ← Complex.exp_add]
    norm_num
  right_inv z := by
    change Complex.exp ((theta : Complex) * Complex.I) *
      (Complex.exp ((-theta : Real) * Complex.I) * z) = z
    rw [← mul_assoc, ← Complex.exp_add]
    norm_num
  map_add' x y := by ring
  map_smul' r z := by
    change Complex.exp ((theta : Complex) * Complex.I) * ((r : Complex) * z) =
      (r : Complex) * (Complex.exp ((theta : Complex) * Complex.I) * z)
    ring
  norm_map' z := by
    change ‖Complex.exp ((theta : Complex) * Complex.I) * z‖ = ‖z‖
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Rotate the first complex coordinate of the ambient `L²(ℂ × ℂ)` space. -/
def su2FirstPhaseAmbient (theta : Real) :
    SU2SphereAmbient ≃ₗᵢ[Real] SU2SphereAmbient :=
  LinearIsometryEquiv.withLpProdCongr 2
    (complexPhaseLinearIsometryEquiv theta)
    (LinearIsometryEquiv.refl Real Complex)

/-- Rotate the second complex coordinate of the ambient space. -/
def su2SecondPhaseAmbient (theta : Real) :
    SU2SphereAmbient ≃ₗᵢ[Real] SU2SphereAmbient :=
  LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.refl Real Complex)
    (complexPhaseLinearIsometryEquiv theta)

/-- Swap the coordinates `Im(a)` and `Re(b)` in `(a,b) ∈ ℂ²`. -/
def su2SwapFirstImagSecondRealFun (z : SU2SphereAmbient) : SU2SphereAmbient :=
  let a := (WithLp.ofLp z).1
  let b := (WithLp.ofLp z).2
  WithLp.toLp 2
    ({ re := a.re, im := b.re }, { re := a.im, im := b.im })

/-- The coordinate swap as an ambient real-linear isometric equivalence. -/
def su2SwapFirstImagSecondReal :
    SU2SphereAmbient ≃ₗᵢ[Real] SU2SphereAmbient where
  toFun := su2SwapFirstImagSecondRealFun
  invFun := su2SwapFirstImagSecondRealFun
  left_inv z := by
    apply WithLp.ofLp_injective
    ext <;> simp [su2SwapFirstImagSecondRealFun]
  right_inv z := by
    apply WithLp.ofLp_injective
    ext <;> simp [su2SwapFirstImagSecondRealFun]
  map_add' x y := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply Complex.ext <;> simp [su2SwapFirstImagSecondRealFun]
    · apply Complex.ext <;> simp [su2SwapFirstImagSecondRealFun]
  map_smul' r z := by
    apply WithLp.ofLp_injective
    simp only [su2SwapFirstImagSecondRealFun, WithLp.ofLp_toLp,
      WithLp.ofLp_smul]
    apply Prod.ext
    · apply Complex.ext
      · simp [(· • ·), SMul.smul]
      · simp [(· • ·), SMul.smul]
    · apply Complex.ext
      · simp [(· • ·), SMul.smul]
      · simp [(· • ·), SMul.smul]
  norm_map' z := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    change
      ‖({ re := (WithLp.ofLp z).1.re, im := (WithLp.ofLp z).2.re } : Complex)‖ ^ 2 +
          ‖({ re := (WithLp.ofLp z).1.im, im := (WithLp.ofLp z).2.im } : Complex)‖ ^ 2 =
        ‖(WithLp.ofLp z).1‖ ^ 2 + ‖(WithLp.ofLp z).2‖ ^ 2
    simp only [Complex.sq_norm, Complex.normSq_apply]
    ring

/-- The first-coordinate phase rotation restricted to the unit sphere. -/
def su2MetricSphereFirstPhase (theta : Real) :
    SU2MetricSphere -> SU2MetricSphere :=
  linearIsometryUnitSphereMap (su2FirstPhaseAmbient theta)

/-- Phase rotation of the second complex coordinate on the unit sphere. -/
def su2MetricSphereSecondPhase (theta : Real) :
    SU2MetricSphere -> SU2MetricSphere :=
  linearIsometryUnitSphereMap (su2SecondPhaseAmbient theta)

/-- The `Im(a) ↔ Re(b)` coordinate interchange on the unit sphere. -/
def su2MetricSphereSwapFirstImagSecondReal :
    SU2MetricSphere -> SU2MetricSphere :=
  linearIsometryUnitSphereMap su2SwapFirstImagSecondReal

/-- Every ambient real-linear isometry preserves the normalized canonical
spherical probability, not only the `SU(2)` action used in the measure bridge. -/
theorem measurePreserving_linearIsometryUnitSphereMap_canonical
    (L : SU2SphereAmbient ≃ₗᵢ[Real] SU2SphereAmbient) :
    MeasurePreserving (linearIsometryUnitSphereMap L)
      (su2CanonicalSphereProbability : Measure SU2MetricSphere)
      (su2CanonicalSphereProbability : Measure SU2MetricSphere) := by
  refine ⟨(continuous_linearIsometryUnitSphereMap L).measurable, ?_⟩
  rw [su2CanonicalSphereProbability, MeasureTheory.FiniteMeasure.normalize]
  split_ifs with hz
  · exfalso
    have hmass : MeasureTheory.FiniteMeasure.mass
        (⟨(volume : Measure SU2SphereAmbient).toSphere,
          inferInstance⟩ : MeasureTheory.FiniteMeasure SU2MetricSphere) ≠ 0 :=
      (MeasureTheory.FiniteMeasure.mass_nonzero_iff
        (⟨(volume : Measure SU2SphereAmbient).toSphere,
          inferInstance⟩ : MeasureTheory.FiniteMeasure SU2MetricSphere)).2 (by
            intro hzero
            apply Measure.toSphere_ne_zero (volume : Measure SU2SphereAmbient)
            simpa using congrArg
              (fun nu : MeasureTheory.FiniteMeasure SU2MetricSphere =>
                (nu : Measure SU2MetricSphere)) hzero)
    exact hmass hz
  · change Measure.map (linearIsometryUnitSphereMap L)
        (_ • (volume : Measure SU2SphereAmbient).toSphere) =
      _ • (volume : Measure SU2SphereAmbient).toSphere
    rw [Measure.map_smul,
      (measurePreserving_linearIsometryUnitSphereMap L volume
        (LinearIsometryEquiv.measurePreserving L)).map_eq]

theorem measurePreserving_su2MetricSphereFirstPhase (theta : Real) :
    MeasurePreserving (su2MetricSphereFirstPhase theta)
      (su2CanonicalSphereProbability : Measure SU2MetricSphere)
      (su2CanonicalSphereProbability : Measure SU2MetricSphere) :=
  measurePreserving_linearIsometryUnitSphereMap_canonical
    (su2FirstPhaseAmbient theta)

theorem integral_comp_linearIsometryUnitSphereMap_canonical
    (L : SU2SphereAmbient ≃ₗᵢ[Real] SU2SphereAmbient)
    (f : SU2MetricSphere -> Real) (hf : Continuous f) :
    ∫ z, f (linearIsometryUnitSphereMap L z)
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) =
      ∫ z, f z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) := by
  let mu : Measure SU2MetricSphere := su2CanonicalSphereProbability
  let T : SU2MetricSphere -> SU2MetricSphere := linearIsometryUnitSphereMap L
  have hT : MeasurePreserving T mu mu :=
    measurePreserving_linearIsometryUnitSphereMap_canonical L
  have hmap := MeasureTheory.integral_map (μ := mu)
    hT.measurable.aemeasurable
    (show AEStronglyMeasurable f (Measure.map T mu) from
      hf.aestronglyMeasurable)
  change (∫ z, f (T z) ∂mu) = ∫ z, f z ∂mu
  rw [← hmap, hT.map_eq]

/-- The real half-trace coordinate.  For the concrete SU(2) model this is the
real part of the upper-left matrix coefficient. -/
def su2HalfTrace (g : SU2) : Real :=
  ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re

theorem continuous_su2HalfTrace : Continuous su2HalfTrace := by
  exact Complex.continuous_re.comp
    ((continuous_apply_apply (0 : Fin 2) (0 : Fin 2)).comp continuous_subtype_val)

theorem su2HalfTrace_mem_Icc (g : SU2) : su2HalfTrace g ∈ Icc (-1 : Real) 1 := by
  have hnorm := su2_norm_apply_zero_zero_le_one g
  constructor
  · have hre : |su2HalfTrace g| ≤ 1 :=
      (Complex.abs_re_le_norm ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0)).trans hnorm
    linarith [neg_le_of_abs_le hre]
  · exact le_trans (le_abs_self _) <|
      (Complex.abs_re_le_norm ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0)).trans hnorm

/-- The actual half-trace marginal of normalized SU(2) Haar. -/
def su2HaarHalfTraceMeasure : Measure Real :=
  su2HaarProb.map su2HalfTrace

instance : IsProbabilityMeasure su2HaarHalfTraceMeasure := by
  constructor
  rw [su2HaarHalfTraceMeasure, Measure.map_apply continuous_su2HalfTrace.measurable MeasurableSet.univ]
  simp

/-- The first real ambient coordinate on Mathlib's canonical unit sphere. -/
def su2MetricSphereFirstReal (z : SU2MetricSphere) : Real :=
  (WithLp.ofLp z.1).1.re

/-- The imaginary companion of the first real ambient coordinate. -/
def su2MetricSphereFirstImag (z : SU2MetricSphere) : Real :=
  (WithLp.ofLp z.1).1.im

def su2MetricSphereSecondReal (z : SU2MetricSphere) : Real :=
  (WithLp.ofLp z.1).2.re

def su2MetricSphereSecondImag (z : SU2MetricSphere) : Real :=
  (WithLp.ofLp z.1).2.im

theorem continuous_su2MetricSphereFirstReal :
    Continuous su2MetricSphereFirstReal := by
  exact Complex.continuous_re.comp
    (continuous_fst.comp
      ((WithLp.prod_continuous_ofLp 2 Complex Complex).comp continuous_subtype_val))

theorem continuous_su2MetricSphereFirstImag :
    Continuous su2MetricSphereFirstImag := by
  exact Complex.continuous_im.comp
    (continuous_fst.comp
      ((WithLp.prod_continuous_ofLp 2 Complex Complex).comp continuous_subtype_val))

theorem continuous_su2MetricSphereSecondReal :
    Continuous su2MetricSphereSecondReal := by
  exact Complex.continuous_re.comp
    (continuous_snd.comp
      ((WithLp.prod_continuous_ofLp 2 Complex Complex).comp continuous_subtype_val))

theorem continuous_su2MetricSphereSecondImag :
    Continuous su2MetricSphereSecondImag := by
  exact Complex.continuous_im.comp
    (continuous_snd.comp
      ((WithLp.prod_continuous_ofLp 2 Complex Complex).comp continuous_subtype_val))

theorem su2MetricSphere_coordinate_sq_sum (z : SU2MetricSphere) :
    su2MetricSphereFirstReal z ^ 2 + su2MetricSphereFirstImag z ^ 2 +
      su2MetricSphereSecondReal z ^ 2 + su2MetricSphereSecondImag z ^ 2 = 1 := by
  have hnorm : ‖z.1‖ = 1 := mem_sphere_zero_iff_norm.1 z.2
  have hsquare := congrArg (fun r : Real => r ^ 2) hnorm
  dsimp at hsquare
  rw [WithLp.prod_norm_sq_eq_of_L2] at hsquare
  norm_num at hsquare
  change ‖(WithLp.ofLp z.1).1‖ ^ 2 + ‖(WithLp.ofLp z.1).2‖ ^ 2 = 1 at hsquare
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply] at hsquare
  simpa [su2MetricSphereFirstReal, su2MetricSphereFirstImag,
    su2MetricSphereSecondReal, su2MetricSphereSecondImag, pow_two,
    add_assoc] using hsquare

theorem su2MetricSphereFirstReal_firstPhase (theta : Real)
    (z : SU2MetricSphere) :
    su2MetricSphereFirstReal (su2MetricSphereFirstPhase theta z) =
      Real.cos theta * su2MetricSphereFirstReal z -
        Real.sin theta * su2MetricSphereFirstImag z := by
  simp [su2MetricSphereFirstReal, su2MetricSphereFirstImag,
    su2MetricSphereFirstPhase, linearIsometryUnitSphereMap,
    su2FirstPhaseAmbient, complexPhaseLinearIsometryEquiv,
    Complex.exp_ofReal_mul_I, Complex.mul_re, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re]

theorem su2MetricSphereFirstReal_secondPhase (theta : Real)
    (z : SU2MetricSphere) :
    su2MetricSphereFirstReal (su2MetricSphereSecondPhase theta z) =
      su2MetricSphereFirstReal z := by
  simp [su2MetricSphereFirstReal, su2MetricSphereSecondPhase,
    linearIsometryUnitSphereMap, su2SecondPhaseAmbient]

theorem su2MetricSphereSecondReal_secondPhase (theta : Real)
    (z : SU2MetricSphere) :
    su2MetricSphereSecondReal (su2MetricSphereSecondPhase theta z) =
      Real.cos theta * su2MetricSphereSecondReal z -
        Real.sin theta * su2MetricSphereSecondImag z := by
  simp [su2MetricSphereSecondReal, su2MetricSphereSecondImag,
    su2MetricSphereSecondPhase, linearIsometryUnitSphereMap,
    su2SecondPhaseAmbient, complexPhaseLinearIsometryEquiv,
    Complex.exp_ofReal_mul_I, Complex.mul_re, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re]

theorem su2MetricSphereFirstReal_swapFirstImagSecondReal
    (z : SU2MetricSphere) :
    su2MetricSphereFirstReal (su2MetricSphereSwapFirstImagSecondReal z) =
      su2MetricSphereFirstReal z := by
  simp [su2MetricSphereFirstReal, su2MetricSphereSwapFirstImagSecondReal,
    linearIsometryUnitSphereMap, su2SwapFirstImagSecondReal,
    su2SwapFirstImagSecondRealFun]

theorem su2MetricSphereFirstImag_swapFirstImagSecondReal
    (z : SU2MetricSphere) :
    su2MetricSphereFirstImag (su2MetricSphereSwapFirstImagSecondReal z) =
      su2MetricSphereSecondReal z := by
  simp [su2MetricSphereFirstImag, su2MetricSphereSecondReal,
    su2MetricSphereSwapFirstImagSecondReal, linearIsometryUnitSphereMap,
    su2SwapFirstImagSecondReal, su2SwapFirstImagSecondRealFun]

/-- Moments of the first real coordinate of normalized spherical measure. -/
def su2SphereCoordinateMoment (k : Nat) : Real :=
  ∫ z : SU2MetricSphere, su2MetricSphereFirstReal z ^ k
    ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)

/-- Rotational invariance turns every phase-rotated coordinate moment into the
same first-coordinate moment. -/
theorem integral_firstPhase_coordinate_pow (theta : Real) (k : Nat) :
    ∫ z : SU2MetricSphere,
        su2MetricSphereFirstReal (su2MetricSphereFirstPhase theta z) ^ k
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) =
      su2SphereCoordinateMoment k := by
  let mu : Measure SU2MetricSphere := su2CanonicalSphereProbability
  let T : SU2MetricSphere -> SU2MetricSphere := su2MetricSphereFirstPhase theta
  let f : SU2MetricSphere -> Real := fun z => su2MetricSphereFirstReal z ^ k
  have hT : MeasurePreserving T mu mu :=
    measurePreserving_su2MetricSphereFirstPhase theta
  have hf : AEStronglyMeasurable f (Measure.map T mu) := by
    exact (continuous_su2MetricSphereFirstReal.pow k).aestronglyMeasurable
  have hmap := MeasureTheory.integral_map hT.measurable.aemeasurable hf
  change (∫ z, f (T z) ∂mu) = _
  rw [← hmap, hT.map_eq]
  rfl

theorem integral_rotated_coordinate_pow (theta : Real) (k : Nat) :
    ∫ z : SU2MetricSphere,
        (Real.cos theta * su2MetricSphereFirstReal z -
          Real.sin theta * su2MetricSphereFirstImag z) ^ k
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) =
      su2SphereCoordinateMoment k := by
  rw [← integral_firstPhase_coordinate_pow theta k]
  apply MeasureTheory.integral_congr_ae
  exact ae_of_all _ fun z => by
    change (Real.cos theta * su2MetricSphereFirstReal z -
      Real.sin theta * su2MetricSphereFirstImag z) ^ k =
        su2MetricSphereFirstReal (su2MetricSphereFirstPhase theta z) ^ k
    rw [su2MetricSphereFirstReal_firstPhase]

/-- The rotated first coordinate and its first two angular derivatives. -/
def su2RotatedCoordinate (theta : Real) (z : SU2MetricSphere) : Real :=
  Real.cos theta * su2MetricSphereFirstReal z -
    Real.sin theta * su2MetricSphereFirstImag z

def su2RotatedCoordinateDeriv (theta : Real) (z : SU2MetricSphere) : Real :=
  -Real.sin theta * su2MetricSphereFirstReal z -
    Real.cos theta * su2MetricSphereFirstImag z

theorem continuous_su2RotatedCoordinate (theta : Real) :
    Continuous (su2RotatedCoordinate theta) := by
  unfold su2RotatedCoordinate
  exact (continuous_const.mul continuous_su2MetricSphereFirstReal).sub
    (continuous_const.mul continuous_su2MetricSphereFirstImag)

theorem continuous_su2RotatedCoordinateDeriv (theta : Real) :
    Continuous (su2RotatedCoordinateDeriv theta) := by
  unfold su2RotatedCoordinateDeriv
  exact (continuous_const.mul continuous_su2MetricSphereFirstReal).sub
    (continuous_const.mul continuous_su2MetricSphereFirstImag)

theorem hasDerivAt_su2RotatedCoordinate (theta : Real)
    (z : SU2MetricSphere) :
    HasDerivAt (fun t => su2RotatedCoordinate t z)
      (su2RotatedCoordinateDeriv theta z) theta := by
  simpa [su2RotatedCoordinate, su2RotatedCoordinateDeriv, mul_comm] using
    ((Real.hasDerivAt_cos theta).mul_const
      (su2MetricSphereFirstReal z)).sub
    ((Real.hasDerivAt_sin theta).mul_const
      (su2MetricSphereFirstImag z))

theorem hasDerivAt_su2RotatedCoordinateDeriv (theta : Real)
    (z : SU2MetricSphere) :
    HasDerivAt (fun t => su2RotatedCoordinateDeriv t z)
      (-su2RotatedCoordinate theta z) theta := by
  have h := ((Real.hasDerivAt_sin theta).neg.mul_const
      (su2MetricSphereFirstReal z)).sub
    ((Real.hasDerivAt_cos theta).mul_const
      (su2MetricSphereFirstImag z))
  simp only [su2RotatedCoordinate, su2RotatedCoordinateDeriv, mul_comm]
  convert h using 1
  · funext t
    simp only [Pi.neg_apply, Pi.sub_apply]
    ring
  · ring

theorem abs_su2MetricSphereFirstReal_le_one (z : SU2MetricSphere) :
    |su2MetricSphereFirstReal z| <= 1 := by
  calc
    |su2MetricSphereFirstReal z| <= ‖(WithLp.ofLp z.1).1‖ :=
      Complex.abs_re_le_norm _
    _ <= ‖z.1‖ := WithLp.norm_fst_le Complex z.1
    _ = 1 := mem_sphere_zero_iff_norm.1 z.2

theorem abs_su2MetricSphereFirstImag_le_one (z : SU2MetricSphere) :
    |su2MetricSphereFirstImag z| <= 1 := by
  calc
    |su2MetricSphereFirstImag z| <= ‖(WithLp.ofLp z.1).1‖ :=
      Complex.abs_im_le_norm _
    _ <= ‖z.1‖ := WithLp.norm_fst_le Complex z.1
    _ = 1 := mem_sphere_zero_iff_norm.1 z.2

theorem abs_su2RotatedCoordinate_le_two (theta : Real)
    (z : SU2MetricSphere) :
    |su2RotatedCoordinate theta z| <= 2 := by
  rw [su2RotatedCoordinate]
  calc
    |Real.cos theta * su2MetricSphereFirstReal z -
        Real.sin theta * su2MetricSphereFirstImag z|
        <= |Real.cos theta * su2MetricSphereFirstReal z| +
          |Real.sin theta * su2MetricSphereFirstImag z| := abs_sub _ _
    _ <= 1 * 1 + 1 * 1 := by
      simp only [abs_mul]
      gcongr
      · exact Real.abs_cos_le_one theta
      · exact abs_su2MetricSphereFirstReal_le_one z
      · exact Real.abs_sin_le_one theta
      · exact abs_su2MetricSphereFirstImag_le_one z
    _ = 2 := by norm_num

theorem abs_su2RotatedCoordinateDeriv_le_two (theta : Real)
    (z : SU2MetricSphere) :
    |su2RotatedCoordinateDeriv theta z| <= 2 := by
  simp only [su2RotatedCoordinateDeriv]
  calc
    |-Real.sin theta * su2MetricSphereFirstReal z -
        Real.cos theta * su2MetricSphereFirstImag z|
        <= |-Real.sin theta * su2MetricSphereFirstReal z| +
          |Real.cos theta * su2MetricSphereFirstImag z| := abs_sub _ _
    _ <= 1 * 1 + 1 * 1 := by
      simp only [abs_mul, abs_neg]
      gcongr
      · exact Real.abs_sin_le_one theta
      · exact abs_su2MetricSphereFirstReal_le_one z
      · exact Real.abs_cos_le_one theta
      · exact abs_su2MetricSphereFirstImag_le_one z
    _ = 2 := by norm_num

def su2RotatedPower (n : Nat) (theta : Real)
    (z : SU2MetricSphere) : Real :=
  su2RotatedCoordinate theta z ^ n

def su2RotatedPowerDeriv (n : Nat) (theta : Real)
    (z : SU2MetricSphere) : Real :=
  (n : Real) * su2RotatedCoordinate theta z ^ (n - 1) *
    su2RotatedCoordinateDeriv theta z

theorem continuous_su2RotatedPower (n : Nat) (theta : Real) :
    Continuous (su2RotatedPower n theta) := by
  exact (continuous_su2RotatedCoordinate theta).pow n

theorem continuous_su2RotatedPowerDeriv (n : Nat) (theta : Real) :
    Continuous (su2RotatedPowerDeriv n theta) := by
  unfold su2RotatedPowerDeriv
  exact (continuous_const.mul
    ((continuous_su2RotatedCoordinate theta).pow (n - 1))).mul
      (continuous_su2RotatedCoordinateDeriv theta)

theorem hasDerivAt_su2RotatedPower (n : Nat) (theta : Real)
    (z : SU2MetricSphere) :
    HasDerivAt (fun t => su2RotatedPower n t z)
      (su2RotatedPowerDeriv n theta z) theta := by
  simpa [su2RotatedPower, su2RotatedPowerDeriv, mul_assoc] using
    (hasDerivAt_su2RotatedCoordinate theta z).pow n

theorem abs_su2RotatedPower_le (n : Nat) (theta : Real)
    (z : SU2MetricSphere) :
    |su2RotatedPower n theta z| <= 2 ^ n := by
  rw [su2RotatedPower, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_su2RotatedCoordinate_le_two theta z) n

theorem abs_su2RotatedPowerDeriv_le (n : Nat) (theta : Real)
    (z : SU2MetricSphere) :
    |su2RotatedPowerDeriv n theta z| <= (n : Real) * 2 ^ n * 2 := by
  rw [su2RotatedPowerDeriv, abs_mul, abs_mul, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg n)]
  have hpow : |su2RotatedCoordinate theta z| ^ (n - 1) <= 2 ^ n := by
    calc
      |su2RotatedCoordinate theta z| ^ (n - 1) <= 2 ^ (n - 1) :=
        pow_le_pow_left₀ (abs_nonneg _)
          (abs_su2RotatedCoordinate_le_two theta z) (n - 1)
      _ <= 2 ^ n := by
        exact pow_le_pow_right₀ (a := (2 : Real))
          (by norm_num) (Nat.sub_le n 1)
  gcongr
  exact abs_su2RotatedCoordinateDeriv_le_two theta z

/-- Differentiation under normalized spherical measure for every rotated
coordinate power.  Compactness is used only through the explicit uniform
coordinate bounds above. -/
theorem hasDerivAt_integral_su2RotatedPower (n : Nat) (theta : Real) :
    HasDerivAt
      (fun t => ∫ z : SU2MetricSphere, su2RotatedPower n t z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere))
      (∫ z : SU2MetricSphere, su2RotatedPowerDeriv n theta z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) theta := by
  let mu : Measure SU2MetricSphere := su2CanonicalSphereProbability
  let C : Real := (n : Real) * 2 ^ n * 2
  have hFint : Integrable (su2RotatedPower n theta) mu := by
    refine (integrable_const (2 ^ n : Real)).mono' ?_ ?_
    · exact (continuous_su2RotatedPower n theta).aestronglyMeasurable
    · exact ae_of_all _ fun z => by
        simpa [Real.norm_eq_abs] using abs_su2RotatedPower_le n theta z
  have hCint : Integrable (fun _z : SU2MetricSphere => C) mu :=
    integrable_const C
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := mu)
    (F := fun t z => su2RotatedPower n t z)
    (F' := fun t z => su2RotatedPowerDeriv n t z)
    (bound := fun _z : SU2MetricSphere => C)
    (s := Set.univ) (x₀ := theta)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      (continuous_su2RotatedPower n t).aestronglyMeasurable)
    hFint
    (continuous_su2RotatedPowerDeriv n theta).aestronglyMeasurable
    (ae_of_all _ fun z t _ht => by
      simpa [C, Real.norm_eq_abs] using
        abs_su2RotatedPowerDeriv_le n t z)
    hCint
    (ae_of_all _ fun z t _ht => hasDerivAt_su2RotatedPower n t z)).2

def su2RotatedPowerSecondDeriv (n : Nat) (theta : Real)
    (z : SU2MetricSphere) : Real :=
  (n : Real) * (n - 1 : Nat) *
      su2RotatedCoordinate theta z ^ (n - 2) *
      su2RotatedCoordinateDeriv theta z ^ 2 -
    (n : Real) * su2RotatedCoordinate theta z ^ n

theorem continuous_su2RotatedPowerSecondDeriv (n : Nat) (theta : Real) :
    Continuous (su2RotatedPowerSecondDeriv n theta) := by
  unfold su2RotatedPowerSecondDeriv
  exact (((continuous_const.mul continuous_const).mul
    ((continuous_su2RotatedCoordinate theta).pow (n - 2))).mul
      ((continuous_su2RotatedCoordinateDeriv theta).pow 2)).sub
    (continuous_const.mul ((continuous_su2RotatedCoordinate theta).pow n))

theorem hasDerivAt_su2RotatedPowerDeriv (n : Nat) (theta : Real)
    (z : SU2MetricSphere) :
    HasDerivAt (fun t => su2RotatedPowerDeriv n t z)
      (su2RotatedPowerSecondDeriv n theta z) theta := by
  have hq := hasDerivAt_su2RotatedCoordinate theta z
  have hqd := hasDerivAt_su2RotatedCoordinateDeriv theta z
  have h := ((hq.pow (n - 1)).const_mul (n : Real)).mul hqd
  simp only [su2RotatedPowerDeriv, su2RotatedPowerSecondDeriv]
  convert h using 1
  · by_cases hn : n = 0
    · subst n
      norm_num
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      rw [show n - 1 - 1 = n - 2 by omega]
      simp only [Pi.pow_apply]
      have hpow : su2RotatedCoordinate theta z ^ (n - 1) *
          su2RotatedCoordinate theta z =
          su2RotatedCoordinate theta z ^ n := by
        rw [← pow_succ]
        congr 1
        omega
      have hpow' : su2RotatedCoordinate theta z *
          su2RotatedCoordinate theta z ^ (n - 1) =
          su2RotatedCoordinate theta z ^ n := by
        rw [mul_comm, hpow]
      have hscaled : (n : Real) * su2RotatedCoordinate theta z *
          su2RotatedCoordinate theta z ^ (n - 1) =
          (n : Real) * su2RotatedCoordinate theta z ^ n := by
        calc
          (n : Real) * su2RotatedCoordinate theta z *
              su2RotatedCoordinate theta z ^ (n - 1) =
              (n : Real) * (su2RotatedCoordinate theta z *
                su2RotatedCoordinate theta z ^ (n - 1)) := by ring
          _ = _ := by rw [hpow']
      ring_nf
      rw [hscaled]

theorem abs_su2RotatedPowerSecondDeriv_le (n : Nat) (theta : Real)
    (z : SU2MetricSphere) :
    |su2RotatedPowerSecondDeriv n theta z| <=
      (n : Real) * (n - 1 : Nat) * 2 ^ n * 4 + (n : Real) * 2 ^ n := by
  rw [su2RotatedPowerSecondDeriv]
  calc
    |(n : Real) * (n - 1 : Nat) * su2RotatedCoordinate theta z ^ (n - 2) *
          su2RotatedCoordinateDeriv theta z ^ 2 -
        (n : Real) * su2RotatedCoordinate theta z ^ n|
        <= |(n : Real) * (n - 1 : Nat) *
          su2RotatedCoordinate theta z ^ (n - 2) *
          su2RotatedCoordinateDeriv theta z ^ 2| +
          |(n : Real) * su2RotatedCoordinate theta z ^ n| := abs_sub _ _
    _ <= (n : Real) * (n - 1 : Nat) * 2 ^ n * 4 +
          (n : Real) * 2 ^ n := by
      simp only [abs_mul, abs_pow]
      rw [abs_of_nonneg (show (0 : Real) <= (n : Real) by positivity),
        abs_of_nonneg (show (0 : Real) <= ((n - 1 : Nat) : Real) by positivity)]
      have hqpow : |su2RotatedCoordinate theta z| ^ (n - 2) <= 2 ^ n := by
        calc
          |su2RotatedCoordinate theta z| ^ (n - 2) <= 2 ^ (n - 2) :=
            pow_le_pow_left₀ (abs_nonneg _)
              (abs_su2RotatedCoordinate_le_two theta z) (n - 2)
          _ <= 2 ^ n := pow_le_pow_right₀ (a := (2 : Real))
            (by norm_num) (Nat.sub_le n 2)
      have hqdpow : |su2RotatedCoordinateDeriv theta z| ^ 2 <= (4 : Real) := by
        nlinarith [sq_nonneg (2 - |su2RotatedCoordinateDeriv theta z|),
          abs_su2RotatedCoordinateDeriv_le_two theta z,
          abs_nonneg (su2RotatedCoordinateDeriv theta z)]
      have hqn : |su2RotatedCoordinate theta z| ^ n <= 2 ^ n :=
        pow_le_pow_left₀ (abs_nonneg _)
          (abs_su2RotatedCoordinate_le_two theta z) n
      gcongr

theorem hasDerivAt_integral_su2RotatedPowerDeriv (n : Nat) (theta : Real) :
    HasDerivAt
      (fun t => ∫ z : SU2MetricSphere, su2RotatedPowerDeriv n t z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere))
      (∫ z : SU2MetricSphere, su2RotatedPowerSecondDeriv n theta z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) theta := by
  let mu : Measure SU2MetricSphere := su2CanonicalSphereProbability
  let C1 : Real := (n : Real) * 2 ^ n * 2
  let C2 : Real :=
    (n : Real) * (n - 1 : Nat) * 2 ^ n * 4 + (n : Real) * 2 ^ n
  have hFint : Integrable (su2RotatedPowerDeriv n theta) mu := by
    refine (integrable_const C1).mono' ?_ ?_
    · exact (continuous_su2RotatedPowerDeriv n theta).aestronglyMeasurable
    · exact ae_of_all _ fun z => by
        simpa [C1, Real.norm_eq_abs] using
          abs_su2RotatedPowerDeriv_le n theta z
  have hCint : Integrable (fun _z : SU2MetricSphere => C2) mu :=
    integrable_const C2
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := mu)
    (F := fun t z => su2RotatedPowerDeriv n t z)
    (F' := fun t z => su2RotatedPowerSecondDeriv n t z)
    (bound := fun _z : SU2MetricSphere => C2)
    (s := Set.univ) (x₀ := theta)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      (continuous_su2RotatedPowerDeriv n t).aestronglyMeasurable)
    hFint
    (continuous_su2RotatedPowerSecondDeriv n theta).aestronglyMeasurable
    (ae_of_all _ fun z t _ht => by
      simpa [C2, Real.norm_eq_abs] using
        abs_su2RotatedPowerSecondDeriv_le n t z)
    hCint
    (ae_of_all _ fun z t _ht => hasDerivAt_su2RotatedPowerDeriv n t z)).2

theorem integral_su2RotatedPower_eq_moment (n : Nat) (theta : Real) :
    ∫ z : SU2MetricSphere, su2RotatedPower n theta z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) =
      su2SphereCoordinateMoment n := by
  simpa [su2RotatedPower, su2RotatedCoordinate] using
    integral_rotated_coordinate_pow theta n

theorem integral_su2RotatedPowerDeriv_eq_zero (n : Nat) (theta : Real) :
    ∫ z : SU2MetricSphere, su2RotatedPowerDeriv n theta z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) = 0 := by
  have hderiv := hasDerivAt_integral_su2RotatedPower n theta
  have hconst : HasDerivAt
      (fun t => ∫ z : SU2MetricSphere, su2RotatedPower n t z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) 0 theta := by
    convert hasDerivAt_const theta (su2SphereCoordinateMoment n) using 1
    funext t
    exact integral_su2RotatedPower_eq_moment n t
  exact hderiv.unique hconst

theorem integral_su2RotatedPowerSecondDeriv_eq_zero
    (n : Nat) (theta : Real) :
    ∫ z : SU2MetricSphere, su2RotatedPowerSecondDeriv n theta z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) = 0 := by
  have hderiv := hasDerivAt_integral_su2RotatedPowerDeriv n theta
  have hconst : HasDerivAt
      (fun t => ∫ z : SU2MetricSphere, su2RotatedPowerDeriv n t z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) 0 theta := by
    convert hasDerivAt_const theta (0 : Real) using 1
    funext t
    exact integral_su2RotatedPowerDeriv_eq_zero n t
  exact hderiv.unique hconst

/-- The infinitesimal plane-rotation identity at angle zero. -/
theorem integral_sphere_rotation_second_identity (n : Nat) :
    ∫ z : SU2MetricSphere,
        ((n : Real) * (n - 1 : Nat) *
            su2MetricSphereFirstReal z ^ (n - 2) *
            su2MetricSphereFirstImag z ^ 2 -
          (n : Real) * su2MetricSphereFirstReal z ^ n)
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) = 0 := by
  simpa [su2RotatedPowerSecondDeriv, su2RotatedCoordinate,
    su2RotatedCoordinateDeriv] using
      integral_su2RotatedPowerSecondDeriv_eq_zero n 0

/-- Mixed first/orthogonal coordinate moment on the canonical three-sphere. -/
def su2SphereCoordinateMixedMoment (n : Nat) : Real :=
  ∫ z : SU2MetricSphere,
      su2MetricSphereFirstReal z ^ (n - 2) *
        su2MetricSphereFirstImag z ^ 2
    ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)

theorem integral_firstReal_pow_mul_secondReal_sq (n : Nat) :
    ∫ z : SU2MetricSphere,
        su2MetricSphereFirstReal z ^ (n - 2) *
          su2MetricSphereSecondReal z ^ 2
      ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) =
      su2SphereCoordinateMixedMoment n := by
  have h := integral_comp_linearIsometryUnitSphereMap_canonical
    su2SwapFirstImagSecondReal
    (fun z : SU2MetricSphere =>
      su2MetricSphereFirstReal z ^ (n - 2) *
        su2MetricSphereFirstImag z ^ 2)
    ((continuous_su2MetricSphereFirstReal.pow (n - 2)).mul
      (continuous_su2MetricSphereFirstImag.pow 2))
  simpa [su2SphereCoordinateMixedMoment,
    su2MetricSphereFirstReal_swapFirstImagSecondReal,
    su2MetricSphereFirstImag_swapFirstImagSecondReal] using h

theorem integral_firstReal_pow_mul_secondImag_sq (n : Nat) :
    ∫ z : SU2MetricSphere,
        su2MetricSphereFirstReal z ^ (n - 2) *
          su2MetricSphereSecondImag z ^ 2
      ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) =
      su2SphereCoordinateMixedMoment n := by
  have h := integral_comp_linearIsometryUnitSphereMap_canonical
    (su2SecondPhaseAmbient (Real.pi / 2))
    (fun z : SU2MetricSphere =>
      su2MetricSphereFirstReal z ^ (n - 2) *
        su2MetricSphereSecondReal z ^ 2)
    ((continuous_su2MetricSphereFirstReal.pow (n - 2)).mul
      (continuous_su2MetricSphereSecondReal.pow 2))
  rw [integral_firstReal_pow_mul_secondReal_sq n] at h
  change (∫ z : SU2MetricSphere,
      su2MetricSphereFirstReal
          (su2MetricSphereSecondPhase (Real.pi / 2) z) ^ (n - 2) *
        su2MetricSphereSecondReal
          (su2MetricSphereSecondPhase (Real.pi / 2) z) ^ 2
      ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) =
    su2SphereCoordinateMixedMoment n at h
  simpa [su2MetricSphereFirstReal_secondPhase,
    su2MetricSphereSecondReal_secondPhase] using h

theorem integrable_continuous_canonicalSphere
    {f : SU2MetricSphere -> Real} (hf : Continuous f) :
    Integrable f
      (su2CanonicalSphereProbability : Measure SU2MetricSphere) := by
  simpa only [integrableOn_univ] using
    hf.continuousOn.integrableOn_compact (K := Set.univ) isCompact_univ

/-- The infinitesimal rotation identity, separated into the pure and mixed
moments. -/
theorem su2SphereCoordinateMoment_rotation_balance (n : Nat) :
    (n : Real) * (n - 1 : Nat) * su2SphereCoordinateMixedMoment n -
        (n : Real) * su2SphereCoordinateMoment n = 0 := by
  let mu : Measure SU2MetricSphere := su2CanonicalSphereProbability
  let f : SU2MetricSphere -> Real := fun z =>
    su2MetricSphereFirstReal z ^ (n - 2) *
      su2MetricSphereFirstImag z ^ 2
  let g : SU2MetricSphere -> Real := fun z =>
    su2MetricSphereFirstReal z ^ n
  have hf : Integrable f mu := integrable_continuous_canonicalSphere
    ((continuous_su2MetricSphereFirstReal.pow (n - 2)).mul
      (continuous_su2MetricSphereFirstImag.pow 2))
  have hg : Integrable g mu := integrable_continuous_canonicalSphere
    (continuous_su2MetricSphereFirstReal.pow n)
  have hsplit :
      (∫ z, ((n : Real) * (n - 1 : Nat)) * f z - (n : Real) * g z ∂mu) =
        (n : Real) * (n - 1 : Nat) * (∫ z, f z ∂mu) -
          (n : Real) * (∫ z, g z ∂mu) := by
    rw [integral_sub (hf.const_mul _) (hg.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  change
    (n : Real) * (n - 1 : Nat) * (∫ z, f z ∂mu) -
      (n : Real) * (∫ z, g z ∂mu) = 0
  rw [← hsplit]
  simpa [mu, f, g, mul_assoc] using
    integral_sphere_rotation_second_identity n

/-- The sphere equation and coordinate symmetry decompose the lower pure
moment into one pure and three equal mixed moments. -/
theorem su2SphereCoordinateMoment_decomposition (n : Nat) (hn : 2 <= n) :
    su2SphereCoordinateMoment (n - 2) =
      su2SphereCoordinateMoment n + 3 * su2SphereCoordinateMixedMoment n := by
  let mu : Measure SU2MetricSphere := su2CanonicalSphereProbability
  let x : SU2MetricSphere -> Real := su2MetricSphereFirstReal
  let y : SU2MetricSphere -> Real := su2MetricSphereFirstImag
  let u : SU2MetricSphere -> Real := su2MetricSphereSecondReal
  let v : SU2MetricSphere -> Real := su2MetricSphereSecondImag
  have hx : Continuous x := continuous_su2MetricSphereFirstReal
  have hy : Continuous y := continuous_su2MetricSphereFirstImag
  have hu : Continuous u := continuous_su2MetricSphereSecondReal
  have hv : Continuous v := continuous_su2MetricSphereSecondImag
  have hxn : Integrable (fun z => x z ^ n) mu :=
    integrable_continuous_canonicalSphere (hx.pow n)
  have hxy : Integrable (fun z => x z ^ (n - 2) * y z ^ 2) mu :=
    integrable_continuous_canonicalSphere ((hx.pow (n - 2)).mul (hy.pow 2))
  have hxu : Integrable (fun z => x z ^ (n - 2) * u z ^ 2) mu :=
    integrable_continuous_canonicalSphere ((hx.pow (n - 2)).mul (hu.pow 2))
  have hxv : Integrable (fun z => x z ^ (n - 2) * v z ^ 2) mu :=
    integrable_continuous_canonicalSphere ((hx.pow (n - 2)).mul (hv.pow 2))
  have hpoint (z : SU2MetricSphere) :
      x z ^ (n - 2) =
        x z ^ n + x z ^ (n - 2) * y z ^ 2 +
          x z ^ (n - 2) * u z ^ 2 + x z ^ (n - 2) * v z ^ 2 := by
    have hsphere : x z ^ 2 + y z ^ 2 + u z ^ 2 + v z ^ 2 = 1 := by
      simpa [x, y, u, v] using su2MetricSphere_coordinate_sq_sum z
    calc
      x z ^ (n - 2) = x z ^ (n - 2) * 1 := by ring
      _ = x z ^ (n - 2) *
          (x z ^ 2 + y z ^ 2 + u z ^ 2 + v z ^ 2) := by rw [hsphere]
      _ = x z ^ n + x z ^ (n - 2) * y z ^ 2 +
          x z ^ (n - 2) * u z ^ 2 + x z ^ (n - 2) * v z ^ 2 := by
        have hxpow : x z ^ (n - 2) * x z ^ 2 = x z ^ n := by
          rw [← pow_add, show n - 2 + 2 = n by omega]
        calc
          x z ^ (n - 2) *
              (x z ^ 2 + y z ^ 2 + u z ^ 2 + v z ^ 2) =
              x z ^ (n - 2) * x z ^ 2 +
                x z ^ (n - 2) * y z ^ 2 +
                x z ^ (n - 2) * u z ^ 2 +
                x z ^ (n - 2) * v z ^ 2 := by ring
          _ = _ := by rw [hxpow]
  change (∫ z, x z ^ (n - 2) ∂mu) = _
  calc
    (∫ z, x z ^ (n - 2) ∂mu) =
        ∫ z, x z ^ n + x z ^ (n - 2) * y z ^ 2 +
          x z ^ (n - 2) * u z ^ 2 + x z ^ (n - 2) * v z ^ 2 ∂mu := by
      apply MeasureTheory.integral_congr_ae
      exact ae_of_all _ hpoint
    _ = (∫ z, x z ^ n ∂mu) +
          (∫ z, x z ^ (n - 2) * y z ^ 2 ∂mu) +
          (∫ z, x z ^ (n - 2) * u z ^ 2 ∂mu) +
          (∫ z, x z ^ (n - 2) * v z ^ 2 ∂mu) := by
      calc
        (∫ z, x z ^ n + x z ^ (n - 2) * y z ^ 2 +
            x z ^ (n - 2) * u z ^ 2 + x z ^ (n - 2) * v z ^ 2 ∂mu) =
            ∫ z, (x z ^ n + x z ^ (n - 2) * y z ^ 2) +
              (x z ^ (n - 2) * u z ^ 2 + x z ^ (n - 2) * v z ^ 2) ∂mu := by
          apply MeasureTheory.integral_congr_ae
          exact ae_of_all _ fun z => by ring
        _ = (∫ z, x z ^ n + x z ^ (n - 2) * y z ^ 2 ∂mu) +
              (∫ z, x z ^ (n - 2) * u z ^ 2 +
                x z ^ (n - 2) * v z ^ 2 ∂mu) := by
          exact integral_add (hxn.add hxy) (hxu.add hxv)
        _ = _ := by
          rw [integral_add hxn hxy, integral_add hxu hxv]
          ring
    _ = su2SphereCoordinateMoment n + 3 * su2SphereCoordinateMixedMoment n := by
      rw [show (∫ z, x z ^ n ∂mu) = su2SphereCoordinateMoment n by rfl]
      rw [show (∫ z, x z ^ (n - 2) * y z ^ 2 ∂mu) =
        su2SphereCoordinateMixedMoment n by rfl]
      rw [show (∫ z, x z ^ (n - 2) * u z ^ 2 ∂mu) =
        su2SphereCoordinateMixedMoment n by
          simpa [x, u, mu] using integral_firstReal_pow_mul_secondReal_sq n]
      rw [show (∫ z, x z ^ (n - 2) * v z ^ 2 ∂mu) =
        su2SphereCoordinateMixedMoment n by
          simpa [x, v, mu] using integral_firstReal_pow_mul_secondImag_sq n]
      ring

/-- Universal moment recurrence for one coordinate of normalized `S^3`.
This is an all-orders statement, not a finite moment computation. -/
theorem su2SphereCoordinateMoment_recurrence (n : Nat) (hn : 2 <= n) :
    ((n : Real) + 2) * su2SphereCoordinateMoment n =
      ((n : Real) - 1) * su2SphereCoordinateMoment (n - 2) := by
  have hrot := su2SphereCoordinateMoment_rotation_balance n
  have hdec := su2SphereCoordinateMoment_decomposition n hn
  have hcast : ((n - 1 : Nat) : Real) = (n : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 <= n)]
    norm_num
  rw [hcast] at hrot
  have hnreal : (2 : Real) <= (n : Real) := by exact_mod_cast hn
  have hnzero : (n : Real) ≠ 0 := by positivity
  have hfactor : (n : Real) *
      (((n : Real) - 1) * su2SphereCoordinateMixedMoment n -
        su2SphereCoordinateMoment n) = 0 := by
    nlinarith [hrot]
  have hrel : ((n : Real) - 1) * su2SphereCoordinateMixedMoment n =
      su2SphereCoordinateMoment n := by
    rcases mul_eq_zero.mp hfactor with hn0 | hrest
    · exact (hnzero hn0).elim
    · linarith
  rw [hdec]
  nlinarith

/-- The closed Haar--canonical bridge really reduces the SU(2) half-trace
marginal to the first-coordinate marginal of Mathlib's normalized spherical
measure.  No Weyl or distributional hypothesis is used here. -/
theorem su2HaarHalfTraceMeasure_eq_canonicalSphereCoordinate :
    su2HaarHalfTraceMeasure =
      (su2CanonicalSphereProbability : Measure SU2MetricSphere).map
        su2MetricSphereFirstReal := by
  rw [su2HaarHalfTraceMeasure, show su2HalfTrace =
      (fun z : SU2RowSphere => z.1.1.re) ∘ su2ToRowSphere by rfl]
  rw [← Measure.map_map (by fun_prop) continuous_su2ToRowSphere.measurable]
  change su2RowSphereHaar.map (fun z : SU2RowSphere => z.1.1.re) = _
  rw [su2RowSphereHaar_eq_su2CanonicalRowSphereMeasure,
    su2CanonicalRowSphereMeasure]
  rw [Measure.map_map (by fun_prop) continuous_metricSphereToRowSphere.measurable]
  rfl

/-- The unnormalized semicircle measure on `[-1,1]`. -/
def su2SemicircleBaseMeasure : Measure Real :=
  (volume.withDensity fun x => ENNReal.ofReal (Real.sqrt (1 - x ^ 2))).restrict (Icc (-1) 1)

/-- The normalized semicircle measure, with density
`(2/pi) sqrt(1-x^2) 1_[-1,1]`. -/
def su2SemicircleMeasure : Measure Real :=
  ENNReal.ofReal (2 / Real.pi) • su2SemicircleBaseMeasure

theorem integral_su2SemicircleBaseMeasure (f : Real -> Real) :
    ∫ x, f x ∂su2SemicircleBaseMeasure =
      ∫ x in (-1 : Real)..1, f x * Real.sqrt (1 - x ^ 2) := by
  rw [su2SemicircleBaseMeasure]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    (by fun_prop) (by simp) f measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : Real) ≤ 1)]
  congr! 2 with x hx
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  simp [smul_eq_mul, mul_comm]

theorem integral_su2SemicircleMeasure (f : Real -> Real) :
    ∫ x, f x ∂su2SemicircleMeasure =
      (2 / Real.pi) *
        ∫ x in (-1 : Real)..1, f x * Real.sqrt (1 - x ^ 2) := by
  rw [su2SemicircleMeasure, MeasureTheory.integral_smul_measure,
    integral_su2SemicircleBaseMeasure]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 / Real.pi)]
  simp [smul_eq_mul]

theorem su2SemicircleMeasure_univ : su2SemicircleMeasure Set.univ = 1 := by
  rw [← ENNReal.toReal_eq_one_iff]
  change su2SemicircleMeasure.real Set.univ = 1
  have hconst : su2SemicircleMeasure.real Set.univ =
      ∫ _x : Real, (1 : Real) ∂su2SemicircleMeasure := by
    simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one]
  rw [hconst]
  rw [integral_su2SemicircleMeasure]
  simp only [one_mul]
  rw [integral_sqrt_one_sub_sq]
  field_simp [Real.pi_ne_zero]

instance : IsProbabilityMeasure su2SemicircleMeasure where
  measure_univ := su2SemicircleMeasure_univ

/-- The semicircle integral is the normalized Weyl-angle integral. -/
theorem integral_su2SemicircleMeasure_eq_angle (f : Real -> Real)
    (hf : Continuous f) :
    ∫ x, f x ∂su2SemicircleMeasure =
      (2 / Real.pi) * ∫ theta : Real in 0..Real.pi,
        f (Real.cos theta) * Real.sin theta ^ 2 := by
  rw [integral_su2SemicircleMeasure]
  congr 1
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := Real.pi) (b := 0)
    (f := Real.cos) (f' := fun theta => -Real.sin theta)
    (g := fun x => f x * Real.sqrt (1 - x ^ 2))
    (fun theta _ => Real.hasDerivAt_cos theta)
    Real.continuous_sin.neg.continuousOn
    (hf.mul (Real.continuous_sqrt.comp
      (continuous_const.sub (continuous_id.pow 2))))
  simp only [Real.cos_pi, Real.cos_zero] at hsub
  rw [← hsub, intervalIntegral.integral_symm]
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro theta htheta
  have htheta' : theta ∈ Set.Icc (0 : Real) Real.pi := by
    rw [Set.uIcc_of_le Real.pi_pos.le] at htheta
    exact htheta
  simp only [Function.comp_apply]
  rw [← Real.sin_eq_sqrt_one_sub_cos_sq htheta'.1 htheta'.2]
  ring

/-- Moments of the normalized semicircle law. -/
def su2SemicircleMoment (n : Nat) : Real :=
  ∫ x : Real, x ^ n ∂su2SemicircleMeasure

theorem su2SemicircleMoment_eq_angle (n : Nat) :
    su2SemicircleMoment n =
      (2 / Real.pi) * ∫ theta : Real in 0..Real.pi,
        Real.cos theta ^ n * Real.sin theta ^ 2 := by
  simpa [su2SemicircleMoment] using
    integral_su2SemicircleMeasure_eq_angle (fun x : Real => x ^ n)
      (continuous_id.pow n)

/-- Denominator-free reduction formula for cosine moments on `[0,π]`. -/
theorem integral_cos_pow_zero_pi_balance (n : Nat) :
    ((n : Real) + 2) *
        (∫ theta : Real in 0..Real.pi, Real.cos theta ^ (n + 2)) =
      ((n : Real) + 1) *
        (∫ theta : Real in 0..Real.pi, Real.cos theta ^ n) := by
  have h := integral_cos_pow (a := (0 : Real)) (b := Real.pi) n
  simp only [Real.sin_pi, Real.sin_zero, mul_zero, sub_self, zero_div,
    zero_add] at h
  rw [h]
  have hden : (n : Real) + 2 ≠ 0 := by positivity
  field_simp

theorem integral_cos_pow_mul_sin_sq_zero_pi (n : Nat) :
    (∫ theta : Real in 0..Real.pi,
        Real.cos theta ^ n * Real.sin theta ^ 2) =
      (∫ theta : Real in 0..Real.pi, Real.cos theta ^ n) -
        (∫ theta : Real in 0..Real.pi, Real.cos theta ^ (n + 2)) := by
  have hcosn : IntervalIntegrable (fun theta : Real => Real.cos theta ^ n)
      volume 0 Real.pi := (Real.continuous_cos.pow n).intervalIntegrable 0 Real.pi
  have hcosn2 : IntervalIntegrable
      (fun theta : Real => Real.cos theta ^ (n + 2)) volume 0 Real.pi :=
    (Real.continuous_cos.pow (n + 2)).intervalIntegrable 0 Real.pi
  rw [← intervalIntegral.integral_sub hcosn hcosn2]
  · apply intervalIntegral.integral_congr
    intro theta _htheta
    have htrig := Real.sin_sq_add_cos_sq theta
    have hsin : Real.sin theta ^ 2 = 1 - Real.cos theta ^ 2 := by linarith
    have hpow : Real.cos theta ^ (n + 2) =
      Real.cos theta ^ n * Real.cos theta ^ 2 := by
      rw [pow_add]
    change Real.cos theta ^ n * Real.sin theta ^ 2 =
      Real.cos theta ^ n - Real.cos theta ^ (n + 2)
    rw [hsin, hpow]
    ring

/-- The semicircle moments satisfy the same universal recurrence as the
canonical spherical coordinate moments. -/
theorem su2SemicircleMoment_recurrence (n : Nat) (hn : 2 <= n) :
    ((n : Real) + 2) * su2SemicircleMoment n =
      ((n : Real) - 1) * su2SemicircleMoment (n - 2) := by
  have hnxt := integral_cos_pow_zero_pi_balance n
  have hprv := integral_cos_pow_zero_pi_balance (n - 2)
  have hcast2 : ((n - 2 : Nat) : Real) = (n : Real) - 2 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hpow : n - 2 + 2 = n := by omega
  rw [hcast2, hpow] at hprv
  rw [su2SemicircleMoment_eq_angle,
    su2SemicircleMoment_eq_angle,
    integral_cos_pow_mul_sin_sq_zero_pi,
    integral_cos_pow_mul_sin_sq_zero_pi]
  rw [hpow]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  ring_nf at hnxt hprv ⊢
  nlinarith

theorem su2SphereCoordinateMoment_zero : su2SphereCoordinateMoment 0 = 1 := by
  simp [su2SphereCoordinateMoment]

theorem su2SphereCoordinateMoment_one : su2SphereCoordinateMoment 1 = 0 := by
  have h := su2SphereCoordinateMoment_rotation_balance 1
  norm_num at h
  exact h

theorem su2SemicircleMoment_zero : su2SemicircleMoment 0 = 1 := by
  simp [su2SemicircleMoment]

theorem su2SemicircleMoment_one : su2SemicircleMoment 1 = 0 := by
  rw [su2SemicircleMoment_eq_angle]
  have h := integral_sin_sq_mul_cos (a := (0 : Real)) (b := Real.pi)
  rw [show (∫ theta : Real in 0..Real.pi,
      Real.cos theta ^ 1 * Real.sin theta ^ 2) = 0 by
    simpa [mul_comm] using h]
  ring

/-- The canonical spherical coordinate and the normalized semicircle law have
identical moments at every order. -/
theorem su2SphereCoordinateMoment_eq_semicircleMoment (n : Nat) :
    su2SphereCoordinateMoment n = su2SemicircleMoment n := by
  induction n using Nat.twoStepInduction with
  | zero => rw [su2SphereCoordinateMoment_zero, su2SemicircleMoment_zero]
  | one => rw [su2SphereCoordinateMoment_one, su2SemicircleMoment_one]
  | more n hn _hn1 =>
      have hs := su2SphereCoordinateMoment_recurrence (n + 2) (by omega)
      have hm := su2SemicircleMoment_recurrence (n + 2) (by omega)
      norm_num only [Nat.add_sub_cancel] at hs hm
      rw [hn] at hs
      have hpos : (0 : Real) < (n : Real) + 4 := by positivity
      nlinarith

theorem integral_pow_su2HaarHalfTraceMeasure (n : Nat) :
    (∫ x : Real, x ^ n ∂su2HaarHalfTraceMeasure) =
      su2SphereCoordinateMoment n := by
  rw [su2HaarHalfTraceMeasure_eq_canonicalSphereCoordinate]
  have hmap := MeasureTheory.integral_map
    (μ := (su2CanonicalSphereProbability : Measure SU2MetricSphere))
    continuous_su2MetricSphereFirstReal.measurable.aemeasurable
    ((continuous_id.pow n).aestronglyMeasurable)
  simpa [su2SphereCoordinateMoment] using hmap

theorem integrable_pow_su2HaarHalfTraceMeasure (n : Nat) :
    Integrable (fun x : Real => x ^ n) su2HaarHalfTraceMeasure := by
  rw [su2HaarHalfTraceMeasure_eq_canonicalSphereCoordinate]
  exact (integrable_map_measure
    ((continuous_id.pow n).aestronglyMeasurable)
    continuous_su2MetricSphereFirstReal.measurable.aemeasurable).2
      (integrable_continuous_canonicalSphere
        (continuous_su2MetricSphereFirstReal.pow n))

theorem ae_su2SemicircleMeasure_mem_Icc :
    ∀ᵐ x : Real ∂su2SemicircleMeasure, x ∈ Icc (-1 : Real) 1 := by
  rw [su2SemicircleMeasure, su2SemicircleBaseMeasure]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

theorem integrable_pow_su2SemicircleMeasure (n : Nat) :
    Integrable (fun x : Real => x ^ n) su2SemicircleMeasure := by
  refine (integrable_const (1 : Real)).mono'
    ((continuous_id.pow n).aestronglyMeasurable) ?_
  filter_upwards [ae_su2SemicircleMeasure_mem_Icc] with x hx
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_one₀ (abs_nonneg x) (abs_le.2 hx)

theorem integral_pow_su2HaarHalfTraceMeasure_eq_semicircle (n : Nat) :
    (∫ x : Real, x ^ n ∂su2HaarHalfTraceMeasure) =
      ∫ x : Real, x ^ n ∂su2SemicircleMeasure := by
  rw [integral_pow_su2HaarHalfTraceMeasure,
    su2SphereCoordinateMoment_eq_semicircleMoment]
  rfl

theorem integrable_polynomial_su2HaarHalfTraceMeasure (p : Real[X]) :
    Integrable (fun x : Real => p.eval x) su2HaarHalfTraceMeasure := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n a =>
      simpa only [Polynomial.eval_monomial] using
        (integrable_pow_su2HaarHalfTraceMeasure n).const_mul a

theorem integrable_polynomial_su2SemicircleMeasure (p : Real[X]) :
    Integrable (fun x : Real => p.eval x) su2SemicircleMeasure := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n a =>
      simpa only [Polynomial.eval_monomial] using
        (integrable_pow_su2SemicircleMeasure n).const_mul a

/-- Equality of all polynomial observables for the two candidate marginal
measures. -/
theorem integral_polynomial_su2HaarHalfTraceMeasure_eq_semicircle
    (p : Real[X]) :
    (∫ x : Real, p.eval x ∂su2HaarHalfTraceMeasure) =
      ∫ x : Real, p.eval x ∂su2SemicircleMeasure := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval_add]
      rw [MeasureTheory.integral_add
          (integrable_polynomial_su2HaarHalfTraceMeasure p)
          (integrable_polynomial_su2HaarHalfTraceMeasure q),
        MeasureTheory.integral_add
          (integrable_polynomial_su2SemicircleMeasure p)
          (integrable_polynomial_su2SemicircleMeasure q), hp, hq]
  | monomial n a =>
      simp only [Polynomial.eval_monomial]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        integral_pow_su2HaarHalfTraceMeasure_eq_semicircle]

theorem ae_su2HaarHalfTraceMeasure_mem_Icc :
    ∀ᵐ x : Real ∂su2HaarHalfTraceMeasure, x ∈ Icc (-1 : Real) 1 := by
  rw [su2HaarHalfTraceMeasure]
  exact (ae_map_iff
    (μ := su2HaarProb)
    continuous_su2HalfTrace.measurable.aemeasurable measurableSet_Icc).2
      (ae_of_all _ su2HalfTrace_mem_Icc)

/-- Compact support plus Weierstrass turns the all-orders moment identity into
literal equality of measures. -/
theorem su2HaarHalfTraceMeasure_eq_su2SemicircleMeasure :
    su2HaarHalfTraceMeasure = su2SemicircleMeasure := by
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  by_contra hne
  let delta : Real :=
    |(∫ x : Real, f x ∂su2HaarHalfTraceMeasure) -
      ∫ x : Real, f x ∂su2SemicircleMeasure|
  have hdelta : 0 < delta := by
    exact abs_pos.mpr (sub_ne_zero.mpr hne)
  let eps : Real := delta / 4
  have heps : 0 < eps := by dsimp [eps]; positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn
    (-1 : Real) 1 (fun x : Real => f x) f.continuous.continuousOn eps heps
  have hHbound : ∀ᵐ x : Real ∂su2HaarHalfTraceMeasure,
      ‖f x - p.eval x‖ <= eps := by
    filter_upwards [ae_su2HaarHalfTraceMeasure_mem_Icc] with x hx
    simpa [Real.norm_eq_abs, abs_sub_comm] using (hp x hx).le
  have hSbound : ∀ᵐ x : Real ∂su2SemicircleMeasure,
      ‖f x - p.eval x‖ <= eps := by
    filter_upwards [ae_su2SemicircleMeasure_mem_Icc] with x hx
    simpa [Real.norm_eq_abs, abs_sub_comm] using (hp x hx).le
  have hHerr := MeasureTheory.norm_integral_le_of_norm_le_const hHbound
  have hSerr := MeasureTheory.norm_integral_le_of_norm_le_const hSbound
  have hfH : Integrable (fun x : Real => f x) su2HaarHalfTraceMeasure :=
    f.integrable su2HaarHalfTraceMeasure
  have hfS : Integrable (fun x : Real => f x) su2SemicircleMeasure :=
    f.integrable su2SemicircleMeasure
  have hpH := integrable_polynomial_su2HaarHalfTraceMeasure p
  have hpS := integrable_polynomial_su2SemicircleMeasure p
  rw [MeasureTheory.integral_sub hfH hpH] at hHerr
  rw [MeasureTheory.integral_sub hfS hpS] at hSerr
  have hHmass : su2HaarHalfTraceMeasure.real Set.univ = 1 := by simp
  have hSmass : su2SemicircleMeasure.real Set.univ = 1 := by simp
  rw [hHmass, mul_one] at hHerr
  rw [hSmass, mul_one] at hSerr
  have hpoly := integral_polynomial_su2HaarHalfTraceMeasure_eq_semicircle p
  have htriangle : delta <=
      |(∫ x : Real, f x ∂su2HaarHalfTraceMeasure) -
        ∫ x : Real, p.eval x ∂su2HaarHalfTraceMeasure| +
      |(∫ x : Real, f x ∂su2SemicircleMeasure) -
        ∫ x : Real, p.eval x ∂su2SemicircleMeasure| := by
    dsimp [delta]
    rw [← hpoly]
    calc
      |(∫ x : Real, f x ∂su2HaarHalfTraceMeasure) -
          ∫ x : Real, f x ∂su2SemicircleMeasure| <=
          |(∫ x : Real, f x ∂su2HaarHalfTraceMeasure) -
            ∫ x : Real, p.eval x ∂su2HaarHalfTraceMeasure| +
          |(∫ x : Real, p.eval x ∂su2HaarHalfTraceMeasure) -
            ∫ x : Real, f x ∂su2SemicircleMeasure| := abs_sub_le _ _ _
      _ = _ := by
        rw [abs_sub_comm
          (∫ x : Real, p.eval x ∂su2HaarHalfTraceMeasure)
          (∫ x : Real, f x ∂su2SemicircleMeasure)]
  have : delta <= 2 * eps := by
    calc
      delta <=
          |(∫ x : Real, f x ∂su2HaarHalfTraceMeasure) -
            ∫ x : Real, p.eval x ∂su2HaarHalfTraceMeasure| +
          |(∫ x : Real, f x ∂su2SemicircleMeasure) -
            ∫ x : Real, p.eval x ∂su2SemicircleMeasure| := htriangle
      _ <= eps + eps := add_le_add hHerr hSerr
      _ = 2 * eps := by ring
  dsimp [eps] at this
  nlinarith

/-- Weyl's angular formula for every continuous observable of the half-trace. -/
theorem integral_su2Haar_halfTrace_eq_angle (f : Real -> Real)
    (hf : Continuous f) :
    (∫ g : SU2, f (su2HalfTrace g) ∂su2HaarProb) =
      (2 / Real.pi) * ∫ theta : Real in 0..Real.pi,
        f (Real.cos theta) * Real.sin theta ^ 2 := by
  have hmap := MeasureTheory.integral_map
    (μ := su2HaarProb)
    continuous_su2HalfTrace.measurable.aemeasurable
    hf.aestronglyMeasurable
  calc
    (∫ g : SU2, f (su2HalfTrace g) ∂su2HaarProb) =
        ∫ x : Real, f x ∂su2HaarHalfTraceMeasure := by
      rw [su2HaarHalfTraceMeasure]
      exact hmap.symm
    _ = ∫ x : Real, f x ∂su2SemicircleMeasure := by
      rw [su2HaarHalfTraceMeasure_eq_su2SemicircleMeasure]
    _ = _ := integral_su2SemicircleMeasure_eq_angle f hf

theorem su2CharacterChebyshev_eq_ofReal (n : Nat) (g : SU2) :
    su2CharacterChebyshev n g =
      (((Polynomial.Chebyshev.U Real (n : Int)).eval
        (su2HalfTrace g) : Real) : Complex) := by
  rw [su2CharacterChebyshev, su2_half_trace_eq_ofReal_re]
  exact (Polynomial.Chebyshev.complex_ofReal_eval_U
    (su2HalfTrace g) (n : Int)).symm

/-- Haar orthogonality of all concrete SU(2) Chebyshev characters, in real
form. -/
theorem integral_su2Chebyshev_real_mul (n m : Nat) :
    (∫ g : SU2,
      (Polynomial.Chebyshev.U Real (n : Int)).eval (su2HalfTrace g) *
      (Polynomial.Chebyshev.U Real (m : Int)).eval (su2HalfTrace g)
      ∂su2HaarProb) = if n = m then 1 else 0 := by
  calc
    (∫ g : SU2,
        (Polynomial.Chebyshev.U Real (n : Int)).eval (su2HalfTrace g) *
          (Polynomial.Chebyshev.U Real (m : Int)).eval (su2HalfTrace g)
        ∂su2HaarProb) =
        (2 / Real.pi) * ∫ theta : Real in 0..Real.pi,
          ((Polynomial.Chebyshev.U Real (n : Int)).eval (Real.cos theta) *
            (Polynomial.Chebyshev.U Real (m : Int)).eval (Real.cos theta)) *
              Real.sin theta ^ 2 :=
      integral_su2Haar_halfTrace_eq_angle
        (fun x : Real =>
          (Polynomial.Chebyshev.U Real (n : Int)).eval x *
            (Polynomial.Chebyshev.U Real (m : Int)).eval x) (by fun_prop)
    _ = _ := by
      rw [intervalIntegral_chebyshevU_mul_chebyshevU_sin_sq]
      split_ifs
      · field_simp [Real.pi_ne_zero]
      · simp

/-- Haar orthogonality of all concrete complex-valued SU(2) characters. -/
theorem integral_su2CharacterChebyshev_mul (n m : Nat) :
    (∫ g : SU2, su2CharacterChebyshev n g * su2CharacterChebyshev m g
      ∂su2HaarProb) = if n = m then 1 else 0 := by
  have hpoint : (fun g : SU2 =>
      su2CharacterChebyshev n g * su2CharacterChebyshev m g) =
      (fun g : SU2 =>
        (((Polynomial.Chebyshev.U Real (n : Int)).eval (su2HalfTrace g) *
          (Polynomial.Chebyshev.U Real (m : Int)).eval (su2HalfTrace g) : Real) :
            Complex)) := by
    funext g
    rw [su2CharacterChebyshev_eq_ofReal, su2CharacterChebyshev_eq_ofReal]
    norm_cast
  rw [hpoint, integral_complex_ofReal,
    integral_su2Chebyshev_real_mul]
  split_ifs <;> norm_num

/-- All Chebyshev-U modes are orthonormal for the normalized semicircle
measure.  This is the analytic consumer needed once the Haar pushforward is
identified with `su2SemicircleMeasure`. -/
theorem integral_chebyshevU_mul_chebyshevU_semicircle (n m : Nat) :
    ∫ x : Real,
      (Polynomial.Chebyshev.U Real (n : Int)).eval x *
        (Polynomial.Chebyshev.U Real (m : Int)).eval x
      ∂su2SemicircleMeasure = if n = m then 1 else 0 := by
  rw [integral_su2SemicircleMeasure_eq_angle]
  · rw [intervalIntegral_chebyshevU_mul_chebyshevU_sin_sq]
    split_ifs
    · field_simp [Real.pi_ne_zero]
    · simp
  · fun_prop

end Lean2dYangMills
