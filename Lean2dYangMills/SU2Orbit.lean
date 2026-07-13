import Lean2dYangMills.SU2Conjugacy

/-!
# The SU(2) orbital coordinate

The first complex row coordinate of normalized Haar on `SU(2)` has squared
norm uniformly distributed on `[0,1]`.  Equivalently, the Hopf/orbital
coordinate `2 |z₁|² - 1` is uniform on `[-1,1]`.

The proof is intrinsic to the canonical `S³` measure.  A real rotation of
the two complex rails and an independent phase rotation give an all-orders
moment recurrence; compact support and Weierstrass then identify the measure.
-/

noncomputable section

open scoped ENNReal Interval Polynomial

namespace Lean2dYangMills

open Matrix Set MeasureTheory intervalIntegral

/-- Simultaneously rotate the two complex rails by a real angle. -/
def su2RailRotationFun (theta : Real)
    (z : SU2SphereAmbient) : SU2SphereAmbient :=
  let a := (WithLp.ofLp z).1
  let b := (WithLp.ofLp z).2
  WithLp.toLp 2
    (Real.cos theta * a - Real.sin theta * b,
      Real.sin theta * a + Real.cos theta * b)

def su2RailRotation (theta : Real) :
    SU2SphereAmbient ≃ₗᵢ[Real] SU2SphereAmbient where
  toFun := su2RailRotationFun theta
  invFun := su2RailRotationFun (-theta)
  left_inv z := by
    have htrig : Complex.cos (theta : Complex) ^ 2 +
        Complex.sin (theta : Complex) ^ 2 = 1 := by
      simpa [add_comm] using Complex.sin_sq_add_cos_sq (theta : Complex)
    apply WithLp.ofLp_injective
    apply Prod.ext
    · simp only [su2RailRotationFun, WithLp.ofLp_toLp, Real.cos_neg,
        Real.sin_neg, map_neg]
      push_cast
      calc
        Complex.cos (theta : Complex) *
              (Complex.cos (theta : Complex) * (WithLp.ofLp z).1 -
                Complex.sin (theta : Complex) * (WithLp.ofLp z).2) -
            (-Complex.sin (theta : Complex)) *
              (Complex.sin (theta : Complex) * (WithLp.ofLp z).1 +
                Complex.cos (theta : Complex) * (WithLp.ofLp z).2) =
            (Complex.cos (theta : Complex) ^ 2 +
              Complex.sin (theta : Complex) ^ 2) * (WithLp.ofLp z).1 := by ring
        _ = _ := by rw [htrig]; simp
    · simp only [su2RailRotationFun, WithLp.ofLp_toLp, Real.cos_neg,
        Real.sin_neg, map_neg]
      push_cast
      calc
        (-Complex.sin (theta : Complex)) *
              (Complex.cos (theta : Complex) * (WithLp.ofLp z).1 -
                Complex.sin (theta : Complex) * (WithLp.ofLp z).2) +
            Complex.cos (theta : Complex) *
              (Complex.sin (theta : Complex) * (WithLp.ofLp z).1 +
                Complex.cos (theta : Complex) * (WithLp.ofLp z).2) =
            (Complex.cos (theta : Complex) ^ 2 +
              Complex.sin (theta : Complex) ^ 2) * (WithLp.ofLp z).2 := by ring
        _ = _ := by rw [htrig]; simp
  right_inv z := by
    have htrig : Complex.cos (theta : Complex) ^ 2 +
        Complex.sin (theta : Complex) ^ 2 = 1 := by
      simpa [add_comm] using Complex.sin_sq_add_cos_sq (theta : Complex)
    apply WithLp.ofLp_injective
    apply Prod.ext
    · simp only [su2RailRotationFun, WithLp.ofLp_toLp, Real.cos_neg,
        Real.sin_neg, map_neg]
      push_cast
      calc
        Complex.cos (theta : Complex) *
              (Complex.cos (theta : Complex) * (WithLp.ofLp z).1 -
                (-Complex.sin (theta : Complex)) * (WithLp.ofLp z).2) -
            Complex.sin (theta : Complex) *
              ((-Complex.sin (theta : Complex)) * (WithLp.ofLp z).1 +
                Complex.cos (theta : Complex) * (WithLp.ofLp z).2) =
            (Complex.cos (theta : Complex) ^ 2 +
              Complex.sin (theta : Complex) ^ 2) * (WithLp.ofLp z).1 := by ring
        _ = _ := by rw [htrig]; simp
    · simp only [su2RailRotationFun, WithLp.ofLp_toLp, Real.cos_neg,
        Real.sin_neg, map_neg]
      push_cast
      calc
        Complex.sin (theta : Complex) *
              (Complex.cos (theta : Complex) * (WithLp.ofLp z).1 -
                (-Complex.sin (theta : Complex)) * (WithLp.ofLp z).2) +
            Complex.cos (theta : Complex) *
              ((-Complex.sin (theta : Complex)) * (WithLp.ofLp z).1 +
                Complex.cos (theta : Complex) * (WithLp.ofLp z).2) =
            (Complex.cos (theta : Complex) ^ 2 +
              Complex.sin (theta : Complex) ^ 2) * (WithLp.ofLp z).2 := by ring
        _ = _ := by rw [htrig]; simp
  map_add' x y := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> simp [su2RailRotationFun] <;> ring
  map_smul' r z := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;>
      simp [su2RailRotationFun, (· • ·), SMul.smul] <;> ring
  norm_map' z := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    change
      ‖(Real.cos theta : Complex) * (WithLp.ofLp z).1 -
          (Real.sin theta : Complex) * (WithLp.ofLp z).2‖ ^ 2 +
        ‖(Real.sin theta : Complex) * (WithLp.ofLp z).1 +
          (Real.cos theta : Complex) * (WithLp.ofLp z).2‖ ^ 2 =
        ‖(WithLp.ofLp z).1‖ ^ 2 + ‖(WithLp.ofLp z).2‖ ^ 2
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im]
    nlinarith [Real.sin_sq_add_cos_sq theta]

def su2MetricSphereRailRotation (theta : Real) :
    SU2MetricSphere -> SU2MetricSphere :=
  linearIsometryUnitSphereMap (su2RailRotation theta)

/-- Squared norm of the first complex rail. -/
def su2FirstRailMass (z : SU2MetricSphere) : Real :=
  su2MetricSphereFirstReal z ^ 2 + su2MetricSphereFirstImag z ^ 2

def su2SecondRailMass (z : SU2MetricSphere) : Real :=
  su2MetricSphereSecondReal z ^ 2 + su2MetricSphereSecondImag z ^ 2

/-- Real part of the Hermitian cross term between the rails. -/
def su2RailCrossRe (z : SU2MetricSphere) : Real :=
  su2MetricSphereFirstReal z * su2MetricSphereSecondReal z +
    su2MetricSphereFirstImag z * su2MetricSphereSecondImag z

/-- Imaginary companion of the Hermitian cross term. -/
def su2RailCrossIm (z : SU2MetricSphere) : Real :=
  su2MetricSphereFirstReal z * su2MetricSphereSecondImag z -
    su2MetricSphereFirstImag z * su2MetricSphereSecondReal z

theorem continuous_su2FirstRailMass : Continuous su2FirstRailMass := by
  unfold su2FirstRailMass
  exact (continuous_su2MetricSphereFirstReal.pow 2).add
    (continuous_su2MetricSphereFirstImag.pow 2)

theorem continuous_su2SecondRailMass : Continuous su2SecondRailMass := by
  unfold su2SecondRailMass
  exact (continuous_su2MetricSphereSecondReal.pow 2).add
    (continuous_su2MetricSphereSecondImag.pow 2)

theorem continuous_su2RailCrossRe : Continuous su2RailCrossRe := by
  unfold su2RailCrossRe
  exact (continuous_su2MetricSphereFirstReal.mul
    continuous_su2MetricSphereSecondReal).add
      (continuous_su2MetricSphereFirstImag.mul
        continuous_su2MetricSphereSecondImag)

theorem continuous_su2RailCrossIm : Continuous su2RailCrossIm := by
  unfold su2RailCrossIm
  exact (continuous_su2MetricSphereFirstReal.mul
    continuous_su2MetricSphereSecondImag).sub
      (continuous_su2MetricSphereFirstImag.mul
        continuous_su2MetricSphereSecondReal)

theorem su2FirstRailMass_add_second (z : SU2MetricSphere) :
    su2FirstRailMass z + su2SecondRailMass z = 1 := by
  simpa [su2FirstRailMass, su2SecondRailMass, add_assoc, add_left_comm,
    add_comm] using su2MetricSphere_coordinate_sq_sum z

theorem su2RailCross_sq_add_sq (z : SU2MetricSphere) :
    su2RailCrossRe z ^ 2 + su2RailCrossIm z ^ 2 =
      su2FirstRailMass z * su2SecondRailMass z := by
  simp [su2RailCrossRe, su2RailCrossIm, su2FirstRailMass,
    su2SecondRailMass]
  ring

theorem su2FirstRailMass_nonneg (z : SU2MetricSphere) :
    0 <= su2FirstRailMass z := by
  unfold su2FirstRailMass
  positivity

theorem su2FirstRailMass_le_one (z : SU2MetricSphere) :
    su2FirstRailMass z <= 1 := by
  have hs := su2FirstRailMass_add_second z
  have hnon : 0 <= su2SecondRailMass z := by
    unfold su2SecondRailMass
    positivity
  linarith

theorem su2FirstRailMass_railRotation (theta : Real)
    (z : SU2MetricSphere) :
    su2FirstRailMass (su2MetricSphereRailRotation theta z) =
      Real.cos theta ^ 2 * su2FirstRailMass z +
        Real.sin theta ^ 2 * su2SecondRailMass z -
        2 * Real.sin theta * Real.cos theta * su2RailCrossRe z := by
  simp [su2FirstRailMass, su2SecondRailMass, su2RailCrossRe,
    su2MetricSphereRailRotation, linearIsometryUnitSphereMap,
    su2RailRotation, su2RailRotationFun,
    su2MetricSphereFirstReal, su2MetricSphereFirstImag,
    su2MetricSphereSecondReal, su2MetricSphereSecondImag,
    Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re]
  ring

/-- The rail-mass coordinate after rotation, written in scalar form. -/
def su2RotatedRailMass (theta : Real) (z : SU2MetricSphere) : Real :=
  Real.cos theta ^ 2 * su2FirstRailMass z +
    Real.sin theta ^ 2 * su2SecondRailMass z -
    2 * Real.sin theta * Real.cos theta * su2RailCrossRe z

def su2RotatedRailMassDeriv (theta : Real) (z : SU2MetricSphere) : Real :=
  2 * Real.sin theta * Real.cos theta *
      (su2SecondRailMass z - su2FirstRailMass z) -
    2 * (Real.cos theta ^ 2 - Real.sin theta ^ 2) * su2RailCrossRe z

def su2RotatedRailMassSecondDeriv (theta : Real)
    (z : SU2MetricSphere) : Real :=
  2 * (Real.cos theta ^ 2 - Real.sin theta ^ 2) *
      (su2SecondRailMass z - su2FirstRailMass z) +
    8 * Real.sin theta * Real.cos theta * su2RailCrossRe z

theorem hasDerivAt_su2RotatedRailMass (theta : Real)
    (z : SU2MetricSphere) :
    HasDerivAt (fun t => su2RotatedRailMass t z)
      (su2RotatedRailMassDeriv theta z) theta := by
  simp only [su2RotatedRailMass, su2RotatedRailMassDeriv]
  have h := (((Real.hasDerivAt_cos theta).pow 2).const_mul
      (su2FirstRailMass z)).add
    (((Real.hasDerivAt_sin theta).pow 2).const_mul
      (su2SecondRailMass z)) |>.sub
    (((Real.hasDerivAt_sin theta).mul (Real.hasDerivAt_cos theta)).const_mul
      (2 * su2RailCrossRe z))
  convert h using 1
  · funext t
    dsimp
    ring
  · ring

theorem hasDerivAt_su2RotatedRailMassDeriv (theta : Real)
    (z : SU2MetricSphere) :
    HasDerivAt (fun t => su2RotatedRailMassDeriv t z)
      (su2RotatedRailMassSecondDeriv theta z) theta := by
  simp only [su2RotatedRailMassDeriv, su2RotatedRailMassSecondDeriv]
  have h := ((((Real.hasDerivAt_sin theta).mul
      (Real.hasDerivAt_cos theta)).const_mul
        (2 * (su2SecondRailMass z - su2FirstRailMass z))).sub
    (((((Real.hasDerivAt_cos theta).pow 2).sub
      ((Real.hasDerivAt_sin theta).pow 2)).const_mul
        (2 * su2RailCrossRe z))))
  convert h using 1
  · funext t
    dsimp
    ring
  · ring

def su2RotatedRailPower (n : Nat) (theta : Real)
    (z : SU2MetricSphere) : Real :=
  su2RotatedRailMass theta z ^ n

def su2RotatedRailPowerDeriv (n : Nat) (theta : Real)
    (z : SU2MetricSphere) : Real :=
  (n : Real) * su2RotatedRailMass theta z ^ (n - 1) *
    su2RotatedRailMassDeriv theta z

def su2RotatedRailPowerSecondDeriv (n : Nat) (theta : Real)
    (z : SU2MetricSphere) : Real :=
  (n : Real) * (n - 1 : Nat) * su2RotatedRailMass theta z ^ (n - 2) *
      su2RotatedRailMassDeriv theta z ^ 2 +
    (n : Real) * su2RotatedRailMass theta z ^ (n - 1) *
      su2RotatedRailMassSecondDeriv theta z

theorem hasDerivAt_su2RotatedRailPower (n : Nat) (theta : Real)
    (z : SU2MetricSphere) :
    HasDerivAt (fun t => su2RotatedRailPower n t z)
      (su2RotatedRailPowerDeriv n theta z) theta := by
  simpa [su2RotatedRailPower, su2RotatedRailPowerDeriv,
    Nat.cast_ofNat, mul_assoc] using
    (hasDerivAt_su2RotatedRailMass theta z).pow n

theorem hasDerivAt_su2RotatedRailPowerDeriv (n : Nat) (theta : Real)
    (z : SU2MetricSphere) :
    HasDerivAt (fun t => su2RotatedRailPowerDeriv n t z)
      (su2RotatedRailPowerSecondDeriv n theta z) theta := by
  by_cases hn : n = 0
  · subst n
    simpa [su2RotatedRailPowerDeriv, su2RotatedRailPowerSecondDeriv] using
      (hasDerivAt_const theta (0 : Real))
  by_cases hnone : n = 1
  · subst n
    simpa [su2RotatedRailPowerDeriv, su2RotatedRailPowerSecondDeriv] using
      hasDerivAt_su2RotatedRailMassDeriv theta z
  have hn1 : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn
  have hn2 : 2 <= n := by omega
  have hp := (hasDerivAt_su2RotatedRailMass theta z).pow (n - 1)
  have hq := hasDerivAt_su2RotatedRailMassDeriv theta z
  convert (hp.mul hq).const_mul (n : Real) using 1
  · funext t
    dsimp
    rw [su2RotatedRailPowerDeriv]
    ring
  · simp only [su2RotatedRailPowerSecondDeriv]
    have hcast : ((n - 1 : Nat) : Real) = (n : Real) - 1 := by
      rw [Nat.cast_sub hn1]
      norm_num
    have hsub : n - 1 - 1 = n - 2 := by omega
    rw [hcast, hsub]
    dsimp
    ring

theorem abs_su2RotatedRailMass_le_one (theta : Real)
    (z : SU2MetricSphere) :
    |su2RotatedRailMass theta z| <= 1 := by
  change |Real.cos theta ^ 2 * su2FirstRailMass z +
        Real.sin theta ^ 2 * su2SecondRailMass z -
        2 * Real.sin theta * Real.cos theta * su2RailCrossRe z| <= 1
  rw [← su2FirstRailMass_railRotation]
  rw [abs_of_nonneg (su2FirstRailMass_nonneg _)]
  exact su2FirstRailMass_le_one _

theorem abs_su2RotatedRailMassDeriv_le_four (theta : Real)
    (z : SU2MetricSphere) :
    |su2RotatedRailMassDeriv theta z| <= 4 := by
  have hr : |su2SecondRailMass z - su2FirstRailMass z| <= 1 := by
    rw [abs_le]
    constructor <;>
      nlinarith [su2FirstRailMass_nonneg z, su2FirstRailMass_le_one z,
        show 0 <= su2SecondRailMass z by
          unfold su2SecondRailMass; positivity,
        su2FirstRailMass_add_second z]
  have hc : |su2RailCrossRe z| <= 1 := by
    have hs := su2RailCross_sq_add_sq z
    have hprod : su2FirstRailMass z * su2SecondRailMass z <= 1 := by
      nlinarith [su2FirstRailMass_nonneg z, su2FirstRailMass_le_one z,
        show 0 <= su2SecondRailMass z by
          unfold su2SecondRailMass; positivity,
        su2FirstRailMass_add_second z]
    nlinarith [sq_nonneg (su2RailCrossIm z), sq_abs (su2RailCrossRe z)]
  have htrig : |Real.cos theta ^ 2 - Real.sin theta ^ 2| <= 1 := by
    rw [abs_le]
    constructor <;>
      nlinarith [sq_nonneg (Real.cos theta), sq_nonneg (Real.sin theta),
        Real.sin_sq_add_cos_sq theta]
  have hfirst :
      |2 * Real.sin theta * Real.cos theta *
        (su2SecondRailMass z - su2FirstRailMass z)| <= 2 := by
    rw [abs_mul, abs_mul, abs_mul]
    calc
      |2| * |Real.sin theta| * |Real.cos theta| *
          |su2SecondRailMass z - su2FirstRailMass z| <=
          2 * 1 * 1 * 1 := by
        gcongr
        · norm_num
        · exact Real.abs_sin_le_one theta
        · exact Real.abs_cos_le_one theta
      _ = 2 := by norm_num
  have hsecond :
      |2 * (Real.cos theta ^ 2 - Real.sin theta ^ 2) *
        su2RailCrossRe z| <= 2 := by
    rw [abs_mul, abs_mul]
    calc
      |2| * |Real.cos theta ^ 2 - Real.sin theta ^ 2| *
          |su2RailCrossRe z| <= 2 * 1 * 1 := by
        gcongr
        · norm_num
      _ = 2 := by norm_num
  simp only [su2RotatedRailMassDeriv]
  calc
    |2 * Real.sin theta * Real.cos theta *
          (su2SecondRailMass z - su2FirstRailMass z) -
        2 * (Real.cos theta ^ 2 - Real.sin theta ^ 2) * su2RailCrossRe z| <=
        |2 * Real.sin theta * Real.cos theta *
          (su2SecondRailMass z - su2FirstRailMass z)| +
        |2 * (Real.cos theta ^ 2 - Real.sin theta ^ 2) * su2RailCrossRe z| :=
      abs_sub _ _
    _ <= 2 + 2 := add_le_add hfirst hsecond
    _ = 4 := by norm_num

theorem abs_su2RotatedRailMassSecondDeriv_le_ten (theta : Real)
    (z : SU2MetricSphere) :
    |su2RotatedRailMassSecondDeriv theta z| <= 10 := by
  have hr : |su2SecondRailMass z - su2FirstRailMass z| <= 1 := by
    rw [abs_le]
    constructor <;>
      nlinarith [su2FirstRailMass_nonneg z, su2FirstRailMass_le_one z,
        show 0 <= su2SecondRailMass z by
          unfold su2SecondRailMass; positivity,
        su2FirstRailMass_add_second z]
  have hc : |su2RailCrossRe z| <= 1 := by
    have hs := su2RailCross_sq_add_sq z
    have hprod : su2FirstRailMass z * su2SecondRailMass z <= 1 := by
      nlinarith [su2FirstRailMass_nonneg z, su2FirstRailMass_le_one z,
        show 0 <= su2SecondRailMass z by
          unfold su2SecondRailMass; positivity,
        su2FirstRailMass_add_second z]
    nlinarith [sq_nonneg (su2RailCrossIm z), sq_abs (su2RailCrossRe z)]
  have htrig : |Real.cos theta ^ 2 - Real.sin theta ^ 2| <= 1 := by
    rw [abs_le]
    constructor <;>
      nlinarith [sq_nonneg (Real.cos theta), sq_nonneg (Real.sin theta),
        Real.sin_sq_add_cos_sq theta]
  have hfirst :
      |2 * (Real.cos theta ^ 2 - Real.sin theta ^ 2) *
        (su2SecondRailMass z - su2FirstRailMass z)| <= 2 := by
    rw [abs_mul, abs_mul]
    calc
      |2| * |Real.cos theta ^ 2 - Real.sin theta ^ 2| *
          |su2SecondRailMass z - su2FirstRailMass z| <= 2 * 1 * 1 := by
        gcongr
        · norm_num
      _ = 2 := by norm_num
  have hsecond :
      |8 * Real.sin theta * Real.cos theta * su2RailCrossRe z| <= 8 := by
    rw [abs_mul, abs_mul, abs_mul]
    calc
      |8| * |Real.sin theta| * |Real.cos theta| * |su2RailCrossRe z| <=
          8 * 1 * 1 * 1 := by
        gcongr
        · norm_num
        · exact Real.abs_sin_le_one theta
        · exact Real.abs_cos_le_one theta
      _ = 8 := by norm_num
  simp only [su2RotatedRailMassSecondDeriv]
  calc
    |2 * (Real.cos theta ^ 2 - Real.sin theta ^ 2) *
          (su2SecondRailMass z - su2FirstRailMass z) +
        8 * Real.sin theta * Real.cos theta * su2RailCrossRe z| <=
        |2 * (Real.cos theta ^ 2 - Real.sin theta ^ 2) *
          (su2SecondRailMass z - su2FirstRailMass z)| +
        |8 * Real.sin theta * Real.cos theta * su2RailCrossRe z| :=
      abs_add_le _ _
    _ <= 2 + 8 := add_le_add hfirst hsecond
    _ = 10 := by norm_num

theorem continuous_su2RotatedRailPower (n : Nat) (theta : Real) :
    Continuous (su2RotatedRailPower n theta) := by
  unfold su2RotatedRailPower
  exact (((continuous_const.mul continuous_su2FirstRailMass).add
    (continuous_const.mul continuous_su2SecondRailMass)).sub
      (continuous_const.mul continuous_su2RailCrossRe)).pow n

theorem continuous_su2RotatedRailPowerDeriv (n : Nat) (theta : Real) :
    Continuous (su2RotatedRailPowerDeriv n theta) := by
  unfold su2RotatedRailPowerDeriv
  have hr : Continuous (su2RotatedRailMass theta) :=
    ((continuous_const.mul continuous_su2FirstRailMass).add
      (continuous_const.mul continuous_su2SecondRailMass)).sub
        (continuous_const.mul continuous_su2RailCrossRe)
  have hd : Continuous (su2RotatedRailMassDeriv theta) :=
    (continuous_const.mul
      (continuous_su2SecondRailMass.sub continuous_su2FirstRailMass)).sub
        (continuous_const.mul continuous_su2RailCrossRe)
  exact (continuous_const.mul (hr.pow (n - 1))).mul hd

theorem continuous_su2RotatedRailPowerSecondDeriv (n : Nat)
    (theta : Real) :
    Continuous (su2RotatedRailPowerSecondDeriv n theta) := by
  unfold su2RotatedRailPowerSecondDeriv
  have hr : Continuous (su2RotatedRailMass theta) :=
    ((continuous_const.mul continuous_su2FirstRailMass).add
      (continuous_const.mul continuous_su2SecondRailMass)).sub
        (continuous_const.mul continuous_su2RailCrossRe)
  have hd : Continuous (su2RotatedRailMassDeriv theta) :=
    (continuous_const.mul
      (continuous_su2SecondRailMass.sub continuous_su2FirstRailMass)).sub
        (continuous_const.mul continuous_su2RailCrossRe)
  have hdd : Continuous (su2RotatedRailMassSecondDeriv theta) :=
    (continuous_const.mul
      (continuous_su2SecondRailMass.sub continuous_su2FirstRailMass)).add
        (continuous_const.mul continuous_su2RailCrossRe)
  exact (((continuous_const.mul continuous_const).mul (hr.pow (n - 2))).mul
    (hd.pow 2)).add ((continuous_const.mul (hr.pow (n - 1))).mul hdd)

theorem abs_su2RotatedRailPowerDeriv_le (n : Nat) (theta : Real)
    (z : SU2MetricSphere) :
    |su2RotatedRailPowerDeriv n theta z| <= (n : Real) * 4 := by
  simp only [su2RotatedRailPowerDeriv, abs_mul, abs_pow]
  rw [abs_of_nonneg (Nat.cast_nonneg n)]
  calc
    (n : Real) * |su2RotatedRailMass theta z| ^ (n - 1) *
        |su2RotatedRailMassDeriv theta z| <=
      (n : Real) * 1 * 4 := by
        gcongr
        · exact pow_le_one₀ (abs_nonneg _) (abs_su2RotatedRailMass_le_one theta z)
        · exact abs_su2RotatedRailMassDeriv_le_four theta z
    _ = _ := by ring

theorem abs_su2RotatedRailPowerSecondDeriv_le (n : Nat) (theta : Real)
    (z : SU2MetricSphere) :
    |su2RotatedRailPowerSecondDeriv n theta z| <=
      (n : Real) * (n - 1 : Nat) * 16 + (n : Real) * 10 := by
  simp only [su2RotatedRailPowerSecondDeriv]
  calc
    |(n : Real) * (n - 1 : Nat) * su2RotatedRailMass theta z ^ (n - 2) *
          su2RotatedRailMassDeriv theta z ^ 2 +
        (n : Real) * su2RotatedRailMass theta z ^ (n - 1) *
          su2RotatedRailMassSecondDeriv theta z| <=
      |(n : Real) * (n - 1 : Nat) * su2RotatedRailMass theta z ^ (n - 2) *
          su2RotatedRailMassDeriv theta z ^ 2| +
        |(n : Real) * su2RotatedRailMass theta z ^ (n - 1) *
          su2RotatedRailMassSecondDeriv theta z| := abs_add_le _ _
    _ <= (n : Real) * (n - 1 : Nat) * 1 * 16 +
        (n : Real) * 1 * 10 := by
      simp only [abs_mul, abs_pow]
      rw [abs_of_nonneg (Nat.cast_nonneg n),
        abs_of_nonneg (Nat.cast_nonneg (n - 1))]
      gcongr
      · exact pow_le_one₀ (abs_nonneg _) (abs_su2RotatedRailMass_le_one theta z)
      · nlinarith [abs_su2RotatedRailMassDeriv_le_four theta z,
          abs_nonneg (su2RotatedRailMassDeriv theta z)]
      · exact pow_le_one₀ (abs_nonneg _) (abs_su2RotatedRailMass_le_one theta z)
      · exact abs_su2RotatedRailMassSecondDeriv_le_ten theta z
    _ = _ := by ring

def su2FirstRailMoment (n : Nat) : Real :=
  ∫ z : SU2MetricSphere, su2FirstRailMass z ^ n
    ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)

theorem su2FirstRailMoment_zero : su2FirstRailMoment 0 = 1 := by
  simp [su2FirstRailMoment]

theorem su2FirstRailMoment_one : su2FirstRailMoment 1 = 1 / 2 := by
  have hxrec := su2SphereCoordinateMoment_recurrence 2 (by omega)
  rw [su2SphereCoordinateMoment_zero] at hxrec
  norm_num at hxrec
  have hxval : su2SphereCoordinateMoment 2 = 1 / 4 := by
    nlinarith [hxrec]
  have hx : (∫ z : SU2MetricSphere,
      su2MetricSphereFirstReal z ^ 2
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) = 1 / 4 := by
    exact hxval
  have hrot := integral_rotated_coordinate_pow (Real.pi / 2) 2
  have hy : (∫ z : SU2MetricSphere,
      su2MetricSphereFirstImag z ^ 2
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) = 1 / 4 := by
    rw [show (fun z : SU2MetricSphere =>
        (Real.cos (Real.pi / 2) * su2MetricSphereFirstReal z -
          Real.sin (Real.pi / 2) * su2MetricSphereFirstImag z) ^ 2) =
      (fun z => su2MetricSphereFirstImag z ^ 2) by
        funext z
        rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
        ring] at hrot
    rw [hxval] at hrot
    exact hrot
  unfold su2FirstRailMoment su2FirstRailMass
  simp only [pow_one]
  rw [MeasureTheory.integral_add]
  · rw [hx, hy]
    ring
  · exact integrable_continuous_canonicalSphere
      (continuous_su2MetricSphereFirstReal.pow 2)
  · exact integrable_continuous_canonicalSphere
      (continuous_su2MetricSphereFirstImag.pow 2)

theorem integral_su2RotatedRailPower_eq_moment (n : Nat) (theta : Real) :
    ∫ z : SU2MetricSphere, su2RotatedRailPower n theta z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) =
      su2FirstRailMoment n := by
  have hfun : (fun z : SU2MetricSphere => su2RotatedRailPower n theta z) =
      (fun z => su2FirstRailMass (su2MetricSphereRailRotation theta z) ^ n) := by
    funext z
    rw [su2RotatedRailPower, su2RotatedRailMass,
      su2FirstRailMass_railRotation]
  rw [hfun]
  simpa [su2FirstRailMoment, su2MetricSphereRailRotation] using
    integral_comp_linearIsometryUnitSphereMap_canonical
      (su2RailRotation theta) (fun z : SU2MetricSphere => su2FirstRailMass z ^ n)
      (continuous_su2FirstRailMass.pow n)

theorem hasDerivAt_integral_su2RotatedRailPower
    (n : Nat) (theta : Real) :
    HasDerivAt
      (fun t => ∫ z : SU2MetricSphere, su2RotatedRailPower n t z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere))
      (∫ z : SU2MetricSphere, su2RotatedRailPowerDeriv n theta z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) theta := by
  let mu : Measure SU2MetricSphere := su2CanonicalSphereProbability
  let C : Real := (n : Real) * 4
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := mu)
    (F := fun t z => su2RotatedRailPower n t z)
    (F' := fun t z => su2RotatedRailPowerDeriv n t z)
    (bound := fun _z : SU2MetricSphere => C)
    (s := Set.univ) (x₀ := theta)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      (continuous_su2RotatedRailPower n t).aestronglyMeasurable)
    (integrable_continuous_canonicalSphere
      (continuous_su2RotatedRailPower n theta))
    (continuous_su2RotatedRailPowerDeriv n theta).aestronglyMeasurable
    (ae_of_all _ fun z t _ht => by
      simpa [C, Real.norm_eq_abs] using
        abs_su2RotatedRailPowerDeriv_le n t z)
    (integrable_const C)
    (ae_of_all _ fun z t _ht => hasDerivAt_su2RotatedRailPower n t z)).2

theorem hasDerivAt_integral_su2RotatedRailPowerDeriv
    (n : Nat) (theta : Real) :
    HasDerivAt
      (fun t => ∫ z : SU2MetricSphere, su2RotatedRailPowerDeriv n t z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere))
      (∫ z : SU2MetricSphere, su2RotatedRailPowerSecondDeriv n theta z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) theta := by
  let mu : Measure SU2MetricSphere := su2CanonicalSphereProbability
  let C : Real := (n : Real) * (n - 1 : Nat) * 16 + (n : Real) * 10
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := mu)
    (F := fun t z => su2RotatedRailPowerDeriv n t z)
    (F' := fun t z => su2RotatedRailPowerSecondDeriv n t z)
    (bound := fun _z : SU2MetricSphere => C)
    (s := Set.univ) (x₀ := theta)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      (continuous_su2RotatedRailPowerDeriv n t).aestronglyMeasurable)
    (integrable_continuous_canonicalSphere
      (continuous_su2RotatedRailPowerDeriv n theta))
    (continuous_su2RotatedRailPowerSecondDeriv n theta).aestronglyMeasurable
    (ae_of_all _ fun z t _ht => by
      simpa [C, Real.norm_eq_abs] using
        abs_su2RotatedRailPowerSecondDeriv_le n t z)
    (integrable_const C)
    (ae_of_all _ fun z t _ht =>
      hasDerivAt_su2RotatedRailPowerDeriv n t z)).2

theorem integral_su2RotatedRailPowerDeriv_eq_zero
    (n : Nat) (theta : Real) :
    ∫ z : SU2MetricSphere, su2RotatedRailPowerDeriv n theta z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) = 0 := by
  have hderiv := hasDerivAt_integral_su2RotatedRailPower n theta
  have hconst : HasDerivAt
      (fun t => ∫ z : SU2MetricSphere, su2RotatedRailPower n t z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) 0 theta := by
    convert hasDerivAt_const theta (su2FirstRailMoment n) using 1
    funext t
    exact integral_su2RotatedRailPower_eq_moment n t
  exact hderiv.unique hconst

theorem integral_su2RotatedRailPowerSecondDeriv_eq_zero
    (n : Nat) (theta : Real) :
    ∫ z : SU2MetricSphere, su2RotatedRailPowerSecondDeriv n theta z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) = 0 := by
  have hderiv := hasDerivAt_integral_su2RotatedRailPowerDeriv n theta
  have hconst : HasDerivAt
      (fun t => ∫ z : SU2MetricSphere, su2RotatedRailPowerDeriv n t z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) 0 theta := by
    convert hasDerivAt_const theta (0 : Real) using 1
    funext t
    exact integral_su2RotatedRailPowerDeriv_eq_zero n t
  exact hderiv.unique hconst

/-- Phase symmetry makes the real and imaginary cross terms equidistributed. -/
theorem integral_firstRail_pow_mul_crossRe_sq_eq_crossIm
    (n : Nat) :
    (∫ z : SU2MetricSphere,
      su2FirstRailMass z ^ n * su2RailCrossRe z ^ 2
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) =
    ∫ z : SU2MetricSphere,
      su2FirstRailMass z ^ n * su2RailCrossIm z ^ 2
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) := by
  have h := integral_comp_linearIsometryUnitSphereMap_canonical
    (su2SecondPhaseAmbient (Real.pi / 2))
    (fun z : SU2MetricSphere =>
      su2FirstRailMass z ^ n * su2RailCrossRe z ^ 2)
    ((continuous_su2FirstRailMass.pow n).mul
      (continuous_su2RailCrossRe.pow 2))
  change (∫ z : SU2MetricSphere,
      su2FirstRailMass (su2MetricSphereSecondPhase (Real.pi / 2) z) ^ n *
        su2RailCrossRe (su2MetricSphereSecondPhase (Real.pi / 2) z) ^ 2
      ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) = _ at h
  symm
  rw [← h]
  apply MeasureTheory.integral_congr_ae
  exact ae_of_all _ fun z => by
    change su2FirstRailMass z ^ n * su2RailCrossIm z ^ 2 =
      su2FirstRailMass (su2MetricSphereSecondPhase (Real.pi / 2) z) ^ n *
        su2RailCrossRe (su2MetricSphereSecondPhase (Real.pi / 2) z) ^ 2
    have hmass :
        su2FirstRailMass (su2MetricSphereSecondPhase (Real.pi / 2) z) =
          su2FirstRailMass z := by
      simp [su2FirstRailMass, su2MetricSphereFirstReal,
        su2MetricSphereFirstImag, su2MetricSphereSecondPhase,
        linearIsometryUnitSphereMap, su2SecondPhaseAmbient,
        complexPhaseLinearIsometryEquiv]
    have hcross :
        su2RailCrossRe (su2MetricSphereSecondPhase (Real.pi / 2) z) =
          -su2RailCrossIm z := by
      simp [su2RailCrossRe, su2RailCrossIm,
      su2MetricSphereFirstReal, su2MetricSphereFirstImag,
      su2MetricSphereSecondReal, su2MetricSphereSecondImag,
      su2MetricSphereSecondPhase, linearIsometryUnitSphereMap,
      su2SecondPhaseAmbient, complexPhaseLinearIsometryEquiv,
      Complex.mul_re, Complex.mul_im]
      ring
    rw [hmass, hcross]
    ring

theorem integral_firstRail_pow_mul_crossRe_sq (n : Nat) :
    2 * (∫ z : SU2MetricSphere,
      su2FirstRailMass z ^ n * su2RailCrossRe z ^ 2
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) =
    ∫ z : SU2MetricSphere,
      su2FirstRailMass z ^ (n + 1) * su2SecondRailMass z
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) := by
  let mu : Measure SU2MetricSphere := su2CanonicalSphereProbability
  have hR : Integrable (fun z : SU2MetricSphere =>
      su2FirstRailMass z ^ n * su2RailCrossRe z ^ 2) mu :=
    integrable_continuous_canonicalSphere
      ((continuous_su2FirstRailMass.pow n).mul
        (continuous_su2RailCrossRe.pow 2))
  have hI : Integrable (fun z : SU2MetricSphere =>
      su2FirstRailMass z ^ n * su2RailCrossIm z ^ 2) mu :=
    integrable_continuous_canonicalSphere
      ((continuous_su2FirstRailMass.pow n).mul
        (continuous_su2RailCrossIm.pow 2))
  rw [show 2 * (∫ z, su2FirstRailMass z ^ n * su2RailCrossRe z ^ 2 ∂mu) =
      (∫ z, su2FirstRailMass z ^ n * su2RailCrossRe z ^ 2 ∂mu) +
      (∫ z, su2FirstRailMass z ^ n * su2RailCrossIm z ^ 2 ∂mu) by
        rw [integral_firstRail_pow_mul_crossRe_sq_eq_crossIm]; ring]
  rw [← MeasureTheory.integral_add hR hI]
  apply MeasureTheory.integral_congr_ae
  exact ae_of_all _ fun z => by
    change su2FirstRailMass z ^ n * su2RailCrossRe z ^ 2 +
      su2FirstRailMass z ^ n * su2RailCrossIm z ^ 2 =
        su2FirstRailMass z ^ (n + 1) * su2SecondRailMass z
    rw [← mul_add, su2RailCross_sq_add_sq]
    ring

/-- All-orders beta(1,1) recurrence for the first complex rail mass. -/
theorem su2FirstRailMoment_recurrence (n : Nat) (hnpos : 1 <= n) :
    ((n : Real) + 1) * su2FirstRailMoment n =
      (n : Real) * su2FirstRailMoment (n - 1) := by
  have hn : n ≠ 0 := Nat.ne_of_gt hnpos
  by_cases hn_one : n = 1
  · subst n
    rw [su2FirstRailMoment_one, su2FirstRailMoment_zero]
    norm_num
  have hn1 : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn
  have hn2 : 2 <= n := by omega
  have hsecond := integral_su2RotatedRailPowerSecondDeriv_eq_zero n 0
  norm_num [su2RotatedRailPowerSecondDeriv, su2RotatedRailMass,
    su2RotatedRailMassDeriv, su2RotatedRailMassSecondDeriv,
    Real.sin_zero, Real.cos_zero] at hsecond
  have hcross := integral_firstRail_pow_mul_crossRe_sq (n - 2)
  have hsub : n - 2 + 1 = n - 1 := by omega
  rw [hsub] at hcross
  have hpoint (z : SU2MetricSphere) :
      su2FirstRailMass z ^ (n - 1) *
          (su2SecondRailMass z - su2FirstRailMass z) =
        su2FirstRailMass z ^ (n - 1) -
          2 * su2FirstRailMass z ^ n := by
    have hs := su2FirstRailMass_add_second z
    have hp : su2FirstRailMass z ^ n =
        su2FirstRailMass z ^ (n - 1) * su2FirstRailMass z := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      su2FirstRailMass z ^ (n - 1) *
          (su2SecondRailMass z - su2FirstRailMass z) =
          su2FirstRailMass z ^ (n - 1) *
            ((1 - su2FirstRailMass z) - su2FirstRailMass z) := by
              rw [show su2SecondRailMass z = 1 - su2FirstRailMass z by linarith]
      _ = su2FirstRailMass z ^ (n - 1) -
          2 * (su2FirstRailMass z ^ (n - 1) * su2FirstRailMass z) := by ring
      _ = _ := by rw [← hp]
  have hIntPoint :
      (∫ z : SU2MetricSphere,
        su2FirstRailMass z ^ (n - 1) *
          (su2SecondRailMass z - su2FirstRailMass z)
          ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) =
        su2FirstRailMoment (n - 1) - 2 * su2FirstRailMoment n := by
    rw [show (fun z : SU2MetricSphere =>
        su2FirstRailMass z ^ (n - 1) *
          (su2SecondRailMass z - su2FirstRailMass z)) =
      (fun z => su2FirstRailMass z ^ (n - 1) -
        2 * su2FirstRailMass z ^ n) by funext z; exact hpoint z]
    rw [MeasureTheory.integral_sub]
    · rw [MeasureTheory.integral_const_mul]
      rfl
    · exact integrable_continuous_canonicalSphere
        (continuous_su2FirstRailMass.pow (n - 1))
    · exact (integrable_continuous_canonicalSphere
        (continuous_su2FirstRailMass.pow n)).const_mul 2
  -- Split the second-variation identity and use phase symmetry.
  have hcrossInt :
      (∫ z : SU2MetricSphere,
        su2FirstRailMass z ^ (n - 2) * su2RailCrossRe z ^ 2
          ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) =
      (1 / 2 : Real) *
        (∫ z : SU2MetricSphere,
          su2FirstRailMass z ^ (n - 1) * su2SecondRailMass z
            ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) := by
    nlinarith [hcross]
  have hsInt :
      (∫ z : SU2MetricSphere,
        su2FirstRailMass z ^ (n - 1) * su2SecondRailMass z
          ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) =
      su2FirstRailMoment (n - 1) - su2FirstRailMoment n := by
    have hp (z : SU2MetricSphere) :
        su2FirstRailMass z ^ (n - 1) * su2SecondRailMass z =
          su2FirstRailMass z ^ (n - 1) - su2FirstRailMass z ^ n := by
      have hs := su2FirstRailMass_add_second z
      have hpow : su2FirstRailMass z ^ n =
          su2FirstRailMass z ^ (n - 1) * su2FirstRailMass z := by
        rw [← pow_succ]
        congr 1
        omega
      calc
        su2FirstRailMass z ^ (n - 1) * su2SecondRailMass z =
            su2FirstRailMass z ^ (n - 1) *
              (1 - su2FirstRailMass z) := by
                rw [show su2SecondRailMass z = 1 - su2FirstRailMass z by linarith]
        _ = su2FirstRailMass z ^ (n - 1) -
            su2FirstRailMass z ^ (n - 1) * su2FirstRailMass z := by ring
        _ = _ := by rw [← hpow]
    rw [show (fun z : SU2MetricSphere =>
        su2FirstRailMass z ^ (n - 1) * su2SecondRailMass z) =
      (fun z => su2FirstRailMass z ^ (n - 1) -
        su2FirstRailMass z ^ n) by funext z; exact hp z]
    rw [MeasureTheory.integral_sub]
    · rfl
    · exact integrable_continuous_canonicalSphere
        (continuous_su2FirstRailMass.pow (n - 1))
    · exact integrable_continuous_canonicalSphere
        (continuous_su2FirstRailMass.pow n)
  rw [hsInt] at hcrossInt
  -- Normalize the integral identity into moments.
  have hsplit :
      (∫ z : SU2MetricSphere,
        (n : Real) * (n - 1 : Nat) * su2FirstRailMass z ^ (n - 2) *
            ((2 * su2RailCrossRe z) ^ 2) +
          (n : Real) * su2FirstRailMass z ^ (n - 1) *
            (2 * (su2SecondRailMass z - su2FirstRailMass z))
        ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) =
      (n : Real) * (n - 1 : Nat) * 4 *
          (∫ z : SU2MetricSphere,
            su2FirstRailMass z ^ (n - 2) * su2RailCrossRe z ^ 2
              ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) +
        (n : Real) * 2 *
          (∫ z : SU2MetricSphere,
            su2FirstRailMass z ^ (n - 1) *
              (su2SecondRailMass z - su2FirstRailMass z)
              ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) := by
    rw [show (fun z : SU2MetricSphere =>
        (n : Real) * (n - 1 : Nat) * su2FirstRailMass z ^ (n - 2) *
            ((2 * su2RailCrossRe z) ^ 2) +
          (n : Real) * su2FirstRailMass z ^ (n - 1) *
            (2 * (su2SecondRailMass z - su2FirstRailMass z))) =
      (fun z => ((n : Real) * (n - 1 : Nat) * 4) *
          (su2FirstRailMass z ^ (n - 2) * su2RailCrossRe z ^ 2) +
        ((n : Real) * 2) *
          (su2FirstRailMass z ^ (n - 1) *
            (su2SecondRailMass z - su2FirstRailMass z))) by
      funext z; ring]
    rw [MeasureTheory.integral_add,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    · exact integrable_continuous_canonicalSphere
        (continuous_const.mul
          ((continuous_su2FirstRailMass.pow (n - 2)).mul
            (continuous_su2RailCrossRe.pow 2)))
    · exact integrable_continuous_canonicalSphere
        (((continuous_const.mul continuous_const).mul
          ((continuous_su2FirstRailMass.pow (n - 1)).mul
            (continuous_su2SecondRailMass.sub continuous_su2FirstRailMass))))
  rw [hsplit, hcrossInt, hIntPoint] at hsecond
  have hcast : ((n - 1 : Nat) : Real) = (n : Real) - 1 := by
    rw [Nat.cast_sub hn1]
    norm_num
  rw [hcast] at hsecond
  have hnreal : (n : Real) ≠ 0 := by exact_mod_cast hn
  nlinarith

theorem su2FirstRailMoment_eq (n : Nat) :
    su2FirstRailMoment n = 1 / ((n : Real) + 1) := by
  induction n with
  | zero => rw [su2FirstRailMoment_zero]; norm_num
  | succ n ih =>
      have h := su2FirstRailMoment_recurrence (n + 1) (by omega)
      norm_num only [Nat.add_sub_cancel] at h
      rw [ih] at h
      norm_num [Nat.cast_add] at h
      have hn1 : (n : Real) + 1 ≠ 0 := by positivity
      field_simp [hn1] at h
      have hn2 : (n : Real) + 2 ≠ 0 := by positivity
      rw [show (((n + 1 : Nat) : Real) + 1) = (n : Real) + 2 by
        push_cast; ring]
      change su2FirstRailMoment (n + 1) = 1 / ((n : Real) + 2)
      apply (eq_div_iff hn2).2
      nlinarith

/-- Pushforward of the canonical spherical probability by the first rail
mass. -/
def su2FirstRailMassMeasure : Measure Real :=
  (su2CanonicalSphereProbability : Measure SU2MetricSphere).map
    su2FirstRailMass

instance : IsProbabilityMeasure su2FirstRailMassMeasure := by
  constructor
  rw [su2FirstRailMassMeasure,
    Measure.map_apply continuous_su2FirstRailMass.measurable MeasurableSet.univ]
  simp

/-- Lebesgue probability on `[0,1]`. -/
def su2UnitIntervalMeasure : Measure Real :=
  volume.restrict (Icc (0 : Real) 1)

theorem su2UnitIntervalMeasure_univ : su2UnitIntervalMeasure Set.univ = 1 := by
  simp [su2UnitIntervalMeasure]

instance : IsProbabilityMeasure su2UnitIntervalMeasure where
  measure_univ := su2UnitIntervalMeasure_univ

theorem ae_su2FirstRailMassMeasure_mem_Icc :
    ∀ᵐ x : Real ∂su2FirstRailMassMeasure, x ∈ Icc (0 : Real) 1 := by
  rw [su2FirstRailMassMeasure]
  exact (ae_map_iff
    (μ := (su2CanonicalSphereProbability : Measure SU2MetricSphere))
    continuous_su2FirstRailMass.measurable.aemeasurable measurableSet_Icc).2
      (ae_of_all _ fun z =>
        ⟨su2FirstRailMass_nonneg z, su2FirstRailMass_le_one z⟩)

theorem ae_su2UnitIntervalMeasure_mem_Icc :
    ∀ᵐ x : Real ∂su2UnitIntervalMeasure, x ∈ Icc (0 : Real) 1 := by
  rw [su2UnitIntervalMeasure]
  exact ae_restrict_mem measurableSet_Icc

theorem integral_pow_su2FirstRailMassMeasure (n : Nat) :
    (∫ x : Real, x ^ n ∂su2FirstRailMassMeasure) = 1 / ((n : Real) + 1) := by
  rw [su2FirstRailMassMeasure]
  have hmap := MeasureTheory.integral_map
    (μ := (su2CanonicalSphereProbability : Measure SU2MetricSphere))
    continuous_su2FirstRailMass.measurable.aemeasurable
    ((continuous_id.pow n).aestronglyMeasurable)
  calc
    (∫ x : Real, x ^ n ∂Measure.map su2FirstRailMass
        (su2CanonicalSphereProbability : Measure SU2MetricSphere)) =
        ∫ z : SU2MetricSphere, su2FirstRailMass z ^ n
          ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) := by
      simpa using hmap
    _ = _ := su2FirstRailMoment_eq n

theorem integral_pow_su2UnitIntervalMeasure (n : Nat) :
    (∫ x : Real, x ^ n ∂su2UnitIntervalMeasure) = 1 / ((n : Real) + 1) := by
  rw [su2UnitIntervalMeasure]
  change (∫ x : Real in Icc (0 : Real) 1, x ^ n) = _
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : Real) <= 1)]
  rw [integral_pow]
  norm_num

theorem integrable_pow_su2FirstRailMassMeasure (n : Nat) :
    Integrable (fun x : Real => x ^ n) su2FirstRailMassMeasure := by
  refine (integrable_const (1 : Real)).mono'
    ((continuous_id.pow n).aestronglyMeasurable) ?_
  filter_upwards [ae_su2FirstRailMassMeasure_mem_Icc] with x hx
  rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hx.1]
  exact pow_le_one₀ hx.1 hx.2

theorem integrable_pow_su2UnitIntervalMeasure (n : Nat) :
    Integrable (fun x : Real => x ^ n) su2UnitIntervalMeasure := by
  refine (integrable_const (1 : Real)).mono'
    ((continuous_id.pow n).aestronglyMeasurable) ?_
  filter_upwards [ae_su2UnitIntervalMeasure_mem_Icc] with x hx
  rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hx.1]
  exact pow_le_one₀ hx.1 hx.2

theorem integrable_polynomial_su2FirstRailMassMeasure (p : Real[X]) :
    Integrable (fun x : Real => p.eval x) su2FirstRailMassMeasure := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n a =>
      simpa only [Polynomial.eval_monomial] using
        (integrable_pow_su2FirstRailMassMeasure n).const_mul a

theorem integrable_polynomial_su2UnitIntervalMeasure (p : Real[X]) :
    Integrable (fun x : Real => p.eval x) su2UnitIntervalMeasure := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n a =>
      simpa only [Polynomial.eval_monomial] using
        (integrable_pow_su2UnitIntervalMeasure n).const_mul a

theorem integral_polynomial_su2FirstRailMassMeasure_eq_uniform
    (p : Real[X]) :
    (∫ x : Real, p.eval x ∂su2FirstRailMassMeasure) =
      ∫ x : Real, p.eval x ∂su2UnitIntervalMeasure := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval_add]
      rw [MeasureTheory.integral_add
          (integrable_polynomial_su2FirstRailMassMeasure p)
          (integrable_polynomial_su2FirstRailMassMeasure q),
        MeasureTheory.integral_add
          (integrable_polynomial_su2UnitIntervalMeasure p)
          (integrable_polynomial_su2UnitIntervalMeasure q), hp, hq]
  | monomial n a =>
      simp only [Polynomial.eval_monomial]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        integral_pow_su2FirstRailMassMeasure,
        integral_pow_su2UnitIntervalMeasure]

/-- Literal beta(1,1) law for the squared first complex coordinate of
normalized `S³`. -/
theorem su2FirstRailMassMeasure_eq_uniform :
    su2FirstRailMassMeasure = su2UnitIntervalMeasure := by
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  by_contra hne
  let delta : Real :=
    |(∫ x : Real, f x ∂su2FirstRailMassMeasure) -
      ∫ x : Real, f x ∂su2UnitIntervalMeasure|
  have hdelta : 0 < delta := abs_pos.mpr (sub_ne_zero.mpr hne)
  let eps : Real := delta / 4
  have heps : 0 < eps := by dsimp [eps]; positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn
    (0 : Real) 1 (fun x : Real => f x) f.continuous.continuousOn eps heps
  have hRbound : ∀ᵐ x : Real ∂su2FirstRailMassMeasure,
      ‖f x - p.eval x‖ <= eps := by
    filter_upwards [ae_su2FirstRailMassMeasure_mem_Icc] with x hx
    simpa [Real.norm_eq_abs, abs_sub_comm] using (hp x hx).le
  have hUbound : ∀ᵐ x : Real ∂su2UnitIntervalMeasure,
      ‖f x - p.eval x‖ <= eps := by
    filter_upwards [ae_su2UnitIntervalMeasure_mem_Icc] with x hx
    simpa [Real.norm_eq_abs, abs_sub_comm] using (hp x hx).le
  have hRerr := MeasureTheory.norm_integral_le_of_norm_le_const hRbound
  have hUerr := MeasureTheory.norm_integral_le_of_norm_le_const hUbound
  have hfR : Integrable (fun x : Real => f x) su2FirstRailMassMeasure :=
    f.integrable su2FirstRailMassMeasure
  have hfU : Integrable (fun x : Real => f x) su2UnitIntervalMeasure :=
    f.integrable su2UnitIntervalMeasure
  have hpR := integrable_polynomial_su2FirstRailMassMeasure p
  have hpU := integrable_polynomial_su2UnitIntervalMeasure p
  rw [MeasureTheory.integral_sub hfR hpR] at hRerr
  rw [MeasureTheory.integral_sub hfU hpU] at hUerr
  have hRmass : su2FirstRailMassMeasure.real Set.univ = 1 := by simp
  have hUmass : su2UnitIntervalMeasure.real Set.univ = 1 := by simp
  rw [hRmass, mul_one] at hRerr
  rw [hUmass, mul_one] at hUerr
  have hpoly := integral_polynomial_su2FirstRailMassMeasure_eq_uniform p
  have htriangle : delta <=
      |(∫ x : Real, f x ∂su2FirstRailMassMeasure) -
        ∫ x : Real, p.eval x ∂su2FirstRailMassMeasure| +
      |(∫ x : Real, f x ∂su2UnitIntervalMeasure) -
        ∫ x : Real, p.eval x ∂su2UnitIntervalMeasure| := by
    dsimp [delta]
    rw [← hpoly]
    calc
      |(∫ x : Real, f x ∂su2FirstRailMassMeasure) -
          ∫ x : Real, f x ∂su2UnitIntervalMeasure| <=
          |(∫ x : Real, f x ∂su2FirstRailMassMeasure) -
            ∫ x : Real, p.eval x ∂su2FirstRailMassMeasure| +
          |(∫ x : Real, p.eval x ∂su2FirstRailMassMeasure) -
            ∫ x : Real, f x ∂su2UnitIntervalMeasure| := abs_sub_le _ _ _
      _ = _ := by
        rw [abs_sub_comm
          (∫ x : Real, p.eval x ∂su2FirstRailMassMeasure)
          (∫ x : Real, f x ∂su2UnitIntervalMeasure)]
  have : delta <= 2 * eps := by
    calc
      delta <= _ := htriangle
      _ <= eps + eps := add_le_add hRerr hUerr
      _ = 2 * eps := by ring
  dsimp [eps] at this
  nlinarith

/-- Continuous integration form of the uniform orbital law. -/
theorem integral_su2FirstRailMass_eq_unitInterval (f : Real -> Real)
    (hf : Continuous f) :
    (∫ z : SU2MetricSphere, f (su2FirstRailMass z)
      ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) =
      ∫ u : Real in Set.Icc (0 : Real) 1, f u := by
  have hmap := MeasureTheory.integral_map
    (μ := (su2CanonicalSphereProbability : Measure SU2MetricSphere))
    continuous_su2FirstRailMass.measurable.aemeasurable
    hf.aestronglyMeasurable
  calc
    (∫ z : SU2MetricSphere, f (su2FirstRailMass z)
      ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere)) =
        ∫ u : Real, f u ∂su2FirstRailMassMeasure := by
      simpa [su2FirstRailMassMeasure] using hmap.symm
    _ = ∫ u : Real, f u ∂su2UnitIntervalMeasure := by
      rw [su2FirstRailMassMeasure_eq_uniform]
    _ = _ := rfl

end Lean2dYangMills
