import Lean2dYangMills.SU2Orbit
import Lean2dYangMills.SU2Convolution
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# All-order character convolution on SU(2)

This file consumes the literal uniform Hopf coordinate from `SU2Orbit`.
The analytic core is the product formula for Chebyshev `U` polynomials;
the group-theoretic core averages a translated character over conjugacy
orbits and then applies the already proved Weyl formula.
-/

noncomputable section

open scoped ENNReal Interval Polynomial

namespace Lean2dYangMills

open Matrix Set MeasureTheory intervalIntegral

instance instIsHaarMeasureSU2HaarProb :
    Measure.IsHaarMeasure su2HaarProb := by
  unfold su2HaarProb
  infer_instance

/-- Normalized Haar on the compact group SU(2) is also right invariant. -/
instance instIsMulRightInvariantSU2HaarProb :
    su2HaarProb.IsMulRightInvariant where
  map_mul_right_eq_self g := by
    let ν : Measure SU2 := Measure.map (fun x : SU2 => x * g) su2HaarProb
    haveI : IsProbabilityMeasure ν := by
      constructor
      change (Measure.map (fun x : SU2 => x * g) su2HaarProb) Set.univ = 1
      calc
        (Measure.map (fun x : SU2 => x * g) su2HaarProb) Set.univ =
            su2HaarProb ((fun x : SU2 => x * g) ⁻¹' Set.univ) :=
          Measure.map_apply_of_aemeasurable
            ((continuous_id.mul continuous_const).measurable.aemeasurable)
            MeasurableSet.univ
        _ = 1 := by simp
    have hν := Measure.isMulInvariant_eq_smul_of_compactSpace ν su2HaarProb
    have hu := congrArg (fun μ : Measure SU2 => μ Set.univ) hν
    have hc : ν.haarScalarFactor su2HaarProb = 1 := by
      simpa [ENNReal.smul_def] using hu.symm
    rw [hc] at hν
    have hOne : (1 : ENNReal) • su2HaarProb = su2HaarProb := by
      ext s hs
      simp [Measure.smul_apply, ENNReal.smul_def, hs]
    change ν = su2HaarProb
    exact hν.trans hOne

private abbrev Ureal (n : Nat) : Real[X] :=
  Polynomial.Chebyshev.U Real (n : Int)

private abbrev Treal (n : Nat) : Real[X] :=
  Polynomial.Chebyshev.T Real (n : Int)

theorem intervalIntegral_chebyshevU_affine
    (m : Nat) (a b : Real) (hb : b ≠ 0) :
    (∫ u : Real in (-1)..1, (Ureal m).eval (a + b * u)) =
      ((Treal (m + 1)).eval (a + b) -
        (Treal (m + 1)).eval (a - b)) /
          (b * ((m : Real) + 1)) := by
  let f : Real -> Real := fun u => a + b * u
  let f' : Real -> Real := fun _ => b
  let g : Real -> Real := fun x => (Treal (m + 1)).eval x
  let g' : Real -> Real := fun x => (Treal (m + 1)).derivative.eval x
  have hf : ∀ x ∈ Set.uIcc (-1 : Real) 1,
      HasDerivAt f (f' x) x := by
    intro x _hx
    simpa [f, f', mul_comm] using (hasDerivAt_id x).const_mul b |>.const_add a
  have hg : ∀ x ∈ Set.uIcc (-1 : Real) 1,
      HasDerivAt g (g' (f x)) (f x) := by
    intro x _hx
    exact (Treal (m + 1)).hasDerivAt (f x)
  have hsub := intervalIntegral.integral_deriv_comp_mul_deriv
    (a := (-1 : Real)) (b := 1) hf hg
    (continuous_const.continuousOn)
    ((Treal (m + 1)).derivative.continuous)
  have hderiv : (Treal (m + 1)).derivative =
      Polynomial.C (((m : Real) + 1)) * Ureal m := by
    rw [Polynomial.Chebyshev.T_derivative_eq_U]
    norm_num [Treal, Ureal]
  have hmain :
      b * ((m : Real) + 1) *
        (∫ u : Real in (-1)..1, (Ureal m).eval (a + b * u)) =
      (Treal (m + 1)).eval (a + b) -
        (Treal (m + 1)).eval (a - b) := by
    rw [show (fun u : Real =>
        (g' ∘ f) u * f' u) =
      (fun u => b * ((m : Real) + 1) * (Ureal m).eval (a + b * u)) by
        funext u
        simp [g', f, f', hderiv]
        ring] at hsub
    rw [intervalIntegral.integral_const_mul] at hsub
    simpa [f, g] using hsub
  have hden : b * ((m : Real) + 1) ≠ 0 := mul_ne_zero hb (by positivity)
  apply (eq_div_iff hden).2
  simpa [mul_comm] using hmain

theorem intervalIntegral_chebyshevU_product_formula_of_sin_ne_zero
    (m : Nat) (theta phi : Real)
    (htheta : Real.sin theta ≠ 0) (hphi : Real.sin phi ≠ 0) :
    (∫ u : Real in (-1)..1,
      (Ureal m).eval
        (Real.cos theta * Real.cos phi +
          Real.sin theta * Real.sin phi * u)) =
      2 * (Ureal m).eval (Real.cos theta) *
        (Ureal m).eval (Real.cos phi) / ((m : Real) + 1) := by
  let a := Real.cos theta * Real.cos phi
  let b := Real.sin theta * Real.sin phi
  have hb : b ≠ 0 := mul_ne_zero htheta hphi
  rw [show (fun u : Real =>
      (Ureal m).eval
        (Real.cos theta * Real.cos phi +
          Real.sin theta * Real.sin phi * u)) =
      (fun u => (Ureal m).eval (a + b * u)) by rfl]
  rw [intervalIntegral_chebyshevU_affine m a b hb]
  have hplus : a + b = Real.cos (theta - phi) := by
    dsimp [a, b]
    rw [Real.cos_sub]
  have hminus : a - b = Real.cos (theta + phi) := by
    dsimp [a, b]
    rw [Real.cos_add]
  rw [hplus, hminus, Polynomial.Chebyshev.T_real_cos,
    Polynomial.Chebyshev.T_real_cos]
  have hUtheta := Polynomial.Chebyshev.U_real_cos theta (m : Int)
  have hUphi := Polynomial.Chebyshev.U_real_cos phi (m : Int)
  have hUtheta' :
      (Ureal m).eval (Real.cos theta) * Real.sin theta =
        Real.sin (((m : Real) + 1) * theta) := by
    convert hUtheta using 1
  have hUphi' :
      (Ureal m).eval (Real.cos phi) * Real.sin phi =
        Real.sin (((m : Real) + 1) * phi) := by
    convert hUphi using 1
  push_cast
  rw [show ((m : Real) + 1) * (theta - phi) =
      ((m : Real) + 1) * theta - ((m : Real) + 1) * phi by ring,
    show ((m : Real) + 1) * (theta + phi) =
      ((m : Real) + 1) * theta + ((m : Real) + 1) * phi by ring,
    Real.cos_sub, Real.cos_add]
  rw [← hUtheta', ← hUphi']
  dsimp [b]
  field_simp
  ring

/-- The Chebyshev product formula in the closed trace square.  Endpoint
cases are included explicitly, so later convolution theorems have no
genericity hypothesis on the group element. -/
theorem intervalIntegral_chebyshevU_product_formula
    (m : Nat) (x y : Real)
    (hx : x ∈ Set.Icc (-1 : Real) 1)
    (hy : y ∈ Set.Icc (-1 : Real) 1) :
    (∫ u : Real in (-1)..1,
      (Ureal m).eval
        (x * y + Real.sqrt (1 - x ^ 2) *
          Real.sqrt (1 - y ^ 2) * u)) =
      2 * (Ureal m).eval x * (Ureal m).eval y /
        ((m : Real) + 1) := by
  by_cases hxm : x = -1
  · subst x
    simp [Polynomial.Chebyshev.U_eval_neg_one,
      Polynomial.Chebyshev.U_eval_neg, Ureal]
    push_cast
    field_simp
    ring
  by_cases hxp : x = 1
  · subst x
    simp [Polynomial.Chebyshev.U_eval_one, Ureal]
    field_simp
    ring
  by_cases hym : y = -1
  · subst y
    simp [Polynomial.Chebyshev.U_eval_neg_one,
      Polynomial.Chebyshev.U_eval_neg, Ureal]
    push_cast
    field_simp
    ring
  by_cases hyp : y = 1
  · subst y
    simp [Polynomial.Chebyshev.U_eval_one, Ureal]
    field_simp
    ring
  have hxint : -1 < x ∧ x < 1 := by
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxm),
      lt_of_le_of_ne hx.2 hxp⟩
  have hyint : -1 < y ∧ y < 1 := by
    exact ⟨lt_of_le_of_ne hy.1 (Ne.symm hym),
      lt_of_le_of_ne hy.2 hyp⟩
  have hsx : Real.sin (Real.arccos x) ≠ 0 := by
    rw [Real.sin_arccos]
    exact (Real.sqrt_pos.2 (by nlinarith)).ne'
  have hsy : Real.sin (Real.arccos y) ≠ 0 := by
    rw [Real.sin_arccos]
    exact (Real.sqrt_pos.2 (by nlinarith)).ne'
  simpa [Real.cos_arccos hx.1 hx.2, Real.cos_arccos hy.1 hy.2,
    Real.sin_arccos] using
      intervalIntegral_chebyshevU_product_formula_of_sin_ne_zero
        m (Real.arccos x) (Real.arccos y) hsx hsy

/-- Affine conversion of the uniform Hopf coordinate from `[0,1]` to
`[-1,1]`. -/
theorem integral_Icc_zero_one_comp_one_sub_two_mul (f : Real -> Real)
    (hf : Continuous f) :
    (∫ r : Real in Set.Icc (0 : Real) 1, f (1 - 2 * r)) =
      (1 / 2 : Real) * ∫ u : Real in (-1)..1, f u := by
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : Real) ≤ 1)]
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : Real)) (b := 1)
    (f := fun r : Real => 1 - 2 * r) (f' := fun _ => -2)
    (g := f)
    (fun r _ => by
      convert (hasDerivAt_const (x := r) (c := (1 : Real))).sub
        ((hasDerivAt_id r).const_mul 2) using 1 <;> ring)
    continuous_const.continuousOn hf
  have hsub' : (-2 : Real) *
      (∫ r : Real in (0 : Real)..1, f (1 - 2 * r)) =
      -(∫ u : Real in (-1 : Real)..1, f u) := by
    calc
      (-2 : Real) * (∫ r : Real in (0 : Real)..1, f (1 - 2 * r)) =
          ∫ r : Real in (0 : Real)..1, f (1 - 2 * r) * -2 := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro r _
        ring
      _ = ∫ u : Real in (1 : Real)..(-1), f u := by
        convert hsub using 1 <;> norm_num
      _ = -(∫ u : Real in (-1 : Real)..1, f u) := by
        exact intervalIntegral.integral_symm (μ := volume) (-1) 1
  linarith

/-- Squared modulus of the upper-left entry of a concrete SU(2) matrix. -/
def su2FirstEntryMass (g : SU2) : Real :=
  Complex.normSq (g.1 0 0)

theorem continuous_su2FirstEntryMass : Continuous su2FirstEntryMass := by
  unfold su2FirstEntryMass
  exact Complex.continuous_normSq.comp (continuous_su2_entry 0 0)

theorem su2FirstRailMass_comp_groupSphere (g : SU2) :
    su2FirstRailMass
      (rowSphereToMetricSphere (su2ToRowSphere g)) = su2FirstEntryMass g := by
  simp [su2FirstRailMass, su2FirstEntryMass,
    su2MetricSphereFirstReal, su2MetricSphereFirstImag,
    rowSphereToMetricSphere, su2ToRowSphere, Complex.normSq_apply]
  ring

/-- The Hopf coordinate used in orbital integration is literally uniform:
the squared upper-left entry of normalized Haar SU(2) has beta(1,1) law. -/
theorem integral_su2FirstEntryMass_eq_unitInterval (f : Real -> Real)
    (hf : Continuous f) :
    (∫ g : SU2, f (su2FirstEntryMass g) ∂su2HaarProb) =
      ∫ r : Real in Set.Icc (0 : Real) 1, f r := by
  let e : SU2 ≃ₜ SU2MetricSphere :=
    su2HomeomorphRowSphere.trans rowSphereHomeomorphMetricSphere
  have hrow : MeasurePreserving rowSphereToMetricSphere su2RowSphereHaar
      (su2CanonicalSphereProbability : Measure SU2MetricSphere) := by
    rw [su2RowSphereHaar_eq_su2CanonicalRowSphereMeasure]
    exact MeasurePreserving.symm
      rowSphereHomeomorphMetricSphere.symm.toMeasurableEquiv
      measurePreserving_metricSphereToRowSphere_canonical
  have hpres : MeasurePreserving e su2HaarProb
      (su2CanonicalSphereProbability : Measure SU2MetricSphere) := by
    exact hrow.comp measurePreserving_su2ToRowSphere
  calc
    (∫ g : SU2, f (su2FirstEntryMass g) ∂su2HaarProb) =
        ∫ g : SU2, f (su2FirstRailMass (e g)) ∂su2HaarProb := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun g => by
        change f (su2FirstEntryMass g) =
          f (su2FirstRailMass
            (rowSphereToMetricSphere (su2ToRowSphere g)))
        rw [su2FirstRailMass_comp_groupSphere]
    _ = ∫ z : SU2MetricSphere, f (su2FirstRailMass z)
          ∂(su2CanonicalSphereProbability : Measure SU2MetricSphere) := by
      simpa using hpres.integral_comp
        e.toMeasurableEquiv.measurableEmbedding
        (fun z : SU2MetricSphere => f (su2FirstRailMass z))
    _ = _ := integral_su2FirstRailMass_eq_unitInterval f hf

/-- Exact half-trace of a conjugated pair of standard representatives.
This is the orbital coordinate identity consumed by the product formula. -/
theorem su2HalfTrace_conjugated_representatives
    (x y : Set.Icc (-1 : Real) 1) (k : SU2) :
    su2HalfTrace
      (k * su2HalfTraceRepresentative x * k⁻¹ *
        su2HalfTraceRepresentative y) =
      x * y + Real.sqrt (1 - x ^ 2) * Real.sqrt (1 - y ^ 2) *
        (1 - 2 * su2FirstEntryMass k) := by
  have hk00 : (k⁻¹ : SU2).1 0 0 = star (k.1 0 0) := by rfl
  have hk10 : (k⁻¹ : SU2).1 1 0 = star (k.1 0 1) := by rfl
  simp [su2HalfTrace, su2HalfTraceRepresentative, rowSphereToSU2,
    Matrix.mul_apply, Fin.sum_univ_two, Complex.normSq_apply,
    Complex.mul_re, hk00, hk10, su2FirstEntryMass]
  have hrow := su2_normSq_row_zero k
  simp [Complex.normSq_apply] at hrow
  linear_combination
    ((x : Real) * (y : Real)) * hrow +
      (Real.sqrt (1 - (x : Real) ^ 2) *
        Real.sqrt (1 - (y : Real) ^ 2)) * hrow

/-- Orbital product formula for every pair of SU(2) conjugacy classes. -/
theorem integral_su2Haar_orbit_character
    (m : Nat) (x y : Set.Icc (-1 : Real) 1) :
    (∫ k : SU2,
      (Ureal m).eval
        (su2HalfTrace
          (k * su2HalfTraceRepresentative x * k⁻¹ *
            su2HalfTraceRepresentative y)) ∂su2HaarProb) =
      (Ureal m).eval (x : Real) * (Ureal m).eval (y : Real) /
        ((m : Real) + 1) := by
  let F : Real -> Real := fun u =>
    (Ureal m).eval
      ((x : Real) * (y : Real) +
        Real.sqrt (1 - (x : Real) ^ 2) *
          Real.sqrt (1 - (y : Real) ^ 2) * u)
  have hF : Continuous F := by
    dsimp [F]
    exact (Ureal m).continuous.comp <| by fun_prop
  calc
    (∫ k : SU2,
      (Ureal m).eval
        (su2HalfTrace
          (k * su2HalfTraceRepresentative x * k⁻¹ *
            su2HalfTraceRepresentative y)) ∂su2HaarProb) =
        ∫ k : SU2, F (1 - 2 * su2FirstEntryMass k) ∂su2HaarProb := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun k => by
        dsimp [F]
        rw [su2HalfTrace_conjugated_representatives]
    _ = ∫ r : Real in Set.Icc (0 : Real) 1, F (1 - 2 * r) :=
      integral_su2FirstEntryMass_eq_unitInterval
        (fun r => F (1 - 2 * r)) (hF.comp <| by fun_prop)
    _ = (1 / 2 : Real) * ∫ u : Real in (-1)..1, F u :=
      integral_Icc_zero_one_comp_one_sub_two_mul F hF
    _ = _ := by
      rw [intervalIntegral_chebyshevU_product_formula m x y x.2 y.2]
      field_simp

theorem su2HalfTrace_conjugate (k g : SU2) :
    su2HalfTrace (k * g * k⁻¹) = su2HalfTrace g := by
  have ht : Matrix.trace ((k * g * k⁻¹ : SU2).1) = Matrix.trace g.1 := by
    change Matrix.trace (k.1 * g.1 * (k⁻¹ : SU2).1) = Matrix.trace g.1
    rw [Matrix.trace_mul_cycle]
    change Matrix.trace ((k⁻¹ * k * g : SU2).1) = Matrix.trace g.1
    simp
  have hl := su2_half_trace_eq_ofReal_re (k * g * k⁻¹)
  have hr := su2_half_trace_eq_ofReal_re g
  have hc : (su2HalfTrace (k * g * k⁻¹) : Complex) =
      (su2HalfTrace g : Complex) := by
    change (((k * g * k⁻¹ : SU2).1 0 0).re : Complex) =
      ((g.1 0 0).re : Complex)
    rw [← hl, ← hr, ht]
  exact_mod_cast hc

@[simp]
theorem su2HalfTrace_inv (g : SU2) :
    su2HalfTrace g⁻¹ = su2HalfTrace g := by
  have h00 : (g⁻¹ : SU2).1 0 0 = star (g.1 0 0) := by rfl
  simp [su2HalfTrace, h00]

/-- Coordinate-free orbital product formula. -/
theorem integral_su2Haar_orbit_character_general
    (m : Nat) (a b : SU2) :
    (∫ k : SU2,
      (Ureal m).eval (su2HalfTrace (k * a * k⁻¹ * b))
        ∂su2HaarProb) =
      (Ureal m).eval (su2HalfTrace a) *
        (Ureal m).eval (su2HalfTrace b) / ((m : Real) + 1) := by
  let x : Set.Icc (-1 : Real) 1 :=
    ⟨su2HalfTrace a, su2HalfTrace_mem_Icc a⟩
  let y : Set.Icc (-1 : Real) 1 :=
    ⟨su2HalfTrace b, su2HalfTrace_mem_Icc b⟩
  obtain ⟨h, ha⟩ := su2_conjugate_of_halfTrace_eq
    (g := a) (h := su2HalfTraceRepresentative x) (by
      rw [su2HalfTrace_representative]
      )
  obtain ⟨l, hb⟩ := su2_conjugate_of_halfTrace_eq
    (g := b) (h := su2HalfTraceRepresentative y) (by
      rw [su2HalfTrace_representative]
      )
  let q : SU2 -> Real := fun k =>
    (Ureal m).eval
      (su2HalfTrace
        (k * su2HalfTraceRepresentative x * k⁻¹ *
          su2HalfTraceRepresentative y))
  have hpoint : (fun k : SU2 =>
      (Ureal m).eval (su2HalfTrace (k * a * k⁻¹ * b))) =
      (fun k : SU2 => q (l⁻¹ * k * h)) := by
    funext k
    dsimp [q]
    rw [ha, hb]
    congr 1
    have hc := su2HalfTrace_conjugate l⁻¹
      (k * (h * su2HalfTraceRepresentative x * h⁻¹) * k⁻¹ *
        (l * su2HalfTraceRepresentative y * l⁻¹))
    rw [← hc]
    congr 1
    group
  rw [hpoint]
  have hright := integral_mul_right_eq_self (μ := su2HaarProb)
    (fun k : SU2 => q (l⁻¹ * k)) h
  have hleft := integral_mul_left_eq_self (μ := su2HaarProb) q l⁻¹
  change (∫ k : SU2, q (l⁻¹ * k * h) ∂su2HaarProb) = _
  have hright' : (∫ k : SU2, q (l⁻¹ * k * h) ∂su2HaarProb) =
      ∫ k : SU2, q (l⁻¹ * k) ∂su2HaarProb := by
    simpa [mul_assoc] using hright
  rw [hright', hleft]
  simpa [x, y] using integral_su2Haar_orbit_character m x y

def su2CharacterReal (n : Nat) (g : SU2) : Real :=
  (Ureal n).eval (su2HalfTrace g)

theorem continuous_su2CharacterReal (n : Nat) :
    Continuous (su2CharacterReal n) := by
  exact (Ureal n).continuous.comp continuous_su2HalfTrace

theorem su2CharacterReal_conjugate (n : Nat) (k g : SU2) :
    su2CharacterReal n (k * g * k⁻¹) = su2CharacterReal n g := by
  simp [su2CharacterReal, su2HalfTrace_conjugate]

theorem abs_su2CharacterReal_le (n : Nat) (g : SU2) :
    |su2CharacterReal n g| ≤ (n : Real) + 1 := by
  exact abs_chebyshevU_real_le_of_mem_Icc n _ (su2HalfTrace_mem_Icc g)

/-- Schur convolution for every pair of SU(2) characters, in real form. -/
theorem integral_su2CharacterReal_mul_translate (n m : Nat) (g : SU2) :
    (∫ x : SU2,
      su2CharacterReal n x * su2CharacterReal m (x⁻¹ * g)
        ∂su2HaarProb) =
      if n = m then su2CharacterReal n g / ((n : Real) + 1) else 0 := by
  let F : SU2 -> Real := fun x =>
    su2CharacterReal n x * su2CharacterReal m (x⁻¹ * g)
  let H : SU2 -> SU2 -> Real := fun k x =>
    su2CharacterReal n x *
      su2CharacterReal m (k * x⁻¹ * k⁻¹ * g)
  have hFconj (k : SU2) :
      (fun x : SU2 => F (k * x * k⁻¹)) = H k := by
    funext x
    dsimp [F, H]
    rw [su2CharacterReal_conjugate]
    congr 1
    group
  have hinv (k : SU2) :
      (∫ x : SU2, H k x ∂su2HaarProb) =
        ∫ x : SU2, F x ∂su2HaarProb := by
    have hl := integral_mul_left_eq_self (μ := su2HaarProb)
      (fun x : SU2 => F (x * k⁻¹)) k
    have hr := integral_mul_right_eq_self (μ := su2HaarProb) F k⁻¹
    have hl' : (∫ x : SU2, F (k * x * k⁻¹) ∂su2HaarProb) =
        ∫ x : SU2, F (x * k⁻¹) ∂su2HaarProb := by
      simpa [mul_assoc] using hl
    rw [← hFconj k, hl', hr]
  have hHcont : Continuous (Function.uncurry H) := by
    dsimp [H, Function.uncurry]
    exact (continuous_su2CharacterReal n).comp continuous_snd |>.mul <|
      (continuous_su2CharacterReal m).comp <| by fun_prop
  calc
    (∫ x : SU2,
      su2CharacterReal n x * su2CharacterReal m (x⁻¹ * g)
        ∂su2HaarProb) = ∫ x : SU2, F x ∂su2HaarProb := rfl
    _ = ∫ k : SU2, (∫ x : SU2, H k x ∂su2HaarProb)
          ∂su2HaarProb := by
      rw [show (fun k : SU2 => ∫ x : SU2, H k x ∂su2HaarProb) =
          fun _ => ∫ x : SU2, F x ∂su2HaarProb by
        funext k
        exact hinv k]
      simp
    _ = ∫ x : SU2, (∫ k : SU2, H k x ∂su2HaarProb)
          ∂su2HaarProb :=
      MeasureTheory.integral_integral_swap_of_hasCompactSupport hHcont
        (HasCompactSupport.of_compactSpace _)
    _ = ∫ x : SU2,
        su2CharacterReal n x *
          (su2CharacterReal m x * su2CharacterReal m g /
            ((m : Real) + 1)) ∂su2HaarProb := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp [H]
        rw [MeasureTheory.integral_const_mul]
        have horb := integral_su2Haar_orbit_character_general m x⁻¹ g
        rw [show (∫ k : SU2,
            su2CharacterReal m (k * x⁻¹ * k⁻¹ * g) ∂su2HaarProb) =
            su2CharacterReal m x⁻¹ * su2CharacterReal m g /
              ((m : Real) + 1) by
          simpa [su2CharacterReal] using horb]
        simp [su2CharacterReal, su2HalfTrace_inv]
    _ = _ := by
      rw [show (fun x : SU2 =>
          su2CharacterReal n x *
            (su2CharacterReal m x * su2CharacterReal m g /
              ((m : Real) + 1))) =
          fun x => (su2CharacterReal m g / ((m : Real) + 1)) *
            (su2CharacterReal n x * su2CharacterReal m x) by
        funext x; ring]
      rw [MeasureTheory.integral_const_mul]
      unfold su2CharacterReal
      rw [integral_su2Chebyshev_real_mul]
      split_ifs with hnm
      · subst m
        ring
      · simp [hnm]

/-- Actual translated group convolution of arbitrary SU(2) characters. -/
theorem su2CharacterChebyshev_convolution (n m : Nat) (g : SU2) :
    su2Convolution (su2CharacterChebyshev n)
      (su2CharacterChebyshev m) g =
      if n = m then (1 / ((n : Complex) + 1)) *
        su2CharacterChebyshev n g else 0 := by
  rw [su2Convolution]
  have hpoint : (fun x : SU2 =>
      su2CharacterChebyshev n x *
        su2CharacterChebyshev m (x⁻¹ * g)) =
      fun x : SU2 =>
        ((su2CharacterReal n x *
          su2CharacterReal m (x⁻¹ * g) : Real) : Complex) := by
    funext x
    simp [su2CharacterChebyshev_eq_ofReal, su2CharacterReal]
  rw [hpoint, integral_complex_ofReal,
    integral_su2CharacterReal_mul_translate]
  split_ifs with hnm
  · subst m
    rw [su2CharacterChebyshev_eq_ofReal]
    push_cast
    field_simp
    exact Polynomial.Chebyshev.complex_ofReal_eval_U
      (su2HalfTrace g) (n : Int)
  · simp

end Lean2dYangMills
