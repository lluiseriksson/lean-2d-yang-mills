import Mathlib.Analysis.Matrix.Spectrum
import Lean2dYangMills.SU2Weyl

/-!
# Conjugacy fibers for SU(2)

This file develops the missing group-theoretic bridge from the radial Weyl
formula to arbitrary continuous class functions.
-/

noncomputable section

namespace Lean2dYangMills

open Matrix Set MeasureTheory

/-- The traceless Hermitian matrix `-i (g - Re(g₀₀) I)` associated to an
SU(2) element. -/
def su2HermitianPart (g : SU2) : Matrix (Fin 2) (Fin 2) Complex :=
  (-Complex.I) •
    ((g : Matrix (Fin 2) (Fin 2) Complex) -
      (su2HalfTrace g : Complex) • (1 : Matrix (Fin 2) (Fin 2) Complex))

theorem su2HermitianPart_apply_zero_zero (g : SU2) :
    su2HermitianPart g 0 0 =
      (((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).im : Complex) := by
  apply Complex.ext <;>
    simp [su2HermitianPart, su2HalfTrace, Matrix.one_apply,
      Complex.mul_re, Complex.mul_im]

theorem su2HermitianPart_apply_one_one (g : SU2) :
    su2HermitianPart g 1 1 =
      (-((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).im : Real) := by
  have h11 := su2_apply_one_one_eq_conj_apply_zero_zero g
  simp only [su2HermitianPart, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply]
  rw [h11]
  have hstar : star ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0) =
      ({ re := ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re,
         im := -((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).im } : Complex) := rfl
  rw [hstar]
  apply Complex.ext <;>
    simp [su2HalfTrace, smul_eq_mul, Complex.mul_re, Complex.mul_im]

theorem su2HermitianPart_apply_zero_one (g : SU2) :
    su2HermitianPart g 0 1 =
      -Complex.I * (g : Matrix (Fin 2) (Fin 2) Complex) 0 1 := by
  simp [su2HermitianPart, Matrix.one_apply]

theorem su2HermitianPart_apply_one_zero (g : SU2) :
    su2HermitianPart g 1 0 =
      ({ re := ((g : Matrix (Fin 2) (Fin 2) Complex) 0 1).im,
         im := ((g : Matrix (Fin 2) (Fin 2) Complex) 0 1).re } : Complex) := by
  have h10 := su2_apply_one_zero_eq_neg_conj_apply_zero_one g
  simp only [su2HermitianPart, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply]
  rw [h10]
  have hstar : star ((g : Matrix (Fin 2) (Fin 2) Complex) 0 1) =
      ({ re := ((g : Matrix (Fin 2) (Fin 2) Complex) 0 1).re,
         im := -((g : Matrix (Fin 2) (Fin 2) Complex) 0 1).im } : Complex) := rfl
  rw [hstar]
  apply Complex.ext <;>
    simp [smul_eq_mul, Complex.mul_re, Complex.mul_im]

theorem su2HermitianPart_isHermitian (g : SU2) :
    Matrix.IsHermitian (su2HermitianPart g) := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j
  · change star (su2HermitianPart g 0 0) = su2HermitianPart g 0 0
    rw [su2HermitianPart_apply_zero_zero]
    simp
  · change star (su2HermitianPart g 1 0) = su2HermitianPart g 0 1
    rw [su2HermitianPart_apply_one_zero, su2HermitianPart_apply_zero_one]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  · change star (su2HermitianPart g 0 1) = su2HermitianPart g 1 0
    rw [su2HermitianPart_apply_zero_one, su2HermitianPart_apply_one_zero]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  · change star (su2HermitianPart g 1 1) = su2HermitianPart g 1 1
    rw [su2HermitianPart_apply_one_one]
    simp

theorem su2HermitianPart_trace (g : SU2) :
    (su2HermitianPart g).trace = 0 := by
  rw [Matrix.trace_fin_two, su2HermitianPart_apply_zero_zero,
    su2HermitianPart_apply_one_one]
  simp

theorem su2HermitianPart_det (g : SU2) :
    (su2HermitianPart g).det =
      ((su2HalfTrace g : Complex) ^ 2 - 1) := by
  have hrow := su2_normSq_row_zero g
  rw [Complex.normSq_apply, Complex.normSq_apply] at hrow
  rw [Matrix.det_fin_two, su2HermitianPart_apply_zero_zero,
    su2HermitianPart_apply_one_one, su2HermitianPart_apply_zero_one,
    su2HermitianPart_apply_one_zero]
  apply Complex.ext
  · simp [su2HalfTrace, pow_two, Complex.mul_re, Complex.mul_im]
    nlinarith
  · simp [su2HalfTrace, pow_two, Complex.mul_re, Complex.mul_im]
    ring

theorem su2HermitianPart_charpoly_eq_of_halfTrace_eq {g h : SU2}
    (htr : su2HalfTrace g = su2HalfTrace h) :
    (su2HermitianPart g).charpoly = (su2HermitianPart h).charpoly := by
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two,
    su2HermitianPart_trace, su2HermitianPart_trace,
    su2HermitianPart_det, su2HermitianPart_det, htr]

/-- A diagonal unitary which corrects the determinant of a two-dimensional
unitary matrix when it is multiplied on the right. -/
def su2UnitaryDetCorrection
    (U : Matrix.unitaryGroup (Fin 2) Complex) :
    Matrix.unitaryGroup (Fin 2) Complex := by
  let D : Matrix (Fin 2) (Fin 2) Complex :=
    Matrix.diagonal (fun i => if i = 0 then star (U.1.det) else 1)
  refine ⟨D, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [D, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply] using (Matrix.det_of_mem_unitary U.prop).1
  · simp [D, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply]
  · simp [D, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply]
  · simp [D, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply]

theorem det_su2Unitary_mul_detCorrection
    (U : Matrix.unitaryGroup (Fin 2) Complex) :
    ((U * su2UnitaryDetCorrection U : Matrix.unitaryGroup (Fin 2) Complex).1).det = 1 := by
  have hdet := Matrix.det_of_mem_unitary U.prop
  change (U.1 * (su2UnitaryDetCorrection U).1).det = 1
  rw [Matrix.det_mul]
  change U.1.det *
    (Matrix.diagonal (fun i : Fin 2 => if i = 0 then star U.1.det else 1)).det = 1
  rw [Matrix.det_diagonal]
  simpa using hdet.2

theorem su2UnitaryDetCorrection_conj_diagonal
    (U : Matrix.unitaryGroup (Fin 2) Complex) (d : Fin 2 -> Complex) :
    Unitary.conjStarAlgAut Complex (Matrix (Fin 2) (Fin 2) Complex)
      (su2UnitaryDetCorrection U) (Matrix.diagonal d) = Matrix.diagonal d := by
  rw [Unitary.conjStarAlgAut_apply]
  change
    (Matrix.diagonal (fun i : Fin 2 => if i = 0 then star U.1.det else 1)) *
        Matrix.diagonal d *
        star (Matrix.diagonal (fun i : Fin 2 => if i = 0 then star U.1.det else 1)) =
      Matrix.diagonal d
  rw [(Matrix.commute_diagonal
    (fun i : Fin 2 => if i = 0 then star U.1.det else 1) d).eq]
  rw [Matrix.mul_assoc]
  have hunit := (su2UnitaryDetCorrection U).prop.2
  change
    (Matrix.diagonal (fun i : Fin 2 => if i = 0 then star U.1.det else 1)) *
        star (Matrix.diagonal (fun i : Fin 2 => if i = 0 then star U.1.det else 1)) = 1 at hunit
  rw [hunit, Matrix.mul_one]

/-- A determinant-one spectral basis for the Hermitian part of `g`. -/
def su2SpecialEigenvector (g : SU2) : SU2 :=
  let U := (su2HermitianPart_isHermitian g).eigenvectorUnitary
  let V := U * su2UnitaryDetCorrection U
  ⟨V.1, V.prop, det_su2Unitary_mul_detCorrection U⟩

theorem su2HermitianPart_spectral_special (g : SU2) :
    su2HermitianPart g =
      (su2SpecialEigenvector g : Matrix (Fin 2) (Fin 2) Complex) *
        Matrix.diagonal
          (RCLike.ofReal ∘ (su2HermitianPart_isHermitian g).eigenvalues) *
        star (su2SpecialEigenvector g : Matrix (Fin 2) (Fin 2) Complex) := by
  let hH := su2HermitianPart_isHermitian g
  let U := hH.eigenvectorUnitary
  let D : Matrix (Fin 2) (Fin 2) Complex :=
    Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)
  have hspectral : su2HermitianPart g =
      Unitary.conjStarAlgAut Complex (Matrix (Fin 2) (Fin 2) Complex) U D :=
    hH.spectral_theorem
  calc
    su2HermitianPart g =
        Unitary.conjStarAlgAut Complex (Matrix (Fin 2) (Fin 2) Complex) U D :=
      hspectral
    _ = Unitary.conjStarAlgAut Complex (Matrix (Fin 2) (Fin 2) Complex)
          (U * su2UnitaryDetCorrection U) D := by
      rw [Unitary.conjStarAlgAut_mul_apply,
        su2UnitaryDetCorrection_conj_diagonal]
    _ = (su2SpecialEigenvector g : Matrix (Fin 2) (Fin 2) Complex) *
          Matrix.diagonal
            (RCLike.ofReal ∘ (su2HermitianPart_isHermitian g).eigenvalues) *
          star (su2SpecialEigenvector g : Matrix (Fin 2) (Fin 2) Complex) := rfl

theorem su2HermitianPart_conjugate_of_halfTrace_eq {g h : SU2}
    (htr : su2HalfTrace g = su2HalfTrace h) :
    ∃ k : SU2,
      su2HermitianPart g =
        (k : Matrix (Fin 2) (Fin 2) Complex) * su2HermitianPart h *
          star (k : Matrix (Fin 2) (Fin 2) Complex) := by
  let hg := su2HermitianPart_isHermitian g
  let hh := su2HermitianPart_isHermitian h
  have hchar : (su2HermitianPart g).charpoly =
      (su2HermitianPart h).charpoly :=
    su2HermitianPart_charpoly_eq_of_halfTrace_eq htr
  have heig : hg.eigenvalues = hh.eigenvalues :=
    (hg.eigenvalues_eq_eigenvalues_iff (hB := hh)).2 hchar
  let Wg := su2SpecialEigenvector g
  let Wh := su2SpecialEigenvector h
  refine ⟨Wg * Wh⁻¹, ?_⟩
  rw [su2HermitianPart_spectral_special g,
    su2HermitianPart_spectral_special h]
  change
    (Wg : Matrix (Fin 2) (Fin 2) Complex) *
        Matrix.diagonal (RCLike.ofReal ∘ hg.eigenvalues) * star Wg.1 =
      ((Wg * Wh⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) Complex) *
        ((Wh : Matrix (Fin 2) (Fin 2) Complex) *
          Matrix.diagonal (RCLike.ofReal ∘ hh.eigenvalues) * star Wh.1) *
        star (((Wg * Wh⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) Complex))
  rw [heig]
  have hinv : (Wh⁻¹ : SU2).1 * Wh.1 = 1 := by
    exact congrArg Subtype.val (inv_mul_cancel Wh)
  have hstarinv : star Wh.1 * star (Wh⁻¹ : SU2).1 = 1 := by
    rw [← Matrix.star_mul, hinv, star_one]
  change
    Wg.1 * Matrix.diagonal (RCLike.ofReal ∘ hh.eigenvalues) * star Wg.1 =
      (Wg.1 * (Wh⁻¹ : SU2).1) *
        (Wh.1 * Matrix.diagonal (RCLike.ofReal ∘ hh.eigenvalues) * star Wh.1) *
        star (Wg.1 * (Wh⁻¹ : SU2).1)
  rw [Matrix.star_mul]
  calc
    Wg.1 * Matrix.diagonal (RCLike.ofReal ∘ hh.eigenvalues) * star Wg.1 =
        Wg.1 *
          ((Wh⁻¹ : SU2).1 * Wh.1 *
            Matrix.diagonal (RCLike.ofReal ∘ hh.eigenvalues) *
            (star Wh.1 * star (Wh⁻¹ : SU2).1)) * star Wg.1 := by
      rw [hinv, hstarinv]
      simp
    _ = (Wg.1 * (Wh⁻¹ : SU2).1) *
        (Wh.1 * Matrix.diagonal (RCLike.ofReal ∘ hh.eigenvalues) * star Wh.1) *
        (star (Wh⁻¹ : SU2).1 * star Wg.1) := by
      noncomm_ring

theorem su2_matrix_eq_halfTrace_add_I_hermitianPart (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) Complex) =
      (su2HalfTrace g : Complex) • (1 : Matrix (Fin 2) (Fin 2) Complex) +
        Complex.I • su2HermitianPart g := by
  ext i j
  fin_cases i <;> fin_cases j
  · change g.1 0 0 = (su2HalfTrace g : Complex) *
        (1 : Matrix (Fin 2) (Fin 2) Complex) 0 0 +
        Complex.I * su2HermitianPart g 0 0
    rw [su2HermitianPart_apply_zero_zero]
    apply Complex.ext <;>
      simp [su2HalfTrace, Matrix.one_apply, Complex.mul_re, Complex.mul_im]

  · change g.1 0 1 = (su2HalfTrace g : Complex) *
        (1 : Matrix (Fin 2) (Fin 2) Complex) 0 1 +
        Complex.I * su2HermitianPart g 0 1
    rw [su2HermitianPart_apply_zero_one]
    apply Complex.ext <;>
      simp [su2HalfTrace, Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · change g.1 1 0 = (su2HalfTrace g : Complex) *
        (1 : Matrix (Fin 2) (Fin 2) Complex) 1 0 +
        Complex.I * su2HermitianPart g 1 0
    rw [su2HermitianPart_apply_one_zero,
      su2_apply_one_zero_eq_neg_conj_apply_zero_one]
    have hzstar : star ((g : Matrix (Fin 2) (Fin 2) Complex) 0 1) =
        ({ re := ((g : Matrix (Fin 2) (Fin 2) Complex) 0 1).re,
           im := -((g : Matrix (Fin 2) (Fin 2) Complex) 0 1).im } : Complex) := rfl
    rw [hzstar]
    apply Complex.ext <;>
      simp [su2HalfTrace, Matrix.one_apply, Complex.mul_re, Complex.mul_im]
  · change g.1 1 1 = (su2HalfTrace g : Complex) *
        (1 : Matrix (Fin 2) (Fin 2) Complex) 1 1 +
        Complex.I * su2HermitianPart g 1 1
    rw [su2HermitianPart_apply_one_one,
      su2_apply_one_one_eq_conj_apply_zero_zero]
    have hzstar : star ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0) =
        ({ re := ((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).re,
           im := -((g : Matrix (Fin 2) (Fin 2) Complex) 0 0).im } : Complex) := rfl
    rw [hzstar]
    apply Complex.ext <;>
      simp [su2HalfTrace, Matrix.one_apply, Complex.mul_re, Complex.mul_im]

/-- The half-trace fibers are exactly the conjugacy classes of `SU(2)`. -/
theorem su2_conjugate_of_halfTrace_eq {g h : SU2}
    (htr : su2HalfTrace g = su2HalfTrace h) :
    ∃ k : SU2, g = k * h * k⁻¹ := by
  obtain ⟨k, hk⟩ := su2HermitianPart_conjugate_of_halfTrace_eq htr
  refine ⟨k, Subtype.ext ?_⟩
  change g.1 = k.1 * h.1 * star k.1
  rw [su2_matrix_eq_halfTrace_add_I_hermitianPart g,
    su2_matrix_eq_halfTrace_add_I_hermitianPart h, htr, hk]
  have hunit : k.1 * star k.1 = 1 := k.prop.1.2
  rw [Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [hunit]

/-- The standard diagonal representative of a half-trace value in `[-1,1]`. -/
def su2HalfTraceRepresentative (x : Set.Icc (-1 : Real) 1) : SU2 := by
  let y : Real := Real.sqrt (1 - (x : Real) ^ 2)
  have hy0 : 0 <= 1 - (x : Real) ^ 2 := by
    rcases x.2 with ⟨hx0, hx1⟩
    nlinarith
  have hy2 : y ^ 2 = 1 - (x : Real) ^ 2 := by
    dsimp [y]
    exact Real.sq_sqrt hy0
  let z : Complex := { re := x, im := y }
  have hz : Complex.normSq z + Complex.normSq (0 : Complex) = 1 := by
    dsimp [z]
    norm_num [Complex.normSq_apply]
    nlinarith
  exact rowSphereToSU2 ⟨(z, 0), hz⟩

theorem su2HalfTrace_representative (x : Set.Icc (-1 : Real) 1) :
    su2HalfTrace (su2HalfTraceRepresentative x) = x := by
  rfl

theorem continuous_su2HalfTraceRepresentative :
    Continuous su2HalfTraceRepresentative := by
  apply continuous_rowSphereToSU2.comp
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · change Continuous (fun x : Set.Icc (-1 : Real) 1 =>
      Complex.equivRealProdCLM.symm (x.1, Real.sqrt (1 - x.1 ^ 2)))
    exact Complex.equivRealProdCLM.symm.continuous.comp <| by fun_prop
  · exact continuous_const

/-- A continuous radial extension of a continuous class observable. -/
def su2ClassRadialExtension (f : SU2 -> Real) (x : Real) : Real :=
  f (su2HalfTraceRepresentative
    (Set.projIcc (-1 : Real) 1 (by norm_num) x))

theorem continuous_su2ClassRadialExtension {f : SU2 -> Real}
    (hf : Continuous f) : Continuous (su2ClassRadialExtension f) := by
  exact hf.comp <| continuous_su2HalfTraceRepresentative.comp continuous_projIcc

theorem su2Class_eq_radialExtension {f : SU2 -> Real}
    (hclass : ∀ k g : SU2, f (k * g * k⁻¹) = f g) (g : SU2) :
    f g = su2ClassRadialExtension f (su2HalfTrace g) := by
  rw [su2ClassRadialExtension,
    Set.projIcc_of_mem (by norm_num : (-1 : Real) <= 1)
      (su2HalfTrace_mem_Icc g)]
  obtain ⟨k, hk⟩ := su2_conjugate_of_halfTrace_eq
    (g := g) (h := su2HalfTraceRepresentative
      ⟨su2HalfTrace g, su2HalfTrace_mem_Icc g⟩) (by
        rw [su2HalfTrace_representative])
  calc
    f g = f (k * su2HalfTraceRepresentative
        ⟨su2HalfTrace g, su2HalfTrace_mem_Icc g⟩ * k⁻¹) := congrArg f hk
    _ = f (su2HalfTraceRepresentative
        ⟨su2HalfTrace g, su2HalfTrace_mem_Icc g⟩) := hclass _ _

/-- The diagonal representative with eigenangles `theta` and `-theta`. -/
def su2AngleRepresentative (theta : Real) : SU2 :=
  su2HalfTraceRepresentative
    ⟨Real.cos theta, Real.neg_one_le_cos theta, Real.cos_le_one theta⟩

theorem su2ClassRadialExtension_cos (f : SU2 -> Real) (theta : Real) :
    su2ClassRadialExtension f (Real.cos theta) =
      f (su2AngleRepresentative theta) := by
  rw [su2ClassRadialExtension,
    Set.projIcc_of_mem (by norm_num : (-1 : Real) <= 1)
      ⟨Real.neg_one_le_cos theta, Real.cos_le_one theta⟩]
  rfl

/-- General Weyl integration for every continuous real-valued class
function on concrete `SU(2)`. -/
theorem integral_su2Haar_class_eq_angle (f : SU2 -> Real)
    (hf : Continuous f)
    (hclass : ∀ k g : SU2, f (k * g * k⁻¹) = f g) :
    (∫ g : SU2, f g ∂su2HaarProb) =
      (2 / Real.pi) * ∫ theta : Real in 0..Real.pi,
        f (su2AngleRepresentative theta) * Real.sin theta ^ 2 := by
  calc
    (∫ g : SU2, f g ∂su2HaarProb) =
        ∫ g : SU2, su2ClassRadialExtension f (su2HalfTrace g) ∂su2HaarProb := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun g =>
        su2Class_eq_radialExtension hclass g
    _ = (2 / Real.pi) * ∫ theta : Real in 0..Real.pi,
        su2ClassRadialExtension f (Real.cos theta) * Real.sin theta ^ 2 :=
      integral_su2Haar_halfTrace_eq_angle (su2ClassRadialExtension f)
        (continuous_su2ClassRadialExtension hf)
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro theta _
      dsimp only
      rw [su2ClassRadialExtension_cos]

end Lean2dYangMills
