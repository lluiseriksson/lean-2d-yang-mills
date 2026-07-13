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

end Lean2dYangMills
