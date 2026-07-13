import Lean2dYangMills.SU2CharacterConvolution

/-!
# The actual SU(2) heat-kernel convolution semigroup

This file consumes all-order translated character convolution and proves
`K_s * K_t = K_{s+t}` for the concrete infinite SU(2) heat kernel.
-/

noncomputable section

namespace Lean2dYangMills

open Matrix Set MeasureTheory

def su2HeatKernelPartial (N : Nat) (t : Real) (g : SU2) : Complex :=
  su2ClassHeatKernelPartial N t g 1

def su2HeatKernel (t : Real) (g : SU2) : Complex :=
  heatKernelCharacterSeries su2CharacterTable t g

theorem su2HeatKernel_eq_class (t : Real) (g : SU2) :
    su2HeatKernel t g = su2ClassHeatKernel t g 1 := by
  exact (su2ClassHeatKernel_right_one t g).symm

theorem continuous_su2HeatKernelPartial (N : Nat) (t : Real) :
    Continuous (su2HeatKernelPartial N t) := by
  unfold su2HeatKernelPartial su2ClassHeatKernelPartial
  exact continuous_finset_sum _ fun n _ =>
    (continuous_const.mul (continuous_su2CharacterChebyshev n)).mul
      continuous_const

theorem tendsto_su2HeatKernelPartial {t : Real} (ht : 0 < t) (g : SU2) :
    Filter.Tendsto (fun N => su2HeatKernelPartial N t g)
      Filter.atTop (nhds (su2HeatKernel t g)) := by
  rw [su2HeatKernel_eq_class]
  exact tendsto_su2ClassHeatKernelPartial ht g 1

theorem norm_su2HeatKernelPartial_le_tsum_majorant
    {t : Real} (ht : 0 < t) (N : Nat) (g : SU2) :
    ‖su2HeatKernelPartial N t g‖ ≤
      ∑' n, su2HeatKernelMajorant t n :=
  norm_su2ClassHeatKernelPartial_le_tsum_majorant ht N g 1

theorem su2HeatKernelPartial_eq_sum (N : Nat) (t : Real) (g : SU2) :
    su2HeatKernelPartial N t g =
      ∑ n ∈ Finset.range N,
        (((n : Complex) + 1) * su2ClassHeatWeight t n) *
          su2CharacterChebyshev n g := by
  unfold su2HeatKernelPartial su2ClassHeatKernelPartial
  apply Finset.sum_congr rfl
  intro n hn
  rw [su2CharacterChebyshev_one]
  ring

/-- Finite translated heat-kernel convolution. -/
theorem su2HeatKernelPartial_convolution
    (N : Nat) (s t : Real) (g : SU2) :
    su2Convolution (su2HeatKernelPartial N s)
      (su2HeatKernelPartial N t) g =
      su2HeatKernelPartial N (s + t) g := by
  let a : Nat -> SU2 -> Complex := fun n x =>
    (((n : Complex) + 1) * su2ClassHeatWeight s n) *
      su2CharacterChebyshev n x
  let b : Nat -> SU2 -> Complex := fun m x =>
    (((m : Complex) + 1) * su2ClassHeatWeight t m) *
      su2CharacterChebyshev m x
  have hab (n m : Nat) : Integrable
      (fun x : SU2 => a n x * b m (x⁻¹ * g)) su2HaarProb := by
    apply integrable_continuous_su2Haar
    dsimp [a, b]
    exact (continuous_const.mul (continuous_su2CharacterChebyshev n)).mul
      (continuous_const.mul
        ((continuous_su2CharacterChebyshev m).comp <| by fun_prop))
  have hint (n m : Nat) :
      (∫ x : SU2, a n x * b m (x⁻¹ * g) ∂su2HaarProb) =
        if n = m then
          (((n : Complex) + 1) * su2ClassHeatWeight (s + t) n) *
            su2CharacterChebyshev n g else 0 := by
    rw [show (fun x : SU2 => a n x * b m (x⁻¹ * g)) =
        fun x =>
          ((((n : Complex) + 1) * su2ClassHeatWeight s n) *
            (((m : Complex) + 1) * su2ClassHeatWeight t m)) *
          (su2CharacterChebyshev n x *
            su2CharacterChebyshev m (x⁻¹ * g)) by
      funext x
      dsimp [a, b]
      ring]
    calc
      (∫ x : SU2,
          ((((n : Complex) + 1) * su2ClassHeatWeight s n) *
            (((m : Complex) + 1) * su2ClassHeatWeight t m)) *
          (su2CharacterChebyshev n x *
            su2CharacterChebyshev m (x⁻¹ * g)) ∂su2HaarProb) =
          ((((n : Complex) + 1) * su2ClassHeatWeight s n) *
            (((m : Complex) + 1) * su2ClassHeatWeight t m)) *
            su2Convolution (su2CharacterChebyshev n)
              (su2CharacterChebyshev m) g :=
        MeasureTheory.integral_const_mul _ _
      _ = _ := by
        rw [su2CharacterChebyshev_convolution]
        split_ifs with hnm
        · subst m
          rw [← su2ClassHeatWeight_add]
          field_simp
        · simp
  rw [su2Convolution]
  simp_rw [su2HeatKernelPartial_eq_sum]
  change (∫ x : SU2,
      (∑ n ∈ Finset.range N, a n x) *
        (∑ m ∈ Finset.range N, b m (x⁻¹ * g)) ∂su2HaarProb) = _
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [MeasureTheory.integral_finset_sum (Finset.range N)
    (fun n _ => integrable_finset_sum (Finset.range N) fun m _ => hab n m)]
  simp_rw [MeasureTheory.integral_finset_sum (Finset.range N)
    (fun m _ => hab _ m)]
  simp_rw [hint]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_eq_single n]
  · rw [if_pos rfl]
  · intro m hm hmn
    rw [if_neg (Ne.symm hmn)]
  · exact fun hn' => (hn' hn).elim

/-- Concrete infinite translated heat-kernel convolution semigroup. -/
theorem su2HeatKernel_convolution
    {s t : Real} (hs : 0 < s) (ht : 0 < t) (g : SU2) :
    su2Convolution (su2HeatKernel s) (su2HeatKernel t) g =
      su2HeatKernel (s + t) g := by
  let Ms : Real := ∑' n, su2HeatKernelMajorant s n
  let Mt : Real := ∑' n, su2HeatKernelMajorant t n
  let F : Nat -> SU2 -> Complex := fun N x =>
    su2HeatKernelPartial N s x * su2HeatKernelPartial N t (x⁻¹ * g)
  let f : SU2 -> Complex := fun x =>
    su2HeatKernel s x * su2HeatKernel t (x⁻¹ * g)
  have hmeas (N : Nat) : AEStronglyMeasurable (F N) su2HaarProb := by
    exact ((continuous_su2HeatKernelPartial N s).mul
      ((continuous_su2HeatKernelPartial N t).comp <| by fun_prop)).aestronglyMeasurable
  have hMs : 0 ≤ Ms := tsum_nonneg fun _ => by
    unfold su2HeatKernelMajorant
    positivity
  have hMt : 0 ≤ Mt := tsum_nonneg fun _ => by
    unfold su2HeatKernelMajorant
    positivity
  have hbound (N : Nat) : ∀ᵐ x : SU2 ∂su2HaarProb,
      ‖F N x‖ ≤ Ms * Mt := by
    exact ae_of_all _ fun x => by
      dsimp [F]
      rw [norm_mul]
      exact mul_le_mul
        (norm_su2HeatKernelPartial_le_tsum_majorant hs N x)
        (norm_su2HeatKernelPartial_le_tsum_majorant ht N (x⁻¹ * g))
        (norm_nonneg _) hMs
  have hlim : ∀ᵐ x : SU2 ∂su2HaarProb,
      Filter.Tendsto (fun N => F N x) Filter.atTop (nhds (f x)) := by
    exact ae_of_all _ fun x =>
      (tendsto_su2HeatKernelPartial hs x).mul
        (tendsto_su2HeatKernelPartial ht (x⁻¹ * g))
  have hleft := tendsto_integral_of_dominated_convergence
    (fun _x : SU2 => Ms * Mt) hmeas (integrable_const (Ms * Mt))
      hbound hlim
  have hright := tendsto_su2HeatKernelPartial (add_pos hs ht) g
  have hseq : (fun N => ∫ x : SU2, F N x ∂su2HaarProb) =
      fun N => su2HeatKernelPartial N (s + t) g := by
    funext N
    exact su2HeatKernelPartial_convolution N s t g
  rw [hseq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Consumer theorem: the semigroup law is an equality of actual translated
group convolutions, with no package field or external hypothesis. -/
theorem su2HeatKernel_convolution_consumer
    {s t : Real} (hs : 0 < s) (ht : 0 < t) :
    su2Convolution (su2HeatKernel s) (su2HeatKernel t) =
      su2HeatKernel (s + t) := by
  funext g
  exact su2HeatKernel_convolution hs ht g

/-- Two adjacent heat-kernel faces sharing the integrated edge `x`.
The external boundary holonomies are `a` and `b`. -/
def su2MigdalTwoFaceDensity (s t : Real) (a b x : SU2) : Complex :=
  su2HeatKernel s (a * x) * su2HeatKernel t (x⁻¹ * b)

/-- **Concrete nontrivial Migdal move.** Integrating the shared edge of two
faces merges the areas and concatenates the external boundary holonomies.
The proof uses actual normalized Haar integration and the infinite translated
heat-kernel convolution theorem. -/
theorem su2Migdal_twoFace_merge
    {s t : Real} (hs : 0 < s) (ht : 0 < t) (a b : SU2) :
    (∫ x : SU2, su2MigdalTwoFaceDensity s t a b x ∂su2HaarProb) =
      su2HeatKernel (s + t) (a * b) := by
  let F : SU2 -> Complex := fun y =>
    su2HeatKernel s y * su2HeatKernel t (y⁻¹ * (a * b))
  have hpoint : (fun x : SU2 => su2MigdalTwoFaceDensity s t a b x) =
      fun x => F (a * x) := by
    funext x
    dsimp [su2MigdalTwoFaceDensity, F]
    congr 2
    group
  rw [hpoint, integral_mul_left_eq_self (μ := su2HaarProb) F a]
  exact su2HeatKernel_convolution hs ht (a * b)

/-- Consumer form of Migdal subdivision invariance with two explicit faces. -/
theorem su2Migdal_subdivision_invariant
    {s t : Real} (hs : 0 < s) (ht : 0 < t) (a b : SU2) :
    (∫ x : SU2,
      su2HeatKernel s (a * x) * su2HeatKernel t (x⁻¹ * b)
        ∂su2HaarProb) =
      su2HeatKernel (s + t) (a * b) :=
  su2Migdal_twoFace_merge hs ht a b

end Lean2dYangMills
