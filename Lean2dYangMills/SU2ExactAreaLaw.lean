import Lean2dYangMills.SU2Convolution

/-!
# Exact simple-loop Wilson coefficients

The normalized `n`th character is integrated against the concrete SU(2)
heat-kernel character density.  The result is the exact Casimir exponential,
for every label and every positive area.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace Lean2dYangMills

open MeasureTheory

def su2NormalizedWilsonCharacter (n : Nat) (g : SU2) : Complex :=
  (1 / ((n : Complex) + 1)) * su2CharacterChebyshev n g

theorem norm_su2NormalizedWilsonCharacter_le_one (n : Nat) (g : SU2) :
    ‖su2NormalizedWilsonCharacter n g‖ <= 1 := by
  rw [su2NormalizedWilsonCharacter, norm_mul, norm_div, norm_one]
  have hdim : ‖((n : Complex) + 1)‖ = (n : Real) + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add, Complex.norm_natCast]
    norm_num
  rw [hdim]
  simpa [div_eq_mul_inv, mul_comm] using
    (div_le_one (by positivity)).2 (abs_su2CharacterChebyshev_le n g)

theorem continuous_su2NormalizedWilsonCharacter (n : Nat) :
    Continuous (su2NormalizedWilsonCharacter n) := by
  unfold su2NormalizedWilsonCharacter
  exact continuous_const.mul (continuous_su2CharacterChebyshev n)

theorem integral_su2NormalizedWilson_mul_partial
    (N : Nat) (t : Real) (n : Nat) :
    (∫ g : SU2,
      su2NormalizedWilsonCharacter n g *
        su2ClassHeatKernelPartial N t g 1 ∂su2HaarProb) =
      if n < N then su2ClassHeatWeight t n else 0 := by
  let F : Nat -> SU2 -> Complex := fun m g =>
    su2NormalizedWilsonCharacter n g *
      (su2ClassHeatWeight t m * su2CharacterChebyshev m g *
        su2CharacterChebyshev m 1)
  have hFint (m : Nat) : Integrable (F m) su2HaarProb :=
    integrable_continuous_su2Haar (by
      dsimp [F]
      exact (continuous_su2NormalizedWilsonCharacter n).mul
        ((continuous_const.mul (continuous_su2CharacterChebyshev m)).mul
          continuous_const))
  have hterm (m : Nat) :
      (∫ g : SU2, F m g ∂su2HaarProb) =
        if n = m then su2ClassHeatWeight t n else 0 := by
    rw [show (fun g : SU2 => F m g) =
        (fun g : SU2 =>
          ((1 / ((n : Complex) + 1)) * su2ClassHeatWeight t m *
            su2CharacterChebyshev m 1) *
          (su2CharacterChebyshev n g * su2CharacterChebyshev m g)) by
      funext g
      dsimp [F, su2NormalizedWilsonCharacter]
      ring]
    calc
      (∫ g : SU2,
          ((1 / ((n : Complex) + 1)) * su2ClassHeatWeight t m *
            su2CharacterChebyshev m 1) *
          (su2CharacterChebyshev n g * su2CharacterChebyshev m g)
          ∂su2HaarProb) =
          ((1 / ((n : Complex) + 1)) * su2ClassHeatWeight t m *
            su2CharacterChebyshev m 1) *
          (∫ g : SU2, su2CharacterChebyshev n g *
            su2CharacterChebyshev m g ∂su2HaarProb) :=
        MeasureTheory.integral_const_mul _ _
      _ = _ := by
        rw [integral_su2CharacterChebyshev_mul]
        split_ifs with hnm
        · subst m
          rw [su2CharacterChebyshev_one]
          field_simp
        · simp
  unfold su2ClassHeatKernelPartial
  simp_rw [Finset.mul_sum]
  change (∫ g : SU2, ∑ m ∈ Finset.range N, F m g ∂su2HaarProb) = _
  rw [integral_finset_sum (Finset.range N) (fun m _ => hFint m)]
  simp_rw [hterm]
  by_cases hn : n < N
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro m hm hmn
      simp [Ne.symm hmn]
    · intro hnmem
      exact (hnmem (Finset.mem_range.mpr hn)).elim
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro m hm
    have hmn : n ≠ m := by
      intro h
      subst m
      exact hn (Finset.mem_range.mp hm)
    simp [hmn]

/-- Exact positive-area simple-loop identity for every SU(2) representation
label in the heat-kernel model. -/
theorem integral_su2NormalizedWilson_mul_heatKernel
    {t : Real} (ht : 0 < t) (n : Nat) :
    (∫ g : SU2,
      su2NormalizedWilsonCharacter n g *
        heatKernelCharacterSeries su2CharacterTable t g ∂su2HaarProb) =
      su2ClassHeatWeight t n := by
  let M : Real := ∑' m, su2HeatKernelMajorant t m
  let F : Nat -> SU2 -> Complex := fun N g =>
    su2NormalizedWilsonCharacter n g * su2ClassHeatKernelPartial N t g 1
  let f : SU2 -> Complex := fun g =>
    su2NormalizedWilsonCharacter n g * su2ClassHeatKernel t g 1
  have hmeas (N : Nat) : AEStronglyMeasurable (F N) su2HaarProb :=
    by
      dsimp [F]
      have hk : Continuous (fun g : SU2 => su2ClassHeatKernelPartial N t g 1) := by
        unfold su2ClassHeatKernelPartial
        exact continuous_finset_sum _ fun m _ =>
          (continuous_const.mul (continuous_su2CharacterChebyshev m)).mul
            continuous_const
      exact ((continuous_su2NormalizedWilsonCharacter n).mul
        hk).aestronglyMeasurable
  have hM0 : 0 <= M := tsum_nonneg fun _ => by
    unfold su2HeatKernelMajorant
    positivity
  have hbound (N : Nat) : ∀ᵐ g : SU2 ∂su2HaarProb, ‖F N g‖ <= M := by
    exact ae_of_all _ fun g => by
      dsimp [F]
      rw [norm_mul]
      calc
        ‖su2NormalizedWilsonCharacter n g‖ *
            ‖su2ClassHeatKernelPartial N t g 1‖ <=
            1 * ‖su2ClassHeatKernelPartial N t g 1‖ := by
          gcongr
          exact norm_su2NormalizedWilsonCharacter_le_one n g
        _ <= M := by
          simpa [M] using
            norm_su2ClassHeatKernelPartial_le_tsum_majorant ht N g 1
  have hlim : ∀ᵐ g : SU2 ∂su2HaarProb,
      Filter.Tendsto (fun N => F N g) Filter.atTop (nhds (f g)) := by
    exact ae_of_all _ fun g =>
      Filter.Tendsto.const_mul _ (tendsto_su2ClassHeatKernelPartial ht g 1)
  have hleft := tendsto_integral_of_dominated_convergence
    (fun _g : SU2 => M) hmeas (integrable_const M) hbound hlim
  have hseq : (fun N => ∫ g : SU2, F N g ∂su2HaarProb) =
      (fun N => if n < N then su2ClassHeatWeight t n else 0) := by
    funext N
    exact integral_su2NormalizedWilson_mul_partial N t n
  rw [hseq] at hleft
  have hright : Filter.Tendsto
      (fun N => if n < N then su2ClassHeatWeight t n else 0)
      Filter.atTop (nhds (su2ClassHeatWeight t n)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_atTop.2 ⟨n + 1, fun N hN => by omega⟩]
      with N hN
    simp [show n < N by omega]
  have hvalue : (∫ g : SU2, f g ∂su2HaarProb) = su2ClassHeatWeight t n :=
    tendsto_nhds_unique hleft hright
  simpa [f, su2ClassHeatKernel_right_one] using hvalue

theorem su2_exact_simpleLoop_areaLaw {t : Real} (ht : 0 < t) (n : Nat) :
    (∫ g : SU2,
      su2NormalizedWilsonCharacter n g *
        heatKernelCharacterSeries su2CharacterTable t g ∂su2HaarProb) =
      ((Real.exp (-t * ((n : Real) * ((n : Real) + 2) / 4)) : Real) : Complex) := by
  rw [integral_su2NormalizedWilson_mul_heatKernel ht n]
  rfl

end Lean2dYangMills
