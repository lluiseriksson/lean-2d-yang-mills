import Lean2dYangMills.SU2Weyl

/-!
# The concrete central SU(2) heat semigroup on class functions

The two-point kernel below is the spectral kernel of the SU(2) heat operator
restricted to class functions.  At the identity it is exactly the concrete
character heat-kernel series already constructed in `SU2Character`.
-/

noncomputable section

open scoped ENNReal Interval Polynomial

namespace Lean2dYangMills

open MeasureTheory Set

def su2ClassHeatWeight (t : Real) (n : Nat) : Complex :=
  (Real.exp (-t * ((n : Real) * ((n : Real) + 2) / 4)) : Real)

def su2ClassHeatKernelPartial (N : Nat) (t : Real) (g h : SU2) : Complex :=
  ∑ n ∈ Finset.range N,
    su2ClassHeatWeight t n * su2CharacterChebyshev n g *
      su2CharacterChebyshev n h

theorem continuous_su2ClassHeatKernelPartial_left
    (N : Nat) (t : Real) (g : SU2) :
    Continuous (fun h : SU2 => su2ClassHeatKernelPartial N t g h) := by
  unfold su2ClassHeatKernelPartial
  exact continuous_finset_sum _ fun n _ =>
    (continuous_const.mul continuous_const).mul
      (continuous_su2CharacterChebyshev n)

theorem integrable_continuous_su2Haar {f : SU2 -> Complex}
    (hf : Continuous f) : Integrable f su2HaarProb := by
  simpa only [integrableOn_univ] using
    hf.continuousOn.integrableOn_compact (K := Set.univ) isCompact_univ

theorem su2ClassHeatWeight_add (s t : Real) (n : Nat) :
    su2ClassHeatWeight s n * su2ClassHeatWeight t n =
      su2ClassHeatWeight (s + t) n := by
  change ((Real.exp _ : Real) : Complex) * ((Real.exp _ : Real) : Complex) =
    ((Real.exp _ : Real) : Complex)
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem integral_su2ClassHeatKernelPartial_mul
    (N : Nat) (s t : Real) (g k : SU2) :
    (∫ h : SU2,
      su2ClassHeatKernelPartial N s g h *
        su2ClassHeatKernelPartial N t k h ∂su2HaarProb) =
      su2ClassHeatKernelPartial N (s + t) g k := by
  let a : Nat -> SU2 -> Complex := fun n h =>
    su2ClassHeatWeight s n * su2CharacterChebyshev n g *
      su2CharacterChebyshev n h
  let b : Nat -> SU2 -> Complex := fun m h =>
    su2ClassHeatWeight t m * su2CharacterChebyshev m k *
      su2CharacterChebyshev m h
  have ha (n : Nat) : Integrable (a n) su2HaarProb :=
    integrable_continuous_su2Haar (by
      dsimp [a]
      exact (continuous_const.mul continuous_const).mul
        (continuous_su2CharacterChebyshev n))
  have hab (n m : Nat) : Integrable (fun h => a n h * b m h) su2HaarProb :=
    integrable_continuous_su2Haar (by
      dsimp [a, b]
      exact ((continuous_const.mul continuous_const).mul
        (continuous_su2CharacterChebyshev n)).mul
          ((continuous_const.mul continuous_const).mul
            (continuous_su2CharacterChebyshev m)))
  have hint (n m : Nat) :
      (∫ h : SU2, a n h * b m h ∂su2HaarProb) =
        (su2ClassHeatWeight s n * su2CharacterChebyshev n g *
          (su2ClassHeatWeight t m * su2CharacterChebyshev m k)) *
            (if n = m then 1 else 0) := by
    rw [show (fun h : SU2 => a n h * b m h) =
        (fun h : SU2 =>
          (su2ClassHeatWeight s n * su2CharacterChebyshev n g *
            (su2ClassHeatWeight t m * su2CharacterChebyshev m k)) *
              (su2CharacterChebyshev n h * su2CharacterChebyshev m h)) by
      funext h
      dsimp [a, b]
      ring]
    calc
      (∫ h : SU2,
          (su2ClassHeatWeight s n * su2CharacterChebyshev n g *
            (su2ClassHeatWeight t m * su2CharacterChebyshev m k)) *
              (su2CharacterChebyshev n h * su2CharacterChebyshev m h)
          ∂su2HaarProb) =
          (su2ClassHeatWeight s n * su2CharacterChebyshev n g *
            (su2ClassHeatWeight t m * su2CharacterChebyshev m k)) *
              (∫ h : SU2, su2CharacterChebyshev n h *
                su2CharacterChebyshev m h ∂su2HaarProb) :=
        MeasureTheory.integral_const_mul _ _
      _ = _ := by rw [integral_su2CharacterChebyshev_mul]
  change (∫ h : SU2,
      (∑ n ∈ Finset.range N, a n h) *
        (∑ m ∈ Finset.range N, b m h) ∂su2HaarProb) = _
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [MeasureTheory.integral_finset_sum (Finset.range N) (fun n _ =>
    integrable_finset_sum (Finset.range N) fun m _ => hab n m)]
  simp_rw [MeasureTheory.integral_finset_sum (Finset.range N)
    (fun m _ => hab _ m)]
  simp_rw [hint]
  rw [su2ClassHeatKernelPartial]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_eq_single n]
  · rw [if_pos rfl]
    calc
      su2ClassHeatWeight s n * su2CharacterChebyshev n g *
          (su2ClassHeatWeight t n * su2CharacterChebyshev n k) * 1 =
          (su2ClassHeatWeight s n * su2ClassHeatWeight t n) *
            su2CharacterChebyshev n g * su2CharacterChebyshev n k := by ring
      _ = _ := by rw [su2ClassHeatWeight_add]
  · intro m hm hmn
    rw [if_neg (Ne.symm hmn)]
    simp
  · exact fun hn' => (hn' hn).elim

def su2ClassHeatKernelTerm (t : Real) (g h : SU2) (n : Nat) : Complex :=
  su2ClassHeatWeight t n * su2CharacterChebyshev n g *
    su2CharacterChebyshev n h

def su2ClassHeatKernel (t : Real) (g h : SU2) : Complex :=
  ∑' n : Nat, su2ClassHeatKernelTerm t g h n

theorem norm_su2ClassHeatKernelTerm_le_majorant
    (t : Real) (g h : SU2) (n : Nat) :
    ‖su2ClassHeatKernelTerm t g h n‖ <= su2HeatKernelMajorant t n := by
  rw [su2ClassHeatKernelTerm, norm_mul, norm_mul]
  change ‖((Real.exp _ : Real) : Complex)‖ *
      ‖su2CharacterChebyshev n g‖ * ‖su2CharacterChebyshev n h‖ <= _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  unfold su2HeatKernelMajorant
  calc
    Real.exp (-t * ((n : Real) * ((n : Real) + 2) / 4)) *
          ‖su2CharacterChebyshev n g‖ * ‖su2CharacterChebyshev n h‖ <=
        Real.exp (-t * ((n : Real) * ((n : Real) + 2) / 4)) *
          ((n : Real) + 1) * ((n : Real) + 1) := by
      gcongr
      · exact abs_su2CharacterChebyshev_le n g
      · exact abs_su2CharacterChebyshev_le n h
    _ = ((n : Real) + 1) ^ 2 *
          Real.exp (-t * ((n : Real) * ((n : Real) + 2)) / 4) := by ring_nf

theorem summable_su2ClassHeatKernelTerm {t : Real} (ht : 0 < t)
    (g h : SU2) : Summable (su2ClassHeatKernelTerm t g h) := by
  exact Summable.of_norm_bounded (summable_su2HeatKernelMajorant ht)
    (norm_su2ClassHeatKernelTerm_le_majorant t g h)

theorem su2ClassHeatKernelPartial_eq_sum (N : Nat) (t : Real) (g h : SU2) :
    su2ClassHeatKernelPartial N t g h =
      ∑ n ∈ Finset.range N, su2ClassHeatKernelTerm t g h n := rfl

theorem tendsto_su2ClassHeatKernelPartial {t : Real} (ht : 0 < t)
    (g h : SU2) :
    Filter.Tendsto (fun N => su2ClassHeatKernelPartial N t g h)
      Filter.atTop (nhds (su2ClassHeatKernel t g h)) := by
  rw [su2ClassHeatKernel]
  exact (summable_su2ClassHeatKernelTerm ht g h).hasSum.tendsto_sum_nat

theorem norm_su2ClassHeatKernelPartial_le_tsum_majorant
    {t : Real} (ht : 0 < t) (N : Nat) (g h : SU2) :
    ‖su2ClassHeatKernelPartial N t g h‖ <= ∑' n, su2HeatKernelMajorant t n := by
  rw [su2ClassHeatKernelPartial_eq_sum]
  calc
    ‖∑ n ∈ Finset.range N, su2ClassHeatKernelTerm t g h n‖ <=
        ∑ n ∈ Finset.range N, ‖su2ClassHeatKernelTerm t g h n‖ :=
      norm_sum_le _ _
    _ <= ∑ n ∈ Finset.range N, su2HeatKernelMajorant t n := by
      exact Finset.sum_le_sum fun n _ =>
        norm_su2ClassHeatKernelTerm_le_majorant t g h n
    _ <= ∑' n, su2HeatKernelMajorant t n :=
      (summable_su2HeatKernelMajorant ht).sum_le_tsum (Finset.range N)
        (fun n _ => by unfold su2HeatKernelMajorant; positivity)

/-- Exact infinite-dimensional heat semigroup on the concrete SU(2) class
sector.  This theorem contains a real Haar integral and no package field. -/
theorem integral_su2ClassHeatKernel_mul
    {s t : Real} (hs : 0 < s) (ht : 0 < t) (g k : SU2) :
    (∫ h : SU2, su2ClassHeatKernel s g h * su2ClassHeatKernel t k h
      ∂su2HaarProb) = su2ClassHeatKernel (s + t) g k := by
  let Ms : Real := ∑' n, su2HeatKernelMajorant s n
  let Mt : Real := ∑' n, su2HeatKernelMajorant t n
  let F : Nat -> SU2 -> Complex := fun N h =>
    su2ClassHeatKernelPartial N s g h * su2ClassHeatKernelPartial N t k h
  let f : SU2 -> Complex := fun h =>
    su2ClassHeatKernel s g h * su2ClassHeatKernel t k h
  have hmeas (N : Nat) : AEStronglyMeasurable (F N) su2HaarProb := by
    exact ((continuous_su2ClassHeatKernelPartial_left N s g).mul
      (continuous_su2ClassHeatKernelPartial_left N t k)).aestronglyMeasurable
  have hMs : 0 <= Ms := by
    dsimp [Ms]
    exact tsum_nonneg fun _ => by unfold su2HeatKernelMajorant; positivity
  have hMt : 0 <= Mt := by
    dsimp [Mt]
    exact tsum_nonneg fun _ => by unfold su2HeatKernelMajorant; positivity
  have hbound (N : Nat) : ∀ᵐ h : SU2 ∂su2HaarProb, ‖F N h‖ <= Ms * Mt := by
    exact ae_of_all _ fun h => by
      dsimp [F]
      rw [norm_mul]
      exact mul_le_mul
        (norm_su2ClassHeatKernelPartial_le_tsum_majorant hs N g h)
        (norm_su2ClassHeatKernelPartial_le_tsum_majorant ht N k h)
        (norm_nonneg _) hMs
  have hboundInt : Integrable (fun _h : SU2 => Ms * Mt) su2HaarProb :=
    integrable_const (Ms * Mt)
  have hlim : ∀ᵐ h : SU2 ∂su2HaarProb,
      Filter.Tendsto (fun N => F N h) Filter.atTop (nhds (f h)) := by
    exact ae_of_all _ fun h =>
      (tendsto_su2ClassHeatKernelPartial hs g h).mul
        (tendsto_su2ClassHeatKernelPartial ht k h)
  have hleft := tendsto_integral_of_dominated_convergence
    (fun _h : SU2 => Ms * Mt) hmeas hboundInt hbound hlim
  have hright := tendsto_su2ClassHeatKernelPartial (add_pos hs ht) g k
  have hseq : (fun N => ∫ h : SU2, F N h ∂su2HaarProb) =
      (fun N => su2ClassHeatKernelPartial N (s + t) g k) := by
    funext N
    exact integral_su2ClassHeatKernelPartial_mul N s t g k
  rw [hseq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- At the identity, the two-point class heat kernel is exactly the concrete
SU(2) character heat-kernel series from `SU2Character`. -/
theorem su2ClassHeatKernel_right_one (t : Real) (g : SU2) :
    su2ClassHeatKernel t g 1 =
      heatKernelCharacterSeries su2CharacterTable t g := by
  unfold su2ClassHeatKernel heatKernelCharacterSeries
  apply tsum_congr
  intro n
  rw [su2ClassHeatKernelTerm, su2CharacterChebyshev_one]
  change su2ClassHeatWeight t n * su2CharacterChebyshev n g *
      ((n : Complex) + 1) =
    ((n + 1 : Nat) : Complex) * su2CharacterChebyshev n g *
      ((Real.exp (-t * (((n : Real) * ((n : Real) + 2)) / 4)) : Real) : Complex)
  simp only [su2ClassHeatWeight]
  push_cast
  ring

def su2TwoFaceClassDensity (s t : Real) (g k h : SU2) : Complex :=
  su2ClassHeatKernel s g h * su2ClassHeatKernel t k h

def su2MergedFaceClassDensity (area : Real) (g k : SU2) : Complex :=
  su2ClassHeatKernel area g k

/-- **First concrete Migdal move.**  Integrating the shared holonomy of two
faces merges their areas exactly.  The theorem has two external holonomies,
a genuine normalized Haar integral, and consumes the concrete infinite
semigroup above. -/
theorem su2Migdal_twoFace_class_merge
    {s t : Real} (hs : 0 < s) (ht : 0 < t) (g k : SU2) :
    (∫ h : SU2, su2TwoFaceClassDensity s t g k h ∂su2HaarProb) =
      su2MergedFaceClassDensity (s + t) g k := by
  exact integral_su2ClassHeatKernel_mul hs ht g k

end Lean2dYangMills
