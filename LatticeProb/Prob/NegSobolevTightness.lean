import LatticeProb.Analysis.Sobolev.HeatEnergy
import LatticeProb.Analysis.Sobolev.NegEnergy
import LatticeProb.Analysis.Sobolev.RieszHeat
import LatticeProb.Analysis.Sobolev.TestFnCutoff
import LatticeProb.Analysis.GammaLaplaceIntegral
import LatticeProb.Prob.FiniteRangeSecondMoment
import Mathlib.Probability.Moments.Variance

/-!
# Covariance decay and negative Sobolev energy

For centered fields with covariance decay of order `β`, the expected Fourier `H^{-s}` energy
of a compactly supported rescaling is bounded uniformly in the scale when `s > β / 2`. The
proof combines the heat-kernel covariance identity, a Riesz-kernel estimate and the Gamma
representation of the Fourier weight.
-/

namespace LatticeProb.Sobolev

open MeasureTheory ProbabilityTheory
open scoped ENNReal FourierTransform

/-- A heat bound with exponential damping gives an integrable negative power. -/
theorem lintegral_negative_power_le_of_heat_bound {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [SFinite μ] {Z : E → ℝ} (hZ : Measurable Z) (hZpos : ∀ x, 0 < Z x)
    {s a A : ℝ} (hs : 0 < s) (hsa : 0 < s - a) (hA : 0 ≤ A)
    (hheat : ∀ t : ℝ, 0 < t → ∫⁻ x, ENNReal.ofReal (Real.exp (-(t * Z x))) ∂μ ≤
      ENNReal.ofReal (A * t ^ (-a) * Real.exp (-t))) :
    ∫⁻ x, ENNReal.ofReal (Z x) ^ (-s) ∂μ ≤
      ENNReal.ofReal (A * Real.Gamma (s - a) / Real.Gamma s) := by
  have hΓ : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs
  let F : E → ℝ → ℝ≥0∞ := fun x t => ENNReal.ofReal (t ^ (s - 1) * Real.exp (-(Z x * t)))
  have hFm : Measurable (Function.uncurry F) := by
    have : Measurable (fun p : E × ℝ => p.2 ^ (s - 1) * Real.exp (-(Z p.1 * p.2))) :=
      (measurable_snd.pow_const _).mul
        (Real.measurable_exp.comp ((hZ.comp measurable_fst).mul measurable_snd).neg)
    exact ENNReal.measurable_ofReal.comp this
  have hmeas : Measurable (fun x => ENNReal.ofReal (Z x) ^ (-s)) :=
    (ENNReal.measurable_ofReal.comp hZ).pow_const _
  have htime : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal
      (t ^ (s - a - 1) * Real.exp (-t))) = ENNReal.ofReal (Real.Gamma (s - a)) := by
    have h := LatticeProb.ofReal_rpow_neg_mul_gamma (z := 1) (q := s - a) zero_lt_one hsa
    simpa using h.symm
  have hstep : (∫⁻ x, ENNReal.ofReal (Z x) ^ (-s) ∂μ) * ENNReal.ofReal (Real.Gamma s) ≤
      ENNReal.ofReal A * ENNReal.ofReal (Real.Gamma (s - a)) := by
    calc
      (∫⁻ x, ENNReal.ofReal (Z x) ^ (-s) ∂μ) * ENNReal.ofReal (Real.Gamma s) =
          ∫⁻ x, ENNReal.ofReal (Z x) ^ (-s) * ENNReal.ofReal (Real.Gamma s) ∂μ :=
        (lintegral_mul_const _ hmeas).symm
      _ = ∫⁻ x, (∫⁻ t in Set.Ioi (0 : ℝ), F x t) ∂μ := by
        refine lintegral_congr fun x => ?_
        exact LatticeProb.ofReal_rpow_neg_mul_gamma (hZpos x) hs
      _ = ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ x, F x t ∂μ :=
        lintegral_lintegral_swap hFm.aemeasurable
      _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (s - 1)) *
          ENNReal.ofReal (A * t ^ (-a) * Real.exp (-t)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        have heq : (∫⁻ x, F x t ∂μ) = ENNReal.ofReal (t ^ (s - 1)) *
            ∫⁻ x, ENNReal.ofReal (Real.exp (-(t * Z x))) ∂μ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun x => ?_
          simp only [F]
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), mul_comm (Z x) t]
        rw [heq]
        exact mul_le_mul' le_rfl (hheat t ht)
      _ = ENNReal.ofReal A * ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal
          (t ^ (s - a - 1) * Real.exp (-t)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        have hp : t ^ (s - 1) * t ^ (-a) = t ^ (s - a - 1) := by
          rw [← Real.rpow_add ht]
          congr 1
          ring
        calc
          ENNReal.ofReal (t ^ (s - 1)) * ENNReal.ofReal (A * t ^ (-a) * Real.exp (-t)) =
              ENNReal.ofReal (t ^ (s - 1) * (A * t ^ (-a) * Real.exp (-t))) :=
            (ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)).symm
          _ = ENNReal.ofReal (A * (t ^ (s - a - 1) * Real.exp (-t))) := by
            congr 1
            rw [← hp]
            ring
          _ = ENNReal.ofReal A * ENNReal.ofReal (t ^ (s - a - 1) * Real.exp (-t)) :=
            ENNReal.ofReal_mul hA
      _ = ENNReal.ofReal A * ENNReal.ofReal (Real.Gamma (s - a)) := by rw [htime]
  have hfin : ENNReal.ofReal (Real.Gamma s) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hne : ENNReal.ofReal (Real.Gamma s) ≠ 0 := (ENNReal.ofReal_pos.2 hΓ).ne'
  have hrhs : ENNReal.ofReal (A * Real.Gamma (s - a) / Real.Gamma s) =
      (ENNReal.ofReal A * ENNReal.ofReal (Real.Gamma (s - a))) /
        ENNReal.ofReal (Real.Gamma s) := by
    rw [ENNReal.ofReal_div_of_pos hΓ, ENNReal.ofReal_mul hA]
  rw [hrhs]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl hfin)).2 hstep

/-- Covariance is unchanged by almost-everywhere modification of either variable. -/
theorem covariance_eq_of_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[P] X') (hY : Y =ᵐ[P] Y') :
    covariance X Y P = covariance X' Y' P := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  apply integral_congr_ae
  filter_upwards [hX, hY] with ω hx hy
  rw [hx, hy]

/-- The diagonal has product-volume measure zero in positive dimension. -/
theorem ae_ne_diagonal (d : ℕ) (hd : 0 < d) :
    ∀ᵐ p : Space d × Space d ∂(volume.prod volume), p.1 ≠ p.2 := by
  have hdim : Module.finrank ℝ (Space d) = d := finrank_euclideanSpace_fin
  let : Nontrivial (Space d) := Module.nontrivial_of_finrank_pos (by rw [hdim]; exact hd)
  apply (Measure.ae_prod_iff_ae_ae (isOpen_ne_fun continuous_fst continuous_snd).measurableSet).2
  filter_upwards with y
  filter_upwards [(volume : Measure (Space d)).ae_ne y] with y' hy'
  exact Ne.symm hy'

/-- A jointly almost-everywhere strongly measurable field has a jointly measurable version
whose sections agree in either order almost everywhere. -/
theorem exists_measurable_version_ae_sections {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] {P : Measure Ω} {ν : Measure E} [SFinite P] [SFinite ν]
    {T : Ω → E → ℝ} (hT : AEStronglyMeasurable (fun q : Ω × E => T q.1 q.2) (P.prod ν)) :
    ∃ U : Ω → E → ℝ, Measurable (fun q : Ω × E => U q.1 q.2) ∧
      (∀ᵐ ω ∂P, ∀ᵐ y ∂ν, T ω y = U ω y) ∧
      (∀ᵐ y ∂ν, ∀ᵐ ω ∂P, T ω y = U ω y) := by
  refine ⟨fun ω y => hT.mk (fun q : Ω × E => T q.1 q.2) (ω, y),
    hT.stronglyMeasurable_mk.measurable, ?_, ?_⟩
  · exact MeasureTheory.Measure.ae_ae_of_ae_prod hT.ae_eq_mk
  · have hswap := (Measure.measurePreserving_swap (μ := ν) (ν := P)).quasiMeasurePreserving.tendsto_ae.eventually
      hT.ae_eq_mk
    exact MeasureTheory.Measure.ae_ae_of_ae_prod hswap

/-- A measurable version can be chosen to vanish at every exceptional spatial point. -/
theorem exists_measurable_version_with_good_sections {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] {P : Measure Ω} {ν : Measure E} [SFinite P] [SFinite ν]
    {T : Ω → E → ℝ} (hT : AEStronglyMeasurable (fun q : Ω × E => T q.1 q.2) (P.prod ν)) :
    ∃ U : Ω → E → ℝ, Measurable (fun q : Ω × E => U q.1 q.2) ∧
      (∀ᵐ ω ∂P, ∀ᵐ y ∂ν, T ω y = U ω y) ∧
      (∀ᵐ y ∂ν, ∀ᵐ ω ∂P, T ω y = U ω y) ∧
      ∀ y, (∀ᵐ ω ∂P, T ω y = U ω y) ∨ ∀ ω, U ω y = 0 := by
  classical
  obtain ⟨U, hUm, hUω, hUy⟩ := exists_measurable_version_ae_sections hT
  have hnull : ν {y | ¬ ∀ᵐ ω ∂P, T ω y = U ω y} = 0 := (ae_iff.mp hUy)
  obtain ⟨s, hs, hsm, hs0⟩ := exists_measurable_superset_of_null hnull
  have hgood : ∀ᵐ y ∂ν, y ∉ s := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hs0
  refine ⟨fun ω y => if y ∈ s then 0 else U ω y, ?_, ?_, ?_, ?_⟩
  · exact Measurable.ite (hsm.preimage measurable_snd) measurable_const hUm
  · filter_upwards [hUω] with ω hω
    filter_upwards [hω, hgood] with y hy hys
    simpa [hys] using hy
  · filter_upwards [hUy, hgood] with y hy hys
    filter_upwards [hy] with ω hω
    simpa [hys] using hω
  · intro y
    by_cases hy : y ∈ s
    · right
      intro ω
      simp [hy]
    · left
      have hsection : ∀ᵐ ω ∂P, T ω y = U ω y := by
        by_contra h
        exact hy (hs h)
      filter_upwards [hsection] with ω hω
      simpa [hy] using hω

/-- A centered field with uniformly bounded diagonal covariance has a jointly measurable version
with centered square-integrable sections satisfying the same uniform second-moment bound. -/
theorem exists_measurable_version_with_bounded_moments {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [Nonempty E] {P : Measure Ω} {ν : Measure E} [SFinite P] [SFinite ν]
    {T : Ω → E → ℝ} {K : ℝ}
    (hT : AEStronglyMeasurable (fun q : Ω × E => T q.1 q.2) (P.prod ν))
    (hLp : ∀ y, MemLp (fun ω => T ω y) 2 P) (hmean : ∀ y, ∫ ω, T ω y ∂P = 0)
    (hcov : ∀ y, |covariance (fun ω => T ω y) (fun ω => T ω y) P| ≤ K) :
    ∃ U : Ω → E → ℝ, Measurable (fun q : Ω × E => U q.1 q.2) ∧
      (∀ᵐ ω ∂P, ∀ᵐ y ∂ν, T ω y = U ω y) ∧
      (∀ᵐ y ∂ν, ∀ᵐ ω ∂P, T ω y = U ω y) ∧
      (∀ y, ∫ ω, U ω y ∂P = 0) ∧
      (∀ y, Integrable (fun ω => U ω y ^ 2) P) ∧
      ∀ y, ∫ ω, U ω y ^ 2 ∂P ≤ K := by
  classical
  obtain ⟨U, hUm, hUω, hUae, hUy⟩ := exists_measurable_version_with_good_sections hT
  obtain ⟨y₀⟩ := ‹Nonempty E›
  have hK : 0 ≤ K := (abs_nonneg _).trans (hcov y₀)
  have hpoint (y : E) : (∫ ω, U ω y ∂P = 0) ∧
      Integrable (fun ω => U ω y ^ 2) P ∧ (∫ ω, U ω y ^ 2 ∂P ≤ K) := by
    have hi : Integrable (fun ω => T ω y ^ 2) P := by
      have h := (hLp y).integrable_mul (hLp y)
      change Integrable (fun ω => T ω y * T ω y) P at h
      simpa only [pow_two] using h
    have hbound : ∫ ω, T ω y ^ 2 ∂P ≤ K := by
      simpa [covariance, hmean y, pow_two] using
        (le_abs_self (covariance (fun ω => T ω y) (fun ω => T ω y) P)).trans (hcov y)
    rcases hUy y with heq | hzero
    · have hsqeq : (fun ω => T ω y ^ 2) =ᵐ[P] fun ω => U ω y ^ 2 := by
        filter_upwards [heq] with ω hω
        rw [hω]
      refine ⟨?_, hi.congr hsqeq, ?_⟩
      · rw [← integral_congr_ae heq]
        exact hmean y
      · rw [← integral_congr_ae hsqeq]
        exact hbound
    · simp [hzero, hK]
  exact ⟨U, hUm, hUω, hUae, fun y => (hpoint y).1, fun y => (hpoint y).2.1,
    fun y => (hpoint y).2.2⟩

/-- Two square-integrable variables with second moments bounded by `K` have absolute product
expectation at most `K`. -/
theorem integral_abs_mul_le_of_second_moment_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ} {K : ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hXK : ∫ ω, X ω ^ 2 ∂P ≤ K) (hYK : ∫ ω, Y ω ^ 2 ∂P ≤ K) :
    ∫ ω, |X ω * Y ω| ∂P ≤ K := by
  have hXi : Integrable (fun ω => X ω ^ 2) P := by
    have h := hX.integrable_mul hX
    change Integrable (fun ω => X ω * X ω) P at h
    simpa only [pow_two] using h
  have hYi : Integrable (fun ω => Y ω ^ 2) P := by
    have h := hY.integrable_mul hY
    change Integrable (fun ω => Y ω * Y ω) P at h
    simpa only [pow_two] using h
  exact (FiniteRange.integral_abs_mul_le hXi hYi).trans (by linarith)

/-- A uniform diagonal covariance bound controls absolute products of centered variables. -/
theorem integral_abs_mul_le_of_centered_covariance_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ} {K : ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hX0 : ∫ ω, X ω ∂P = 0) (hY0 : ∫ ω, Y ω ∂P = 0)
    (hXK : |covariance X X P| ≤ K) (hYK : |covariance Y Y P| ≤ K) :
    ∫ ω, |X ω * Y ω| ∂P ≤ K := by
  apply integral_abs_mul_le_of_second_moment_le hX hY
  · simpa [covariance, hX0, pow_two] using (le_abs_self (covariance X X P)).trans hXK
  · simpa [covariance, hY0, pow_two] using (le_abs_self (covariance Y Y P)).trans hYK

/-- An integrable nonnegative kernel convolved with a bounded function is uniformly bounded. -/
theorem integral_abs_mul_sub_le (d : ℕ) {f k : Space d → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hfB : ∀ x, |f x| ≤ B)
    (hk : Integrable k) (hk0 : ∀ x, 0 ≤ k x) (y : Space d) :
    ∫ x, |f x| * k (y - x) ≤ B * ∫ x, k x := by
  have hki : Integrable (fun x => k (y - x)) := hk.comp_sub_left y
  have hfi : Integrable (fun x => |f x| * k (y - x)) := by
    apply hki.bdd_mul (by simpa only [Real.norm_eq_abs] using hf.norm)
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_abs] using hfB x
  calc
    ∫ x, |f x| * k (y - x) ≤ ∫ x, B * k (y - x) :=
      integral_mono hfi (hki.const_mul B) fun x =>
        mul_le_mul_of_nonneg_right (hfB x) (hk0 (y - x))
    _ = B * ∫ x, k (y - x) := integral_const_mul B _
    _ = B * ∫ x, k x := by rw [integral_sub_left_eq_self]

/-- A bounded integrable function times an integrable difference kernel is integrable on the
product space. -/
theorem integrable_abs_mul_kernel (d : ℕ) {f k : Space d → ℝ} {B : ℝ}
    (hfi : Integrable f) (hfB : ∀ x, |f x| ≤ B) (hki : Integrable k) :
    Integrable (fun p : Space d × Space d => |f p.1| * |f p.2| * k (p.1 - p.2))
      (volume.prod volume) := by
  have hbase := hfi.abs.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hki
  have hfmeas : AEStronglyMeasurable (fun p : Space d × Space d => |f p.1|)
      (volume.prod volume) := hfi.abs.aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst
  have h := hbase.mul_bdd hfmeas (Filter.Eventually.of_forall fun p => by
    simpa only [Real.norm_eq_abs, abs_abs] using hfB p.1)
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  change |f p.2| * k (p.1 - p.2) * |f p.1| = |f p.1| * |f p.2| * k (p.1 - p.2)
  ring

/-- The integral of a nonnegative convolution against an integrable bounded function. -/
theorem integral_abs_mul_convolution_le (d : ℕ) {f k : Space d → ℝ} {B : ℝ}
    (hfm : StronglyMeasurable f) (hfi : Integrable f) (hfB : ∀ x, |f x| ≤ B)
    (hkm : StronglyMeasurable k) (hki : Integrable k) (hk0 : ∀ x, 0 ≤ k x) :
    ∫ y, |f y| * (∫ x, |f x| * k (y - x)) ≤
      B * (∫ x, k x) * ∫ y, |f y| := by
  have hm : StronglyMeasurable (fun p : Space d × Space d => |f p.2| * k (p.1 - p.2)) := by
    have hf : StronglyMeasurable (fun p : Space d × Space d => |f p.2|) := by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using
        (hfm.comp_measurable measurable_snd).norm
    exact hf.mul (hkm.comp_measurable (measurable_fst.sub measurable_snd))
  have hm' : StronglyMeasurable (fun y : Space d => ∫ x, |f x| * k (y - x)) :=
    hm.integral_prod_right'
  have hinner (y : Space d) : 0 ≤ ∫ x, |f x| * k (y - x) :=
    integral_nonneg fun x => mul_nonneg (abs_nonneg _) (hk0 _)
  have hbound (y : Space d) :
      |f y| * (∫ x, |f x| * k (y - x)) ≤ |f y| * (B * ∫ x, k x) :=
    mul_le_mul_of_nonneg_left (integral_abs_mul_sub_le d hfm.aestronglyMeasurable hfB hki hk0 y)
      (abs_nonneg _)
  have hmajor : Integrable (fun y => |f y| * (B * ∫ x, k x)) := hfi.abs.mul_const _
  have hmain : Integrable (fun y => |f y| * (∫ x, |f x| * k (y - x))) := by
    have hfmabs : StronglyMeasurable (fun y => |f y|) := by
      simpa only [Real.norm_eq_abs] using hfm.norm
    apply hmajor.mono' (hfmabs.mul hm').aestronglyMeasurable
    filter_upwards with y
    change ‖|f y| * (∫ x, |f x| * k (y - x))‖ ≤ |f y| * (B * ∫ x, k x)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hinner y))]
    exact hbound y
  calc
    ∫ y, |f y| * (∫ x, |f x| * k (y - x)) ≤ ∫ y, |f y| * (B * ∫ x, k x) :=
      integral_mono hmain hmajor hbound
    _ = B * (∫ x, k x) * ∫ y, |f y| := by rw [integral_mul_const]; ring

/-- The Riesz-heat convolution of a bounded integrable function has the expected time decay. -/
theorem rieszHeat_convolution_bound (d : ℕ) (β : ℝ) (hβ : 0 < β) (hβd : β < d)
    {f : Space d → ℝ} {B : ℝ} (hfm : StronglyMeasurable f) (hfi : Integrable f)
    (hfB : ∀ x, |f x| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      (∫ y, |f y| * (∫ x, |f x| * (‖y - x‖ ^ (-β) * heatKernel d t (y - x)))) ≤
        B * (C * t ^ (-β / 2)) * ∫ y, |f y| := by
  obtain ⟨C, hC, hCt⟩ := rieszHeat_bound d β hβ hβd
  refine ⟨C, hC, ?_⟩
  intro t ht
  let k : Space d → ℝ := fun z => ‖z‖ ^ (-β) * heatKernel d t z
  have hp : Measurable (fun x : ℝ => x ^ (-β)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x hx
    exact (Real.continuousAt_rpow_const x (-β) (Or.inl hx)).continuousWithinAt
  have hkm : StronglyMeasurable k := by
    exact ((hp.comp continuous_norm.measurable).mul (continuous_heatKernel d t).measurable).stronglyMeasurable
  have hki : Integrable k := (hCt t ht).1
  have hk0 (z : Space d) : 0 ≤ k z :=
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (heatKernel_nonneg d ht z)
  have hB : 0 ≤ B := (abs_nonneg (f 0)).trans (hfB 0)
  have hf0 : 0 ≤ ∫ y, |f y| := integral_nonneg fun y => abs_nonneg _
  calc
    (∫ y, |f y| * (∫ x, |f x| * k (y - x))) ≤ B * (∫ x, k x) * ∫ y, |f y| :=
      integral_abs_mul_convolution_le d hfm hfi hfB hkm hki hk0
    _ ≤ B * (C * t ^ (-β / 2)) * ∫ y, |f y| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hCt t ht).2 hB) hf0

/-- Fubini expresses a bounded-kernel second moment through the covariance of a centered field. -/
theorem integral_pair_kernel_eq_covariance {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {ν : Measure E} [SFinite P] [SFinite ν] {T : Ω → E → ℝ}
    (hT : Measurable fun q : Ω × E => T q.1 q.2) {g : E → ℝ}
    (hgm : Measurable g) (hg : Integrable g ν) {B : ℝ}
    (hsq : ∀ z, g z ≠ 0 → Integrable (fun ω => T ω z ^ 2) P)
    (hB : ∀ z, g z ≠ 0 → ∫ ω, T ω z ^ 2 ∂P ≤ B)
    (hmean : ∀ z, ∫ ω, T ω z ∂P = 0)
    {k : E × E → ℝ} (hkm : Measurable k) {M : ℝ} (hkM : ∀ p, ‖k p‖ ≤ M) :
    (∫ ω, ∫ p : E × E, (g p.1 * T ω p.1 * (g p.2 * T ω p.2)) * k p ∂(ν.prod ν) ∂P) =
      ∫ p : E × E, (g p.1 * g p.2 * k p) *
        covariance (fun ω => T ω p.1) (fun ω => T ω p.2) P ∂(ν.prod ν) := by
  have hi := FiniteRange.integrable_mul_prod_of_sq hT hgm hg hsq hB
  have hkmeas : AEStronglyMeasurable (fun q : Ω × (E × E) => k q.2)
      (P.prod (ν.prod ν)) := (hkm.comp measurable_snd).aestronglyMeasurable
  have hprod : Integrable (fun q : Ω × (E × E) =>
      (g q.2.1 * T q.1 q.2.1 * (g q.2.2 * T q.1 q.2.2)) * k q.2)
      (P.prod (ν.prod ν)) :=
    hi.mul_bdd hkmeas (Filter.Eventually.of_forall fun q => hkM q.2)
  rw [integral_integral_swap hprod]
  apply integral_congr_ae
  filter_upwards with p
  rw [covariance, hmean p.1, hmean p.2]
  simp only [sub_zero]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  ring

private theorem measurable_spatial_pair {Ω V F : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    [MeasurableSpace F] {h : V × V → F} (hh : Measurable h) :
    Measurable (fun q : (Ω × V) × V => h (q.2, q.1.2)) :=
  hh.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))

/-- A jointly measurable field has a jointly measurable Fourier transform after multiplication
by a measurable spatial weight. -/
theorem measurable_fourier_field {Ω : Type*} [MeasurableSpace Ω] (d : ℕ)
    {T : Ω → Space d → ℝ} (hT : Measurable fun q : Ω × Space d => T q.1 q.2)
    {g : Space d → ℝ} (hg : Measurable g) :
    Measurable (fun p : Ω × Space d =>
      𝓕 (fun x => ((g x * T p.1 x : ℝ) : ℂ)) p.2) := by
  have htrip : Measurable (fun q : (Ω × Space d) × Space d =>
      phase q.2 q.1.2 * ((g q.2 * T q.1.1 q.2 : ℝ) : ℂ)) := by
    have hphase : Measurable (fun q : (Ω × Space d) × Space d => phase q.2 q.1.2) :=
      measurable_spatial_pair (continuous_phase d).measurable
    have hq : Measurable (fun q : (Ω × Space d) × Space d => (q.1.1, q.2)) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have hfield : Measurable (fun q : (Ω × Space d) × Space d => T q.1.1 q.2) := hT.comp hq
    exact hphase.mul (Complex.measurable_ofReal.comp ((hg.comp measurable_snd).mul hfield))
  have hi := (htrip.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  convert hi using 1
  funext p
  exact fourier_eq_phase _ _

/-- Gaussian-damped Fourier energy is integrable for an integrable function. -/
theorem integrable_heat_fourier (d : ℕ) {g : Space d → ℝ} (hg : Integrable g)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun ξ : Space d => Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) *
      ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2) := by
  have hw : Integrable (fun ξ : Space d => Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2))) := by
    have h := (integrable_gaussian_weight d ht).re
    change Integrable (fun ξ : Space d => Complex.re
      ((Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ)) at h
    simpa only [Complex.ofReal_re] using h
  have hcont : Continuous (fun ξ : Space d => 𝓕 (fun x => (g x : ℂ)) ξ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg.ofReal
  have hL : 0 ≤ ∫ x : Space d, ‖(g x : ℂ)‖ := integral_nonneg fun x => norm_nonneg _
  have hbound (ξ : Space d) : ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ≤ ∫ x : Space d, ‖(g x : ℂ)‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ (Space d))
      (fun x => (g x : ℂ)) ξ
  have hi := hw.bdd_mul (c := (∫ x : Space d, ‖(g x : ℂ)‖) ^ 2)
    (hcont.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      change ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2 ≤ (∫ x : Space d, ‖(g x : ℂ)‖) ^ 2
      nlinarith [norm_nonneg (𝓕 (fun x => (g x : ℂ)) ξ), hbound ξ])
  simpa only [Pi.pow_apply, mul_comm] using hi

/-- The covariance integral associated with a bounded kernel is integrable. -/
theorem integrable_pair_kernel_covariance {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {ν : Measure E} [SFinite P] [SFinite ν] {T : Ω → E → ℝ}
    (hT : Measurable fun q : Ω × E => T q.1 q.2) {g : E → ℝ}
    (hgm : Measurable g) (hg : Integrable g ν) {B : ℝ}
    (hsq : ∀ z, g z ≠ 0 → Integrable (fun ω => T ω z ^ 2) P)
    (hB : ∀ z, g z ≠ 0 → ∫ ω, T ω z ^ 2 ∂P ≤ B)
    (hmean : ∀ z, ∫ ω, T ω z ∂P = 0)
    {k : E × E → ℝ} (hkm : Measurable k) {M : ℝ} (hkM : ∀ p, ‖k p‖ ≤ M) :
    Integrable (fun p : E × E => (g p.1 * g p.2 * k p) *
      covariance (fun ω => T ω p.1) (fun ω => T ω p.2) P) (ν.prod ν) := by
  have hi := FiniteRange.integrable_mul_prod_of_sq hT hgm hg hsq hB
  have hkmeas : AEStronglyMeasurable (fun q : Ω × (E × E) => k q.2)
      (P.prod (ν.prod ν)) := (hkm.comp measurable_snd).aestronglyMeasurable
  have hprod : Integrable (fun q : Ω × (E × E) =>
      (g q.2.1 * T q.1 q.2.1 * (g q.2.2 * T q.1 q.2.2)) * k q.2)
      (P.prod (ν.prod ν)) :=
    hi.mul_bdd hkmeas (Filter.Eventually.of_forall fun q => hkM q.2)
  refine hprod.integral_prod_right.congr (Filter.Eventually.of_forall fun p => ?_)
  change (∫ ω, (g p.1 * T ω p.1 * (g p.2 * T ω p.2)) * k p ∂P) =
    (g p.1 * g p.2 * k p) * covariance (fun ω => T ω p.1) (fun ω => T ω p.2) P
  rw [covariance, hmean p.1, hmean p.2]
  simp only [sub_zero]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  ring

/-- Expected Gaussian-damped Fourier energy is integrable under uniform second moments. -/
theorem integrable_expected_heatEnergy {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] (d : ℕ) {T : Ω → Space d → ℝ}
    (hT : Measurable fun q : Ω × Space d => T q.1 q.2) {g : Space d → ℝ}
    (hgm : Measurable g) (hg : Integrable g) {B : ℝ}
    (hsq : ∀ z, g z ≠ 0 → Integrable (fun ω => T ω z ^ 2) P)
    (hB : ∀ z, g z ≠ 0 → ∫ ω, T ω z ^ 2 ∂P ≤ B)
    (hfield : ∀ᵐ ω ∂P, Integrable (fun y => g y * T ω y)) {t : ℝ} (ht : 0 < t) :
    Integrable (fun ω => ∫ ξ : Space d, Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) *
      ‖𝓕 (fun x => ((g x * T ω x : ℝ) : ℂ)) ξ‖ ^ 2) P := by
  let k : Space d × Space d → ℝ := fun p => heatKernel d t (p.1 - p.2)
  have hkm : Measurable k := ((continuous_heatKernel d t).comp
    (continuous_fst.sub continuous_snd)).measurable
  have hkbound (p : Space d × Space d) : ‖k p‖ ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg d ht _)]
    exact heatKernel_le d ht _
  have hprod : Integrable (fun q : Ω × (Space d × Space d) =>
      (g q.2.1 * T q.1 q.2.1 * (g q.2.2 * T q.1 q.2.2)) * k q.2)
      (P.prod (volume.prod volume)) :=
    (FiniteRange.integrable_mul_prod_of_sq hT hgm hg hsq hB).mul_bdd
      (hkm.comp measurable_snd).aestronglyMeasurable (Filter.Eventually.of_forall fun q => hkbound q.2)
  refine hprod.integral_prod_left.congr ?_
  filter_upwards [hfield] with ω hω
  change (∫ p : Space d × Space d,
      (g p.1 * T ω p.1 * (g p.2 * T ω p.2)) * k p ∂(volume.prod volume)) = _
  rw [heatEnergy_eq d t ht (fun x => g x * T ω x) hω]
  have hint : Integrable (fun p : Space d × Space d =>
      (g p.1 * T ω p.1 * (g p.2 * T ω p.2)) * k p) (volume.prod volume) :=
    (hω.mul_prod hω).mul_bdd hkm.aestronglyMeasurable (Filter.Eventually.of_forall hkbound)
  rw [integral_prod _ hint]

/-- The nonnegative integral of the damped energy equals the corresponding real expectation. -/
theorem lintegral_heatEnergy_eq_ofReal {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] (d : ℕ) {T : Ω → Space d → ℝ}
    (hT : Measurable fun q : Ω × Space d => T q.1 q.2) {g : Space d → ℝ}
    (hgm : Measurable g) (hg : Integrable g) {B : ℝ}
    (hsq : ∀ z, g z ≠ 0 → Integrable (fun ω => T ω z ^ 2) P)
    (hB : ∀ z, g z ≠ 0 → ∫ ω, T ω z ^ 2 ∂P ≤ B)
    (hfield : ∀ᵐ ω ∂P, Integrable (fun y => g y * T ω y)) {t : ℝ} (ht : 0 < t) :
    (∫⁻ ω, (∫⁻ ξ : Space d, ENNReal.ofReal
      (Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) *
        ‖𝓕 (fun x => ((g x * T ω x : ℝ) : ℂ)) ξ‖ ^ 2)) ∂P) =
      ENNReal.ofReal (∫ ω, (∫ ξ : Space d, Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) *
        ‖𝓕 (fun x => ((g x * T ω x : ℝ) : ℂ)) ξ‖ ^ 2) ∂P) := by
  have hi := integrable_expected_heatEnergy d hT hgm hg hsq hB hfield ht
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun ω =>
    integral_nonneg fun ξ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  apply lintegral_congr_ae
  filter_upwards [hfield] with ω hω
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_heat_fourier d hω ht)
    (Filter.Eventually.of_forall fun ξ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))).symm

/-- The heat transform of the Fourier-energy measure is the damped expected heat energy. -/
theorem lintegral_spectral_heat {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] (d : ℕ) {T : Ω → Space d → ℝ}
    (hT : Measurable fun q : Ω × Space d => T q.1 q.2) {g : Space d → ℝ}
    (hgm : Measurable g) (hg : Integrable g) {B A : ℝ} (hA : 0 ≤ A)
    (hsq : ∀ z, g z ≠ 0 → Integrable (fun ω => T ω z ^ 2) P)
    (hB : ∀ z, g z ≠ 0 → ∫ ω, T ω z ^ 2 ∂P ≤ B)
    (hfield : ∀ᵐ ω ∂P, Integrable (fun y => g y * T ω y)) {t : ℝ} (ht : 0 < t) :
    (∫⁻ p : Ω × Space d, ENNReal.ofReal (Real.exp
        (-(t * (1 + 4 * Real.pi ^ 2 * ‖p.2‖ ^ 2)))) ∂
      (P.prod volume).withDensity (fun p => ENNReal.ofReal
        (A * ‖𝓕 (fun x => ((g x * T p.1 x : ℝ) : ℂ)) p.2‖ ^ 2))) =
      ENNReal.ofReal (A * Real.exp (-t)) * ENNReal.ofReal
        (∫ ω, (∫ ξ : Space d, Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) *
          ‖𝓕 (fun x => ((g x * T ω x : ℝ) : ℂ)) ξ‖ ^ 2) ∂P) := by
  let F : Ω × Space d → ℝ := fun p => ‖𝓕 (fun x => ((g x * T p.1 x : ℝ) : ℂ)) p.2‖ ^ 2
  let Z : Ω × Space d → ℝ := fun p => 1 + 4 * Real.pi ^ 2 * ‖p.2‖ ^ 2
  have hFm : Measurable F := (measurable_fourier_field d hT hgm).norm.pow_const 2
  have hZm : Measurable Z := by
    dsimp [Z]
    fun_prop
  have hden : Measurable (fun p => ENNReal.ofReal (A * F p)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hFm)
  have hexp : Measurable (fun p => ENNReal.ofReal (Real.exp (-(t * Z p)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hZm).neg)
  have hheatm : Measurable (fun p => ENNReal.ofReal
      (Real.exp (-(4 * Real.pi ^ 2 * t * ‖p.2‖ ^ 2)) * F p)) := by
    apply ENNReal.measurable_ofReal.comp
    have hw : Measurable (fun p : Ω × Space d => Real.exp (-(4 * Real.pi ^ 2 * t * ‖p.2‖ ^ 2))) := by
      fun_prop
    exact hw.mul hFm
  calc
    (∫⁻ p, ENNReal.ofReal (Real.exp (-(t * Z p))) ∂(P.prod volume).withDensity
        (fun p => ENNReal.ofReal (A * F p))) =
        ∫⁻ p, ENNReal.ofReal (A * F p) * ENNReal.ofReal (Real.exp (-(t * Z p))) ∂(P.prod volume) :=
      lintegral_withDensity_eq_lintegral_mul (P.prod volume) hden hexp
    _ = ∫⁻ p, ENNReal.ofReal (A * Real.exp (-t)) * ENNReal.ofReal
        (Real.exp (-(4 * Real.pi ^ 2 * t * ‖p.2‖ ^ 2)) * F p) ∂(P.prod volume) := by
      refine lintegral_congr fun p => ?_
      rw [← ENNReal.ofReal_mul (mul_nonneg hA (sq_nonneg _)),
        ← ENNReal.ofReal_mul (mul_nonneg hA (Real.exp_pos _).le)]
      congr 1
      dsimp [Z]
      rw [show -(t * (1 + 4 * Real.pi ^ 2 * ‖p.2‖ ^ 2)) =
        -t + -(4 * Real.pi ^ 2 * t * ‖p.2‖ ^ 2) by ring, Real.exp_add]
      ring
    _ = ENNReal.ofReal (A * Real.exp (-t)) * ∫⁻ p, ENNReal.ofReal
        (Real.exp (-(4 * Real.pi ^ 2 * t * ‖p.2‖ ^ 2)) * F p) ∂(P.prod volume) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (A * Real.exp (-t)) * ENNReal.ofReal
        (∫ ω, (∫ ξ : Space d, Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) *
          ‖𝓕 (fun x => ((g x * T ω x : ℝ) : ℂ)) ξ‖ ^ 2) ∂P) := by
      rw [lintegral_prod _ hheatm.aemeasurable,
        lintegral_heatEnergy_eq_ofReal d hT hgm hg hsq hB hfield ht]

/-- Integrating a Gaussian heat estimate gives a weighted Fourier-energy estimate. -/
theorem lintegral_fourier_energy_le_of_heat {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] (d : ℕ) {T : Ω → Space d → ℝ}
    (hT : Measurable fun q : Ω × Space d => T q.1 q.2) {g : Space d → ℝ}
    (hgm : Measurable g) (hg : Integrable g) {B A M s a : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hs : 0 < s) (hsa : 0 < s - a)
    (hsq : ∀ z, g z ≠ 0 → Integrable (fun ω => T ω z ^ 2) P)
    (hB : ∀ z, g z ≠ 0 → ∫ ω, T ω z ^ 2 ∂P ≤ B)
    (hfield : ∀ᵐ ω ∂P, Integrable (fun y => g y * T ω y))
    (hheat : ∀ t : ℝ, 0 < t → A * (∫ ω,
      (∫ ξ : Space d, Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) *
        ‖𝓕 (fun x => ((g x * T ω x : ℝ) : ℂ)) ξ‖ ^ 2) ∂P) ≤ M * t ^ (-a)) :
    (∫⁻ ω, (∫⁻ ξ : Space d, ENNReal.ofReal
      ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s) *
        (A * ‖𝓕 (fun x => ((g x * T ω x : ℝ) : ℂ)) ξ‖ ^ 2))) ∂P) ≤
      ENNReal.ofReal (M * Real.Gamma (s - a) / Real.Gamma s) := by
  let F : Ω × Space d → ℝ := fun p => ‖𝓕 (fun x => ((g x * T p.1 x : ℝ) : ℂ)) p.2‖ ^ 2
  let Z : Ω × Space d → ℝ := fun p => 1 + 4 * Real.pi ^ 2 * ‖p.2‖ ^ 2
  have hFm : Measurable F := (measurable_fourier_field d hT hgm).norm.pow_const 2
  have hZm : Measurable Z := by dsimp [Z]; fun_prop
  have hZpos (p : Ω × Space d) : 0 < Z p := by dsimp [Z]; positivity
  have hden : Measurable (fun p => ENNReal.ofReal (A * F p)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hFm)
  have hneg : Measurable (fun p => ENNReal.ofReal (Z p) ^ (-s)) :=
    (ENNReal.measurable_ofReal.comp hZm).pow_const _
  let μ := (P.prod volume).withDensity (fun p => ENNReal.ofReal (A * F p))
  have hheatμ (t : ℝ) (ht : 0 < t) : ∫⁻ p, ENNReal.ofReal (Real.exp (-(t * Z p))) ∂μ ≤
      ENNReal.ofReal (M * t ^ (-a) * Real.exp (-t)) := by
    rw [lintegral_spectral_heat d hT hgm hg hA hsq hB hfield ht]
    rw [← ENNReal.ofReal_mul (mul_nonneg hA (Real.exp_pos _).le)]
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_right (hheat t ht) (Real.exp_pos (-t)).le
    nlinarith
  have hγ := lintegral_negative_power_le_of_heat_bound hZm hZpos hs hsa hM hheatμ
  rw [lintegral_withDensity_eq_lintegral_mul (P.prod volume) hden hneg] at hγ
  have hEm : Measurable (fun p => ENNReal.ofReal
      (Z p ^ (-s) * (A * F p))) := ENNReal.measurable_ofReal.comp
        ((hZm.pow_const _).mul (measurable_const.mul hFm))
  calc
    (∫⁻ ω, (∫⁻ ξ : Space d, ENNReal.ofReal
        ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s) *
          (A * ‖𝓕 (fun x => ((g x * T ω x : ℝ) : ℂ)) ξ‖ ^ 2))) ∂P) =
        ∫⁻ p, ENNReal.ofReal (Z p ^ (-s) * (A * F p)) ∂(P.prod volume) :=
      (lintegral_prod _ hEm.aemeasurable).symm
    _ = ∫⁻ p, (fun p => ENNReal.ofReal (A * F p)) p *
          ENNReal.ofReal (Z p) ^ (-s) ∂(P.prod volume) := by
      refine lintegral_congr fun p => ?_
      rw [ENNReal.ofReal_rpow_of_pos (hZpos p),
        ENNReal.ofReal_mul (Real.rpow_nonneg (hZpos p).le _), mul_comm]
    _ ≤ ENNReal.ofReal (M * Real.Gamma (s - a) / Real.Gamma s) := hγ

/-- The expectation of heat-damped Fourier energy is a heat-kernel covariance integral. -/
theorem integral_heatEnergy_eq_covariance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] (d : ℕ) {T : Ω → Space d → ℝ}
    (hT : Measurable fun q : Ω × Space d => T q.1 q.2) {g : Space d → ℝ}
    (hgm : Measurable g) (hg : Integrable g) {B : ℝ}
    (hsq : ∀ z, g z ≠ 0 → Integrable (fun ω => T ω z ^ 2) P)
    (hB : ∀ z, g z ≠ 0 → ∫ ω, T ω z ^ 2 ∂P ≤ B)
    (hmean : ∀ z, ∫ ω, T ω z ∂P = 0)
    (hfield : ∀ᵐ ω ∂P, Integrable (fun y => g y * T ω y)) {t : ℝ} (ht : 0 < t) :
    (∫ ω, (∫ ξ : Space d, Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) *
      ‖𝓕 (fun x => ((g x * T ω x : ℝ) : ℂ)) ξ‖ ^ 2) ∂P) =
      ∫ p : Space d × Space d, (g p.1 * g p.2 * heatKernel d t (p.1 - p.2)) *
        covariance (fun ω => T ω p.1) (fun ω => T ω p.2) P ∂(volume.prod volume) := by
  let k : Space d × Space d → ℝ := fun p => heatKernel d t (p.1 - p.2)
  have hkm : Measurable k := ((continuous_heatKernel d t).comp
    (continuous_fst.sub continuous_snd)).measurable
  have hkbound (p : Space d × Space d) : ‖k p‖ ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg d ht _)]
    exact heatKernel_le d ht _
  calc
    (∫ ω, (∫ ξ : Space d, Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) *
        ‖𝓕 (fun x => ((g x * T ω x : ℝ) : ℂ)) ξ‖ ^ 2) ∂P) =
        ∫ ω, (∫ p : Space d × Space d,
          (g p.1 * T ω p.1 * (g p.2 * T ω p.2)) * k p ∂(volume.prod volume)) ∂P := by
      apply integral_congr_ae
      filter_upwards [hfield] with ω hω
      rw [heatEnergy_eq d t ht (fun x => g x * T ω x) hω]
      have hint : Integrable (fun p : Space d × Space d =>
          (g p.1 * T ω p.1 * (g p.2 * T ω p.2)) * k p) (volume.prod volume) :=
        (hω.mul_prod hω).mul_bdd hkm.aestronglyMeasurable
          (Filter.Eventually.of_forall hkbound)
      rw [integral_prod _ hint]
    _ = ∫ p : Space d × Space d, (g p.1 * g p.2 * k p) *
        covariance (fun ω => T ω p.1) (fun ω => T ω p.2) P ∂(volume.prod volume) :=
      integral_pair_kernel_eq_covariance hT hgm hg hsq hB hmean hkm hkbound

/-- Rescaling a decaying covariance kernel gives a bound by the Riesz kernel away from zero. -/
theorem rescaled_covariance_kernel_le_riesz {β R r : ℝ} (hβ : 0 ≤ β)
    (hR : 0 < R) (hr : 0 < r) :
    R ^ β * (1 + R * r) ^ (-β) ≤ r ^ (-β) := by
  have h : (1 + R * r) ^ (-β) ≤ (R * r) ^ (-β) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hR hr) (by linarith) (neg_nonpos.mpr hβ)
  calc
    R ^ β * (1 + R * r) ^ (-β) ≤ R ^ β * (R * r) ^ (-β) :=
      mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hR.le _)
    _ = r ^ (-β) := by
      rw [Real.mul_rpow hR.le hr.le, ← mul_assoc, ← Real.rpow_add hR,
        add_neg_cancel, Real.rpow_zero, one_mul]

/-- The corresponding estimate for any covariance bounded by the decay kernel. -/
theorem rescaled_covariance_le_riesz {β R r K c : ℝ} (hβ : 0 ≤ β)
    (hR : 0 < R) (hr : 0 < r) (hK : 0 ≤ K)
    (hc : |c| ≤ K * (1 + R * r) ^ (-β)) :
    R ^ β * |c| ≤ K * r ^ (-β) := by
  calc
    R ^ β * |c| ≤ R ^ β * (K * (1 + R * r) ^ (-β)) :=
      mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hR.le _)
    _ = K * (R ^ β * (1 + R * r) ^ (-β)) := by ring
    _ ≤ K * r ^ (-β) := mul_le_mul_of_nonneg_left
      (rescaled_covariance_kernel_le_riesz hβ hR hr) hK

/-- Covariance decay gives a scale-uniform bound for the heat-kernel covariance integral. -/
theorem heat_covariance_integral_bound (d : ℕ) (β : ℝ) (hβ : 0 < β) (hβd : β < d)
    {f : Space d → ℝ} {B K : ℝ} (hfm : StronglyMeasurable f) (hfi : Integrable f)
    (hfB : ∀ x, |f x| ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R t : ℝ, 0 < R → 0 < t → ∀ c : Space d × Space d → ℝ,
      Integrable (fun p => (f p.1 * f p.2 * heatKernel d t (p.1 - p.2)) * c p)
        (volume.prod volume) →
      (∀ᵐ p ∂(volume.prod volume), |c p| ≤ K * (1 + R * ‖p.1 - p.2‖) ^ (-β)) →
      R ^ β * (∫ p : Space d × Space d,
        (f p.1 * f p.2 * heatKernel d t (p.1 - p.2)) * c p ∂(volume.prod volume)) ≤
          K * (B * (C * t ^ (-β / 2)) * ∫ y, |f y|) := by
  obtain ⟨C, hC, hconv⟩ := rieszHeat_convolution_bound d β hβ hβd hfm hfi hfB
  obtain ⟨D, _, hD⟩ := rieszHeat_bound d β hβ hβd
  refine ⟨C, hC, ?_⟩
  intro R t hR ht c hcint hcov
  let k : Space d → ℝ := fun z => ‖z‖ ^ (-β) * heatKernel d t z
  have hkint : Integrable k := (hD t ht).1
  have hmajor := integrable_abs_mul_kernel d hfi hfB hkint
  have hd : 0 < d := by
    have : (0 : ℝ) < d := lt_trans hβ hβd
    exact_mod_cast this
  have hA : 0 ≤ R ^ β := Real.rpow_nonneg hR.le _
  have hpoint : ∀ᵐ p : Space d × Space d ∂(volume.prod volume),
      R ^ β * ((f p.1 * f p.2 * heatKernel d t (p.1 - p.2)) * c p) ≤
        K * (|f p.1| * |f p.2| * k (p.1 - p.2)) := by
    filter_upwards [hcov, ae_ne_diagonal d hd] with p hp hne
    have hr : 0 < ‖p.1 - p.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hdecay := rescaled_covariance_le_riesz hβ.le hR hr hK hp
    have hheat := heatKernel_nonneg d ht (p.1 - p.2)
    calc
      R ^ β * ((f p.1 * f p.2 * heatKernel d t (p.1 - p.2)) * c p) ≤
          R ^ β * |(f p.1 * f p.2 * heatKernel d t (p.1 - p.2)) * c p| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hA
      _ = |f p.1| * |f p.2| * heatKernel d t (p.1 - p.2) * (R ^ β * |c p|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hheat]
        ring
      _ ≤ |f p.1| * |f p.2| * heatKernel d t (p.1 - p.2) *
          (K * ‖p.1 - p.2‖ ^ (-β)) :=
        mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ = K * (|f p.1| * |f p.2| * k (p.1 - p.2)) := by dsimp [k]; ring
  have hmono := integral_mono_ae (hcint.const_mul (R ^ β)) (hmajor.const_mul K) hpoint
  rw [integral_const_mul, integral_const_mul] at hmono
  have heq : (∫ p : Space d × Space d, |f p.1| * |f p.2| * k (p.1 - p.2)
      ∂(volume.prod volume)) = ∫ y, |f y| * (∫ x, |f x| * k (y - x)) := by
    rw [integral_prod _ hmajor]
    apply integral_congr_ae
    filter_upwards with y
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [heq] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left (hconv t ht) hK)

/-- Covariance decay bounds the expected heat-damped Fourier energy. -/
theorem expected_heatEnergy_bound (d : ℕ) (β : ℝ) (hβ : 0 < β) (hβd : β < d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {g : Space d → ℝ} {B K : ℝ} (hgm : StronglyMeasurable g) (hg : Integrable g)
    (hgB : ∀ x, |g x| ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R t : ℝ, 0 < R → 0 < t → ∀ T : Ω → Space d → ℝ,
      Measurable (fun q : Ω × Space d => T q.1 q.2) →
      (∀ z, g z ≠ 0 → Integrable (fun ω => T ω z ^ 2) P) →
      (∀ z, g z ≠ 0 → ∫ ω, T ω z ^ 2 ∂P ≤ K) →
      (∀ z, ∫ ω, T ω z ∂P = 0) →
      (∀ᵐ ω ∂P, Integrable (fun y => g y * T ω y)) →
      (∀ᵐ p ∂(volume.prod volume),
        |covariance (fun ω => T ω p.1) (fun ω => T ω p.2) P| ≤
          K * (1 + R * ‖p.1 - p.2‖) ^ (-β)) →
      R ^ β * (∫ ω, (∫ ξ : Space d, Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) *
        ‖𝓕 (fun x => ((g x * T ω x : ℝ) : ℂ)) ξ‖ ^ 2) ∂P) ≤
          K * (B * (C * t ^ (-β / 2)) * ∫ y, |g y|) := by
  obtain ⟨C, hC, hbound⟩ := heat_covariance_integral_bound d β hβ hβd hgm hg hgB hK
  refine ⟨C, hC, ?_⟩
  intro R t hR ht T hT hsq hB hmean hfield hcov
  let k : Space d × Space d → ℝ := fun p => heatKernel d t (p.1 - p.2)
  have hkm : Measurable k := ((continuous_heatKernel d t).comp
    (continuous_fst.sub continuous_snd)).measurable
  have hkbound (p : Space d × Space d) : ‖k p‖ ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg d ht _)]
    exact heatKernel_le d ht _
  have hi := integrable_pair_kernel_covariance hT hgm.measurable hg hsq hB hmean hkm hkbound
  rw [integral_heatEnergy_eq_covariance d hT hgm.measurable hg hsq hB hmean hfield ht]
  exact hbound R t hR ht _ hi hcov

/-- Uniform boundedness of the expected negative Sobolev energy under covariance decay. -/
def SecondMomentEnergyStmt : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (β K : ℝ), 0 < β → β < (d : ℝ) → ∀ s : ℝ, β / 2 < s →
    ∀ (P : Measure Ω) [IsProbabilityMeasure P] (u : ℝ → Ω → Space d → ℝ),
      (∀ R : ℝ, 1 ≤ R → ∀ ω : Ω,
        Measurable (fun y => u R ω y) ∧
          ∀ φ : Space d → ℝ, IsTestFn Set.univ φ → Integrable (fun y => u R ω y * φ y)) →
      (∀ R : ℝ, 1 ≤ R →
        AEStronglyMeasurable (fun p : Ω × Space d => u R p.1 p.2) (P.prod volume)) →
      (∀ R : ℝ, 1 ≤ R → ∀ y : Space d, MemLp (fun ω => u R ω y) 2 P) →
      (∀ R : ℝ, 1 ≤ R → ∀ y : Space d, ∫ ω, u R ω y ∂P = 0) →
      (∀ R : ℝ, 1 ≤ R → ∀ y y' : Space d,
        |covariance (fun ω => u R ω y) (fun ω => u R ω y') P| ≤
          K * (1 + R * ‖y - y'‖) ^ (-β)) →
      ∀ χ : Space d → ℝ, IsTestFn Set.univ χ →
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
          ∫⁻ ω, fourierNegEnergy d s (fun x => R ^ (β / 2) * (χ x * u R ω x)) ∂P ≤ C

/-- Scaling an almost-everywhere equal function scales its Fourier energy by `R ^ β`. -/
theorem fourierNegEnergy_scale_of_ae_eq (d : ℕ) (s β R : ℝ) (hR : 0 < R)
    {f g : Space d → ℝ} (hfg : f =ᵐ[volume] g) :
    fourierNegEnergy d s (fun x => R ^ (β / 2) * f x) =
      ∫⁻ ξ : Space d, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s) *
        (R ^ β * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2)) := by
  have hp : 0 ≤ R ^ (β / 2) := Real.rpow_nonneg hR.le _
  have hs : (R ^ (β / 2)) ^ 2 = R ^ β := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 1
    ring
  have hF (ξ : Space d) : 𝓕 (fun x => ((R ^ (β / 2) * f x : ℝ) : ℂ)) ξ =
      ((R ^ (β / 2) : ℝ) : ℂ) * 𝓕 (fun x => (g x : ℂ)) ξ := by
    calc
      𝓕 (fun x => ((R ^ (β / 2) * f x : ℝ) : ℂ)) ξ =
          𝓕 (fun x => (((R ^ (β / 2) : ℝ) : ℂ) * (g x : ℂ))) ξ := by
        apply Real.fourier_congr_ae
        filter_upwards [hfg] with x hx
        rw [hx]
        push_cast
        rfl
      _ = ((R ^ (β / 2) : ℝ) : ℂ) * 𝓕 (fun x => (g x : ℂ)) ξ := by
        rw [fourier_eq_phase, fourier_eq_phase, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        ring
  unfold fourierNegEnergy
  refine lintegral_congr fun ξ => ?_
  have hbase : 1 + (2 * Real.pi * ‖ξ‖) ^ 2 = 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by ring
  rw [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp, hbase]
  simp only [mul_pow, hs]

/-- Covariance decay bounds the expected negative Sobolev energy uniformly over scales. -/
theorem secondMomentEnergy_holds : SecondMomentEnergyStmt := by
  intro Ω _ d β K hβ hβd s hs P _ u hlocal hjoint hLp hmean hcov χ hχ
  have hK : 0 ≤ K := by
    have h := hcov 1 (le_refl 1) (0 : Space d) 0
    simp only [sub_self, norm_zero, mul_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  have hgm : StronglyMeasurable χ := hχ.1.continuous.stronglyMeasurable
  have hg : Integrable χ := hχ.integrable
  obtain ⟨B, hB⟩ := hχ.2.1.exists_bound_of_continuous hχ.1.continuous
  have hgB (x : Space d) : |χ x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
  have hB0 : 0 ≤ B := (abs_nonneg (χ 0)).trans (hgB 0)
  have hg0 : 0 ≤ ∫ y, |χ y| := integral_nonneg fun y => abs_nonneg _
  have hs0 : 0 < s := by linarith
  have hsa : 0 < s - β / 2 := by linarith
  obtain ⟨C, hC, hheat⟩ := expected_heatEnergy_bound (P := P) d β hβ hβd hgm hg hgB hK
  let M : ℝ := K * (B * C * ∫ y, |χ y|)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨ENNReal.ofReal (M * Real.Gamma (s - β / 2) / Real.Gamma s), ENNReal.ofReal_ne_top, ?_⟩
  intro R hR
  have hR0 : 0 < R := by linarith
  have hdiag (y : Space d) : |covariance (fun ω => u R ω y) (fun ω => u R ω y) P| ≤ K := by
    simpa only [sub_self, norm_zero, mul_zero, add_zero, Real.one_rpow, mul_one] using
      hcov R hR y y
  obtain ⟨U, hUm, hUω, hUy, hUmean, hUsq, hUB⟩ :=
    exists_measurable_version_with_bounded_moments (hjoint R hR) (hLp R hR) (hmean R hR) hdiag
  have hfield : ∀ᵐ ω ∂P, Integrable (fun y => χ y * U ω y) := by
    filter_upwards [hUω] with ω hω
    refine ((hlocal R hR ω).2 χ hχ).congr ?_
    filter_upwards [hω] with y hy
    rw [hy, mul_comm]
  have hcovU : ∀ᵐ p : Space d × Space d ∂(volume.prod volume),
      |covariance (fun ω => U ω p.1) (fun ω => U ω p.2) P| ≤
        K * (1 + R * ‖p.1 - p.2‖) ^ (-β) := by
    have hfst := (Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure (Space d))) (ν := (volume : Measure (Space d)))).tendsto_ae.eventually hUy
    have hsnd := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (Space d))) (ν := (volume : Measure (Space d)))).tendsto_ae.eventually hUy
    filter_upwards [hfst, hsnd] with p hp1 hp2
    rw [← covariance_eq_of_ae_eq hp1 hp2]
    exact hcov R hR p.1 p.2
  have hsq : ∀ z, χ z ≠ 0 → Integrable (fun ω => U ω z ^ 2) P := fun z _ => hUsq z
  have hUB' : ∀ z, χ z ≠ 0 → ∫ ω, U ω z ^ 2 ∂P ≤ K := fun z _ => hUB z
  have hheat' (t : ℝ) (ht : 0 < t) : R ^ β * (∫ ω,
      (∫ ξ : Space d, Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) *
        ‖𝓕 (fun x => ((χ x * U ω x : ℝ) : ℂ)) ξ‖ ^ 2) ∂P) ≤ M * t ^ (-(β / 2)) := by
    have h := hheat R t hR0 ht U hUm hsq hUB' hUmean hfield hcovU
    have heq : K * (B * (C * t ^ (-β / 2)) * ∫ y, |χ y|) = M * t ^ (-(β / 2)) := by
      have hexp : -β / 2 = -(β / 2) := by ring
      rw [hexp]
      dsimp [M]
      ring
    rw [heq] at h
    exact h
  have hspec := lintegral_fourier_energy_le_of_heat d hUm hgm.measurable hg
    (B := K) (A := R ^ β) (M := M) (s := s) (a := β / 2)
    (Real.rpow_nonneg hR0.le _) hM hs0 hsa hsq hUB' hfield hheat'
  calc
    (∫⁻ ω, fourierNegEnergy d s (fun x => R ^ (β / 2) * (χ x * u R ω x)) ∂P) =
        ∫⁻ ω, (∫⁻ ξ : Space d, ENNReal.ofReal
          ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-s) *
            (R ^ β * ‖𝓕 (fun x => ((χ x * U ω x : ℝ) : ℂ)) ξ‖ ^ 2))) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hUω] with ω hω
      apply fourierNegEnergy_scale_of_ae_eq d s β R hR0
      filter_upwards [hω] with x hx
      rw [hx]
    _ ≤ ENNReal.ofReal (M * Real.Gamma (s - β / 2) / Real.Gamma s) := hspec

/-- Tightness of negative Sobolev norms on bounded domains. -/
def TightInNegSobolev {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (s : ℝ)
    (P : Measure Ω) (F : ℝ → Ω → (Space d → ℝ) → ℝ) : Prop :=
  ∀ D : Set (Space d), IsDomain D → ∀ ε : ℝ, 0 < ε →
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
      P {ω | M < negSobolevNorm d s D (F R ω)} ≤ ENNReal.ofReal ε

/-- A covariance decay criterion for negative Sobolev tightness. -/
def ContinuumBesovTightnessStmt (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (d : ℕ) (β K : ℝ), 0 < β → β < (d : ℝ) → ∀ s : ℝ, β / 2 < s →
    ∀ (P : Measure Ω) [IsProbabilityMeasure P] (u : ℝ → Ω → Space d → ℝ),
      (∀ R : ℝ, 1 ≤ R → ∀ ω : Ω,
        Measurable (fun y => u R ω y) ∧
          ∀ φ : Space d → ℝ, IsTestFn Set.univ φ → Integrable (fun y => u R ω y * φ y)) →
      (∀ R : ℝ, 1 ≤ R →
        AEStronglyMeasurable (fun p : Ω × Space d => u R p.1 p.2) (P.prod volume)) →
      (∀ R : ℝ, 1 ≤ R → ∀ y : Space d, MemLp (fun ω => u R ω y) 2 P) →
      (∀ R : ℝ, 1 ≤ R → ∀ y : Space d, ∫ ω, u R ω y ∂P = 0) →
      (∀ R : ℝ, 1 ≤ R → ∀ y y' : Space d,
        |covariance (fun ω => u R ω y) (fun ω => u R ω y') P| ≤
          K * (1 + R * ‖y - y'‖) ^ (-β)) →
      TightInNegSobolev d s P
        (fun R ω φ => R ^ (β / 2) * ∫ y : Space d, u R ω y * φ y)

/-- Fourier energy of a cut-off jointly almost-everywhere measurable field is almost everywhere
measurable in the random variable. -/
theorem aemeasurable_fourierNegEnergy_field {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (s : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    {u : Ω → Space d → ℝ} (hu : AEStronglyMeasurable
      (fun p : Ω × Space d => u p.1 p.2) (P.prod volume))
    {χ : Space d → ℝ} (hχ : Measurable χ) :
    AEMeasurable (fun ω => fourierNegEnergy d s (fun x => χ x * u ω x)) P := by
  obtain ⟨U, hUm, hUω, _⟩ := exists_measurable_version_ae_sections hu
  have hF := measurable_fourier_field d hUm hχ
  have hE : Measurable (fun ω => fourierNegEnergy d s (fun x => χ x * U ω x)) := by
    unfold fourierNegEnergy
    apply Measurable.lintegral_prod_right
    exact ENNReal.measurable_ofReal.comp
      (((measurable_const.add ((measurable_const.mul measurable_snd.norm).pow_const 2)).pow_const _).mul
        (hF.norm.pow_const 2))
  apply hE.aemeasurable.congr
  filter_upwards [hUω] with ω hω
  unfold fourierNegEnergy
  apply lintegral_congr
  intro ξ
  have hf : 𝓕 (fun x => ((χ x * U ω x : ℝ) : ℂ)) ξ =
      𝓕 (fun x => ((χ x * u ω x : ℝ) : ℂ)) ξ := by
    apply Real.fourier_congr_ae
    filter_upwards [hω] with x hx
    rw [hx]
  rw [hf]

universe u

set_option maxHeartbeats 400000 in
/-- A second-moment energy bound implies the covariance tightness criterion. -/
theorem continuumBesovTightness_of_secondMomentEnergy
    (henergy : SecondMomentEnergyStmt.{u}) (Ω : Type u) [MeasurableSpace Ω] :
    ContinuumBesovTightnessStmt Ω := by
  intro d β K hβ hβd s hs P _ u hlocal hjoint hLp hmean hcov D hD ε hε
  obtain ⟨r, hr⟩ := hD.2.1.subset_closedBall (0 : Space d)
  let D' : Set (Space d) := Metric.ball 0 (max r 0 + 1)
  have hD' : IsDomain D' := by
    refine ⟨Metric.isOpen_ball, Metric.isBounded_ball, ?_⟩
    exact ⟨0, by simp [D']; positivity⟩
  have hsub : closure D ⊆ D' := by
    have hc : closure D ⊆ Metric.closedBall (0 : Space d) r :=
      closure_minimal hr Metric.isClosed_closedBall
    intro x hx
    have hx' := hc hx
    rw [Metric.mem_closedBall] at hx'
    rw [show D' = Metric.ball 0 (max r 0 + 1) by rfl, Metric.mem_ball]
    linarith [le_max_left r 0]
  obtain ⟨χ, hχ, _, hχone⟩ := exists_isTestFn_eqOn_one' hD' hD.2.1.isCompact_closure hsub
  have hχuniv : IsTestFn Set.univ χ := ⟨hχ.1, hχ.2.1, Set.subset_univ _⟩
  obtain ⟨C, hC, hCbound⟩ := henergy (Ω := Ω) d β K hβ hβd s hs P u hlocal hjoint hLp hmean hcov χ hχuniv
  let e : ℝ≥0∞ := ENNReal.ofReal ε
  let T : ℝ≥0∞ := (C + 1) / e
  have he0 : e ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have het : e ≠ ⊤ := ENNReal.ofReal_ne_top
  have hT0 : T ≠ 0 := by
    apply (ENNReal.div_pos_iff.mpr ⟨?_, het⟩).ne'
    simp
  have hTt : T ≠ ⊤ := ENNReal.div_ne_top (ENNReal.add_ne_top.mpr ⟨hC, by simp⟩) he0
  refine ⟨T ^ (1 / 2 : ℝ), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hTt, ?_⟩
  intro R hR
  let Z : Ω → ℝ≥0∞ := fun ω => fourierNegEnergy d s
    (fun x => R ^ (β / 2) * (χ x * u R ω x))
  have hZm : AEMeasurable Z P := by
    have hm := aemeasurable_fourierNegEnergy_field d s P (hjoint R hR)
      (χ := fun x => R ^ (β / 2) * χ x)
      (measurable_const.mul hχ.1.continuous.measurable)
    simpa only [Z, mul_assoc] using hm
  have hnorm (ω : Ω) :
      negSobolevNorm d s D (fun φ => R ^ (β / 2) * ∫ y, u R ω y * φ y) ≤
        Z ω ^ (1 / 2 : ℝ) := by
    have h := negSobolevNorm_le_fourierNegEnergy d s D χ
      (fun x => R ^ (β / 2) * u R ω x) hχuniv
      (fun x hx => hχone (subset_closure hx))
      (fun φ hφ => (((hlocal R hR ω).2 φ hφ).const_mul (R ^ (β / 2))).congr
        (Filter.Eventually.of_forall fun x => by ring))
    have hf : (fun φ : Space d → ℝ => ∫ y, (R ^ (β / 2) * u R ω y) * φ y) =
        (fun φ => R ^ (β / 2) * ∫ y, u R ω y * φ y) := by
      funext φ
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      ring
    have hg : (fun x => χ x * (R ^ (β / 2) * u R ω x)) =
        (fun x => R ^ (β / 2) * (χ x * u R ω x)) := by
      funext x
      ring
    rw [hf, hg] at h
    exact h
  calc
    P {ω | T ^ (1 / 2 : ℝ) < negSobolevNorm d s D
        (fun φ => R ^ (β / 2) * ∫ y, u R ω y * φ y)}
      ≤ P {ω | T ≤ Z ω} := by
        apply measure_mono
        intro ω hω
        have hlt : T ^ (1 / 2 : ℝ) < Z ω ^ (1 / 2 : ℝ) := lt_of_lt_of_le hω (hnorm ω)
        exact le_of_lt ((ENNReal.rpow_lt_rpow_iff (by norm_num)).mp hlt)
    _ ≤ (∫⁻ ω, Z ω ∂P) / T := meas_ge_le_lintegral_div hZm hT0 hTt
    _ ≤ C / T := ENNReal.div_le_div_right (hCbound R hR) _
    _ ≤ e := by
      apply (ENNReal.div_le_iff hT0 hTt).2
      have heq : e * T = C + 1 := by
        dsimp [T]
        rw [mul_comm, ENNReal.div_mul_cancel he0 het]
      rw [heq]
      exact le_add_right le_rfl

/-- Covariance decay implies tightness in negative Sobolev spaces. -/
theorem continuumBesovTightness_holds (Ω : Type u) [MeasurableSpace Ω] :
    ContinuumBesovTightnessStmt Ω :=
  continuumBesovTightness_of_secondMomentEnergy secondMomentEnergy_holds Ω

end LatticeProb.Sobolev
