/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatSqOpen at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSqLim
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Killed heat kernel of the square, part 4: dyadic versus continuous staying
(task P2-KHSQ4, target `killedHeat_sqOpen`)

`KilledHeatSq.stayGrid_ae_eq`: for `z ∈ Q = sqOpen a L` and `t ≠ 0`, staying in `Q` at all dyadic
times `≤ t` agrees a.s. with staying in `Q` at all times `≤ t`.

Proof (own elementary argument; DEVIATIONS entry KHSQ4-1 proposed): on the dyadic event the
continuous path lies in the closed square on `[0, t]`, so `z + μ^{-1/2} B_s ∈ Q` for every
`μ > 1`. By Brownian scaling (`isPlanarBM_scaleBM`) and the fact that the staying probability
does not depend on the Brownian motion (`lintegral_killedHeat_eq`), this event has probability
`P(z + B_s ∈ Q, s ≤ t/μ)`. Letting `μ ↓ 1` gives `P(z + B_s ∈ Q, s < t)`, and the endpoint
`s = t` costs nothing because `B_t` has no atom on the four boundary lines.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeatSq

open KilledHeat HeatSq

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℂ} {P : Measure Ω}

/-- In `A` at all times `≤ t`. -/
def stayAll (A : Set ℂ) (B : ℝ≥0 → Ω → ℂ) (z : ℂ) (t : ℝ≥0) : Set Ω :=
  {ω | ∀ s : ℝ≥0, s ≤ t → z + B s ω ∈ A}

/-- Brownian scaling `s ↦ μ^{-1/2} B_{μ s}`. -/
def scaleBM (μ : ℝ≥0) (B : ℝ≥0 → Ω → ℂ) : ℝ≥0 → Ω → ℂ :=
  fun s ω ↦ (((Real.sqrt μ)⁻¹ : ℝ) : ℂ) * B (μ * s) ω

lemma coordProc_scaleBM (μ : ℝ≥0) (B : ℝ≥0 → Ω → ℂ) (p : Bool × ℝ≥0) :
    coordProc (scaleBM μ B) p = fun ω ↦ (Real.sqrt μ)⁻¹ • coordProc B (p.1, μ * p.2) ω := by
  ext ω
  rcases p with ⟨b, s⟩
  cases b <;> simp only [coordProc, scaleBM, Bool.false_eq_true, ite_false, ite_true, smul_eq_mul,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul]

theorem isPlanarBM_scaleBM (hB : IsPlanarBM B P) {μ : ℝ≥0} (hμ : μ ≠ 0) :
    IsPlanarBM (scaleBM μ B) P := by
  have hμ' : (0 : ℝ) < μ := lt_of_le_of_ne (NNReal.coe_nonneg μ) (Ne.symm (by exact_mod_cast hμ))
  refine ⟨?_, ?_, fun p ↦ ?_, fun p q ↦ ?_⟩
  · filter_upwards [hB.cont] with ω hω
    unfold scaleBM
    exact continuous_const.mul (hω.comp (continuous_const.mul continuous_id))
  · have h0 : IsGaussianProcess (fun p : Bool × ℝ≥0 ↦ fun ω ↦ coordProc B (p.1, μ * p.2) ω) P :=
      hB.gauss.comp_right (fun p : Bool × ℝ≥0 ↦ (p.1, μ * p.2))
    have := h0.smul (fun _ : Bool × ℝ≥0 ↦ (Real.sqrt μ)⁻¹)
    rw [funext (coordProc_scaleBM μ B)]
    exact this
  · rw [coordProc_scaleBM]
    simp only [smul_eq_mul]
    rw [integral_const_mul, hB.mean, mul_zero]
  · rw [coordProc_scaleBM, coordProc_scaleBM]
    simp only [smul_eq_mul]
    rw [covariance_const_mul_left, covariance_const_mul_right, hB.cov]
    rcases p with ⟨b, s⟩
    rcases q with ⟨b', r⟩
    simp only
    split_ifs
    · have hst : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt hμ'.le
      rw [min_mul_mul_left, NNReal.coe_mul]
      field_simp
      rw [Real.sq_sqrt hμ'.le]
    · ring

/-- The staying probability does not depend on the planar Brownian motion. -/
lemma measure_stayAll_eq {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {B' : ℝ≥0 → Ω' → ℂ}
    {P' : Measure Ω'} (hB : IsPlanarBM B P) (hB' : IsPlanarBM B' P') {A : Set ℂ} (hA : IsOpen A)
    {t : ℝ≥0} (ht : t ≠ 0) (z : ℂ) : P (stayAll A B z t) = P' (stayAll A B' z t) := by
  have h := lintegral_killedHeat_eq hA ht hB z MeasurableSet.univ
  have h' := lintegral_killedHeat_eq hA ht hB' z MeasurableSet.univ
  simp only [Set.mem_univ, true_and] at h h'
  exact h.symm.trans h'

lemma nullMeasurableSet_stayAll (hB : IsPlanarBM B P) {A : Set ℂ} (hA : IsOpen A) (z : ℂ)
    (t : ℝ≥0) : NullMeasurableSet (stayAll A B z t) P := by
  have hC : NullMeasurableSet (⋃ n : ℕ, ⋂ q : ℚ, {ω | z + B (clampT t q) ω ∈ innerSet A n}) P :=
    NullMeasurableSet.iUnion fun n ↦ NullMeasurableSet.iInter fun q ↦
      ((aemeasurable_const.add (aemeasurable_B hB _)).nullMeasurable
        (isClosed_innerSet A n).measurableSet)
  refine hC.congr ?_
  filter_upwards [hB.cont] with ω hω
  apply propext
  simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq, stayAll]
  exact (forall_mem_iff_exists_clamp (continuous_const.add hω) hA t).symm

lemma nullMeasurableSet_stayGrid (hB : IsPlanarBM B P) {Q : Set ℂ} (hQ : MeasurableSet Q)
    (z : ℂ) (t : ℝ≥0) : NullMeasurableSet (stayGrid Q B z t) P := by
  refine NullMeasurableSet.iInter fun n ↦ ?_
  have e : stayUpTo Q B z t n (2 ^ n + 1) =
      ⋂ j : Fin (2 ^ n + 1), {ω | z + B (gridT t n j) ω ∈ Q} := by
    ext ω
    simp only [stayUpTo, Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h j ↦ h j j.2, fun h j hj ↦ h ⟨j, hj⟩⟩
  rw [e]
  exact NullMeasurableSet.iInter fun j ↦
    (aemeasurable_const.add (aemeasurable_B hB _)).nullMeasurable hQ

lemma stayAll_subset_stayGrid (Q : Set ℂ) (z : ℂ) (t : ℝ≥0) :
    stayAll Q B z t ⊆ stayGrid Q B z t := fun ω hω ↦
  Set.mem_iInter.mpr fun n j hj ↦ hω _ (gridT_le (by omega))

/-- The closed square. -/
def sqClosed (a L : ℝ) : Set ℂ := {y | a ≤ y.re ∧ y.re ≤ a + L ∧ a ≤ y.im ∧ y.im ≤ a + L}

lemma isClosed_sqClosed (a L : ℝ) : IsClosed (sqClosed a L) := by
  have e : sqClosed a L = {y : ℂ | a ≤ y.re} ∩ {y | y.re ≤ a + L} ∩ {y | a ≤ y.im} ∩
      {y | y.im ≤ a + L} := by
    ext y; simp [sqClosed, and_assoc]
  rw [e]
  exact (((isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le Complex.continuous_re continuous_const)).inter
    (isClosed_le continuous_const Complex.continuous_im)).inter
    (isClosed_le Complex.continuous_im continuous_const)

lemma sqOpen_subset_sqClosed (a L : ℝ) : sqOpen a L ⊆ sqClosed a L := fun _ h ↦
  ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩

/-- Pulling a point of the closed square towards an interior point lands in the open square. -/
lemma add_smul_mem_sqOpen {a L : ℝ} {z y : ℂ} (hz : z ∈ sqOpen a L) (hy : z + y ∈ sqClosed a L)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) : z + (c : ℂ) * y ∈ sqOpen a L := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  obtain ⟨g1, g2, g3, g4⟩ := hy
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero] at g1 g2 g3 g4 ⊢
  have hc := sub_pos.2 hc1
  have hre : (z + (c : ℂ) * y).re = z.re + c * y.re := by simp
  have him : (z + (c : ℂ) * y).im = z.im + c * y.im := by simp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hre, him]
  · nlinarith [mul_pos hc (sub_pos.2 h1), mul_nonneg hc0.le (sub_nonneg.2 g1)]
  · nlinarith [mul_pos hc (sub_pos.2 h2), mul_nonneg hc0.le (sub_nonneg.2 g2)]
  · nlinarith [mul_pos hc (sub_pos.2 h3), mul_nonneg hc0.le (sub_nonneg.2 g3)]
  · nlinarith [mul_pos hc (sub_pos.2 h4), mul_nonneg hc0.le (sub_nonneg.2 g4)]

/-- A continuous path in `Q` at all dyadic times `≤ t` lies in the closed square on `[0, t]`. -/
lemma mem_sqClosed_of_stayGrid {a L : ℝ} {z : ℂ} {t : ℝ≥0} {ω : Ω}
    (hc : Continuous fun s ↦ B s ω) (hω : ω ∈ stayGrid (sqOpen a L) B z t) {s : ℝ≥0}
    (hs : s ≤ t) : z + B s ω ∈ sqClosed a L := by
  by_cases ht : t = 0
  · have hs0 : s = 0 := le_antisymm (ht ▸ hs) zero_le
    have := Set.mem_iInter.mp hω 0 0 (by norm_num)
    simp only [gridT, Nat.cast_zero, zero_mul, zero_div] at this
    exact sqOpen_subset_sqClosed a L (hs0 ▸ this)
  have ht' : (0 : ℝ) < t := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm (by exact_mod_cast ht))
  set j : ℕ → ℕ := fun n ↦ ⌊(2 : ℝ) ^ n * s / t⌋₊
  have hj : ∀ n, j n ≤ 2 ^ n := fun n ↦ by
    have : (2 : ℝ) ^ n * s / t ≤ 2 ^ n := by
      rw [div_le_iff₀ ht']
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs) (by positivity)
    exact Nat.floor_le_of_le (by push_cast; exact this)
  have hlim : Tendsto (fun n ↦ gridT t n (j n)) atTop (𝓝 s) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hb : ∀ n, dist (gridT t n (j n)) s ≤ (t : ℝ) / 2 ^ n := fun n ↦ by
      rw [NNReal.dist_eq]
      unfold gridT
      push_cast
      have hpos : (0 : ℝ) < 2 ^ n := by positivity
      have hfl := Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 ^ n * s / t)
      have hlt := Nat.lt_floor_add_one ((2 : ℝ) ^ n * s / t)
      have e1 : (j n : ℝ) * t / 2 ^ n - s = t / 2 ^ n * ((j n : ℝ) - 2 ^ n * s / t) := by
        field_simp
      rw [e1, abs_mul, abs_of_pos (by positivity)]
      refine mul_le_of_le_one_right (by positivity) ?_
      rw [abs_le]
      constructor <;> linarith
    refine squeeze_zero (fun _ ↦ dist_nonneg) hb ?_
    have e : (fun n : ℕ ↦ (t : ℝ) / 2 ^ n) = fun n ↦ (t : ℝ) * (1 / 2) ^ n := by
      funext n; rw [one_div_pow, mul_one_div]
    rw [e]
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (t : ℝ)
    rwa [mul_zero] at h
  refine (isClosed_sqClosed a L).mem_of_tendsto
    ((continuous_const.add hc).continuousAt.tendsto.comp hlim) (Eventually.of_forall fun n ↦ ?_)
  exact sqOpen_subset_sqClosed a L (Set.mem_iInter.mp hω n (j n) (by have := hj n; omega))

/-- `B_t` has no atom on a line `{coordinate = c}`. -/
lemma ae_coordProc_ne (hB : IsPlanarBM B P) {t : ℝ≥0} (ht : t ≠ 0) (b : Bool) (c : ℝ) :
    ∀ᵐ ω ∂P, coordProc B (b, t) ω ≠ c := by
  have h := hasLaw_coordProc hB b t
  have := nullSingletonClass_gaussianReal (μ := 0) ht
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have e : P {ω | coordProc B (b, t) ω = c} = (gaussianReal 0 t) {c} := by
    rw [← h.map_eq, Measure.map_apply₀ h.aemeasurable
      (measurableSet_singleton c).nullMeasurableSet]
    rfl
  rw [e]
  exact measure_singleton c

/-- **Dyadic versus continuous staying**: for `z ∈ Q` and `t ≠ 0`, staying in the open square at
all dyadic times `≤ t` agrees a.s. with staying in it at all times `≤ t`. -/
theorem stayGrid_ae_eq (hB : IsPlanarBM B P) {a L : ℝ} {z : ℂ} (hz : z ∈ sqOpen a L) {t : ℝ≥0}
    (ht : t ≠ 0) : stayGrid (sqOpen a L) B z t =ᵐ[P] stayAll (sqOpen a L) B z t := by
  have := hB.gauss.isProbabilityMeasure
  have hQo := isOpen_sqOpen a L
  refine (ae_eq_of_subset_of_measure_ge (stayAll_subset_stayGrid _ z t) ?_
    (nullMeasurableSet_stayAll hB hQo z t) (measure_ne_top _ _)).symm
  set μ : ℕ → ℝ≥0 := fun n ↦ 1 + 1 / ((n : ℝ≥0) + 1) with hμ
  have hμ1 : ∀ n, 1 < μ n := fun n ↦ lt_add_of_pos_right _ (by positivity)
  have hμ0 : ∀ n, μ n ≠ 0 := fun n ↦ (zero_lt_one.trans (hμ1 n)).ne'
  set T : ℕ → Set Ω := fun n ↦ stayAll (sqOpen a L) B z (t / μ n) with hT
  have hA : ∀ n, P (stayGrid (sqOpen a L) B z t) ≤ P (T n) := by
    intro n
    rw [hT, measure_stayAll_eq hB (isPlanarBM_scaleBM hB (hμ0 n)) hQo (div_ne_zero ht (hμ0 n)) z]
    refine measure_mono_ae ?_
    filter_upwards [hB.cont] with ω hc hω
    intro s hs
    show z + (((Real.sqrt (μ n))⁻¹ : ℝ) : ℂ) * B (μ n * s) ω ∈ sqOpen a L
    have hμ1' : (1 : ℝ) < μ n := by exact_mod_cast hμ1 n
    refine add_smul_mem_sqOpen hz (mem_sqClosed_of_stayGrid hc hω ?_) ?_ ?_
    · calc μ n * s ≤ μ n * (t / μ n) := by gcongr
        _ = t := mul_div_cancel₀ t (hμ0 n)
    · exact inv_pos.2 (Real.sqrt_pos.2 (by linarith))
    · rw [inv_lt_one₀ (Real.sqrt_pos.2 (by linarith)), Real.lt_sqrt zero_le_one]
      simpa using hμ1'
  have hanti : Antitone T := by
    intro n m hnm ω hω s hs
    refine hω s (hs.trans ?_)
    simp only [hμ]
    gcongr
  have hB2 : P (⋂ n, T n) ≤ P (stayAll (sqOpen a L) B z t) := by
    refine measure_mono_ae ?_
    filter_upwards [hB.cont, ae_coordProc_ne hB ht false (a - z.re),
      ae_coordProc_ne hB ht false (a + L - z.re), ae_coordProc_ne hB ht true (a - z.im),
      ae_coordProc_ne hB ht true (a + L - z.im)] with ω hc h1 h2 h3 h4 hω
    have hlt : ∀ s : ℝ≥0, s < t → z + B s ω ∈ sqOpen a L := by
      intro s hs
      obtain ⟨n, hn⟩ := exists_nat_ge ((s : ℝ) / ((t : ℝ) - s))
      refine Set.mem_iInter.mp hω n s ?_
      have hs' : (s : ℝ) < t := by exact_mod_cast hs
      rw [← NNReal.coe_le_coe, NNReal.coe_div, le_div_iff₀ (by simp [hμ]; positivity)]
      simp only [hμ]
      push_cast
      rw [div_le_iff₀ (by linarith)] at hn
      field_simp
      nlinarith
    intro s hs
    rcases lt_or_eq_of_le hs with hs | rfl
    · exact hlt s hs
    have hcl : z + B s ω ∈ sqClosed a L := by
      have hsub : Set.Iio s ⊆ (fun r ↦ z + B r ω) ⁻¹' sqClosed a L := fun r hr ↦
        sqOpen_subset_sqClosed a L (hlt r hr)
      have hcl := (isClosed_sqClosed a L).preimage (f := fun r ↦ z + B r ω)
        (continuous_const.add hc)
      have hmem : s ∈ closure (Set.Iio s) := by
        rw [closure_Iio' ⟨0, pos_iff_ne_zero.mpr ht⟩]
        exact Set.mem_Iic.mpr le_rfl
      exact hcl.closure_subset_iff.mpr hsub hmem
    obtain ⟨g1, g2, g3, g4⟩ := hcl
    simp only [coordProc, Bool.false_eq_true, ite_false, ite_true, ne_eq] at h1 h2 h3 h4
    simp only [Complex.add_re, Complex.add_im] at g1 g2 g3 g4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Complex.add_re, Complex.add_im]
    · exact lt_of_le_of_ne g1 fun h ↦ h1 (by linarith)
    · exact lt_of_le_of_ne g2 fun h ↦ h2 (by linarith)
    · exact lt_of_le_of_ne g3 fun h ↦ h3 (by linarith)
    · exact lt_of_le_of_ne g4 fun h ↦ h4 (by linarith)
  calc P (stayGrid (sqOpen a L) B z t) ≤ ⨅ n, P (T n) := le_iInf hA
    _ = P (⋂ n, T n) := (hanti.measure_iInter
        (fun n ↦ nullMeasurableSet_stayAll hB hQo z _) ⟨0, measure_ne_top _ _⟩).symm
    _ ≤ _ := hB2

end KilledHeatSq
end LQGMetric
