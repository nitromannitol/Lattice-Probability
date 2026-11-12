/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatSqStop at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSqMarkov
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareCK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Killed heat kernel of the square, part 2: optional stopping on a dyadic grid
(task P2-KHSQ3, target `killedHeat_sqOpen`)

Grid times `g_i = i t / 2ⁿ`. Let `E_m` be the event that `z + B` is in `Q` at the grid times
`g_0, …, g_{m−1}` and not at `g_m` (first exit from `Q` on the grid at step `m`). Since
`1 = 1_{stay up to M} + ∑_{m < M} 1_{E_m}` and `E_m` is a function of `(B_{g_j})_{j ≤ m}`, the
Markov step `integral_mul_sqMode_eq` gives (`KilledHeatSq.integral_stayN_sqMode`)

  `E[φ_p(z + B_t); grid path in Q] = e^{−λ_p t/2} φ_p(z) − ∑_{m ≤ 2ⁿ} e^{−λ_p (t − g_m)/2} E[φ_p(z + B_{g_m}); E_m]`.

This is the discrete optional stopping theorem for the martingale `e^{λ_p s/2} φ_p(z + B_s)` at
the first grid exit time (Karatzas–Shreve §4.3; Feller II §X.5 for the resulting image/sine
series). Own elementary assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeatSq

open KilledHeat HeatSq Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℂ} {P : Measure Ω}

/-- Dyadic grid times `i t / 2ⁿ`. -/
def gridT (t : ℝ≥0) (n i : ℕ) : ℝ≥0 := (i : ℝ≥0) * t / 2 ^ n

lemma gridT_le {t : ℝ≥0} {n i : ℕ} (hi : i ≤ 2 ^ n) : gridT t n i ≤ t := by
  unfold gridT
  rw [div_le_iff₀ (by positivity), mul_comm]
  gcongr
  exact_mod_cast hi

lemma gridT_mono {t : ℝ≥0} {n i j : ℕ} (hij : i ≤ j) : gridT t n i ≤ gridT t n j := by
  unfold gridT
  gcongr

lemma gridT_pow (t : ℝ≥0) (n : ℕ) : gridT t n (2 ^ n) = t := by
  unfold gridT
  push_cast
  field_simp

/-- In `Q` at the grid times `g_0, …, g_{m−1}`. -/
def stayUpTo (Q : Set ℂ) (B : ℝ≥0 → Ω → ℂ) (z : ℂ) (t : ℝ≥0) (n m : ℕ) : Set Ω :=
  {ω | ∀ j < m, z + B (gridT t n j) ω ∈ Q}

/-- First grid exit at step `m`. -/
def exitAt (Q : Set ℂ) (B : ℝ≥0 → Ω → ℂ) (z : ℂ) (t : ℝ≥0) (n m : ℕ) : Set Ω :=
  {ω | (∀ j < m, z + B (gridT t n j) ω ∈ Q) ∧ z + B (gridT t n m) ω ∉ Q}

lemma indicator_stayUpTo_succ (Q : Set ℂ) (z : ℂ) (t : ℝ≥0) (n m : ℕ) (ω : Ω) :
    (stayUpTo Q B z t n m).indicator (1 : Ω → ℝ) ω =
      (stayUpTo Q B z t n (m + 1)).indicator 1 ω + (exitAt Q B z t n m).indicator 1 ω := by
  by_cases h : ∀ j < m, z + B (gridT t n j) ω ∈ Q
  · by_cases hm : z + B (gridT t n m) ω ∈ Q
    · have h1 : ω ∈ stayUpTo Q B z t n (m + 1) := fun j hj ↦ by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h j hj
        · exact hm
      have h2 : ω ∉ exitAt Q B z t n m := fun h' ↦ h'.2 hm
      rw [Set.indicator_of_mem (show ω ∈ stayUpTo Q B z t n m from h),
        Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
      simp
    · have h1 : ω ∉ stayUpTo Q B z t n (m + 1) := fun h' ↦ hm (h' m (Nat.lt_succ_self m))
      have h2 : ω ∈ exitAt Q B z t n m := ⟨h, hm⟩
      rw [Set.indicator_of_mem (show ω ∈ stayUpTo Q B z t n m from h),
        Set.indicator_of_notMem h1, Set.indicator_of_mem h2]
      simp
  · have h0 : ω ∉ stayUpTo Q B z t n m := h
    have h1 : ω ∉ stayUpTo Q B z t n (m + 1) := fun h' ↦ h fun j hj ↦ h' j (by omega)
    have h2 : ω ∉ exitAt Q B z t n m := fun h' ↦ h h'.1
    rw [Set.indicator_of_notMem h0, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    simp

/-- The grid-exit event as a set of coordinate vectors. -/
def exitSet (Q : Set ℂ) (z : ℂ) (m : ℕ) : Set (Bool × ℕ → ℝ) :=
  (⋂ j : ℕ, ⋂ (_ : j < m), {y | z + toC (fun b ↦ y (b, j)) ∈ Q}) ∩
    {y | z + toC (fun b ↦ y (b, m)) ∈ Q}ᶜ

lemma measurable_toC_slice (j : ℕ) :
    Measurable fun y : Bool × ℕ → ℝ ↦ toC (fun b ↦ y (b, j)) :=
  measurable_toC.comp (measurable_pi_iff.mpr fun _ ↦ measurable_pi_apply _)

lemma measurableSet_exitSet {Q : Set ℂ} (hQ : MeasurableSet Q) (z : ℂ) (m : ℕ) :
    MeasurableSet (exitSet Q z m) := by
  refine MeasurableSet.inter (MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦ ?_) ?_
  · exact (measurable_const.add (measurable_toC_slice j)) hQ
  · exact ((measurable_const.add (measurable_toC_slice m)) hQ).compl

lemma indicator_exitSet_pastVec (Q : Set ℂ) (z : ℂ) (t : ℝ≥0) (n m : ℕ) (ω : Ω) :
    (exitSet Q z m).indicator (1 : (Bool × ℕ → ℝ) → ℝ)
        (pastVec B (fun j ↦ gridT t n (min j m)) ω) =
      (exitAt Q B z t n m).indicator 1 ω := by
  have hc : ∀ j, toC (fun b ↦ pastVec B (fun j ↦ gridT t n (min j m)) ω (b, j)) =
      B (gridT t n (min j m)) ω := fun j ↦ toC_coordProc B _ ω
  have hiff : pastVec B (fun j ↦ gridT t n (min j m)) ω ∈ exitSet Q z m ↔
      ω ∈ exitAt Q B z t n m := by
    simp only [exitSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_compl_iff,
      hc, exitAt]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun j hj ↦ by simpa [min_eq_left hj.le] using h1 j hj, by simpa using h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun j hj ↦ by simpa [min_eq_left hj.le] using h1 j hj, by simpa using h2⟩
  by_cases h : ω ∈ exitAt Q B z t n m
  · simp [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mpr h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' ↦ h (hiff.mp h'))]

lemma abs_indicator_one_le {α : Type*} (S : Set α) (x : α) : |S.indicator (1 : α → ℝ) x| ≤ 1 := by
  by_cases h : x ∈ S
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- The Markov step on the grid-exit event `E_m`. -/
lemma integral_exitAt_sqMode (hB : IsPlanarBM B P) {Q : Set ℂ} (hQ : MeasurableSet Q)
    (a L : ℝ) (p : ℕ × ℕ) (z : ℂ) {t : ℝ≥0} {n m : ℕ} (hm : m ≤ 2 ^ n) :
    ∫ ω, (exitAt Q B z t n m).indicator 1 ω * sqMode a L p (z + B t ω) ∂P =
      sqDecay L ((t - gridT t n m : ℝ≥0) : ℝ) p *
        ∫ ω, (exitAt Q B z t n m).indicator 1 ω * sqMode a L p (z + B (gridT t n m) ω) ∂P := by
  have h := integral_mul_sqMode_eq hB (r := fun j ↦ gridT t n (min j m))
    (s := gridT t n m) (fun j ↦ gridT_mono (min_le_right j m)) (i0 := m) (by simp)
    (gridT_le hm) a L p z ((measurable_one.indicator (measurableSet_exitSet hQ z m)))
    (fun y ↦ abs_indicator_one_le _ y)
  simp only [indicator_exitSet_pastVec] at h
  exact h

lemma ae_zero (hB : IsPlanarBM B P) : ∀ᵐ ω ∂P, B 0 ω = 0 := by
  have := hB.gauss.isProbabilityMeasure
  have hc : ∀ b : Bool, ∀ᵐ ω ∂P, coordProc B (b, 0) ω = 0 := by
    intro b
    have hL := hasLaw_coordProc hB b 0
    have hd : P.map (coordProc B (b, 0)) = Measure.dirac 0 := by
      rw [hL.map_eq]
      simpa using gaussianReal_zero_var (0 : ℝ)
    have : ∀ᵐ x ∂(P.map (coordProc B (b, 0))), x = 0 := by
      rw [hd]
      exact (ae_dirac_iff (measurableSet_singleton (0 : ℝ))).mpr rfl
    exact ae_of_ae_map hL.aemeasurable this
  filter_upwards [hc false, hc true] with ω h1 h2
  rw [← toC_coordProc B 0 ω]
  simp [toC, h1, h2]

/-- `E[φ_p(z + B_t)] = e^{−λ_p t/2} φ_p(z)`. -/
lemma integral_sqMode_free (hB : IsPlanarBM B P) (a L : ℝ) (p : ℕ × ℕ) (z : ℂ) (t : ℝ≥0) :
    ∫ ω, sqMode a L p (z + B t ω) ∂P = sqDecay L t p * sqMode a L p z := by
  have := hB.gauss.isProbabilityMeasure
  have h := integral_mul_sqMode_eq hB (r := fun _ : Unit ↦ (0 : ℝ≥0)) (s := 0) (t := t)
    (fun _ ↦ le_rfl) (i0 := ()) rfl (zero_le (a := t)) a L p z (measurable_const (a := (1 : ℝ)))
    (C := 1) (fun _ ↦ by simp)
  simp only [one_mul, tsub_zero] at h
  rw [h]
  congr 1
  rw [integral_congr_ae (g := fun _ ↦ sqMode a L p z)]
  · simp
  · filter_upwards [ae_zero hB] with ω hω
    simp [hω]

lemma indicator_stayUpTo_eq (Q : Set ℂ) (z : ℂ) (t : ℝ≥0) (n M : ℕ) (ω : Ω) :
    (stayUpTo Q B z t n M).indicator (1 : Ω → ℝ) ω =
      1 - ∑ m ∈ Finset.range M, (exitAt Q B z t n m).indicator 1 ω := by
  induction M with
  | zero =>
    have h0 : ω ∈ stayUpTo Q B z t n 0 := fun j hj ↦ absurd hj (Nat.not_lt_zero j)
    simp [Set.indicator_of_mem h0]
  | succ M ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ← ih, indicator_stayUpTo_succ Q z t n M ω]
    ring

lemma aemeasurable_B (hB : IsPlanarBM B P) (t : ℝ≥0) : AEMeasurable (B t) P := by
  have h : AEMeasurable (fun ω (b : Bool) ↦ coordProc B (b, t) ω) P :=
    AEMeasurable.of_eval fun _ ↦ hB.gauss.aemeasurable _
  have e : B t = toC ∘ fun ω (b : Bool) ↦ coordProc B (b, t) ω :=
    funext fun ω ↦ (toC_coordProc B t ω).symm
  rw [e]
  exact measurable_toC.comp_aemeasurable h

lemma integrable_exitAt_mul (hB : IsPlanarBM B P) {Q : Set ℂ} (hQ : MeasurableSet Q)
    (a L : ℝ) (p : ℕ × ℕ) (z : ℂ) (t s : ℝ≥0) (n m : ℕ) :
    Integrable (fun ω ↦ (exitAt Q B z t n m).indicator (1 : Ω → ℝ) ω *
      sqMode a L p (z + B s ω)) P := by
  have := hB.gauss.isProbabilityMeasure
  have e : (fun ω ↦ (exitAt Q B z t n m).indicator (1 : Ω → ℝ) ω) =
      (exitSet Q z m).indicator 1 ∘ pastVec B (fun j ↦ gridT t n (min j m)) :=
    funext fun ω ↦ (indicator_exitSet_pastVec Q z t n m ω).symm
  have hm : AEMeasurable (fun ω ↦ (exitAt Q B z t n m).indicator (1 : Ω → ℝ) ω) P := by
    rw [e]
    exact (measurable_one.indicator (measurableSet_exitSet hQ z m)).comp_aemeasurable
      (aemeasurable_pastVec hB _)
  have hφ : AEMeasurable (fun ω ↦ sqMode a L p (z + B s ω)) P :=
    (continuous_sqMode a L p).measurable.comp_aemeasurable
      (aemeasurable_const.add (aemeasurable_B hB s))
  refine (integrable_const (1 : ℝ)).mono' (hm.mul hφ).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_eq_abs]
  exact abs_G_trig_le (abs_indicator_one_le _ ω) (abs_sinMode_le _ _ _ _) (abs_sinMode_le _ _ _ _)

/-- **Discrete optional stopping** at the first grid exit time. -/
theorem integral_stayUpTo_sqMode (hB : IsPlanarBM B P) {Q : Set ℂ} (hQ : MeasurableSet Q)
    (a L : ℝ) (p : ℕ × ℕ) (z : ℂ) (t : ℝ≥0) (n : ℕ) {M : ℕ} (hM : M ≤ 2 ^ n + 1) :
    ∫ ω, (stayUpTo Q B z t n M).indicator 1 ω * sqMode a L p (z + B t ω) ∂P =
      sqDecay L t p * sqMode a L p z - ∑ m ∈ Finset.range M,
        sqDecay L ((t - gridT t n m : ℝ≥0) : ℝ) p *
          ∫ ω, (exitAt Q B z t n m).indicator 1 ω * sqMode a L p (z + B (gridT t n m) ω) ∂P := by
  have := hB.gauss.isProbabilityMeasure
  have e : (fun ω ↦ (stayUpTo Q B z t n M).indicator (1 : Ω → ℝ) ω * sqMode a L p (z + B t ω)) =
      fun ω ↦ sqMode a L p (z + B t ω) - ∑ m ∈ Finset.range M,
        (exitAt Q B z t n m).indicator (1 : Ω → ℝ) ω * sqMode a L p (z + B t ω) := by
    funext ω
    rw [indicator_stayUpTo_eq, sub_mul, one_mul, Finset.sum_mul]
  have hφ : Integrable (fun ω ↦ sqMode a L p (z + B t ω)) P := by
    refine (integrable_const (1 : ℝ)).mono' ((continuous_sqMode a L p).measurable.comp_aemeasurable
      (aemeasurable_const.add (aemeasurable_B hB t))).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs]
    exact abs_sqMode_le a L p _
  rw [e, integral_sub hφ (integrable_finsetSum _ fun m _ ↦
      integrable_exitAt_mul hB hQ a L p z t t n m),
    integral_finsetSum _ fun m _ ↦ integrable_exitAt_mul hB hQ a L p z t t n m,
    integral_sqMode_free hB a L p z t]
  congr 1
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  exact integral_exitAt_sqMode hB hQ a L p z (by simp at hm; omega)

end KilledHeatSq
end LQGMetric
