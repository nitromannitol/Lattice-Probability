/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatDens at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatGauss

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
(task P2-KILLED, decision D-KHK1)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 404–411, eq. (eq:heat_kernel)) define
`p_A(s; z, ·)` as the density of `B ↦ P^z(B_s ∈ B, τ_A > s)`. With our bridge definition this is a
theorem (`lintegral_killedHeat_eq`): for open `A`, `t > 0`, measurable `E` and any planar Brownian
motion `B`,
`∫_E p_A(t; z, w) dw = P(z + B_t ∈ E, z + B_s ∈ A for all s ≤ t)`.

Proof (the standard bridge decomposition, e.g. Mörters–Peres, *Brownian Motion*, §1.1, Brownian
bridge, Exercise 1.4 / Revuz–Yor I.3): `B_s = (s/t)B_t + β_s` with `β = B − (s/t)B_t`
independent of `B_t` (jointly Gaussian and uncorrelated: mathlib
`IsGaussianProcess.indepFun_of_covariance_eq_zero`), so conditioning on `B_t = w − z` gives
`P(bridge from z to w stays in A) = q_A(t; z, w)` and `B_t` has density `p_t(0, ·)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace KilledHeat

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The complex number with real part `v false` and imaginary part `v true`. -/
def toC (v : Bool → ℝ) : ℂ := (v false : ℂ) + (v true : ℂ) * Complex.I

lemma measurable_toC : Measurable toC := by unfold toC; fun_prop

lemma toC_coordProc (B : ℝ≥0 → Ω → ℂ) (t : ℝ≥0) (ω : Ω) :
    toC (fun b ↦ coordProc B (b, t) ω) = B t ω := by
  simp [toC, coordProc, Complex.re_add_im]

section
variable {B : ℝ≥0 → Ω → ℂ} {P : Measure Ω}

/-- The endpoint coordinates and the sampled bridge are jointly Gaussian. -/
lemma isGaussianProcess_end_bridge (hB : IsPlanarBM B P) (t : ℝ≥0) :
    IsGaussianProcess (Sum.elim (fun b : Bool ↦ coordProc B (b, t))
      (sampled t (bridgeOf t B))) P := by
  classical
  refine hB.gauss.of_isGaussianProcess fun i ↦ ?_
  rcases i with b | p
  · exact ⟨{(b, t)}, ContinuousLinearMap.proj ⟨(b, t), by simp⟩, fun ω ↦ rfl⟩
  · refine ⟨{(p.1, clampT t p.2), (p.1, t)}, (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : ({(p.1, clampT t p.2), (p.1, t)} : Finset (Bool × ℝ≥0)) ↦ ℝ)
      ⟨(p.1, clampT t p.2), by simp⟩) - (((clampT t p.2 : ℝ≥0) : ℝ) / t) •
      (ContinuousLinearMap.proj ⟨(p.1, t), by simp⟩), fun ω ↦ ?_⟩
    simp only [Sum.elim_inr, sampled]
    rw [coordProc_bridgeOf]
    simp

lemma cov_end_bridge (hB : IsPlanarBM B P) (t : ℝ≥0) (b : Bool) (p : Bool × ℚ) :
    cov[coordProc B (b, t), sampled t (bridgeOf t B) p; P] = 0 := by
  have := hB.gauss.isProbabilityMeasure
  have hL2 : ∀ p, MemLp (coordProc B p) 2 P := fun p ↦ (hB.gauss.hasGaussianLaw_eval p).memLp_two
  have hs : clampT t p.2 ≤ t := clampT_le t p.2
  show cov[coordProc B (b, t), coordProc (bridgeOf t B) (p.1, clampT t p.2); P] = 0
  rw [coordProc_bridgeOf, covariance_fun_sub_right (hL2 _) (hL2 _) ((hL2 _).const_mul _),
    covariance_const_mul_right, hB.cov, hB.cov]
  split_ifs
  · rw [min_eq_right hs, min_self]
    rcases eq_or_ne t 0 with ht | ht
    · subst ht
      simp [le_antisymm hs zero_le]
    · have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
      field_simp
      ring
  · ring

lemma indepFun_end_bridge (hB : IsPlanarBM B P) (t : ℝ≥0) :
    IndepFun (fun ω ↦ B t ω) (fun ω p ↦ sampled t (bridgeOf t B) p ω) P := by
  have hG := isGaussianProcess_end_bridge hB t
  have h := hG.indepFun_of_covariance_eq_zero (fun b ↦ hG.aemeasurable (Sum.inl b))
    (fun p ↦ hG.aemeasurable (Sum.inr p))
    (fun b p ↦ cov_end_bridge hB t b p)
  have e1 : (fun ω ↦ B t ω) = toC ∘ (fun ω s ↦ coordProc B (s, t) ω) :=
    funext fun ω ↦ (toC_coordProc B t ω).symm
  rw [e1]
  exact h.comp measurable_toC measurable_id

lemma hasLaw_coordProc (hB : IsPlanarBM B P) (b : Bool) (t : ℝ≥0) :
    HasLaw (coordProc B (b, t)) (gaussianReal 0 t) P := by
  have hG := hB.gauss.hasGaussianLaw_eval (b, t)
  refine ⟨hB.gauss.aemeasurable _, ?_⟩
  rw [hG.map_eq_gaussianReal, hB.mean, ← covariance_self (hB.gauss.aemeasurable _), hB.cov]
  simp

/-- `B_t` has density `p_t(0, ·)`. -/
theorem map_eq_withDensity_of_isPlanarBM (hB : IsPlanarBM B P) {t : ℝ≥0} (ht : t ≠ 0) :
    P.map (B t) = volume.withDensity (fun y ↦ ENNReal.ofReal (heatKernel t 0 y)) := by
  have := hB.gauss.isProbabilityMeasure
  have hG : IsGaussianProcess (Sum.elim (fun _ : Unit ↦ coordProc B (false, t))
      (fun _ : Unit ↦ coordProc B (true, t))) P := by
    have e : Sum.elim (fun _ : Unit ↦ coordProc B (false, t))
        (fun _ : Unit ↦ coordProc B (true, t)) =
        coordProc B ∘ Sum.elim (fun _ : Unit ↦ (false, t)) (fun _ : Unit ↦ (true, t)) := by
      funext i
      rcases i with _ | _ <;> rfl
    rw [e]
    exact hB.gauss.comp_right _
  have h := hG.indepFun_of_covariance_eq_zero (fun _ ↦ hB.gauss.aemeasurable _)
    (fun _ ↦ hB.gauss.aemeasurable _) (fun _ _ ↦ by rw [hB.cov]; simp)
  exact map_eq_withDensity_heatKernel ht (hasLaw_coordProc hB false t)
    (hasLaw_coordProc hB true t) (h.comp (measurable_pi_apply ()) (measurable_pi_apply ()))

/-- The joint event `{z + x ∈ E, sampled bridge from z to z + x stays in A}`. -/
def gSet (A : Set ℂ) (t : ℝ≥0) (z : ℂ) (E : Set ℂ) : Set (ℂ × (Bool × ℚ → ℝ)) :=
  {p | z + p.1 ∈ E ∧ p.2 ∈ cEvent A t z (z + p.1)}

lemma measurableSet_gSet (A : Set ℂ) (t : ℝ≥0) (z : ℂ) {E : Set ℂ} (hE : MeasurableSet E) :
    MeasurableSet (gSet A t z E) := by
  have h1 : MeasurableSet {p : ℂ × (Bool × ℚ → ℝ) | z + p.1 ∈ E} :=
    (measurable_const.add measurable_fst) hE
  have h2 : MeasurableSet {p : ℂ × (Bool × ℚ → ℝ) | p.2 ∈ cEvent A t z (z + p.1)} := by
    have : {p : ℂ × (Bool × ℚ → ℝ) | p.2 ∈ cEvent A t z (z + p.1)} = ⋃ n : ℕ, ⋂ q : ℚ,
        {p | z + ((((clampT t q : ℝ≥0) : ℝ) / t : ℝ) : ℂ) * (z + p.1 - z) + cpt p.2 q ∈
          innerSet A n} := by
      ext p
      simp [cEvent]
    rw [this]
    refine MeasurableSet.iUnion fun n ↦ MeasurableSet.iInter fun q ↦ ?_
    have hm : Measurable fun p : ℂ × (Bool × ℚ → ℝ) ↦
        z + ((((clampT t q : ℝ≥0) : ℝ) / t : ℝ) : ℂ) * (z + p.1 - z) + cpt p.2 q := by
      unfold cpt
      fun_prop
    exact hm (isClosed_innerSet A n).measurableSet
  exact h1.inter h2

lemma heatKernel_add_left (t : ℝ) (z x : ℂ) : heatKernel t z (z + x) = heatKernel t 0 x := by
  unfold heatKernel
  rw [show z - (z + x) = 0 - x by ring]

/-- **DZZ's definition (eq:heat_kernel) as a theorem**: `p_A(t; z, ·)` is the density of
`E ↦ P^z(B_t ∈ E, τ_A > t)` (`LBM_LGDarXiv.tex` l. 404–411), for every planar Brownian motion. -/
theorem lintegral_killedHeat_eq {A : Set ℂ} (hA : IsOpen A) {t : ℝ≥0} (ht : t ≠ 0)
    (hB : IsPlanarBM B P) (z : ℂ) {E : Set ℂ} (hE : MeasurableSet E) :
    ∫⁻ w in E, ENNReal.ofReal (killedHeat A t z w) =
      P {ω | z + B t ω ∈ E ∧ ∀ s : ℝ≥0, s ≤ t → z + B s ω ∈ A} := by
  have := hB.gauss.isProbabilityMeasure
  have hβ : IsPlanarBridge t (bridgeOf t B) P := hB.isPlanarBridge t ht
  let Y : Ω → (Bool × ℚ → ℝ) := fun ω p ↦ sampled t (bridgeOf t B) p ω
  have hYm : AEMeasurable Y P := .of_eval fun p ↦ (sampled_isGaussianProcess hβ).aemeasurable p
  have hXm : AEMeasurable (B t) P := by
    have e : B t = toC ∘ (fun ω b ↦ coordProc B (b, t) ω) :=
      funext fun ω ↦ (toC_coordProc B t ω).symm
    rw [e]
    exact measurable_toC.comp_aemeasurable (.of_eval fun b ↦ hB.gauss.aemeasurable _)
  have h1 : P {ω | z + B t ω ∈ E ∧ ∀ s : ℝ≥0, s ≤ t → z + B s ω ∈ A} =
      P {ω | (B t ω, Y ω) ∈ gSet A t z E} := by
    refine measure_congr ?_
    filter_upwards [hβ.cont] with ω hω
    have key := mem_bridgeEvent_iff A hA t z (z + B t ω) (bridgeOf t B) hω
    have hpath : ∀ s : ℝ≥0, bridgePath t z (z + B t ω) (bridgeOf t B) s ω = z + B s ω := by
      intro s
      simp only [bridgePath, bridgeOf]
      ring
    simp only [bridgeEvent, hpath, Set.mem_ofPred_eq] at key
    apply propext
    simp only [gSet, Set.mem_ofPred_eq]
    rw [key]
  have hden : Measurable fun x : ℂ ↦ ENNReal.ofReal (heatKernel t 0 x) :=
    (Continuous.measurable (by unfold heatKernel; fun_prop)).ennreal_ofReal
  rw [h1, measure_pair_mem_eq_lintegral hXm hYm (indepFun_end_bridge hB t)
    (measurableSet_gSet A t z hE), map_eq_withDensity_of_isPlanarBM hB ht,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hden
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
    ← lintegral_indicator hE,
    ← lintegral_add_left_eq_self (E.indicator fun w ↦ ENNReal.ofReal (killedHeat A t z w)) z]
  refine lintegral_congr fun x ↦ ?_
  have hq : P.map Y (cEvent A t z (z + x)) = ENNReal.ofReal (bridgeStay A t z (z + x)) := by
    rw [← measure_bridgeEvent_eq_map hβ hA, ← bridgeStay_eq_of_isPlanarBridge hA ht hβ,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp only [Pi.mul_apply, Set.indicator]
  by_cases hx : z + x ∈ E
  · have hsec : Prod.mk x ⁻¹' gSet A t z E = cEvent A t z (z + x) := by
      ext g
      simp [gSet, hx]
    simp only [hx, ↓reduceIte]
    rw [hsec, hq, killedHeat, ENNReal.ofReal_mul (heatKernel_nonneg' _ _ _),
      heatKernel_add_left]
  · have hsec : Prod.mk x ⁻¹' gSet A t z E = ∅ := by
      ext g
      simp [gSet, hx]
    simp only [hx, ↓reduceIte]
    rw [hsec, measure_empty, mul_zero]

end

end KilledHeat
end LQGMetric
