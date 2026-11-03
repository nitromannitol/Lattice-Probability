/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.RegularClosure at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleDefs
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleFubini
import LatticeProb.Bonanno.QuantumZipper.Zipper.Maps
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Closure properties of regular samples (blueprint node M4-R4)

Deterministic facts about `IsRegularSample` (`RegularSampleDefs`):

* consequence: `evalReg x (foldedCircle v s) = F (foldH v, s)` for **every** circle;
* regularity is preserved by `addConst`, by adding `ofFun φ` for `φ` continuous on `Hbar`
  or `φ = α (−log|· − s|)` with `s ∈ ℝ`, by real translations, by the reflection `z ↦ −z̄`,
  and by `rescale x Q b` (`b > 0`);
* `rescale (rescale x Q b) Q c` and `rescale x Q (b c)` satisfy `RegEq`.

The first section collects the circle-integral tools (angle formula, continuity in the
parameters, Lipschitz bounds), which are also used by the proof of M4-R3.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Real Topology ComplexConjugate

namespace QuantumZipper
namespace RegClosure

open CircleFubini
open Metric (closedBall mem_closedBall)

/-! ## 1. Folded circles: support, angle formula, symmetries -/

theorem fc_ae_mem_Hbar (w : ℂ) (r : ℝ) : ∀ᵐ u ∂foldedCircle w r, u ∈ Hbar := by
  rw [foldedCircle]
  exact (ae_map_iff measurable_foldH.aemeasurable (p := fun u => u ∈ Hbar)
    isClosed_Hbar.measurableSet).2 (ae_of_all _ fun u => foldH_mem_Hbar' u)

theorem continuous_comp_foldH {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) :
    Continuous (fun u => g (foldH u)) :=
  hg.comp_continuous continuous_foldH' foldH_mem_Hbar'

/-- Angle formula for folded-circle integrals of functions continuous on `Hbar`. -/
theorem integral_fc_eq {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) (w : ℂ) (r : ℝ) :
    ∫ u, g u ∂foldedCircle w r =
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, g (foldH (circleMap w r θ)) := by
  have hc := continuous_comp_foldH hg
  have h1 : ∫ u, g u ∂foldedCircle w r = ∫ u, g (foldH u) ∂foldedCircle w r :=
    integral_congr_ae ((fc_ae_mem_Hbar w r).mono fun u hu => by simp only [foldH_of_mem' hu])
  rw [h1, foldedCircle, integral_map measurable_foldH.aemeasurable hc.aestronglyMeasurable]
  simp only [foldH_of_mem' (foldH_mem_Hbar' _)]
  rw [circleUnif, integral_smul_measure,
    integral_map (measurable_circleMap w r).aemeasurable hc.aestronglyMeasurable,
    intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo,
    ← integral_Ico_eq_integral_Ioo, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul]

theorem integrable_fc {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) (w : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    Integrable g (foldedCircle w r) := by
  have h := (hg.mono inter_subset_right).integrableOn_compact (μ := foldedCircle w r)
    (isCompact_ballH (‖w‖ + r))
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
    (ae_iff.2 (foldedCircle_support hr (le_refl _)))] at h

theorem intervalIntegrable_fc {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) (w : ℂ) (r : ℝ) :
    IntervalIntegrable (fun θ => g (foldH (circleMap w r θ))) volume 0 (2 * π) :=
  ((continuous_comp_foldH hg).comp (continuous_circleMap w r)).intervalIntegrable _ _

/-- Uniform comparison of two folded-circle integrals through the angle parametrization. -/
theorem abs_integral_fc_sub_le {g g' : ℂ → ℝ} (hg : ContinuousOn g Hbar)
    (hg' : ContinuousOn g' Hbar) {w w' : ℂ} {r r' C : ℝ}
    (h : ∀ θ, |g (foldH (circleMap w r θ)) - g' (foldH (circleMap w' r' θ))| ≤ C) :
    |∫ u, g u ∂foldedCircle w r - ∫ u, g' u ∂foldedCircle w' r'| ≤ C := by
  rw [integral_fc_eq hg, integral_fc_eq hg', ← mul_sub,
    ← intervalIntegral.integral_sub (intervalIntegrable_fc hg w r) (intervalIntegrable_fc hg' w' r')]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 2 * π) (C := C)
    (f := fun θ => g (foldH (circleMap w r θ)) - g' (foldH (circleMap w' r' θ)))
    (fun θ _ => by rw [Real.norm_eq_abs]; exact h θ)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos (show (0 : ℝ) < 2 * π by positivity)] at hb
  rw [abs_mul, abs_of_pos (by positivity)]
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π,
        (g (foldH (circleMap w r θ)) - g' (foldH (circleMap w' r' θ)))|
      ≤ (2 * π)⁻¹ * (C * (2 * π)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C := by field_simp

theorem integral_fc_const_add {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) (w : ℂ) {r : ℝ}
    (hr : 0 ≤ r) (c : ℝ) : ∫ u, (g u + c) ∂foldedCircle w r = ∫ u, g u ∂foldedCircle w r + c := by
  rw [integral_add (integrable_fc hg w hr) (integrable_const c), integral_const, smul_eq_mul,
    probReal_univ, one_mul]

theorem foldH_conj (u : ℂ) : foldH (conj u) = foldH u := by
  rw [foldH_eq_mk, foldH_eq_mk]; simp

theorem foldH_add_real (u : ℂ) (t : ℝ) : foldH (u + t) = foldH u + t := by
  rw [foldH_eq_mk, foldH_eq_mk]
  apply Complex.ext <;> simp

theorem foldH_mul_pos (u : ℂ) {b : ℝ} (hb : 0 < b) : foldH ((b : ℂ) * u) = (b : ℂ) * foldH u := by
  rw [foldH_eq_mk, foldH_eq_mk]
  apply Complex.ext <;> simp [abs_mul, abs_of_pos hb]

theorem foldH_neg_conj (u : ℂ) : foldH (-conj u) = -conj (foldH u) := by
  rw [foldH_eq_mk, foldH_eq_mk]
  apply Complex.ext <;> simp

theorem circleMap_conj (c : ℂ) (R θ : ℝ) :
    conj (circleMap c R θ) = circleMap (conj c) R (-θ) := by
  simp only [circleMap, map_add, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I]
  congr 2; push_cast; ring

theorem circleMap_add_real (c : ℂ) (t R θ : ℝ) :
    circleMap c R θ + t = circleMap (c + t) R θ := by
  simp only [circleMap]; ring

theorem circleMap_mul_pos (c : ℂ) (b R θ : ℝ) :
    (b : ℂ) * circleMap c R θ = circleMap ((b : ℂ) * c) (b * R) θ := by
  simp only [circleMap]; push_cast; ring

theorem neg_conj_circleMap (c : ℂ) (R θ : ℝ) :
    -conj (circleMap c R θ) = circleMap (-conj c) R (π - θ) := by
  rw [circleMap_conj]
  simp only [circleMap]
  rw [show ((π - θ : ℝ) : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I + (π : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- Folding the centre does not change folded-circle integrals. -/
theorem integral_fc_foldH {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) (v : ℂ) (s : ℝ) :
    ∫ u, g u ∂foldedCircle (foldH v) s = ∫ u, g u ∂foldedCircle v s := by
  by_cases hv : v ∈ Hbar
  · rw [foldH_of_mem' hv]
  have hfv : foldH v = conj v := by simp only [foldH]; exact if_neg hv
  rw [hfv, integral_fc_eq hg, integral_fc_eq hg]
  congr 1
  set f : ℝ → ℝ := fun θ => g (foldH (circleMap v s θ)) with hf
  have hper : Function.Periodic f (2 * π) := fun θ => by
    simp only [hf, periodic_circleMap v s θ]
  have e : ∀ θ, g (foldH (circleMap (conj v) s θ)) = f (-θ) := fun θ => by
    simp only [hf]
    rw [← foldH_conj (circleMap v s (-θ)), circleMap_conj, neg_neg]
  simp_rw [e]
  rw [intervalIntegral.integral_comp_neg, neg_zero]
  have := hper.intervalIntegral_add_eq (-(2 * π)) 0
  rwa [neg_add_cancel, zero_add] at this

/-- Real translations of folded circles. -/
theorem integral_fc_comp_add_real {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) (w : ℂ) (r t : ℝ) :
    ∫ u, g (u + t) ∂foldedCircle w r = ∫ u, g u ∂foldedCircle (w + t) r := by
  have hg' : ContinuousOn (fun u => g (u + t)) Hbar :=
    hg.comp (continuous_id.add continuous_const).continuousOn fun u (hu : 0 ≤ u.im) =>
      show 0 ≤ (u + t).im by simpa using hu
  rw [integral_fc_eq hg', integral_fc_eq hg]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [← foldH_add_real, circleMap_add_real]

/-- Dilations of folded circles. -/
theorem integral_fc_comp_mul {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) (w : ℂ) (r : ℝ) {b : ℝ}
    (hb : 0 < b) :
    ∫ u, g ((b : ℂ) * u) ∂foldedCircle w r = ∫ u, g u ∂foldedCircle ((b : ℂ) * w) (b * r) := by
  have hg' : ContinuousOn (fun u => g ((b : ℂ) * u)) Hbar :=
    hg.comp (continuous_const.mul continuous_id).continuousOn fun u (hu : 0 ≤ u.im) =>
      show 0 ≤ ((b : ℂ) * u).im by simpa using mul_nonneg hb.le hu
  rw [integral_fc_eq hg', integral_fc_eq hg]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [← foldH_mul_pos _ hb, circleMap_mul_pos]

/-- The reflection `z ↦ −z̄` of folded circles. -/
theorem integral_fc_comp_neg_conj {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) (w : ℂ) (r : ℝ) :
    ∫ u, g (-conj u) ∂foldedCircle w r = ∫ u, g u ∂foldedCircle (-conj w) r := by
  have hg' : ContinuousOn (fun u => g (-conj u)) Hbar :=
    hg.comp (Complex.continuous_conj.neg).continuousOn fun u (hu : 0 ≤ u.im) =>
      show 0 ≤ (-conj u).im by simpa using hu
  rw [integral_fc_eq hg', integral_fc_eq hg]
  congr 1
  set f : ℝ → ℝ := fun θ => g (foldH (circleMap (-conj w) r θ)) with hf
  have hper : Function.Periodic f (2 * π) := fun θ => by
    simp only [hf, periodic_circleMap (-conj w) r θ]
  have e : ∀ θ, g (-conj (foldH (circleMap w r θ))) = f (π - θ) := fun θ => by
    simp only [hf]
    rw [← foldH_neg_conj, neg_conj_circleMap]
  simp_rw [e]
  rw [intervalIntegral.integral_comp_sub_left, sub_zero]
  have := hper.intervalIntegral_add_eq (π - 2 * π) 0
  rwa [sub_add_cancel, zero_add] at this

/-! ## 2. Continuity in the parameters -/

/-- Parametric continuity of folded-circle integrals. -/
theorem continuousOn_integral_fc {P : Type*} [TopologicalSpace P] {S : Set P}
    {H : P → ℂ → ℝ} (hH : ContinuousOn (fun q : P × ℂ => H q.1 q.2) (S ×ˢ Hbar))
    {c : P → ℂ} {r : P → ℝ} (hc : ContinuousOn c S) (hr : ContinuousOn r S) :
    ContinuousOn (fun p => ∫ u, H p u ∂foldedCircle (c p) (r p)) S := by
  have hHp : ∀ p ∈ S, ContinuousOn (H p) Hbar := fun p hp =>
    hH.comp (continuousOn_const.prodMk continuousOn_id) fun u hu => ⟨hp, hu⟩
  have e : EqOn (fun p => ∫ u, H p u ∂foldedCircle (c p) (r p))
      (fun p => (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, H p (foldH (circleMap (c p) (r p) θ))) S :=
    fun p hp => integral_fc_eq (hHp p hp) _ _
  refine ContinuousOn.congr ?_ e
  refine continuousOn_const.mul ?_
  rw [continuousOn_iff_continuous_restrict] at hc hr ⊢
  have hcm : Continuous fun q : S × ℝ => circleMap (c q.1) (r q.1) q.2 := by
    simp only [circleMap]
    exact (hc.comp continuous_fst).add (((Complex.continuous_ofReal.comp (hr.comp
      continuous_fst))).mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)))
  have hcont : Continuous fun q : S × ℝ => H q.1 (foldH (circleMap (c q.1) (r q.1) q.2)) := by
    refine hH.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_foldH'.comp hcm)) fun q => ⟨q.1.2, foldH_mem_Hbar' _⟩
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (p : S) θ => H p (foldH (circleMap (c p) (r p) θ))) hcont 0 (2 * π)

/-! ## 3. Locally uniform convergence helpers -/

section TLUO

variable {ι κ α : Type*} [TopologicalSpace α] {p : Filter ι} {s : Set α}
  {F G : ι → α → ℝ} {f g : α → ℝ}

theorem tluo_of_dist_le (h : TendstoLocallyUniformlyOn F f p s)
    (hle : ∀ᶠ n in p, ∀ y ∈ s, dist (g y) (G n y) ≤ dist (f y) (F n y)) :
    TendstoLocallyUniformlyOn G g p s := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at h ⊢
  intro ε hε x hx
  obtain ⟨t, ht, H⟩ := h ε hε x hx
  exact ⟨t ∩ s, inter_mem ht self_mem_nhdsWithin,
    (H.and hle).mono fun n hn y hy => (hn.2 y hy.2).trans_lt (hn.1 y hy.1)⟩

theorem tluo_add (hF : TendstoLocallyUniformlyOn F f p s)
    (hG : TendstoLocallyUniformlyOn G g p s) :
    TendstoLocallyUniformlyOn (fun n y => F n y + G n y) (fun y => f y + g y) p s := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hF hG ⊢
  intro ε hε x hx
  obtain ⟨t, ht, H⟩ := hF (ε / 2) (by positivity) x hx
  obtain ⟨t', ht', H'⟩ := hG (ε / 2) (by positivity) x hx
  refine ⟨t ∩ t', inter_mem ht ht', (H.and H').mono fun n hn y hy => ?_⟩
  calc dist (f y + g y) (F n y + G n y) ≤ dist (f y) (F n y) + dist (g y) (G n y) :=
        dist_add_add_le _ _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hn.1 y hy.1) (hn.2 y hy.2)
    _ = ε := add_halves ε

theorem tluo_add_const (hF : TendstoLocallyUniformlyOn F f p s) (c : ℝ) :
    TendstoLocallyUniformlyOn (fun n y => F n y + c) (fun y => f y + c) p s :=
  tluo_of_dist_le hF (Eventually.of_forall fun n y _ => by rw [dist_add_right])

theorem tluo_comp_tendsto (h : TendstoLocallyUniformlyOn F f p s) {φ : κ → ι} {q : Filter κ}
    (hφ : Tendsto φ q p) : TendstoLocallyUniformlyOn (fun n => F (φ n)) f q s :=
  fun u hu x hx => let ⟨t, ht, H⟩ := h u hu x hx; ⟨t, ht, hφ.eventually H⟩

end TLUO

/-! ## 4. First consequences of regularity -/

variable {x : FieldSample} {F : ℂ × ℝ → ℝ}

theorem tendsto_radius_nhdsGT : Tendsto radius atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
    Eventually.of_forall radius_pos⟩

theorem tendsto_dyadicRoundC (z : ℂ) : Tendsto (fun n => dyadicRoundC n z) atTop (𝓝 z) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => CircleCont.norm_dyadicRoundC_sub_le n z) ?_
  have : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa [one_div, inv_pow] using this.const_mul 2

theorem continuousOn_slice (hc : ContinuousOn F (Hbar ×ˢ Ioi 0)) {σ : ℝ} (hσ : 0 < σ) :
    ContinuousOn (fun u => F (u, σ)) Hbar :=
  hc.comp (continuousOn_id.prodMk continuousOn_const) fun _ hu => ⟨hu, hσ⟩

theorem _root_.QuantumZipper.IsRegularWith.avgReg_eq (h : IsRegularWith x F) (k : ℕ) {z : ℂ} (hz : z ∈ Hbar) :
    avgReg x k z = F (z, radius k) :=
  (h.2.1 k z hz).limUnder_eq

/-- **Every-circle evaluation.** For a regular sample, `evalReg` of every folded circle is
given by the witness at the folded centre. -/
theorem _root_.QuantumZipper.IsRegularWith.evalReg_fc (h : IsRegularWith x F) (v : ℂ) {s : ℝ} (hs : 0 < s) :
    evalReg x (foldedCircle v s) = F (foldH v, s) := by
  have e : ∀ k : ℕ, ∫ u, avgReg x k u ∂foldedCircle v s =
      ∫ u, F (u, radius k) ∂foldedCircle (foldH v) s := by
    intro k
    rw [integral_congr_ae ((fc_ae_mem_Hbar v s).mono fun u hu => h.avgReg_eq k hu),
      integral_fc_foldH (continuousOn_slice h.1 (radius_pos k))]
  unfold evalReg
  simp_rw [e]
  exact ((h.2.2.tendsto_at (a := (foldH v, s)) ⟨foldH_mem_Hbar' v, hs⟩).comp tendsto_radius_nhdsGT).limUnder_eq

theorem _root_.QuantumZipper.IsRegularWith.evalReg_fc_of_mem (h : IsRegularWith x F) {v : ℂ} (hv : v ∈ Hbar) {s : ℝ}
    (hs : 0 < s) : evalReg x (foldedCircle v s) = F (v, s) := by
  rw [h.evalReg_fc v hs, foldH_of_mem' hv]

/-- The canonical witness: a regular sample is regular with `F (w, r) = evalReg x (fc w r)`. -/
theorem _root_.QuantumZipper.IsRegularWith.congr_evalReg (h : IsRegularWith x F) :
    IsRegularWith x (fun q => evalReg x (foldedCircle q.1 q.2)) := by
  have hEq : EqOn F (fun q => evalReg x (foldedCircle q.1 q.2)) (Hbar ×ˢ Ioi 0) :=
    fun q hq => (h.evalReg_fc_of_mem hq.1 hq.2).symm
  refine ⟨h.1.congr fun q hq => (hEq hq).symm, fun k z hz => ?_, ?_⟩
  · rw [← hEq (show (z, radius k) ∈ Hbar ×ˢ Ioi 0 from ⟨hz, radius_pos k⟩)]; exact h.2.1 k z hz
  · refine tluo_of_dist_le h.2.2 ?_
    filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ) q hq
    have e : ∫ u, evalReg x (foldedCircle u ρ) ∂foldedCircle q.1 q.2 =
        ∫ u, F (u, ρ) ∂foldedCircle q.1 q.2 :=
      integral_congr_ae ((fc_ae_mem_Hbar _ _).mono fun u hu =>
        (hEq (show (u, ρ) ∈ Hbar ×ˢ Ioi 0 from ⟨hu, hρ⟩)).symm)
    rw [e, show F q = evalReg x (foldedCircle q.1 q.2) from hEq hq]

/-! ## 5. Closure under deterministic operations -/

/-- Generic transfer: a sample `y` whose folded-circle values at centres in `Hbar` are
`G (d, r)` for a function `G` continuous on `Hbar × (0,∞)` satisfies clause (i). -/
theorem tendsto_of_eval_eq {y : FieldSample} {G : ℂ × ℝ → ℝ} (hG : ContinuousOn G (Hbar ×ˢ Ioi 0))
    (hy : ∀ d ∈ Hbar, ∀ r > 0, y (foldedCircle d r) = G (d, r)) (k : ℕ) {z : ℂ}
    (hz : z ∈ Hbar) :
    Tendsto (fun n => y (foldedCircle (dyadicRoundC n z) (radius k))) atTop
      (𝓝 (G (z, radius k))) := by
  have hmem : ∀ n, dyadicRoundC n z ∈ Hbar := fun n => CircleCont.dyadicRoundC_mem_Hbar hz n
  simp_rw [hy _ (hmem _) _ (radius_pos k)]
  have hc := continuousOn_slice hG (radius_pos k) z hz
  exact hc.tendsto.comp (tendsto_nhdsWithin_iff.2
    ⟨tendsto_dyadicRoundC z, Eventually.of_forall hmem⟩)

theorem _root_.QuantumZipper.IsRegularWith.addConst' (h : IsRegularWith x F) (c : ℝ) :
    IsRegularWith (addConst x c) (fun q => F q + c) := by
  refine ⟨h.1.add continuousOn_const, fun k z hz => ?_, ?_⟩
  · have e : ∀ n, addConst x c (foldedCircle (dyadicRoundC n z) (radius k)) =
        x (foldedCircle (dyadicRoundC n z) (radius k)) + c := fun n => by
      simp [QuantumZipper.addConst]
    simp_rw [e]
    exact (h.2.1 k z hz).add_const c
  · refine tluo_of_dist_le (tluo_add_const h.2.2 c) ?_
    filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ) q hq
    rw [integral_fc_const_add (continuousOn_slice h.1 hρ) _ (le_of_lt hq.2)]

theorem _root_.QuantumZipper.IsRegularSample.addConst' (h : IsRegularSample x) (c : ℝ) :
    IsRegularSample (addConst x c) :=
  let ⟨_, hF⟩ := h; ⟨_, hF.addConst' c⟩

theorem measurable_avgReg_slice (x : FieldSample) (k : ℕ) : Measurable (avgReg x k) :=
  (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)

/-- `evalReg` of an image measure, for a regular sample. -/
theorem _root_.QuantumZipper.IsRegularWith.evalReg_map_eq (h : IsRegularWith x F) {m : ℂ → ℂ} (hm : Measurable m)
    (hmH : MapsTo m Hbar Hbar) {ν : Measure ℂ} (hν : ∀ᵐ u ∂ν, u ∈ Hbar) {G : ℕ → ℝ}
    (hG : ∀ k, ∫ u, F (m u, radius k) ∂ν = G k) {L : ℝ} (hL : Tendsto G atTop (𝓝 L)) :
    evalReg x (ν.map m) = L := by
  have e : ∀ k : ℕ, ∫ u, avgReg x k u ∂ν.map m = G k := by
    intro k
    rw [integral_map hm.aemeasurable (measurable_avgReg_slice x k).aestronglyMeasurable, ← hG k]
    exact integral_congr_ae (hν.mono fun u hu => h.avgReg_eq k (hmH hu))
  unfold evalReg
  simp_rw [e]
  exact hL.limUnder_eq

theorem mapsTo_add_real (t : ℝ) : MapsTo (fun u : ℂ => u + t) Hbar Hbar :=
  fun u (hu : 0 ≤ u.im) => show 0 ≤ (u + t).im by simpa using hu

theorem mapsTo_mul_pos {b : ℝ} (hb : 0 < b) : MapsTo (fun u : ℂ => (b : ℂ) * u) Hbar Hbar :=
  fun u (hu : 0 ≤ u.im) => show 0 ≤ ((b : ℂ) * u).im by simpa using mul_nonneg hb.le hu

theorem mapsTo_neg_conj : MapsTo (fun u : ℂ => -conj u) Hbar Hbar :=
  fun u (hu : 0 ≤ u.im) => show 0 ≤ (-conj u).im by simpa using hu

theorem translate_fc_eq (h : IsRegularWith x F) (t : ℝ) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ}
    (hr : 0 < r) : translate x (t : ℂ) (foldedCircle d r) = F (d + t, r) :=
  h.evalReg_map_eq (by fun_prop) (mapsTo_add_real t) (fc_ae_mem_Hbar d r)
    (fun k => integral_fc_comp_add_real (g := fun u => F (u, radius k))
      (continuousOn_slice h.1 (radius_pos k)) d r t)
    ((h.2.2.tendsto_at (a := (d + t, r)) ⟨mapsTo_add_real t hd, hr⟩).comp tendsto_radius_nhdsGT)

/-- Real translations preserve regularity. -/
theorem _root_.QuantumZipper.IsRegularWith.translate' (h : IsRegularWith x F) (t : ℝ) :
    IsRegularWith (translate x (t : ℂ)) (fun q => F (q.1 + t, q.2)) := by
  set g : ℂ × ℝ → ℂ × ℝ := fun q => (q.1 + t, q.2) with hg
  have hgS : MapsTo g (Hbar ×ˢ Ioi 0) (Hbar ×ˢ Ioi 0) :=
    fun q hq => ⟨mapsTo_add_real t hq.1, hq.2⟩
  have hgc : ContinuousOn g (Hbar ×ˢ Ioi 0) := by fun_prop
  have hc : ContinuousOn (fun q => F (q.1 + t, q.2)) (Hbar ×ˢ Ioi 0) := h.1.comp hgc hgS
  refine ⟨hc, fun k z hz => tendsto_of_eval_eq hc
    (fun d hd r hr => translate_fc_eq h t hd hr) k hz, ?_⟩
  refine tluo_of_dist_le (h.2.2.comp g hgS hgc) ?_
  filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ) q hq
  simp only [Function.comp, hg]
  rw [integral_fc_comp_add_real (g := fun u => F (u, ρ)) (continuousOn_slice h.1 hρ)]

theorem _root_.QuantumZipper.IsRegularSample.translate' (h : IsRegularSample x) (t : ℝ) :
    IsRegularSample (translate x (t : ℂ)) :=
  let ⟨_, hF⟩ := h; ⟨_, hF.translate' t⟩

theorem integral_log_deriv_mul {b : ℝ} (hb : 0 < b) (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    ∫ z, Real.log ‖deriv (fun z : ℂ => (b : ℂ) * z) z‖ ∂μ = Real.log b := by
  have : ∀ z : ℂ, deriv (fun z : ℂ => (b : ℂ) * z) z = b := fun z => by
    rw [deriv_const_mul_field']; simp
  simp only [this, Complex.norm_real, Real.norm_of_nonneg hb.le, integral_const, smul_eq_mul,
    probReal_univ, one_mul]

theorem rescale_fc_eq (h : IsRegularWith x F) (Q : ℝ) {b : ℝ} (hb : 0 < b) (d : ℂ) {r : ℝ}
    (hr : 0 < r) : rescale x Q b (foldedCircle d r) = F (foldH ((b : ℂ) * d), b * r) + Q * Real.log b := by
  unfold rescale coordChange
  rw [integral_log_deriv_mul hb]
  congr 1
  refine h.evalReg_map_eq (by fun_prop) (mapsTo_mul_pos hb) (fc_ae_mem_Hbar d r)
    (fun k => ?_) ((h.2.2.tendsto_at (a := (foldH ((b : ℂ) * d), b * r)) ⟨foldH_mem_Hbar' _, mul_pos hb hr⟩).comp tendsto_radius_nhdsGT)
  rw [integral_fc_comp_mul (g := fun u => F (u, radius k)) (continuousOn_slice h.1 (radius_pos k))
    d r hb, ← integral_fc_foldH (continuousOn_slice h.1 (radius_pos k))]
  rfl

/-- Dilations by `b > 0` preserve regularity: `F_b (w, r) = F (b w, b r) + Q log b`. -/
theorem _root_.QuantumZipper.IsRegularWith.rescale' (h : IsRegularWith x F) (Q : ℝ) {b : ℝ} (hb : 0 < b) :
    IsRegularWith (rescale x Q b)
      (fun q => F ((b : ℂ) * q.1, b * q.2) + Q * Real.log b) := by
  set g : ℂ × ℝ → ℂ × ℝ := fun q => ((b : ℂ) * q.1, b * q.2) with hg
  have hgS : MapsTo g (Hbar ×ˢ Ioi 0) (Hbar ×ˢ Ioi 0) :=
    fun q hq => ⟨mapsTo_mul_pos hb hq.1, mul_pos hb hq.2⟩
  have hgc : ContinuousOn g (Hbar ×ˢ Ioi 0) := by fun_prop
  have hc : ContinuousOn (fun q => F ((b : ℂ) * q.1, b * q.2) + Q * Real.log b)
      (Hbar ×ˢ Ioi 0) := (h.1.comp hgc hgS).add continuousOn_const
  refine ⟨hc, fun k z hz => tendsto_of_eval_eq hc (fun d hd r hr => ?_) k hz, ?_⟩
  · rw [rescale_fc_eq h Q hb d hr, foldH_of_mem' (mapsTo_mul_pos hb hd)]
  have h1 := tluo_add_const (tluo_comp_tendsto (h.2.2.comp g hgS hgc)
    (φ := fun ρ => b * ρ) (q := 𝓝[>] 0) (tendsto_nhdsWithin_iff.2 ⟨
      tendsto_nhdsWithin_of_tendsto_nhds ((continuous_const_mul b).tendsto' 0 0 (mul_zero b)),
      eventually_nhdsWithin_of_forall fun ρ (hρ : 0 < ρ) => mul_pos hb hρ⟩)) (Q * Real.log b)
  refine tluo_of_dist_le h1 ?_
  filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ) q hq
  simp only [Function.comp, hg]
  have hcont : ContinuousOn (fun u => F ((b : ℂ) * u, b * ρ)) Hbar :=
    (continuousOn_slice h.1 (mul_pos hb hρ)).comp (continuous_const.mul continuous_id).continuousOn
      (mapsTo_mul_pos hb)
  rw [integral_fc_const_add (g := fun u => F ((b : ℂ) * u, b * ρ)) hcont _ (le_of_lt hq.2),
    integral_fc_comp_mul (g := fun u => F (u, b * ρ)) (continuousOn_slice h.1 (mul_pos hb hρ))
      _ _ hb]

theorem _root_.QuantumZipper.IsRegularSample.rescale' (h : IsRegularSample x) (Q : ℝ) {b : ℝ} (hb : 0 < b) :
    IsRegularSample (rescale x Q b) :=
  let ⟨_, hF⟩ := h; ⟨_, hF.rescale' Q hb⟩

/-- Composition of rescalings, up to `RegEq`. -/
theorem _root_.QuantumZipper.IsRegularSample.regEq_rescale_rescale (h : IsRegularSample x) (Q : ℝ) {b c : ℝ}
    (hb : 0 < b) (hc : 0 < c) :
    RegEq (rescale (rescale x Q b) Q c) (rescale x Q (b * c)) := by
  obtain ⟨F, hF⟩ := h
  have hFb := hF.rescale' Q hb
  have key : ∀ d : ℂ, ∀ r > 0, rescale (rescale x Q b) Q c (foldedCircle d r) =
      rescale x Q (b * c) (foldedCircle d r) := by
    intro d r hr
    rw [rescale_fc_eq hFb Q hc d hr, rescale_fc_eq hF Q (mul_pos hb hc) d hr]
    have e1 : (b : ℂ) * foldH ((c : ℂ) * d) = foldH (((b * c : ℝ) : ℂ) * d) := by
      rw [← foldH_mul_pos _ hb]; push_cast; ring_nf
    rw [e1, show b * (c * r) = b * c * r by ring, Real.log_mul hb.ne' hc.ne']
    ring
  intro k z
  unfold avgReg
  simp_rw [key _ _ (radius_pos k)]

/-- The reflection `z ↦ −z̄` of a field sample. -/
def reflectH (x : FieldSample) : FieldSample := fun μ => evalReg x (μ.map fun z => -conj z)

theorem reflectH_fc_eq (h : IsRegularWith x F) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    reflectH x (foldedCircle d r) = F (-conj d, r) :=
  h.evalReg_map_eq (by fun_prop) mapsTo_neg_conj (fc_ae_mem_Hbar d r)
    (fun k => integral_fc_comp_neg_conj (g := fun u => F (u, radius k))
      (continuousOn_slice h.1 (radius_pos k)) d r)
    ((h.2.2.tendsto_at (a := (-conj d, r)) ⟨mapsTo_neg_conj hd, hr⟩).comp tendsto_radius_nhdsGT)

/-- The reflection `z ↦ −z̄` preserves regularity. -/
theorem _root_.QuantumZipper.IsRegularWith.reflectH' (h : IsRegularWith x F) :
    IsRegularWith (reflectH x) (fun q => F (-conj q.1, q.2)) := by
  set g : ℂ × ℝ → ℂ × ℝ := fun q => (-conj q.1, q.2) with hg
  have hgS : MapsTo g (Hbar ×ˢ Ioi 0) (Hbar ×ˢ Ioi 0) :=
    fun q hq => ⟨mapsTo_neg_conj hq.1, hq.2⟩
  have hgc : ContinuousOn g (Hbar ×ˢ Ioi 0) :=
    ((Complex.continuous_conj.comp continuous_fst).neg.prodMk continuous_snd).continuousOn
  have hc : ContinuousOn (fun q => F (-conj q.1, q.2)) (Hbar ×ˢ Ioi 0) := h.1.comp hgc hgS
  refine ⟨hc, fun k z hz => tendsto_of_eval_eq hc
    (fun d hd r hr => reflectH_fc_eq h hd hr) k hz, ?_⟩
  refine tluo_of_dist_le (h.2.2.comp g hgS hgc) ?_
  filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ) q hq
  simp only [Function.comp, hg]
  rw [integral_fc_comp_neg_conj (g := fun u => F (u, ρ)) (continuousOn_slice h.1 hρ)]

theorem _root_.QuantumZipper.IsRegularSample.reflectH' (h : IsRegularSample x) : IsRegularSample (reflectH x) :=
  let ⟨_, hF⟩ := h; ⟨_, hF.reflectH'⟩

/-! ## 6. Adding deterministic functions -/

theorem norm_circleMap_le' (c : ℂ) (r θ : ℝ) : ‖circleMap c r θ‖ ≤ ‖c‖ + |r| := by
  calc ‖circleMap c r θ‖ = ‖c + (circleMap c r θ - c)‖ := by ring_nf
    _ ≤ ‖c‖ + ‖circleMap c r θ - c‖ := norm_add_le _ _
    _ = ‖c‖ + |r| := by rw [circleMap_sub_center, norm_circleMap_zero]

theorem continuousOn_integral_fc_fun {φ : ℂ → ℝ} (hφ : ContinuousOn φ Hbar) :
    ContinuousOn (fun q : ℂ × ℝ => ∫ v, φ v ∂foldedCircle q.1 q.2) univ :=
  continuousOn_integral_fc (P := ℂ × ℝ) (S := univ) (H := fun _ v => φ v)
    (c := fun q => q.1) (r := fun q => q.2) (hφ.comp continuousOn_snd fun q hq => hq.2)
    continuousOn_fst continuousOn_snd

/-- Vanishing circle smoothing of a function continuous on `Hbar`, locally uniformly. -/
theorem tluo_smooth_continuous {φ : ℂ → ℝ} (hφ : ContinuousOn φ Hbar) :
    TendstoLocallyUniformlyOn
      (fun ρ (p : ℂ × ℝ) => ∫ u, (∫ v, φ v ∂foldedCircle u ρ) ∂foldedCircle p.1 p.2)
      (fun p => ∫ v, φ v ∂foldedCircle p.1 p.2) (𝓝[>] 0) (Hbar ×ˢ Ioi 0) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  set R := ‖x.1‖ + x.2 + 2 with hR
  have hg := continuous_comp_foldH hφ
  have huc := (isCompact_closedBall (0 : ℂ) (R + 1)).uniformContinuousOn_of_continuous
    hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc (ε / 2) (by positivity)
  set t : Set (ℂ × ℝ) := {p | ‖p.1‖ + p.2 < R} with ht_def
  have ht : t ∈ 𝓝[Hbar ×ˢ Ioi 0] x := by
    refine mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds (isOpen_lt (by fun_prop) continuous_const) ?_)
    show ‖x.1‖ + x.2 < R
    linarith
  refine ⟨t ∩ (Hbar ×ˢ Ioi 0), inter_mem ht self_mem_nhdsWithin, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ one_pos)] with ρ hρ p hp
  have hρ0 : 0 < ρ := hρ.1
  have hΦc : ContinuousOn (fun u => ∫ v, φ v ∂foldedCircle u ρ) Hbar :=
    (continuousOn_integral_fc_fun hφ).comp (continuous_id.prodMk continuous_const).continuousOn
      fun _ _ => mem_univ _
  have hin : ∀ u ∈ Hbar, ‖u‖ ≤ R → |φ u - ∫ v, φ v ∂foldedCircle u ρ| ≤ ε / 2 := by
    intro u hu huR
    have key := abs_integral_fc_sub_le (g := fun _ => φ u) (g' := φ) (w := u) (w' := u) (r := ρ)
      (r' := ρ) (C := ε / 2) continuousOn_const hφ (fun θ => by
        have h1 : φ (foldH u) = φ u := by rw [foldH_of_mem' hu]
        rw [← h1]
        have hd : dist u (circleMap u ρ θ) < δ := by
          rw [dist_comm, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
            abs_of_pos hρ0]
          exact hρ.2.trans_le (min_le_left _ _)
        have hu1 : u ∈ closedBall (0 : ℂ) (R + 1) := by
          rw [mem_closedBall, dist_zero_right]; linarith
        have hu2 : circleMap u ρ θ ∈ closedBall (0 : ℂ) (R + 1) := by
          rw [mem_closedBall, dist_zero_right]
          have := norm_circleMap_le' u ρ θ
          rw [abs_of_pos hρ0] at this
          linarith [hρ.2.trans_le (min_le_right _ _)]
        have := hδ' _ hu1 _ hu2 hd
        rw [Real.dist_eq] at this
        exact this.le)
    simpa using key
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (abs_integral_fc_sub_le (g := φ) (C := ε / 2)
    (g' := fun u => ∫ v, φ v ∂foldedCircle u ρ) hφ hΦc fun θ => ?_) (by linarith : ε / 2 < ε)
  refine hin _ (foldH_mem_Hbar' _) ?_
  rw [norm_foldH']
  have := norm_circleMap_le' p.1 p.2 θ
  have hp2 : 0 < p.2 := hp.2.2
  rw [abs_of_pos hp2] at this
  have := hp.1
  simp only [ht_def, mem_setOf_eq] at this
  linarith

/-- Adding a deterministic function continuous on `Hbar` preserves regularity. -/
theorem _root_.QuantumZipper.IsRegularWith.add_ofFun' (h : IsRegularWith x F) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Hbar) :
    IsRegularWith (x + ofFun φ) (fun q => F q + ∫ v, φ v ∂foldedCircle q.1 q.2) := by
  have hΦ := (continuousOn_integral_fc_fun hφ).mono (subset_univ (Hbar ×ˢ Ioi (0 : ℝ)))
  refine ⟨h.1.add hΦ, fun k z hz => ?_, ?_⟩
  · exact (h.2.1 k z hz).add (tendsto_of_eval_eq (y := ofFun φ) hΦ (fun d _ r _ => rfl) k hz)
  · refine tluo_of_dist_le (tluo_add h.2.2 (tluo_smooth_continuous hφ)) ?_
    filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ) q hq
    have hΦc : ContinuousOn (fun u => ∫ v, φ v ∂foldedCircle u ρ) Hbar :=
      (continuousOn_integral_fc_fun hφ).comp (continuous_id.prodMk continuous_const).continuousOn
        fun _ _ => mem_univ _
    rw [integral_add (integrable_fc (continuousOn_slice h.1 hρ) _ hq.2.le)
      (integrable_fc hΦc _ hq.2.le)]

theorem _root_.QuantumZipper.IsRegularSample.add_ofFun' (h : IsRegularSample x) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Hbar) : IsRegularSample (x + ofFun φ) :=
  let ⟨_, hF⟩ := h; ⟨_, hF.add_ofFun' hφ⟩

open CircleCont (circPot continuous_circPot integral_neumannH_foldedCircle_right
  abs_circPot_sub_le)

theorem circPot_symm' (ρ : ℝ) (u x : ℂ) : circPot ρ u x = circPot ρ x u := by
  unfold circPot
  rw [norm_sub_rev u x, show ‖u - conj x‖ = ‖x - conj u‖ by
    rw [← Complex.norm_conj, map_sub, Complex.conj_conj, norm_sub_rev]]

/-- Exchange of two folded-circle integrations of the Neumann kernel. -/
theorem integral_circPot_swap {a b : ℂ} (ha : a ∈ Hbar) (hb : b ∈ Hbar) {r ρ : ℝ} (hr : 0 < r)
    (hρ : 0 < ρ) :
    ∫ u, circPot ρ b u ∂foldedCircle a r = ∫ y, circPot r a y ∂foldedCircle b ρ := by
  have e1 : ∀ u, circPot ρ b u = ∫ y, neumannH u y ∂foldedCircle b ρ := fun u =>
    (integral_neumannH_foldedCircle_right b u hρ).symm
  simp_rw [e1]
  rw [integral_integral_swap (f := fun u y => neumannH u y)
    (integrable_neumannH_prod (isAdmissibleH_foldedCircle ha hr)
      (isAdmissibleH_foldedCircle hb hρ))]
  exact integral_congr_ae (ae_of_all _ fun y => integral_neumannH_foldedCircle a y hr)

theorem neumannH_real (v : ℂ) (s : ℝ) : neumannH v s = 2 * (-Real.log ‖v - s‖) := by
  unfold neumannH; rw [Complex.conj_ofReal]; ring

theorem integral_neg_log_fc (w : ℂ) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    ∫ v, -Real.log ‖v - s‖ ∂foldedCircle w r = circPot r w s / 2 := by
  have e : ∀ v : ℂ, -Real.log ‖v - s‖ = neumannH v s / 2 := fun v => by
    rw [neumannH_real]; ring
  simp_rw [e]
  rw [integral_div, integral_neumannH_foldedCircle w s hr]
  rfl

theorem continuousOn_circPot_real (s : ℝ) :
    ContinuousOn (fun q : ℂ × ℝ => circPot q.2 q.1 s) (Hbar ×ˢ Ioi 0) := by
  unfold circPot
  have h1 : ContinuousOn (fun q : ℂ × ℝ => max q.2 ‖q.1 - s‖) (Hbar ×ˢ Ioi 0) := by fun_prop
  have h2 : ContinuousOn (fun q : ℂ × ℝ => max q.2 ‖q.1 - conj (s : ℂ)‖) (Hbar ×ˢ Ioi 0) := by
    fun_prop
  exact (h1.log fun q hq => (lt_of_lt_of_le hq.2 (le_max_left _ _)).ne').neg.sub
    (h2.log fun q hq => (lt_of_lt_of_le hq.2 (le_max_left _ _)).ne')

/-- Adding a logarithmic singularity `α (−log |· − s|)` at a boundary point `s ∈ ℝ` preserves
regularity; its circle averages are `α (−log max(r, |w − s|))` (written `α circPot r w s / 2`). -/
theorem _root_.QuantumZipper.IsRegularWith.add_ofFun_log' (h : IsRegularWith x F) (α s : ℝ) :
    IsRegularWith (x + ofFun fun v => α * -Real.log ‖v - s‖)
      (fun q => F q + α * (circPot q.2 q.1 s / 2)) := by
  have hΦ : ContinuousOn (fun q : ℂ × ℝ => α * (circPot q.2 q.1 s / 2)) (Hbar ×ˢ Ioi 0) :=
    continuousOn_const.mul ((continuousOn_circPot_real s).div_const 2)
  have hint : ∀ w : ℂ, ∀ r > 0, ∫ v, α * -Real.log ‖v - s‖ ∂foldedCircle w r =
      α * (circPot r w s / 2) := fun w r hr => by
    rw [integral_const_mul, integral_neg_log_fc w hr]
  have hsH : ((s : ℂ)) ∈ Hbar := show 0 ≤ (s : ℂ).im by simp
  refine ⟨h.1.add hΦ, fun k z hz => ?_, ?_⟩
  · exact (h.2.1 k z hz).add (tendsto_of_eval_eq (y := ofFun fun v => α * -Real.log ‖v - s‖)
      hΦ (fun d _ r hr => hint d r hr) k hz)
  · have hsm : TendstoLocallyUniformlyOn
        (fun ρ (p : ℂ × ℝ) => ∫ u, α * (circPot ρ u s / 2) ∂foldedCircle p.1 p.2)
        (fun p => α * (circPot p.2 p.1 s / 2)) (𝓝[>] 0) (Hbar ×ˢ Ioi 0) := by
      rw [Metric.tendstoLocallyUniformlyOn_iff]
      intro ε hε x hx
      have hx2 : 0 < x.2 := hx.2
      refine ⟨{p | x.2 / 2 < p.2} ∩ (Hbar ×ˢ Ioi 0), inter_mem (mem_nhdsWithin_of_mem_nhds
        (IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd) (by
          show x.2 / 2 < x.2; linarith))) self_mem_nhdsWithin, ?_⟩
      have hpos : 0 < ε * x.2 / (2 * (|α| + 1)) := by positivity
      filter_upwards [Ioo_mem_nhdsGT hpos] with ρ hρ p hp
      have hρ0 : 0 < ρ := hρ.1
      have hp2 : 0 < p.2 := hp.2.2
      have hpx : x.2 / 2 < p.2 := hp.1
      have e1 : ∫ u, α * (circPot ρ u s / 2) ∂foldedCircle p.1 p.2 =
          α * ((∫ y, circPot p.2 p.1 y ∂foldedCircle s ρ) / 2) := by
        rw [integral_const_mul, integral_div]
        simp_rw [circPot_symm' ρ _ (s : ℂ)]
        rw [integral_circPot_swap hp.2.1 hsH hp2 hρ0]
      have hb : |circPot p.2 p.1 s - ∫ y, circPot p.2 p.1 y ∂foldedCircle s ρ| ≤ 2 * ρ / p.2 := by
        have := abs_integral_fc_sub_le (g := fun _ => circPot p.2 p.1 s)
          (g' := circPot p.2 p.1) (w := s) (w' := s) (r := ρ) (r' := ρ) (C := 2 * ρ / p.2)
          continuousOn_const (continuous_circPot hp2 _).continuousOn (fun θ => by
            rw [circPot_symm' p.2 p.1 s, circPot_symm' p.2 p.1]
            refine (abs_circPot_sub_le hp2 _ _ _).trans ?_
            rw [norm_sub_rev]
            have e : foldH (circleMap (s : ℂ) ρ θ) - s = foldH (circleMap (s : ℂ) ρ θ - s) := by
              rw [sub_eq_add_neg, sub_eq_add_neg, show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring,
                foldH_add_real]
            rw [e, norm_foldH', circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ0])
        simpa using this
      rw [e1, Real.dist_eq]
      have e2 : α * (circPot p.2 p.1 s / 2) - α * ((∫ y, circPot p.2 p.1 y ∂foldedCircle s ρ) / 2)
          = α / 2 * (circPot p.2 p.1 s - ∫ y, circPot p.2 p.1 y ∂foldedCircle s ρ) := by ring
      rw [e2, abs_mul]
      have ha2 : |α / 2| ≤ (|α| + 1) / 2 := by rw [abs_div]; norm_num; linarith
      have hrat : 2 * ρ / p.2 ≤ 4 * ρ / x.2 := by
        rw [div_le_div_iff₀ hp2 hx2]; nlinarith
      calc |α / 2| * |circPot p.2 p.1 s - ∫ y, circPot p.2 p.1 y ∂foldedCircle s ρ|
          ≤ ((|α| + 1) / 2) * (4 * ρ / x.2) :=
            mul_le_mul ha2 (hb.trans hrat) (abs_nonneg _) (by positivity)
        _ = 2 * (|α| + 1) * ρ / x.2 := by ring
        _ < ε := by
            rw [div_lt_iff₀ hx2]
            have := hρ.2
            rw [lt_div_iff₀ (by positivity)] at this
            nlinarith
    refine tluo_of_dist_le (tluo_add h.2.2 hsm) ?_
    filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ) q hq
    have hc : ContinuousOn (fun u : ℂ => α * (circPot ρ u s / 2)) Hbar :=
      (continuousOn_const.mul (((continuousOn_circPot_real s).comp
        (continuous_id.prodMk continuous_const).continuousOn fun u hu => ⟨hu, hρ⟩).div_const 2))
    rw [integral_add (integrable_fc (continuousOn_slice h.1 hρ) _ hq.2.le)
      (integrable_fc hc _ hq.2.le)]

theorem _root_.QuantumZipper.IsRegularSample.add_ofFun_log' (h : IsRegularSample x) (α s : ℝ) :
    IsRegularSample (x + ofFun fun v => α * -Real.log ‖v - s‖) :=
  let ⟨_, hF⟩ := h; ⟨_, hF.add_ofFun_log' α s⟩

end RegClosure
end QuantumZipper
