/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.FrostmanReg at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Regularization
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import LatticeProb.Bonanno.QuantumZipper.Statements.CouplingFields
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.TietzeExtension

/-!
# RC1: Frostman regularization for the free GFF

Let `X` be a free-boundary GFF modulo constants and `ν` a finite measure supported in
`closedBall 0 R ∩ Hbar` with a Frostman bound `ν(B(w,r)) ≤ C r^α`, `α > 0`.

* (i) `isAdmissibleH_of_frostman`: `ν` is admissible (layer cake: the `log⁻` potential of `ν` is
  at most `C/α`).
* (ii) `ae_tendsto_integral_avgReg_frostman`, `ae_evalReg_eq_frostman`: almost surely
  `∫ avgReg (X ω) k dν → X ω ν`, hence `evalReg (X ω) ν = X ω ν`.
* (iii) the same for `ofFun h + X ω` with `h` continuous on `Hbar`
  (`ae_tendsto_integral_avgReg_ofFun_add_frostman`), with `h` continuous on an open
  neighbourhood of the support (`..._of_continuousOn_open`), and with `h = h0rev κ` when `0` is
  not in the support (`..._h0rev_frostman`).
* (iv) random measures `ν (θ ω)` with `θ` independent of `X`
  (`ae_tendsto_evalReg_frostman_random`, `ae_tendsto_evalReg_ofFun_add_frostman_random`).

Proof of (ii): with `νk = ν.bind (foldedCircle · 2^{-k})`, one has
`Var(X νk - X ν) = Λ(ν) - Λ(νk)`, where `Λ(p) = ∫ p(dx) ∫ ν(dw) Lr(w,x)` and
`0 ≤ Lr(w,x) ≤ 2 log⁺(r/|w-x|)`. The Frostman bound gives `0 ≤ ∫ Lr(w,x) dν(w) ≤ 2 C r^α/α`
uniformly in `x`, so the variance is `O(2^{-kα})`; Borel–Cantelli and
`ae_integral_avgReg_eq` finish.

All results hold for any additive-constant convention allowed by `IsFreeGFFModConstH`.
-/

noncomputable section

open MeasureTheory Filter ProbabilityTheory
open scoped Real ComplexConjugate ENNReal NNReal Topology

namespace QuantumZipper

/-- Frostman bound of exponent `α` and constant `C` for a measure on `ℂ`. -/
def IsFrostman (ν : Measure ℂ) (α C : ℝ) : Prop :=
  ∀ w : ℂ, ∀ r : ℝ, 0 < r → (ν (Metric.closedBall w r)).toReal ≤ C * r ^ α

namespace FrostmanReg

open SmoothConv Regularization CircleFubini

variable {ν : Measure ℂ} {α C : ℝ}

/-! ## Deterministic Frostman estimates -/

theorem ae_mem_of_compl_null_frostman {μ : Measure ℂ} {S : Set ℂ} (h : μ Sᶜ = 0) :
    ∀ᵐ w ∂μ, w ∈ S :=
  mem_ae_iff.2 h

theorem frostman_const_nonneg (h : IsFrostman ν α C) : 0 ≤ C := by
  have := h 0 1 one_pos
  rw [Real.one_rpow, mul_one] at this
  exact ENNReal.toReal_nonneg.trans this

theorem frostman_measure_le [IsFiniteMeasure ν] (h : IsFrostman ν α C) (w : ℂ) {r : ℝ}
    (hr : 0 < r) : ν (Metric.closedBall w r) ≤ ENNReal.ofReal (C * r ^ α) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top ν _)]
  exact ENNReal.ofReal_le_ofReal (h w r hr)

theorem frostman_measure_singleton [IsFiniteMeasure ν] (h : IsFrostman ν α C) (hα : 0 < α)
    (x : ℂ) : ν {x} = 0 := by
  have hT : Tendsto (fun s : ℝ => C * s ^ α) (𝓝[>] 0) (𝓝 0) := by
    have h1 := ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto).const_mul C
    rw [Real.zero_rpow hα.ne', mul_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hle : (ν {x}).toReal ≤ 0 := by
    refine ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun s hs => ?_)
    refine le_trans (ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono ?_)) (h x s hs)
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy, Metric.mem_closedBall, dist_self]
    exact (le_of_lt hs)
  rcases (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm hle ENNReal.toReal_nonneg) with h0 | h0
  · exact h0
  · exact absurd h0 (measure_ne_top ν _)

/-- Layer cake: the truncated logarithmic potential at scale `r` of a Frostman measure is at
most `C r^α / α`. -/
theorem frostman_lintegral_logNeg_le [IsFiniteMeasure ν] (h : IsFrostman ν α C) (hα : 0 < α)
    (y : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ENNReal.ofReal (-Real.log (‖x - y‖ / r)) ∂ν ≤ ENNReal.ofReal (C * r ^ α / α) := by
  have hC := frostman_const_nonneg h
  set f : ℂ → ℝ := fun x => max 0 (-Real.log (‖x - y‖ / r)) with hf
  have hfm : Measurable f := measurable_const.max
    ((Real.measurable_log.comp ((measurable_id.sub_const y).norm.div_const r)).neg)
  have e1 : ∀ x, ENNReal.ofReal (-Real.log (‖x - y‖ / r)) = ENNReal.ofReal (f x) := by
    intro x
    simp only [hf]
    rcases le_total 0 (-Real.log (‖x - y‖ / r)) with h0 | h0
    · rw [max_eq_right h0]
    · rw [max_eq_left h0, ENNReal.ofReal_of_nonpos h0, ENNReal.ofReal_zero]
  simp_rw [e1]
  rw [lintegral_eq_lintegral_meas_lt ν (f := f)
    (ae_of_all _ fun x => (le_max_left _ _ : (0 : ℝ) ≤ f x)) hfm.aemeasurable]
  have hb : ∀ t ∈ Set.Ioi (0 : ℝ),
      ν {a | t < f a} ≤ ENNReal.ofReal (C * r ^ α * Real.exp ((-α) * t)) := by
    intro t ht
    have ht : 0 < t := ht
    have hsub : {a | t < f a} ⊆ Metric.closedBall y (r * Real.exp (-t)) := by
      intro a ha
      simp only [Set.mem_ofPred_eq, hf] at ha
      have h1 : t < -Real.log (‖a - y‖ / r) := by
        rcases lt_max_iff.1 ha with h | h
        · linarith
        · exact h
      rw [Metric.mem_closedBall, dist_eq_norm]
      rcases eq_or_ne a y with rfl | hay
      · simp only [sub_self, norm_zero, zero_div, Real.log_zero, neg_zero] at h1
        linarith
      · have hpos : 0 < ‖a - y‖ / r := div_pos (norm_pos_iff.2 (sub_ne_zero.2 hay)) hr
        have h2 : Real.log (‖a - y‖ / r) < -t := by linarith
        rw [Real.log_lt_iff_lt_exp hpos, div_lt_iff₀ hr] at h2
        linarith
    calc ν {a | t < f a} ≤ ν (Metric.closedBall y (r * Real.exp (-t))) := measure_mono hsub
      _ ≤ ENNReal.ofReal (C * (r * Real.exp (-t)) ^ α) :=
          frostman_measure_le h y (mul_pos hr (Real.exp_pos _))
      _ = _ := by
          rw [Real.mul_rpow hr.le (Real.exp_pos _).le, ← Real.exp_mul,
            show -t * α = (-α) * t by ring]
          ring_nf
  have hint : IntegrableOn (fun t => C * r ^ α * Real.exp ((-α) * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  calc ∫⁻ t in Set.Ioi 0, ν {a | t < f a}
      ≤ ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (C * r ^ α * Real.exp ((-α) * t)) :=
        setLIntegral_mono' measurableSet_Ioi hb
    _ = ENNReal.ofReal (∫ t in Set.Ioi 0, C * r ^ α * Real.exp ((-α) * t)) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t =>
          mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hr.le _)) (Real.exp_pos _).le)).symm
    _ = _ := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero,
          neg_div_neg_eq, mul_one_div]

/-- **(i)** A finite Frostman measure supported in `closedBall 0 R ∩ Hbar` is admissible. -/
theorem isAdmissibleH_of_frostman [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α) :
    IsAdmissibleH ν :=
  admissible_of_bounds (R := R) hsupp (C := ENNReal.ofReal (C * 1 ^ α / α)) ENNReal.ofReal_ne_top
    fun y => by simpa using frostman_lintegral_logNeg_le h hα y one_pos

theorem isAdmissibleH_bind_fc_of_supp [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) {r : ℝ} (hr : 0 < r) :
    IsAdmissibleH (ν.bind fun w => foldedCircle w r) := by
  have := isFiniteMeasure_bind_circle (r := r) ν
  refine admissible_of_bounds (R := R + r)
    (bind_circle_support ν hr.le hsupp (R₀ := R) (fun z hz => by simpa using hz.1) le_rfl)
    (C := ν Set.univ * (2 * ENNReal.ofReal (potConst r))) ?_
    (bind_circle_pot ν (fun z y => foldedCircle_pot_le hr z y))
  exact ENNReal.mul_ne_top (measure_ne_top _ _)
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top)

theorem log_max_sub_log_frostman {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Real.log (max r s) - Real.log s = max 0 (-Real.log (s / r)) := by
  rw [Real.log_div hs.ne' hr.ne']
  rcases le_total r s with h | h
  · rw [max_eq_right h, sub_self, max_eq_left]
    linarith [Real.log_le_log hr h]
  · rw [max_eq_left h, max_eq_right (by linarith [Real.log_le_log hs h])]
    ring

/-- The smoothing defect is nonnegative and bounded by `2 log⁺(r/|w-x|)`. -/
theorem Lr_bounds_frostman {r : ℝ} (hr : 0 < r) {w x : ℂ} (hw : w ∈ Hbar) (hx : x ∈ Hbar)
    (hwx : w ≠ x) :
    0 ≤ Lr r w x ∧ Lr r w x ≤ 2 * max 0 (-Real.log (‖w - x‖ / r)) := by
  have ha : 0 < ‖w - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hwx)
  have hab : ‖w - x‖ ≤ ‖w - conj x‖ := norm_sub_le_norm_sub_conj hw hx
  have hb : 0 < ‖w - conj x‖ := ha.trans_le hab
  have e : Lr r w x = (Real.log (max r ‖w - x‖) - Real.log ‖w - x‖) +
      (Real.log (max r ‖w - conj x‖) - Real.log ‖w - conj x‖) := by
    unfold Lr Nr neumannH; ring
  rw [e, log_max_sub_log_frostman hr ha, log_max_sub_log_frostman hr hb]
  have hmono : -Real.log (‖w - conj x‖ / r) ≤ -Real.log (‖w - x‖ / r) :=
    neg_le_neg (Real.log_le_log (div_pos ha hr) ((div_le_div_iff_of_pos_right hr).2 hab))
  constructor
  · exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  · linarith [max_le_max (le_refl (0 : ℝ)) hmono]

theorem ae_ne_frostman [IsFiniteMeasure ν] (h : IsFrostman ν α C) (hα : 0 < α) (x : ℂ) :
    ∀ᵐ w ∂ν, w ≠ x := by
  have h0 := frostman_measure_singleton h hα x
  rw [ae_iff]
  have e : {a : ℂ | ¬a ≠ x} = {x} := by
    ext a; simp only [ne_eq, not_not, Set.mem_singleton_iff]; rfl
  rw [e]; exact h0

theorem ae_Lr_bound_frostman [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α)
    {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ∈ Hbar) :
    ∀ᵐ w ∂ν, 0 ≤ Lr r w x ∧
      Lr r w x ≤ 2 * (ENNReal.ofReal (-Real.log (‖w - x‖ / r))).toReal := by
  filter_upwards [ae_mem_of_compl_null_frostman hsupp, ae_ne_frostman h hα x] with w hw hwx
  obtain ⟨h0, h1⟩ := Lr_bounds_frostman hr hw.2 hx hwx
  refine ⟨h0, ?_⟩
  rw [ENNReal.toReal_ofReal', max_comm]
  exact h1

theorem measurable_logNeg_frostman (x : ℂ) (r : ℝ) :
    Measurable fun w : ℂ => ENNReal.ofReal (-Real.log (‖w - x‖ / r)) :=
  (Real.measurable_log.comp ((measurable_id.sub_const x).norm.div_const r)).neg.ennreal_ofReal

theorem integrable_logNeg_frostman [IsFiniteMeasure ν] (h : IsFrostman ν α C) (hα : 0 < α)
    (x : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun w => (ENNReal.ofReal (-Real.log (‖w - x‖ / r))).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (measurable_logNeg_frostman x r).aemeasurable
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (frostman_lintegral_logNeg_le h hα x hr))

theorem integral_logNeg_le_frostman [IsFiniteMeasure ν] (h : IsFrostman ν α C) (hα : 0 < α)
    (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ w, 2 * (ENNReal.ofReal (-Real.log (‖w - x‖ / r))).toReal ∂ν ≤ 2 * (C * r ^ α / α) := by
  have hC := frostman_const_nonneg h
  rw [integral_const_mul, integral_toReal (measurable_logNeg_frostman x r).aemeasurable
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal ?_
    (frostman_lintegral_logNeg_le h hα x hr)) (by norm_num)
  exact div_nonneg (mul_nonneg hC (Real.rpow_nonneg hr.le _)) hα.le

theorem measurable_Lr_left_frostman {r : ℝ} (hr : 0 < r) (x : ℂ) :
    Measurable fun w => Lr r w x := by
  have h1 := measurable_Lr hr
  have h2 : Measurable fun w : ℂ => (w, x) := measurable_id.prodMk measurable_const
  have h3 := h1.comp h2
  exact h3

theorem integrable_Lr_frostman [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α)
    {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ∈ Hbar) :
    Integrable (fun w => Lr r w x) ν := by
  refine Integrable.mono' ((integrable_logNeg_frostman h hα x hr).const_mul 2)
    (measurable_Lr_left_frostman hr x).aestronglyMeasurable ?_
  filter_upwards [ae_Lr_bound_frostman hsupp h hα hr hx] with w hw
  rw [Real.norm_eq_abs, abs_of_nonneg hw.1]
  exact hw.2

theorem integral_Lr_nonneg_frostman [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α)
    {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ∈ Hbar) :
    0 ≤ ∫ w, Lr r w x ∂ν := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_Lr_bound_frostman hsupp h hα hr hx] with w hw
  exact hw.1

theorem integral_Lr_le_frostman [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α)
    {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ∈ Hbar) :
    ∫ w, Lr r w x ∂ν ≤ 2 * (C * r ^ α / α) := by
  refine le_trans (integral_mono_ae (integrable_Lr_frostman hsupp h hα hr hx)
    ((integrable_logNeg_frostman h hα x hr).const_mul 2) ?_)
    (integral_logNeg_le_frostman h hα x hr)
  filter_upwards [ae_Lr_bound_frostman hsupp h hα hr hx] with w hw
  exact hw.2

/-- The `ν`-average of the smoothing defect is in `[0, 2 C r^α / α]`, uniformly in `x`. -/
theorem frostman_integral_Lr [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α)
    {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ∈ Hbar) :
    Integrable (fun w => Lr r w x) ν ∧ 0 ≤ ∫ w, Lr r w x ∂ν ∧
      ∫ w, Lr r w x ∂ν ≤ 2 * (C * r ^ α / α) :=
  ⟨integrable_Lr_frostman hsupp h hα hr hx, integral_Lr_nonneg_frostman hsupp h hα hr hx,
    integral_Lr_le_frostman hsupp h hα hr hx⟩

/-- Smoothing the second argument of `kernelCov neumannH` against a Frostman measure. -/
theorem kernelCov_bind_frostman {p : Measure ℂ} (hp : IsAdmissibleH p) [IsFiniteMeasure ν]
    {R : ℝ} (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C)
    (hα : 0 < α) {r : ℝ} (hr : 0 < r) :
    kernelCov neumannH p (ν.bind fun w => foldedCircle w r) =
      kernelCov neumannH p ν - ∫ x, ∫ w, Lr r w x ∂ν ∂p := by
  have hνA := isAdmissibleH_of_frostman hsupp h hα
  have hkA := isAdmissibleH_bind_fc_of_supp hsupp hr
  have := isFiniteMeasure_bind_circle (r := r) ν
  have := hp.1
  obtain ⟨K, -, hKH, hKc⟩ := hp.2.1
  have hpH : ∀ᵐ x ∂p, x ∈ Hbar :=
    (ae_mem_of_compl_null_frostman hKc).mono fun x hx => hKH hx
  have i1 := (integrable_neumannH_prod hp hkA).prod_right_ae
  have i2 := (integrable_neumannH_prod hp hνA).prod_right_ae
  unfold kernelCov
  have h1 : ∀ᵐ x ∂p, ∫ y, neumannH x y ∂(ν.bind fun w => foldedCircle w r) =
      ∫ w, neumannH x w ∂ν - ∫ w, Lr r w x ∂ν := by
    filter_upwards [hpH, i1, i2] with x hx hi1 hi2
    rw [integral_bind_neumannH hr x hi1,
      ← integral_sub hi2 (frostman_integral_Lr hsupp h hα hr hx).1]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [Lr, neumannH_symm w x]; ring
  rw [integral_congr_ae h1]
  have hF : Integrable (fun x => ∫ w, neumannH x w ∂ν) p :=
    (integrable_neumannH_prod hp hνA).integral_prod_left
  have hGm : AEStronglyMeasurable (fun x => ∫ w, Lr r w x ∂ν) p :=
    (((measurable_Lr hr).comp measurable_swap).aestronglyMeasurable
      (μ := p.prod ν)).integral_prod_right'
  have hG : Integrable (fun x => ∫ w, Lr r w x ∂ν) p :=
    Integrable.of_bound hGm (2 * (C * r ^ α / α)) (hpH.mono fun x hx => by
      obtain ⟨-, h0, h1⟩ := frostman_integral_Lr hsupp h hα hr hx
      rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  exact integral_sub hF hG

theorem Lam_bounds_frostman {p : Measure ℂ} (hp : IsAdmissibleH p) [IsFiniteMeasure ν]
    {R : ℝ} (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C)
    (hα : 0 < α) {r : ℝ} (hr : 0 < r) :
    0 ≤ ∫ x, ∫ w, Lr r w x ∂ν ∂p ∧
      ∫ x, ∫ w, Lr r w x ∂ν ∂p ≤ 2 * (C * r ^ α / α) * (p Set.univ).toReal := by
  have := hp.1
  obtain ⟨K, -, hKH, hKc⟩ := hp.2.1
  have hpH : ∀ᵐ x ∂p, x ∈ Hbar :=
    (ae_mem_of_compl_null_frostman hKc).mono fun x hx => hKH hx
  refine ⟨integral_nonneg_of_ae (hpH.mono fun x hx =>
    (frostman_integral_Lr hsupp h hα hr hx).2.1), ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := p) (f := fun x => ∫ w, Lr r w x ∂ν)
    (C := 2 * (C * r ^ α / α)) (hpH.mono fun x hx => by
      obtain ⟨-, h0, h1⟩ := frostman_integral_Lr hsupp h hα hr hx
      rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans this)

/-- The Neumann energy of `νk - ν` is at most `2 C r^α ν(ℂ) / α`. -/
theorem abs_energy_frostman_le [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α)
    {r : ℝ} (hr : 0 < r) :
    |kernelCov2 neumannH (ν.bind fun w => foldedCircle w r, ν)
        (ν.bind fun w => foldedCircle w r, ν)| ≤ 2 * (C * r ^ α / α) * (ν Set.univ).toReal := by
  have hνA := isAdmissibleH_of_frostman hsupp h hα
  have hkA := isAdmissibleH_bind_fc_of_supp hsupp hr
  have mk : (ν.bind fun w => foldedCircle w r) Set.univ = ν Set.univ := bind_fc_univ ν r
  obtain ⟨a0, a1⟩ := Lam_bounds_frostman hνA hsupp h hα hr
  obtain ⟨b0, b1⟩ := Lam_bounds_frostman hkA hsupp h hα hr
  rw [mk] at b1
  unfold kernelCov2
  simp only
  rw [kernelCov_bind_frostman hkA hsupp h hα hr, kernelCov_bind_frostman hνA hsupp h hα hr]
  rw [abs_le]
  constructor <;> linarith

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integral_sq_frostman_le {X : Ω → Measure ℂ → ℝ} {P : Measure Ω}
    (hX : IsFreeGFFModConstH X P) [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α)
    {r : ℝ} (hr : 0 < r) :
    ∫ ω, (X ω (ν.bind fun w => foldedCircle w r) - X ω ν) ^ 2 ∂P ≤
      2 * (C * r ^ α / α) * (ν Set.univ).toReal := by
  have hνA := isAdmissibleH_of_frostman hsupp h hα
  have hkA := isAdmissibleH_bind_fc_of_supp hsupp hr
  have mA : (ν.bind fun w => foldedCircle w r) Set.univ = ν Set.univ := bind_fc_univ ν r
  have c1 := hX.covariance_eq ((ν.bind fun w => foldedCircle w r), ν)
    ((ν.bind fun w => foldedCircle w r), ν) hkA hνA mA hkA hνA mA
  dsimp only at c1
  have hm := hX.centered _ _ hkA hνA mA
  have key : ∫ ω, (X ω (ν.bind fun w => foldedCircle w r) - X ω ν) ^ 2 ∂P =
      cov[fun ω => X ω (ν.bind fun w => foldedCircle w r) - X ω ν,
        fun ω => X ω (ν.bind fun w => foldedCircle w r) - X ω ν; P] := by
    unfold covariance
    rw [hm]
    simp only [sub_zero, sq]
  rw [key, c1]
  exact (le_abs_self _).trans (abs_energy_frostman_le hsupp h hα hr)

/-- Borel–Cantelli for a geometric second-moment bound. -/
theorem ae_tendsto_zero_of_sq_geom_frostman {P : Measure Ω} {sd : ℕ → Ω → ℝ}
    (hmeas : ∀ k, Measurable (sd k)) (hint : ∀ k, Integrable (fun ω => sd k ω ^ 2) P)
    {A q : ℝ} (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hb : ∀ k, ∫ ω, sd k ω ^ 2 ∂P ≤ A * q ^ k) :
    ∀ᵐ ω ∂P, Tendsto (fun k => sd k ω) atTop (𝓝 0) := by
  set f : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (sd k ω ^ 2) with hf
  have hfm : ∀ k, Measurable (f k) := fun k => ((hmeas k).pow_const 2).ennreal_ofReal
  have hbound : ∀ k, ∫⁻ ω, f k ω ∂P ≤ ENNReal.ofReal A * ENNReal.ofReal q ^ k := by
    intro k
    calc ∫⁻ ω, f k ω ∂P = ENNReal.ofReal (∫ ω, sd k ω ^ 2 ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal (hint k) (ae_of_all _ fun ω => sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal (A * q ^ k) := ENNReal.ofReal_le_ofReal (hb k)
      _ = _ := by rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_pow hq0]
  have hsum : ∫⁻ ω, ∑' k, f k ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun k => (hfm k).aemeasurable]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 ?_)
    refine (tsub_pos_of_lt ?_).ne'
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hq1
  have hae := ae_lt_top' (AEMeasurable.tsum fun k => (hfm k).aemeasurable) hsum
  filter_upwards [hae] with ω hω
  have h1 : Tendsto (fun k => f k ω) atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact ENNReal.tendsto_cofinite_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun k => sd k ω ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [f, Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _)] using this
  have h4 := (Real.continuous_sqrt.tendsto 0).comp h2
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at h4
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 h4

theorem radius_rpow_frostman (k : ℕ) : radius k ^ α = ((2 : ℝ)⁻¹ ^ α) ^ k := by
  unfold radius
  calc ((2 : ℝ)⁻¹ ^ k) ^ α = ((2 : ℝ)⁻¹ ^ (k : ℝ)) ^ α := by rw [Real.rpow_natCast]
    _ = (2 : ℝ)⁻¹ ^ ((k : ℝ) * α) := by rw [← Real.rpow_mul (by norm_num)]
    _ = ((2 : ℝ)⁻¹ ^ α) ^ (k : ℝ) := by rw [mul_comm, Real.rpow_mul (by norm_num)]
    _ = ((2 : ℝ)⁻¹ ^ α) ^ k := by rw [Real.rpow_natCast]

/-- Almost sure convergence `X νk → X ν` for a Frostman measure `ν`. -/
theorem ae_tendsto_bind_frostman {X : Ω → Measure ℂ → ℝ} {P : Measure Ω}
    (hX : IsFreeGFFModConstH X P) [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α) :
    ∀ᵐ ω ∂P, Tendsto (fun k => X ω (ν.bind fun w => foldedCircle w (radius k))) atTop
      (𝓝 (X ω ν)) := by
  have hνA := isAdmissibleH_of_frostman hsupp h hα
  have hC := frostman_const_nonneg h
  have hq0 : 0 ≤ (2 : ℝ)⁻¹ ^ α := Real.rpow_nonneg (by norm_num) _
  have hq1 : (2 : ℝ)⁻¹ ^ α < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  set sd : ℕ → Ω → ℝ := fun k ω =>
    X ω (ν.bind fun w => foldedCircle w (radius k)) - X ω ν with hsd
  have hmeas : ∀ k, Measurable (sd k) := fun k =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hint : ∀ k, Integrable (fun ω => sd k ω ^ 2) P := fun k =>
    (memLp_pair_sc hX (isAdmissibleH_bind_fc_of_supp hsupp (radius_pos k)) hνA
      (bind_fc_univ ν _)).integrable_sq
  have hA : 0 ≤ 2 * (C / α) * (ν Set.univ).toReal :=
    mul_nonneg (mul_nonneg (by norm_num) (div_nonneg hC hα.le)) ENNReal.toReal_nonneg
  have hb : ∀ k, ∫ ω, sd k ω ^ 2 ∂P ≤
      (2 * (C / α) * (ν Set.univ).toReal) * ((2 : ℝ)⁻¹ ^ α) ^ k := by
    intro k
    refine (integral_sq_frostman_le hX hsupp h hα (radius_pos k)).trans (le_of_eq ?_)
    rw [radius_rpow_frostman]; ring
  filter_upwards [ae_tendsto_zero_of_sq_geom_frostman hmeas hint hA hq0 hq1 hb] with ω hω
  have h5 := hω.add_const (X ω ν)
  simp only [sd, sub_add_cancel, zero_add] at h5
  exact h5

/-- **(ii) Frostman regularization.** For a free GFF modulo constants and a finite Frostman
measure `ν` supported in `closedBall 0 R ∩ Hbar`, almost surely the integrated regularized
circle averages converge to the raw coordinate `X ω ν`. -/
theorem ae_tendsto_integral_avgReg_frostman {X : Ω → FieldSample} {P : Measure Ω}
    [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α) :
    ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, avgReg (X ω) k z ∂ν) atTop (𝓝 (X ω ν)) := by
  have h1 : ∀ᵐ ω ∂P, ∀ k, ∫ z, avgReg (X ω) k z ∂ν =
      X ω (ν.bind fun w => foldedCircle w (radius k)) :=
    ae_all_iff.2 fun k => ae_integral_avgReg_eq hX k ν
      ((isCompact_closedBall 0 R).inter_right isClosed_Hbar) Set.inter_subset_right hsupp
  filter_upwards [h1, ae_tendsto_bind_frostman hX hsupp h hα] with ω h1 h2
  simp only [h1]
  exact h2

/-- **(ii')** Consequently `evalReg (X ω) ν = X ω ν` almost surely. -/
theorem ae_evalReg_eq_frostman {X : Ω → FieldSample} {P : Measure Ω}
    [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α) :
    ∀ᵐ ω ∂P, evalReg (X ω) ν = X ω ν := by
  filter_upwards [ae_tendsto_integral_avgReg_frostman hX hsupp h hα] with ω h
  exact h.limUnder_eq

/-! ## (iii) Adding a deterministic function -/

/-- Almost surely, at scale `k`, the circle averages of `X ω` are continuous on `Hbar` and are
genuine limits along the dyadic approximations of the centre. -/
theorem ae_circleAvg_tendsto_frostman {X : Ω → FieldSample} {P : Measure Ω}
    [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (k : ℕ) :
    ∀ᵐ ω ∂P, ContinuousOn (fun z => avgReg (X ω) k z) Hbar ∧ ∀ z ∈ Hbar,
      Tendsto (fun n => X ω (foldedCircle (dyadicRoundC n z) (radius k))) atTop
        (𝓝 (avgReg (X ω) k z)) := by
  have hr := radius_pos k
  obtain ⟨Y, hc, -, hlim⟩ := CircleCont.exists_continuous_modification
    (Z := fun z ω => X ω (foldedCircle z (radius k)) - X ω (foldedCircle 0 (radius k)))
    (fun z => ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable)
    (mul_nonneg (pow_nonneg (div_nonneg (by norm_num) hr.le) 4) (gaussianAbsMoment_nonneg 8))
    (CircleCont.momentBound_circleDiff hX hr 0)
  filter_upwards [hlim] with ω hω
  have ht : ∀ z ∈ Hbar, Tendsto (fun n => X ω (foldedCircle (dyadicRoundC n z) (radius k)))
      atTop (𝓝 (Y z ω + X ω (foldedCircle 0 (radius k)))) := fun z hz => by
    have := (hω z hz).add_const (X ω (foldedCircle 0 (radius k)))
    simpa only [sub_add_cancel] using this
  have heq : ∀ z ∈ Hbar, avgReg (X ω) k z = Y z ω + X ω (foldedCircle 0 (radius k)) :=
    fun z hz => (ht z hz).limUnder_eq
  refine ⟨((hc ω).add continuousOn_const).congr heq, fun z hz => ?_⟩
  rw [heq z hz]
  exact ht z hz

theorem integrable_of_continuousOn_frostman [IsFiniteMeasure ν] {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ Hbar) (hνK : ν Kᶜ = 0) {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) :
    Integrable g ν := by
  have hae : ∀ᵐ z ∂ν, z ∈ K := mem_ae_iff.2 hνK
  have : IntegrableOn g K ν := (hg.mono hKH).integrableOn_compact hK
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at this

theorem tendsto_integral_smoothFun_frostman [IsFiniteMeasure ν] {h : ℂ → ℝ}
    (hh : ContinuousOn h Hbar) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar)
    (hνK : ν Kᶜ = 0) :
    Tendsto (fun k => ∫ z, GoodSample.smoothFun h z (radius k) ∂ν) atTop
      (𝓝 (∫ z, h z ∂ν)) := by
  have hae : ∀ᵐ z ∂ν, z ∈ K := mem_ae_iff.2 hνK
  rw [Metric.tendsto_nhds]
  intro ε hε
  set m := (ν Set.univ).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hev := RegClosure.tendsto_radius_nhdsGT.eventually
    (GoodSample.smooth_unif hh hK hKH (ε / (m + 1)) (by positivity))
  filter_upwards [hev] with k hk
  rw [Real.dist_eq, ← integral_sub
    (integrable_of_continuousOn_frostman hK hKH hνK
      (GoodSample.continuous_smoothFun hh _).continuousOn)
    (integrable_of_continuousOn_frostman hK hKH hνK hh)]
  have h1 := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun z => GoodSample.smoothFun h z (radius k) - h z) (C := ε / (m + 1))
    (hae.mono fun z hz => by rw [Real.norm_eq_abs]; exact (hk z hz).le)
  rw [Real.norm_eq_abs] at h1
  refine lt_of_le_of_lt h1 ?_
  have h2 : ν.real Set.univ = m := rfl
  rw [h2, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

theorem norm_foldH_sub_le_frostman {u z : ℂ} (hz : z ∈ Hbar) : ‖foldH u - z‖ ≤ ‖u - z‖ := by
  unfold foldH
  split_ifs with hu
  · exact le_rfl
  · have hu' : starRingEnd ℂ u ∈ Hbar := by
      show 0 ≤ (starRingEnd ℂ u).im
      rw [Complex.conj_im]; push Not at hu; linarith
    calc ‖starRingEnd ℂ u - z‖ ≤ ‖starRingEnd ℂ u - conj z‖ := norm_sub_le_norm_sub_conj hu' hz
      _ = ‖u - z‖ := by rw [← map_sub, Complex.norm_conj]

/-- A folded circle centred near `z ∈ Hbar` only charges points of `Hbar` near `z`. -/
theorem foldedCircle_ae_near_frostman {c z : ℂ} (hz : z ∈ Hbar) {r : ℝ} (hr : 0 ≤ r) :
    ∀ᵐ v ∂foldedCircle c r, v ∈ Hbar ∧ ‖v - z‖ ≤ r + ‖c - z‖ := by
  set S : Set ℂ := Metric.closedBall z (r + ‖c - z‖) ∩ Hbar
  have hS : MeasurableSet S := measurableSet_closedBall.inter isClosed_Hbar.measurableSet
  have h0 : foldedCircle c r Sᶜ = 0 := by
    rw [foldedCircle, Measure.map_apply measurable_foldH hS.compl, circleUnif, Measure.smul_apply,
      Measure.map_apply (measurable_circleMap c r) (measurable_foldH hS.compl)]
    have : circleMap c r ⁻¹' (foldH ⁻¹' Sᶜ) = ∅ := by
      ext θ
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
        not_not]
      refine ⟨?_, foldH_mem_Hbar' _⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖foldH (circleMap c r θ) - z‖ ≤ ‖circleMap c r θ - z‖ := norm_foldH_sub_le_frostman hz
        _ = ‖(circleMap c r θ - c) + (c - z)‖ := by ring_nf
        _ ≤ ‖circleMap c r θ - c‖ + ‖c - z‖ := norm_add_le _ _
        _ = r + ‖c - z‖ := by rw [circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg hr]
    rw [this]; simp
  filter_upwards [mem_ae_iff.2 h0] with v hv
  refine ⟨hv.2, ?_⟩
  have := hv.1
  rwa [Metric.mem_closedBall, dist_eq_norm] at this

/-! ## (iv) Random Frostman measures independent of the field -/

end FrostmanReg

end QuantumZipper
