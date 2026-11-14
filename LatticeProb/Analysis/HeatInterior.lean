import Mathlib
import LatticeProb.Analysis.HeatKernel
import LatticeProb.Analysis.HeatMollify

/-!
# Interior regularity of weak solutions of the heat equation

For the operator `L = (2d)⁻¹ Δ` of `LatticeProb.WhiteNoise.contOp` on `ℝ × ℝ ^ d`, a continuous weak
solution `u` of `∂_s u = L u` in an open set `U` is a classical solution in `U`.

The two ingredients taken as hypotheses are the smoothness of the heat kernel off the hyperplane
`x = 0` and the local representation formula of classical solutions by the cutoff kernel.
For a cutoff `ζ` equal to `1` near a point `p₀`, the mollifications of `u` satisfy the representation
formula near `p₀`, and passing to the limit gives it for `u`. The kernel is smooth away from the
support of the derivatives of `ζ`, so `u` coincides near `p₀` with a smooth function. A smooth weak
solution is a classical solution by integration by parts.
-/

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution
open LatticeProb.WhiteNoise

namespace LatticeProb.Heat

namespace Interior

section ByParts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

theorem integral_mul_fderiv_eq_neg {F ψ : E → ℝ} (hF : ContDiff ℝ ∞ F) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (v : E) :
    ∫ x, F x * fderiv ℝ ψ x v ∂μ = -∫ x, fderiv ℝ F x v * ψ x ∂μ := by
  have hFc : Continuous F := hF.continuous
  have hF'c : Continuous fun x => fderiv ℝ F x v := (contDiff_fderiv_apply hF v).continuous
  have hψ'c : Continuous fun x => fderiv ℝ ψ x v := (contDiff_fderiv_apply hψ v).continuous
  have hψ'cs : HasCompactSupport fun x => fderiv ℝ ψ x v := hc.fderiv_apply ℝ v
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun x _ => hF.differentiable (by simp) x) (fun x _ => hψ.differentiable (by simp) x)
  · exact (hF'c.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact (hFc.mul hψ'c).integrable_of_hasCompactSupport hψ'cs.mul_left
  · exact (hFc.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left

theorem integral_mul_fderiv_fderiv_eq {F ψ : E → ℝ} (hF : ContDiff ℝ ∞ F) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (v : E) :
    ∫ x, F x * fderiv ℝ (fun z => fderiv ℝ ψ z v) x v ∂μ =
      ∫ x, fderiv ℝ (fun z => fderiv ℝ F z v) x v * ψ x ∂μ := by
  have h1 : ∫ x, F x * fderiv ℝ (fun z => fderiv ℝ ψ z v) x v ∂μ =
      -∫ x, fderiv ℝ F x v * fderiv ℝ ψ x v ∂μ :=
    integral_mul_fderiv_eq_neg (ψ := fun z => fderiv ℝ ψ z v) hF (contDiff_fderiv_apply hψ v)
      (hc.fderiv_apply ℝ v) v
  have h2 : ∫ x, fderiv ℝ F x v * fderiv ℝ ψ x v ∂μ =
      -∫ x, fderiv ℝ (fun z => fderiv ℝ F z v) x v * ψ x ∂μ :=
    integral_mul_fderiv_eq_neg (F := fun z => fderiv ℝ F z v) (contDiff_fderiv_apply hF v) hψ hc v
  rw [h1, h2, neg_neg]

end ByParts

section Weak

variable {d : ℕ}

theorem integral_mul_spaceOp {F ψ : ℝ × (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ∫ p, F p * spaceOp d ψ p = ∫ p, spaceOp d F p * ψ p := by
  unfold spaceOp
  have hint : ∀ i : Fin d, Integrable (fun p => F p *
      fderiv ℝ (fun z => fderiv ℝ ψ z (spaceDir d i)) p (spaceDir d i)) := fun i =>
    (hF.continuous.mul (contDiff_fderiv_apply (contDiff_fderiv_apply hψ _) _).continuous)
      |>.integrable_of_hasCompactSupport (((hc.fderiv_apply ℝ _).fderiv_apply ℝ _).mul_left)
  have hint' : ∀ i : Fin d, Integrable (fun p =>
      fderiv ℝ (fun z => fderiv ℝ F z (spaceDir d i)) p (spaceDir d i) * ψ p) := fun i =>
    ((contDiff_fderiv_apply (contDiff_fderiv_apply hF _) _).continuous.mul hψ.continuous)
      |>.integrable_of_hasCompactSupport hc.mul_left
  have e1 : ∀ p, F p * ((∑ i : Fin d,
      fderiv ℝ (fun z => fderiv ℝ ψ z (spaceDir d i)) p (spaceDir d i)) / (2 * d)) =
      (∑ i : Fin d, F p * fderiv ℝ (fun z => fderiv ℝ ψ z (spaceDir d i)) p (spaceDir d i)) /
        (2 * d) := fun p => by rw [mul_div_assoc', Finset.mul_sum]
  have e2 : ∀ p, (∑ i : Fin d,
      fderiv ℝ (fun z => fderiv ℝ F z (spaceDir d i)) p (spaceDir d i)) / (2 * d) * ψ p =
      (∑ i : Fin d, fderiv ℝ (fun z => fderiv ℝ F z (spaceDir d i)) p (spaceDir d i) * ψ p) /
        (2 * d) := fun p => by rw [div_mul_eq_mul_div, Finset.sum_mul]
  simp_rw [e1, e2]
  rw [integral_div, integral_div, integral_finsetSum _ fun i _ => hint i,
    integral_finsetSum _ fun i _ => hint' i]
  congr 1
  exact Finset.sum_congr rfl fun i _ => integral_mul_fderiv_fderiv_eq hF hψ hc _

theorem continuous_spaceOp {G : ℝ × (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) :
    Continuous (spaceOp d G) := by
  unfold spaceOp
  exact (continuous_finsetSum _ fun i _ =>
    (contDiff_fderiv_apply (contDiff_fderiv_apply hG _) _).continuous).div_const _

theorem deriv_slice_time_eq {G : ℝ × (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G)
    (p : ℝ × (Fin d → ℝ)) : deriv (fun s => G (s, p.2)) p.1 = fderiv ℝ G p (timeDir d) :=
  (hasDerivAt_slice_time (hG.differentiable (by simp)) p.1 p.2).deriv

theorem contOp_slice_eq {G : ℝ × (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G)
    (p : ℝ × (Fin d → ℝ)) : contOp d (fun x => G (p.1, x)) p.2 = spaceOp d G p := by
  unfold contOp spaceOp
  rw [lap_slice hG p.1 p.2]

theorem deriv_slice_space_eq {G : ℝ × (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G)
    (q : ℝ × (Fin d → ℝ)) (i : Fin d) :
    deriv (fun t => G (q.1, Function.update q.2 i t)) (q.2 i) = fderiv ℝ G q (spaceDir d i) := by
  have h := hasDerivAt_slice_space (hG.differentiable (by simp)) q.1 q.2 i (q.2 i)
  rw [Function.update_eq_self] at h
  exact h.deriv

theorem hasDerivAt_slice_of_weak {B : Set (ℝ × (Fin d → ℝ))} (hB : IsOpen B)
    {F : ℝ × (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hweak : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ B → -∫ p : ℝ × (Fin d → ℝ), F p * deriv (fun s => ψ (s, p.2)) p.1
        = ∫ p : ℝ × (Fin d → ℝ), F p * contOp d (fun x => ψ (p.1, x)) p.2) :
    ∀ p ∈ B, HasDerivAt (fun s => F (s, p.2)) (contOp d (fun x => F (p.1, x)) p.2) p.1 := by
  have hdt : ∀ G : ℝ × (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ G → ∀ p : ℝ × (Fin d → ℝ),
      deriv (fun s => G (s, p.2)) p.1 = fderiv ℝ G p (timeDir d) := fun G hG p =>
    deriv_slice_time_eq hG p
  have hop : ∀ G : ℝ × (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ G → ∀ p : ℝ × (Fin d → ℝ),
      contOp d (fun x => G (p.1, x)) p.2 = spaceOp d G p := fun G hG p => contOp_slice_eq hG p
  have hcont : Continuous fun p => fderiv ℝ F p (timeDir d) - spaceOp d F p := by
    exact (contDiff_fderiv_apply hF _).continuous.sub (continuous_spaceOp hF)
  have hzero : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ B → ∫ p, ψ p • (fderiv ℝ F p (timeDir d) - spaceOp d F p) = 0 := by
    intro ψ hψ hc hsupp
    have h := hweak ψ hψ hc hsupp
    simp_rw [hdt ψ hψ, hop ψ hψ] at h
    have h1 := integral_mul_fderiv_eq_neg (μ := (volume : Measure (ℝ × (Fin d → ℝ)))) hF hψ hc
      (timeDir d)
    have h2 := integral_mul_spaceOp hF hψ hc
    have hi1 : Integrable (fun p => fderiv ℝ F p (timeDir d) * ψ p) :=
      ((contDiff_fderiv_apply hF _).continuous.mul hψ.continuous).integrable_of_hasCompactSupport
        hc.mul_left
    have hi2 : Integrable (fun p => spaceOp d F p * ψ p) :=
      ((continuous_spaceOp hF).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
    simp_rw [smul_eq_mul, mul_sub, integral_sub (hi1.congr (Filter.Eventually.of_forall
      fun p => mul_comm _ _)) (hi2.congr (Filter.Eventually.of_forall fun p => mul_comm _ _))]
    simp_rw [mul_comm (ψ _)]
    linarith
  have hae := hB.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hcont.locallyIntegrable.locallyIntegrableOn _) hzero
  have heq : EqOn (fun p => fderiv ℝ F p (timeDir d) - spaceOp d F p) (fun _ => 0) B :=
    Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hB.measurableSet).2 hae) hB hcont.continuousOn
      continuousOn_const
  intro p hp
  rw [hop F hF p]
  have h := hasDerivAt_slice_time (hF.differentiable (by simp)) p.1 p.2
  have h0 : fderiv ℝ F p (timeDir d) = spaceOp d F p := sub_eq_zero.mp (heq hp)
  rwa [h0] at h

end Weak

section Kernel

variable {d : ℕ}

/-- The cutoff kernel of the representation formula, written as in the representation hypothesis. -/
noncomputable def repK (d : ℕ) (ζ : ℝ × (Fin d → ℝ) → ℝ) (p q : ℝ × (Fin d → ℝ)) : ℝ :=
  heatKernel d (p.1 - q.1) (p.2 - q.2) *
      (deriv (fun s => ζ (s, q.2)) q.1 + contOp d (fun y => ζ (q.1, y)) q.2) +
    (1 / (d : ℝ)) * ∑ i : Fin d,
      deriv (fun t => heatKernel d (p.1 - q.1) (p.2 - Function.update q.2 i t)) (q.2 i) *
        deriv (fun t => ζ (q.1, Function.update q.2 i t)) (q.2 i)

/-- The factor `∂_s ζ + L ζ` of the cutoff kernel. -/
noncomputable def cutT (d : ℕ) (ζ : ℝ × (Fin d → ℝ) → ℝ) (q : ℝ × (Fin d → ℝ)) : ℝ :=
  fderiv ℝ ζ q (timeDir d) + spaceOp d ζ q

/-- The factor `∂_{y_i} ζ` of the cutoff kernel. -/
noncomputable def cutS (d : ℕ) (ζ : ℝ × (Fin d → ℝ) → ℝ) (i : Fin d)
    (q : ℝ × (Fin d → ℝ)) : ℝ :=
  fderiv ℝ ζ q (spaceDir d i)

/-- The cutoff kernel with the heat kernel replaced by a smooth function `Ψ`. -/
noncomputable def smoothK (d : ℕ) (Ψ ζ : ℝ × (Fin d → ℝ) → ℝ) (p q : ℝ × (Fin d → ℝ)) : ℝ :=
  Ψ (p - q) * cutT d ζ q +
    (1 / (d : ℝ)) * ∑ i : Fin d, (-fderiv ℝ Ψ (p - q) (spaceDir d i)) * cutS d ζ i q

theorem fderiv_eq_zero_of_eventually_const {ζ : ℝ × (Fin d → ℝ) → ℝ} {q : ℝ × (Fin d → ℝ)}
    {c : ℝ} (h : ∀ᶠ y in 𝓝 q, ζ y = c) : fderiv ℝ ζ q = 0 := by
  have h' : ζ =ᶠ[𝓝 q] fun _ => c := h
  rw [h'.fderiv_eq]
  simp

theorem spaceOp_eq_zero_of_eventually_const {ζ : ℝ × (Fin d → ℝ) → ℝ} {q : ℝ × (Fin d → ℝ)}
    {c : ℝ} (h : ∀ᶠ y in 𝓝 q, ζ y = c) : spaceOp d ζ q = 0 := by
  have h2 : ∀ v, fderiv ℝ (fun z => fderiv ℝ ζ z v) q v = 0 := fun v => by
    have h3 : (fun z => fderiv ℝ ζ z v) =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [h.eventually_nhds] with z hz
      rw [fderiv_eq_zero_of_eventually_const hz]
      simp
    rw [h3.fderiv_eq]
    simp
  unfold spaceOp
  simp [h2]

theorem cutT_eq_zero {ζ : ℝ × (Fin d → ℝ) → ℝ} {q : ℝ × (Fin d → ℝ)} {c : ℝ}
    (h : ∀ᶠ y in 𝓝 q, ζ y = c) : cutT d ζ q = 0 := by
  unfold cutT
  simp [fderiv_eq_zero_of_eventually_const h, spaceOp_eq_zero_of_eventually_const h]

theorem cutS_eq_zero {ζ : ℝ × (Fin d → ℝ) → ℝ} {q : ℝ × (Fin d → ℝ)} {c : ℝ}
    (h : ∀ᶠ y in 𝓝 q, ζ y = c) (i : Fin d) : cutS d ζ i q = 0 := by
  unfold cutS
  simp [fderiv_eq_zero_of_eventually_const h]

theorem deriv_kernel_slice {Ψ : ℝ × (Fin d → ℝ) → ℝ} (hΨ : Differentiable ℝ Ψ)
    {p q : ℝ × (Fin d → ℝ)} (h : Ψ =ᶠ[𝓝 (p - q)] fun z => heatKernel d z.1 z.2) (i : Fin d) :
    deriv (fun t => heatKernel d (p.1 - q.1) (p.2 - Function.update q.2 i t)) (q.2 i) =
      -fderiv ℝ Ψ (p - q) (spaceDir d i) := by
  set γ : ℝ → ℝ × (Fin d → ℝ) := fun t => (p.1 - q.1, p.2 - Function.update q.2 i t) with hγdef
  have hγ : HasDerivAt γ (0, 0 - Pi.single i (1 : ℝ)) (q.2 i) :=
    (hasDerivAt_const _ (p.1 - q.1)).prodMk
      ((hasDerivAt_const _ p.2).sub (hasDerivAt_update q.2 i (q.2 i)))
  have hγq : γ (q.2 i) = p - q := by
    simp [hγdef, Prod.ext_iff]
  have ht : Filter.Tendsto γ (𝓝 (q.2 i)) (𝓝 (p - q)) := by
    rw [← hγq]
    exact hγ.continuousAt.tendsto
  have hev : (fun t => heatKernel d (p.1 - q.1) (p.2 - Function.update q.2 i t)) =ᶠ[𝓝 (q.2 i)]
      fun t => Ψ (γ t) := (h.comp_tendsto ht).symm
  rw [hev.deriv_eq]
  have : deriv (fun t => Ψ (γ t)) (q.2 i) =
      fderiv ℝ Ψ (γ (q.2 i)) (0, 0 - Pi.single i (1 : ℝ)) :=
    ((hΨ (γ (q.2 i))).hasFDerivAt.comp_hasDerivAt (q.2 i) hγ).deriv
  rw [this, hγq]
  have hv : ((0 : ℝ), (0 : Fin d → ℝ) - Pi.single i (1 : ℝ)) = -spaceDir d i := by
    simp [spaceDir]
  rw [hv, map_neg]

/-- The cutoff kernel is the smooth cutoff kernel when `Ψ` agrees with the heat kernel near
`p - q` or when the cutoff is locally constant at `q`. -/
theorem repK_eq_smoothK {Ψ ζ : ℝ × (Fin d → ℝ) → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hζ : ContDiff ℝ ∞ ζ)
    {p q : ℝ × (Fin d → ℝ)}
    (h : (∃ c, ∀ᶠ y in 𝓝 q, ζ y = c) ∨ Ψ =ᶠ[𝓝 (p - q)] fun z => heatKernel d z.1 z.2) :
    repK d ζ p q = smoothK d Ψ ζ p q := by
  have e1 : deriv (fun s => ζ (s, q.2)) q.1 + contOp d (fun y => ζ (q.1, y)) q.2 = cutT d ζ q := by
    rw [deriv_slice_time_eq hζ, contOp_slice_eq hζ]
    rfl
  have e2 : ∀ i, deriv (fun t => ζ (q.1, Function.update q.2 i t)) (q.2 i) = cutS d ζ i q :=
    fun i => deriv_slice_space_eq hζ q i
  unfold repK smoothK
  rw [e1]
  simp_rw [e2]
  rcases h with ⟨c, hc⟩ | h
  · simp [cutT_eq_zero hc, cutS_eq_zero hc]
  · have h0 : heatKernel d (p.1 - q.1) (p.2 - q.2) = Ψ (p - q) := h.eq_of_nhds.symm
    rw [h0]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [deriv_kernel_slice (hΨ.differentiable (by simp)) h]

theorem continuous_cutT {ζ : ℝ × (Fin d → ℝ) → ℝ} (hζ : ContDiff ℝ ∞ ζ) :
    Continuous (cutT d ζ) :=
  (contDiff_fderiv_apply hζ _).continuous.add (continuous_spaceOp hζ)

theorem continuous_cutS {ζ : ℝ × (Fin d → ℝ) → ℝ} (hζ : ContDiff ℝ ∞ ζ) (i : Fin d) :
    Continuous (cutS d ζ i) :=
  (contDiff_fderiv_apply hζ _).continuous

theorem hasCompactSupport_cutT {ζ : ℝ × (Fin d → ℝ) → ℝ} (hζc : HasCompactSupport ζ) :
    HasCompactSupport (cutT d ζ) :=
  HasCompactSupport.intro hζc fun _ hq =>
    cutT_eq_zero (c := 0) (notMem_tsupport_iff_eventuallyEq.1 hq)

theorem hasCompactSupport_cutS {ζ : ℝ × (Fin d → ℝ) → ℝ} (hζc : HasCompactSupport ζ) (i : Fin d) :
    HasCompactSupport (cutS d ζ i) :=
  HasCompactSupport.intro hζc fun _ hq =>
    cutS_eq_zero (c := 0) (notMem_tsupport_iff_eventuallyEq.1 hq) i

/-- The convolution of a continuous function with a smooth compactly supported kernel is smooth. -/
theorem contDiff_integral_mul_comp_sub {f Ψ' : ℝ × (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hΨ : ContDiff ℝ ∞ Ψ') (hc : HasCompactSupport Ψ') :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin d → ℝ) => ∫ q, f q * Ψ' (p - q)) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable hΨ

/-- The cutoff kernel integrated against a continuous function is smooth in `p`. -/
theorem contDiff_integral_smoothK {Ψ ζ w : ℝ × (Fin d → ℝ) → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hΨc : HasCompactSupport Ψ) (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (hw : Continuous w) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin d → ℝ) => ∫ q, smoothK d Ψ ζ p q * w q) := by
  have hΨ' : ∀ i : Fin d, ContDiff ℝ ∞ (fun z => -fderiv ℝ Ψ z (spaceDir d i)) := fun i =>
    (contDiff_fderiv_apply hΨ _).neg
  have hΨ'c : ∀ i : Fin d, HasCompactSupport (fun z => -fderiv ℝ Ψ z (spaceDir d i)) := fun i =>
    (hΨc.fderiv_apply ℝ _).neg
  have hT : HasCompactSupport (fun q => cutT d ζ q * w q) :=
    (hasCompactSupport_cutT hζc).mul_right
  have hS : ∀ i : Fin d, HasCompactSupport (fun q => cutS d ζ i q * w q) := fun i =>
    (hasCompactSupport_cutS hζc i).mul_right
  have hTc : Continuous (fun q => cutT d ζ q * w q) := (continuous_cutT hζ).mul hw
  have hSc : ∀ i : Fin d, Continuous (fun q => cutS d ζ i q * w q) := fun i =>
    (continuous_cutS hζ i).mul hw
  have hpt : ∀ p q, smoothK d Ψ ζ p q * w q = (cutT d ζ q * w q) * Ψ (p - q) +
      (1 / (d : ℝ)) * ∑ i : Fin d, (cutS d ζ i q * w q) * (-fderiv ℝ Ψ (p - q) (spaceDir d i)) := by
    intro p q
    unfold smoothK
    rw [add_mul, mul_assoc (1 / (d : ℝ)), Finset.sum_mul]
    congr 1
    · ring
    · congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
  have hi1 : ∀ p, Integrable (fun q => (cutT d ζ q * w q) * Ψ (p - q)) := fun p =>
    (hTc.mul (hΨ.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hT.mul_right
  have hi2 : ∀ p, ∀ i : Fin d, Integrable (fun q =>
      (cutS d ζ i q * w q) * (-fderiv ℝ Ψ (p - q) (spaceDir d i))) := fun p i =>
    (( hSc i).mul ((hΨ' i).continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (hS i).mul_right
  have heq : (fun p : ℝ × (Fin d → ℝ) => ∫ q, smoothK d Ψ ζ p q * w q) = fun p =>
      (∫ q, (cutT d ζ q * w q) * Ψ (p - q)) +
        (1 / (d : ℝ)) * ∑ i : Fin d,
          ∫ q, (cutS d ζ i q * w q) * (-fderiv ℝ Ψ (p - q) (spaceDir d i)) := by
    funext p
    simp_rw [hpt]
    rw [integral_add (hi1 p) ((integrable_finsetSum _ fun i _ => hi2 p i).const_mul _),
      integral_const_mul, integral_finsetSum _ fun i _ => hi2 p i]
  rw [heq]
  exact (contDiff_integral_mul_comp_sub hTc hΨ hΨc).add (contDiff_const.mul
    (ContDiff.sum fun i _ => contDiff_integral_mul_comp_sub (hSc i) (hΨ' i) (hΨ'c i)))

end Kernel

section Limit

variable {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

/-- Integrals against a continuous compactly supported weight pass to the limit under uniform
convergence on the support. -/
theorem tendsto_integral_mul_of_tendstoUniformlyOn {C : Set X} (hC : IsCompact C)
    {k : X → ℝ} (hk : Continuous k) (hkC : ∀ q, q ∉ C → k q = 0) {wn : ℕ → X → ℝ} {w : X → ℝ}
    (hwn : ∀ᶠ n in atTop, ContinuousOn (wn n) C) (hw : ContinuousOn w C)
    (hu : TendstoUniformlyOn wn w atTop C) :
    Tendsto (fun n => ∫ q, k q * wn n q ∂μ) atTop (𝓝 (∫ q, k q * w q ∂μ)) := by
  have hsupp : ∀ f : X → ℝ, (∀ q, q ∉ C → f q = 0) → Function.support f ⊆ C := fun f hf q hq => by
    by_contra hqC
    exact hq (hf q hqC)
  have hint : ∀ v : X → ℝ, ContinuousOn v C → Integrable (fun q => k q * v q) μ := by
    intro v hv
    have h : IntegrableOn (fun q => k q * v q) C μ :=
      (hk.continuousOn.mul hv).integrableOn_compact hC
    exact (integrableOn_iff_integrable_of_support_subset
      (hsupp _ fun q hq => by simp [hkC q hq])).1 h
  have hk1 : Integrable k μ :=
    (integrableOn_iff_integrable_of_support_subset (hsupp _ hkC)).1
      (hk.continuousOn.integrableOn_compact hC)
  set M : ℝ := ∫ q, |k q| ∂μ with hM
  have hM0 : 0 ≤ M := integral_nonneg fun q => abs_nonneg _
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hη : 0 < ε / (M + 1) := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu _ hη, hwn] with n hn hwn'
  rw [Real.dist_eq, ← integral_sub (hint _ hwn') (hint _ hw)]
  have hle : ‖∫ q, (k q * wn n q - k q * w q) ∂μ‖ ≤ ∫ q, ε / (M + 1) * |k q| ∂μ := by
    refine norm_integral_le_of_norm_le (hk1.abs.const_mul _) (Eventually.of_forall fun q => ?_)
    by_cases hq : q ∈ C
    · rw [Real.norm_eq_abs, ← mul_sub, abs_mul, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have := hn q hq
      rw [Real.dist_eq, abs_sub_comm] at this
      exact this.le
    · simp [hkC q hq]
  rw [integral_const_mul] at hle
  rw [← Real.norm_eq_abs]
  refine lt_of_le_of_lt hle ?_
  rw [← hM, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

end Limit


section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A function smooth away from the origin is a smooth function with compact support on the
annulus `a ≤ ‖z‖ ≤ b`, after multiplication with a cutoff that vanishes near the origin. -/
theorem exists_smooth_cutoff_kernel {Φ : E → ℝ} (hΦ : ∀ z : E, z ≠ 0 → ContDiffAt ℝ ∞ Φ z)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ Ψ : E → ℝ, ContDiff ℝ ∞ Ψ ∧ HasCompactSupport Ψ ∧
      ∀ z : E, a ≤ ‖z‖ → ‖z‖ ≤ b → Ψ =ᶠ[𝓝 z] Φ := by
  have hb : 0 < b := ha.trans hab
  obtain ⟨big, hbi, hbo⟩ : ∃ f : ContDiffBump (0 : E), f.rIn = b + 1 ∧ f.rOut = b + 2 :=
    ⟨⟨b + 1, b + 2, by linarith, by linarith⟩, rfl, rfl⟩
  obtain ⟨small, hsi, hso⟩ : ∃ f : ContDiffBump (0 : E), f.rIn = a / 4 ∧ f.rOut = a / 2 :=
    ⟨⟨a / 4, a / 2, by positivity, by linarith⟩, rfl, rfl⟩
  refine ⟨fun z => big z * (1 - small z) * Φ z, ?_, ?_, fun z hza hzb => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z = 0
    · subst hz
      have h0 : (fun z => big z * (1 - small z) * Φ z) =ᶠ[𝓝 (0 : E)] fun _ => 0 := by
        filter_upwards [closedBall_mem_nhds (0 : E) (show 0 < a / 4 by positivity)] with y hy
        rw [small.one_of_mem_closedBall (by rwa [hsi])]
        simp
      exact contDiffAt_const.congr_of_eventuallyEq h0
    · exact ((big.contDiff.contDiffAt).mul
        (contDiffAt_const.sub small.contDiff.contDiffAt)).mul (hΦ z hz)
  · exact big.hasCompactSupport.mul_right.mul_right
  · have h1 : ∀ᶠ y in 𝓝 z, big y = 1 := by
      filter_upwards [isOpen_ball.mem_nhds (show z ∈ ball (0 : E) (b + 1) by
        rw [mem_ball_zero_iff]; linarith)] with y hy
      exact big.one_of_mem_closedBall (by rw [hbi]; exact ball_subset_closedBall hy)
    have h2 : ∀ᶠ y in 𝓝 z, small y = 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
        (show a / 2 < ‖z‖ by linarith)] with y hy
      refine small.zero_of_le_dist ?_
      rw [hso, dist_zero_right]
      exact hy.le
    filter_upwards [h1, h2] with y hy1 hy2
    simp [hy1, hy2]

/-- A smooth cutoff with compact support in `closedBall p₀ R`, equal to `1` on the half ball. -/
theorem exists_cutoff (p₀ : E) {R : ℝ} (hR : 0 < R) :
    ∃ ζ : E → ℝ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ closedBall p₀ R ∧
      ∀ q ∈ closedBall p₀ (R / 2), ζ q = 1 := by
  obtain ⟨f, hin, hout⟩ : ∃ f : ContDiffBump p₀, f.rIn = R / 2 ∧ f.rOut = R :=
    ⟨⟨R / 2, R, by positivity, by linarith⟩, rfl, rfl⟩
  refine ⟨f, f.contDiff, f.hasCompactSupport, ?_, fun q hq => ?_⟩
  · rw [f.tsupport_eq, hout]
  · exact f.one_of_mem_closedBall (by rwa [hin])

/-- A sequence of smooth nonnegative mollifiers of integral one with shrinking supports. -/
theorem exists_mollifier_seq [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] :
    ∃ (ε : ℕ → ℝ) (ρ : ℕ → E → ℝ), (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ρ n) ∧ HasCompactSupport (ρ n) ∧
        tsupport (ρ n) ⊆ closedBall 0 (ε n) ∧ (∀ x, 0 ≤ ρ n x) ∧ ∫ x, ρ n x ∂μ = 1 := by
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose f hf using fun n : ℕ =>
    (show ∃ f : ContDiffBump (0 : E), f.rIn = 1 / ((n : ℝ) + 1) / 2 ∧ f.rOut = 1 / ((n : ℝ) + 1) from
      ⟨⟨_, _, by have := hε n; positivity, by have := hε n; linarith⟩, rfl, rfl⟩)
  refine ⟨fun n => 1 / ((n : ℝ) + 1), fun n => (f n).normed μ, hε,
    tendsto_one_div_add_atTop_nhds_zero_nat, fun n => ⟨(f n).contDiff_normed,
      (f n).hasCompactSupport_normed, ?_, fun x => (f n).nonneg_normed x, (f n).integral_normed⟩⟩
  rw [(f n).tsupport_normed_eq, (hf n).2]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Compact subsets of an open set have an open neighbourhood whose small closed balls stay in it. -/
theorem exists_open_thickening {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ δ > 0, ∃ O : Set E, IsOpen O ∧ K ⊆ O ∧ ∀ ε, ε ≤ δ → ∀ p ∈ O, closedBall p ε ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨δ / 2, half_pos hδ, thickening (δ / 2) K, isOpen_thickening,
    self_subset_thickening (half_pos hδ) K, fun ε hε p hp y hy => ?_⟩
  obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.1 hp
  refine hsub (closedBall_subset_cthickening hz δ ?_)
  rw [mem_closedBall] at hy ⊢
  linarith [dist_triangle y p z]

end Cutoff

section Local

variable {d : ℕ}

theorem exists_classical_approx {U K : Set (ℝ × (Fin d → ℝ))} (hU : IsOpen U)
    {u : ℝ × (Fin d → ℝ) → ℝ} (hu : ContinuousOn u U) (hweak : IsWeakHeat d U u)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (un : ℕ → ℝ × (Fin d → ℝ) → ℝ) (O : Set (ℝ × (Fin d → ℝ))), IsOpen O ∧ K ⊆ O ∧
      (∀ᶠ n in atTop, IsClassicalHeat d O (un n)) ∧
      ∀ C : Set (ℝ × (Fin d → ℝ)), IsCompact C → C ⊆ U →
        TendstoUniformlyOn un u atTop C := by
  obtain ⟨ε, ρ, hε, hεt, hρ⟩ := exists_mollifier_seq (volume : Measure (ℝ × (Fin d → ℝ)))
  obtain ⟨hcl, hconv⟩ := heat_mollify d U u ε ρ hU hu hweak hε hεt hρ
  obtain ⟨δ, hδ, O, hO, hKO, hOsub⟩ := exists_open_thickening hU hK hKU
  refine ⟨fun n => convolution (U.indicator u) (ρ n) (ContinuousLinearMap.mul ℝ ℝ) volume, O, hO,
    hKO, ?_, hconv⟩
  filter_upwards [hεt.eventually (eventually_le_nhds hδ)] with n hn
  exact ⟨(hcl n).1.mono fun p hp => hOsub _ hn p hp,
    fun p hp => (hcl n).2 p (hOsub _ hn p hp)⟩

/-- Near every point of `U`, a continuous weak solution coincides with a smooth function. -/
theorem exists_smooth_local
    (hΦ : ∀ z : ℝ × (Fin d → ℝ), z ≠ 0 →
      ContDiffAt ℝ ∞ (fun z : ℝ × (Fin d → ℝ) => heatKernel d z.1 z.2) z)
    (hrep : ∀ O : Set (ℝ × (Fin d → ℝ)), IsOpen O → ∀ ζ w : ℝ × (Fin d → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ O → IsClassicalHeat d O w →
        ∀ p : ℝ × (Fin d → ℝ), (∀ᶠ q in 𝓝 p, ζ q = 1) →
          w p = ∫ q : ℝ × (Fin d → ℝ), repK d ζ p q * w q)
    {U : Set (ℝ × (Fin d → ℝ))} (hU : IsOpen U) {u : ℝ × (Fin d → ℝ) → ℝ} (hu : Continuous u)
    (hweak : IsWeakHeat d U u) {p₀ : ℝ × (Fin d → ℝ)} (hp₀ : p₀ ∈ U) :
    ∃ B : Set (ℝ × (Fin d → ℝ)), IsOpen B ∧ p₀ ∈ B ∧ B ⊆ U ∧
      ∃ F : ℝ × (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ F ∧ ∀ p ∈ B, u p = F p := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU p₀ hp₀
  set R : ℝ := r / 2 with hRdef
  have hR : 0 < R := by positivity
  have hKU : closedBall p₀ R ⊆ U :=
    (closedBall_subset_ball (by rw [hRdef]; linarith)).trans hrU
  have hKc : IsCompact (closedBall p₀ R) := isCompact_closedBall _ _
  obtain ⟨ζ, hζ, hζc, hζsub, hζ1⟩ := exists_cutoff p₀ hR
  obtain ⟨Ψ, hΨ, hΨc, hΨev⟩ := exists_smooth_cutoff_kernel hΦ (a := R / 4) (b := 5 * R / 4)
    (by positivity) (by linarith)
  obtain ⟨un, O, hO, hKO, hcl, hconv⟩ := exists_classical_approx hU hu.continuousOn hweak hKc hKU
  have hBK : ball p₀ (R / 4) ⊆ closedBall p₀ R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  refine ⟨ball p₀ (R / 4), isOpen_ball, mem_ball_self (by positivity),
    (hBK.trans hKU), fun p => ∫ q, smoothK d Ψ ζ p q * u q,
    contDiff_integral_smoothK hΨ hΨc hζ hζc hu, fun p hp => ?_⟩
  have hpK : p ∈ closedBall p₀ R := hBK hp
  have hpN : ∀ᶠ q in 𝓝 p, ζ q = 1 := by
    filter_upwards [isOpen_ball.mem_nhds (show p ∈ ball p₀ (R / 2) from
      ball_subset_ball (by linarith) hp)] with y hy
    exact hζ1 y (ball_subset_closedBall hy)
  have hpt : ∀ q, repK d ζ p q = smoothK d Ψ ζ p q := by
    intro q
    refine repK_eq_smoothK hΨ hζ ?_
    by_cases hq : q ∈ tsupport ζ
    · by_cases hqN : q ∈ ball p₀ (R / 2)
      · left
        refine ⟨1, ?_⟩
        filter_upwards [isOpen_ball.mem_nhds hqN] with y hy
        exact hζ1 y (ball_subset_closedBall hy)
      · right
        have h1 : R / 2 ≤ dist q p₀ := not_lt.1 (by rwa [mem_ball] at hqN)
        have h2 : dist p p₀ < R / 4 := hp
        have h3 : dist q p₀ ≤ R := hζsub hq
        refine hΨev (p - q) ?_ ?_
        · rw [← dist_eq_norm]
          linarith [dist_triangle q p p₀, dist_comm p q]
        · rw [← dist_eq_norm]
          linarith [dist_triangle p p₀ q, dist_comm p₀ q, dist_comm q p₀]
    · left
      exact ⟨0, notMem_tsupport_iff_eventuallyEq.1 hq⟩
  have hkc : Continuous fun q => smoothK d Ψ ζ p q := by
    unfold smoothK
    refine Continuous.add ?_ (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_))
    · exact (hΨ.continuous.comp (continuous_const.sub continuous_id)).mul (continuous_cutT hζ)
    · exact ((contDiff_fderiv_apply hΨ _).continuous.comp
        (continuous_const.sub continuous_id)).neg.mul (continuous_cutS hζ i)
  have hkC : ∀ q, q ∉ closedBall p₀ R → smoothK d Ψ ζ p q = 0 := by
    intro q hq
    have h0 : ∀ᶠ y in 𝓝 q, ζ y = 0 :=
      notMem_tsupport_iff_eventuallyEq.1 fun h => hq (hζsub h)
    unfold smoothK
    simp [cutT_eq_zero h0, cutS_eq_zero h0]
  have hlim := tendsto_integral_mul_of_tendstoUniformlyOn (μ := volume) hKc hkc hkC
    (wn := un) (w := u) (hcl.mono fun n hn => hn.1.continuousOn.mono hKO)
    hu.continuousOn (hconv _ hKc hKU)
  have hpe : ∀ᶠ n in atTop, un n p = ∫ q, smoothK d Ψ ζ p q * un n q := by
    filter_upwards [hcl] with n hn
    have := hrep O hO ζ (un n) hζ hζc (hζsub.trans (hKO |> fun h => (subset_refl _).trans h)) hn p hpN
    simpa only [hpt] using this
  exact tendsto_nhds_unique ((hconv _ hKc hKU).tendsto_at hpK) (hlim.congr' (hpe.mono fun n hn => hn.symm))


theorem isClassicalHeat_of_local {U : Set (ℝ × (Fin d → ℝ))} {u : ℝ × (Fin d → ℝ) → ℝ}
    (hweak : IsWeakHeat d U u)
    (hloc : ∀ p₀ ∈ U, ∃ B : Set (ℝ × (Fin d → ℝ)), IsOpen B ∧ p₀ ∈ B ∧ B ⊆ U ∧
      ∃ F : ℝ × (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ F ∧ ∀ p ∈ B, u p = F p) :
    IsClassicalHeat d U u := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨B, hB, hpB, -, F, hF, hFu⟩ := hloc p hp
    have hev : u =ᶠ[𝓝 p] F := Filter.eventuallyEq_of_mem (hB.mem_nhds hpB) hFu
    exact (hF.contDiffAt.congr_of_eventuallyEq hev).contDiffWithinAt
  · obtain ⟨B, hB, hpB, hBU, F, hF, hFu⟩ := hloc p hp
    have hFweak : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ B → -∫ q : ℝ × (Fin d → ℝ), F q * deriv (fun s => ψ (s, q.2)) q.1
          = ∫ q : ℝ × (Fin d → ℝ), F q * contOp d (fun x => ψ (q.1, x)) q.2 := by
      intro ψ hψ hc hsupp
      have h := hweak ψ hψ hc (hsupp.trans hBU)
      have e1 : ∀ q, u q * deriv (fun s => ψ (s, q.2)) q.1 = F q * deriv (fun s => ψ (s, q.2)) q.1 := by
        intro q
        by_cases hq : q ∈ B
        · rw [hFu q hq]
        · have h0 : ∀ᶠ y in 𝓝 q, ψ y = 0 :=
            notMem_tsupport_iff_eventuallyEq.1 fun hh => hq (hsupp hh)
          rw [deriv_slice_time_eq hψ, fderiv_eq_zero_of_eventually_const h0]
          simp
      have e2 : ∀ q, u q * contOp d (fun x => ψ (q.1, x)) q.2 =
          F q * contOp d (fun x => ψ (q.1, x)) q.2 := by
        intro q
        by_cases hq : q ∈ B
        · rw [hFu q hq]
        · have h0 : ∀ᶠ y in 𝓝 q, ψ y = 0 :=
            notMem_tsupport_iff_eventuallyEq.1 fun hh => hq (hsupp hh)
          rw [contOp_slice_eq hψ, spaceOp_eq_zero_of_eventually_const h0]
          simp
      simp_rw [e1, e2] at h
      exact h
    have hd := hasDerivAt_slice_of_weak hB hF hFweak p hpB
    have hev : u =ᶠ[𝓝 p] F := Filter.eventuallyEq_of_mem (hB.mem_nhds hpB) hFu
    have hev1 : (fun s => u (s, p.2)) =ᶠ[𝓝 p.1] fun s => F (s, p.2) :=
      hev.comp_tendsto (show Tendsto (fun s : ℝ => (s, p.2)) (𝓝 p.1) (𝓝 p) from
        (continuous_id.prodMk continuous_const).continuousAt.tendsto)
    have hev2 : (fun x => u (p.1, x)) =ᶠ[𝓝 p.2] fun x => F (p.1, x) :=
      hev.comp_tendsto (show Tendsto (fun x : Fin d → ℝ => (p.1, x)) (𝓝 p.2) (𝓝 p) from
        (continuous_const.prodMk continuous_id).continuousAt.tendsto)
    have hc : contOp d (fun x => u (p.1, x)) p.2 = contOp d (fun x => F (p.1, x)) p.2 := by
      unfold contOp
      rw [lap_congr_of_eventuallyEq hev2]
    rw [hc]
    exact hd.congr_of_eventuallyEq hev1


/-- In dimension `d = 0` the equation says that the solution is locally constant. -/
theorem isClassicalHeat_zero {U : Set (ℝ × (Fin 0 → ℝ))} (hU : IsOpen U)
    {u : ℝ × (Fin 0 → ℝ) → ℝ} (hu : Continuous u) (hweak : IsWeakHeat 0 U u) :
    IsClassicalHeat 0 U u := by
  have hop : ∀ (φ : (Fin 0 → ℝ) → ℝ) (x : Fin 0 → ℝ), contOp 0 φ x = 0 := fun φ x => by
    simp [contOp]
  have hlocc : ∀ p₀ ∈ U, ∃ R > 0, ∀ q ∈ ball p₀ R, u q = u p₀ := by
    intro p₀ hp₀
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU p₀ hp₀
    have hR : 0 < r / 2 := by positivity
    have hKU : closedBall p₀ (r / 2) ⊆ U :=
      (closedBall_subset_ball (by linarith)).trans hrU
    have hKc : IsCompact (closedBall p₀ (r / 2)) := isCompact_closedBall _ _
    obtain ⟨un, O, hO, hKO, hcl, hconv⟩ :=
      exists_classical_approx hU hu.continuousOn hweak hKc hKU
    refine ⟨r / 2, hR, fun q hq => ?_⟩
    have hconst : ∀ᶠ n in atTop, un n q = un n p₀ := by
      filter_upwards [hcl] with n hn
      have hball : ball p₀ (r / 2) ⊆ O := ball_subset_closedBall.trans hKO
      refine isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball _ _).isPreconnected
        ((hn.1.differentiableOn (by simp)).mono hball) (fun z hz => ?_) hq (mem_ball_self hR)
      have hzO : z ∈ O := hball hz
      have hdiff : DifferentiableAt ℝ (un n) z :=
        (hn.1.contDiffAt (hO.mem_nhds hzO)).differentiableAt (by simp)
      have hd' : HasDerivAt (fun s => un n (s, z.2)) (fderiv ℝ (un n) z (timeDir 0)) z.1 :=
        hdiff.hasFDerivAt.comp_hasDerivAt z.1
          ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
      have h0 : fderiv ℝ (un n) z (timeDir 0) = 0 := by
        have := hd'.unique (hn.2 z hzO)
        rw [this, hop]
      refine ContinuousLinearMap.ext fun v => ?_
      have hv : v = v.1 • timeDir 0 := Prod.ext (by simp [timeDir]) (Subsingleton.elim _ _)
      rw [hv, map_smul, h0]
      simp
    have hq' : q ∈ closedBall p₀ (r / 2) := ball_subset_closedBall hq
    have T1 := ((hconv _ hKc hKU).tendsto_at hq').congr' hconst
    exact tendsto_nhds_unique T1 ((hconv _ hKc hKU).tendsto_at (mem_closedBall_self hR.le))
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨R, hR, hc⟩ := hlocc p hp
    have hev : u =ᶠ[𝓝 p] fun _ => u p := Filter.mem_of_superset (ball_mem_nhds p hR) hc
    exact (contDiffAt_const.congr_of_eventuallyEq hev).contDiffWithinAt
  · obtain ⟨R, hR, hc⟩ := hlocc p hp
    have hev : u =ᶠ[𝓝 p] fun _ => u p := Filter.mem_of_superset (ball_mem_nhds p hR) hc
    have hs : (fun s => u (s, p.2)) =ᶠ[𝓝 p.1] fun _ => u p :=
      hev.comp_tendsto (show Tendsto (fun s : ℝ => (s, p.2)) (𝓝 p.1) (𝓝 p) from
        (continuous_id.prodMk continuous_const).continuousAt.tendsto)
    rw [hop]
    exact (hasDerivAt_const _ _).congr_of_eventuallyEq hs

/-- The heat kernel is smooth away from the origin of space-time, given its smoothness off `x = 0`. -/
theorem contDiffAt_heatKernel_of_ne_zero (hd : 1 ≤ d)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => heatKernel d p.1 p.2)
      {p | p.2 ≠ 0}) (z : ℝ × (Fin d → ℝ)) (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : ℝ × (Fin d → ℝ) => heatKernel d z.1 z.2) z := by
  by_cases h2 : z.2 = 0
  · have h1 : z.1 ≠ 0 := fun h1 => hz (Prod.ext h1 h2)
    rcases lt_or_gt_of_ne h1 with h1 | h1
    · have hev : (fun z : ℝ × (Fin d → ℝ) => heatKernel d z.1 z.2) =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds
          (show z.1 < 0 from h1)] with y hy
        exact heatKernel_of_nonpos hy.le _
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact (contDiffOn_heatKernel hd).contDiffAt
        ((isOpen_lt continuous_const continuous_fst).mem_nhds (show 0 < z.1 from h1))
  · exact hA.contDiffAt ((isOpen_ne_fun continuous_snd continuous_const).mem_nhds h2)

end Local

end Interior

/-- **Regularity of continuous weak solutions of the heat equation.** If the heat kernel is smooth
off the hyperplane `x = 0` and classical solutions satisfy the local representation formula by the
cutoff kernel, then every continuous weak solution of `∂_s u = (2d)⁻¹ Δ u` in an open set `U` is a
classical solution in `U`. -/
theorem heatWeakRegularity_of_representation
    (hA : ∀ d : ℕ, 1 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => heatKernel d p.1 p.2)
      {p | p.2 ≠ 0})
    (hR : ∀ (d : ℕ), 1 ≤ d → ∀ (O : Set (ℝ × (Fin d → ℝ))), IsOpen O →
      ∀ (ζ w : ℝ × (Fin d → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ O → IsClassicalHeat d O w → ∀ p : ℝ × (Fin d → ℝ), (∀ᶠ q in 𝓝 p, ζ q = 1) →
          w p = ∫ q : ℝ × (Fin d → ℝ),
            (heatKernel d (p.1 - q.1) (p.2 - q.2) *
                (deriv (fun s => ζ (s, q.2)) q.1 + contOp d (fun y => ζ (q.1, y)) q.2) +
              (1 / (d : ℝ)) * ∑ i : Fin d,
                deriv (fun t => heatKernel d (p.1 - q.1) (p.2 - Function.update q.2 i t)) (q.2 i) *
                  deriv (fun t => ζ (q.1, Function.update q.2 i t)) (q.2 i)) * w q) :
    ∀ (d : ℕ) (U : Set (ℝ × (Fin d → ℝ))), IsOpen U → ∀ u : ℝ × (Fin d → ℝ) → ℝ, Continuous u →
      IsWeakHeat d U u → ∃ v : ℝ × (Fin d → ℝ) → ℝ, IsClassicalHeat d U v ∧ ∀ p ∈ U, u p = v p := by
  intro d U hU u hu hweak
  refine ⟨u, ?_, fun _ _ => rfl⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Interior.isClassicalHeat_zero hU hu hweak
  · refine Interior.isClassicalHeat_of_local hweak fun p₀ hp₀ => ?_
    exact Interior.exists_smooth_local (Interior.contDiffAt_heatKernel_of_ne_zero hd (hA d hd))
      (fun O hO ζ w hζ hζc hsub hw p hp => hR d hd O hO ζ w hζ hζc hsub hw p hp) hU hu hweak hp₀

/-- **Interior regularity of weak solutions of the heat equation (Parking form).** Under the same two
hypotheses, a continuous weak solution of `∂_s u = (2d)⁻¹ Δ u` in an open set `U ⊆ {s > 0}` against
the space-time test functions agrees on `U` with a classical solution. -/
theorem heatInteriorRegularity_of_representation
    (hA : ∀ d : ℕ, 1 ≤ d → ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => heatKernel d p.1 p.2)
      {p | p.2 ≠ 0})
    (hR : ∀ (d : ℕ), 1 ≤ d → ∀ (O : Set (ℝ × (Fin d → ℝ))), IsOpen O →
      ∀ (ζ w : ℝ × (Fin d → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ O → IsClassicalHeat d O w → ∀ p : ℝ × (Fin d → ℝ), (∀ᶠ q in 𝓝 p, ζ q = 1) →
          w p = ∫ q : ℝ × (Fin d → ℝ),
            (heatKernel d (p.1 - q.1) (p.2 - q.2) *
                (deriv (fun s => ζ (s, q.2)) q.1 + contOp d (fun y => ζ (q.1, y)) q.2) +
              (1 / (d : ℝ)) * ∑ i : Fin d,
                deriv (fun t => heatKernel d (p.1 - q.1) (p.2 - Function.update q.2 i t)) (q.2 i) *
                  deriv (fun t => ζ (q.1, Function.update q.2 i t)) (q.2 i)) * w q) :
    ∀ (d : ℕ) (U : Set (ℝ × (Fin d → ℝ))), IsOpen U →
      U ⊆ {p : ℝ × (Fin d → ℝ) | 0 < p.1} →
      ∀ u : ℝ × (Fin d → ℝ) → ℝ, Continuous u →
        (∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ → tsupport ψ ⊆ U →
          -∫ p : ℝ × (Fin d → ℝ), u p * deriv (fun s => ψ (s, p.2)) p.1
            = ∫ p : ℝ × (Fin d → ℝ), u p * contOp d (fun x => ψ (p.1, x)) p.2) →
        ∃ v : ℝ × (Fin d → ℝ) → ℝ,
          ContDiffOn ℝ (⊤ : ℕ∞) v U ∧
          (∀ p ∈ U, u p = v p) ∧
          (∀ p ∈ U, HasDerivAt (fun s => v (s, p.2))
            (contOp d (fun x => v (p.1, x)) p.2) p.1) := by
  intro d U hU hUpos u hu hw
  obtain ⟨v, ⟨h1, h2⟩, h3⟩ := heatWeakRegularity_of_representation hA hR d U hU u hu
    fun ψ hψ hc hs => hw ψ ⟨hψ, hc, fun p hp => hUpos (hs hp)⟩ hs
  exact ⟨v, h1, h3, h2⟩

end LatticeProb.Heat
