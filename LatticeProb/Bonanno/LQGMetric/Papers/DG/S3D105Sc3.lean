/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3D105Sc3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Mu2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.CircleKernel

/-!
# D105 packet P7, part 1: `ĥ_δ` as a continuous field; its circle averages

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`: `ĥ_t` (3.1), DG:907–917
(`ĥ_t(z) = √π ∫_{t²}^1 ∫ p_{s/2}(z, w) W(dw, ds)`); Lemma 3.3 (`lem-measure-scale`, DG:1014–1036),
whose weight `e^{γ ĥ_δ(δ·+b)}` is the continuous field `ĥ_δ`. Decision D105 (decisions/DEC-105.md
§3 N6).

* `hatDelta W P δ := phiVer W P δ 1`: the continuous version of `ĥ_δ` (DDDF's `φ_{δ,1}` is the same
  white-noise integral, `WhiteNoise.phi`, `Field/WhiteNoisePhi.lean`; `Icc` vs `Ioc` in time is a
  null set).
* `integral_phiKernelL2_circle`: the `L²`-Bochner circle average of the kernels of `ĥ_δ(x)` is the
  kernel of `ĥ_δ(σ_{z,r})` (`hatMeasKerIL2 (δ²,1] σ_{z,r}`, used by `dgHatCoarse`).
* **`ae_circleAvg_hatDelta`**: a.s. `∫ ĥ_δ dσ_{z,r} = dgHatCoarse W δ z r`
  (stochastic Fubini `ae_integral_eq_wn`, as in `dg_lemma31_hU_hat_circ`).

Own elementary glue (stochastic Fubini plus a kernel identity; DG use it implicitly at DG:1010).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DG

open WhiteNoise KilledHeat GFFExist DZZ GMCIdent QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the continuous version of `ĥ_δ` (DG (3.1) with the time cut `s ≥ δ²`) -/
def hatDelta (W : WNSpace → Ω → ℝ) (P : Measure Ω) (δ : ℝ) : ℂ → Ω → ℝ :=
  DDDF.phiVer W P δ 1

lemma hatDelta_spec (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    DDDF.IsPhiVersion W P δ 1 (hatDelta W P δ) :=
  DDDF.isPhiVersion_phiVer hW hδ hδ1

/-- `phiKernel δ 1 x = hatKerI (δ², 1] x` off the null set `{s = δ²}` -/
lemma phiKernel_eq_hatKerI {δ : ℝ} (x : ℂ) {p : ℝ × ℂ} (hp : p.1 ≠ δ ^ 2) :
    phiKernel δ 1 x p = hatKerI (Ioc (δ ^ 2) 1) x p := by
  have e : p ∈ Icc (δ ^ 2) ((1 : ℝ) ^ 2) ×ˢ (univ : Set ℂ) ↔ p.1 ∈ Ioc (δ ^ 2) 1 := by
    simp only [mem_prod, mem_Icc, mem_Ioc, mem_univ, and_true, one_pow]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm hp), h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.le, h2⟩
  unfold phiKernel hatKerI
  by_cases h : p.1 ∈ Ioc (δ ^ 2) 1
  · rw [indicator_of_mem (e.2 h), indicator_of_mem h]
  · rw [indicator_of_notMem (fun h' => h (e.1 h')), indicator_of_notMem h]

lemma ae_ne_fst (c : ℝ) : ∀ᵐ p : ℝ × ℂ ∂volume, p.1 ≠ c := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have e : {p : ℝ × ℂ | p.1 = c} = ({c} : Set ℝ) ×ˢ (univ : Set ℂ) := by
    ext p; simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod]
  simp

lemma integral_phiKernelL2_aux {δ : ℝ} (hδ : 0 < δ) (σ : Measure ℂ) [IsFiniteMeasure σ]
    (hk : Integrable (phiKernelL2 δ 1) σ) {E : Set (ℝ × ℂ)} (hE : MeasurableSet E)
    (hEf : volume E < ⊤)
    (hint : Integrable (fun q : ℂ × (ℝ × ℂ) => hatKerI (Ioc (δ ^ 2) 1) q.1 q.2)
        (σ.prod (volume.restrict E))) :
    ∫ p in E, ((∫ x, phiKernelL2 δ 1 x ∂σ : WNSpace) : ℝ × ℂ → ℝ) p =
      ∫ p in E, hatMeasKerI (Ioc (δ ^ 2) 1) σ p := by
  rw [← L2.inner_indicatorConstLp_one hE hEf.ne,
    ← integral_inner (𝕜 := ℝ) hk (indicatorConstLp 2 hE hEf.ne (1 : ℝ))]
  have h1 : ∀ x, ⟪indicatorConstLp 2 hE hEf.ne (1 : ℝ), phiKernelL2 δ 1 x⟫ =
      ∫ p in E, hatKerI (Ioc (δ ^ 2) 1) x p := by
    intro x
    rw [L2.inner_indicatorConstLp_one hE hEf.ne]
    refine setIntegral_congr_ae hE ?_
    filter_upwards [coeFn_phiKernelL2 δ 1 hδ x, ae_ne_fst (δ ^ 2)] with p hp hp' _
    rw [hp, phiKernel_eq_hatKerI x hp']
  simp_rw [h1]
  rw [integral_integral_swap (f := fun x p => hatKerI (Ioc (δ ^ 2) 1) x p) hint]
  rfl

lemma measurable_hatKerI_swap {δ : ℝ} :
    Measurable fun q : ℂ × (ℝ × ℂ) => hatKerI (Ioc (δ ^ 2) 1) q.1 q.2 := by
  have h : Measurable ((fun q : (ℝ × ℂ) × ℂ => hatKerI (Ioc (δ ^ 2) 1) q.2 q.1) ∘ Prod.swap) :=
    (measurable_hatKerI_uncurry measurableSet_Ioc).comp measurable_swap
  exact h

lemma integrable_hatKerI_prod {δ : ℝ} (hδ : 0 < δ) (σ : Measure ℂ) [IsFiniteMeasure σ]
    {E : Set (ℝ × ℂ)} (hEf : volume E < ⊤) :
    Integrable (fun q : ℂ × (ℝ × ℂ) => hatKerI (Ioc (δ ^ 2) 1) q.1 q.2)
      (σ.prod (volume.restrict E)) := by
  have hd2 : 0 < δ ^ 2 := by positivity
  have hFm := measurable_hatKerI_swap (δ := δ)
  have : Fact (volume E < ⊤) := ⟨hEf⟩
  refine Integrable.of_bound hFm.aestronglyMeasurable (Real.pi * δ ^ 2)⁻¹
    (Eventually.of_forall fun q => ?_)
  rw [Real.norm_of_nonneg (hatKerI_nonneg (fun s hs => hd2.trans hs.1) _ _)]
  exact hatKerI_le hd2 (fun s hs => hs.1) _ _

/-- the `L²`-Bochner circle average of the kernels `k_{δ,1}(x)` of `ĥ_δ(x)` is the kernel of
`ĥ_δ(σ)` for a probability measure `σ` carried by a compact set -/
theorem integral_phiKernelL2_ae_eq {δ : ℝ} (hδ : 0 < δ) (σ : Measure ℂ)
    [IsFiniteMeasure σ] (hk : Integrable (phiKernelL2 δ 1) σ) :
    ((∫ x, phiKernelL2 δ 1 x ∂σ : WNSpace) : ℝ × ℂ → ℝ) =ᵐ[volume]
      hatMeasKerI (Ioc (δ ^ 2) 1) σ := by
  have hd2 : 0 < δ ^ 2 := by positivity
  have hIm : MeasurableSet (Ioc (δ ^ 2) 1) := measurableSet_Ioc
  have hI0 : Ioc (δ ^ 2) 1 ⊆ Ioi (δ ^ 2) := fun s hs => hs.1
  have hIp : Ioc (δ ^ 2) 1 ⊆ Ioi 0 := fun s hs => hd2.trans hs.1
  have hmem := memLp_hatMeasKerI hIm hd2 (subset_refl _) σ
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun E hE hEf => ?_)
    (fun E hE hEf => ?_) (fun E hE hEf => ?_)
  · have : Fact (volume E < ⊤) := ⟨hEf⟩
    exact ((Lp.memLp _).restrict E).integrable one_le_two
  · have : Fact (volume E < ⊤) := ⟨hEf⟩
    exact (hmem.restrict E).integrable one_le_two
  · exact integral_phiKernelL2_aux hδ σ hk hE hEf (integrable_hatKerI_prod hδ σ hEf)

/-- the `L²` kernel identity: `∫ k_{δ,1}(x) σ(dx) = hatMeasKerIL2 (δ², 1] σ` -/
theorem integral_phiKernelL2_eq {δ : ℝ} (hδ : 0 < δ) (σ : Measure ℂ) [IsFiniteMeasure σ]
    (hk : Integrable (phiKernelL2 δ 1) σ) :
    (∫ x, phiKernelL2 δ 1 x ∂σ : WNSpace) = hatMeasKerIL2 (Ioc (δ ^ 2) 1) σ := by
  have hd2 : 0 < δ ^ 2 := by positivity
  have hmem := memLp_hatMeasKerI measurableSet_Ioc hd2 (subset_refl (Ioc (δ ^ 2) 1)) σ
  refine Lp.ext ?_
  rw [hatMeasKerIL2, dite_eq_left_of_eq_true (eq_true hmem)]
  exact (integral_phiKernelL2_ae_eq hδ σ hk).trans hmem.coeFn_toLp.symm

/-- **the circle averages of the continuous field `ĥ_δ` are `ĥ_δ(σ_{z,r})`**: a.s.
`∫ ĥ_δ dσ_{z,r} = dgHatCoarse W δ z r` (stochastic Fubini) -/
theorem ae_circleAvg_hatDelta (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    (fun ω => ∫ x, hatDelta W P δ x ω ∂(circleUnif z r)) =ᵐ[P] dgHatCoarse W δ z r := by
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hY := hatDelta_spec hW hδ hδ1
  set S := closedBall z r
  have hSc : IsCompact S := isCompact_closedBall z r
  set σ := circleUnif z r
  have hσS : σ Sᶜ = 0 := circleUnif_compl_closedBall hr z
  have hSae : ∀ᵐ x ∂σ, x ∈ S := mem_ae_iff.2 hσS
  have hkc : Continuous (phiKernelL2 δ 1) := DGo.continuous_phiKernelL2 hδ hδ1
  obtain ⟨M, hM⟩ := hSc.exists_bound_of_continuousOn hkc.continuousOn
  have hki : Integrable (phiKernelL2 δ 1) σ :=
    Integrable.of_bound hkc.aestronglyMeasurable M (hSae.mono fun x hx => hM x hx)
  set Y' : ℂ → Ω → ℝ := fun x ω => hatDelta W P δ x ω / Real.sqrt Real.pi
  have hYW' : ∀ x ∈ S, Y' x =ᵐ[P] W (phiKernelL2 δ 1 x) := fun x _ => by
    filter_upwards [hY.ae_eq x] with ω h
    simp only [Y', h, phi]; field_simp
  have hF := ae_integral_eq_wn hW hSc hσS hM (fun ω => (hY.cont ω).div_const _)
    (fun x => (hY.meas x).div_const _) hYW' hki
  rw [integral_phiKernelL2_eq hδ σ hki] at hF
  filter_upwards [hF] with ω h1
  have e : ∫ x, hatDelta W P δ x ω ∂σ = Real.sqrt Real.pi * ∫ x, Y' x ω ∂σ := by
    rw [← integral_const_mul]; congr 1; funext x; simp only [Y']; field_simp
  rw [e, h1]
  rfl

end DG
end LQGMetric
