/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3TrInv3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3TrInv2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Mu2
import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.Prop16MeasArea

/-!
# The law of `μ_{ĥ^tr}`, `μ_ĥ` does not depend on the white noise (P2-DGTRINV, part 3)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, DG:1243: "the re-centered field
`ĥ^tr(· − v_S + v_𝕊)` agrees in law with `ĥ^tr`. By Lemma 3.12, it therefore follows that …
`P[E_S^ε] = P[E_𝕊^ε]`" (and DG:944, DG:953: the law of `ĥ`, `ĥ^tr` is translation invariant,
"immediate from the definition"). For `muOfMod W γ K Y = e^{−γY} μ_{h^𝕍}|_K` (S3MuHat), with `Y`
a continuous modification whose circle averages are a fixed functional `Φ` of the white noise:

* `triMass`: a measurable functional of `(W, (Y(e_i))_i)` (`e` dense in `interior K`): the
  supremum over QZ's cut-offs `openBump` of the limits `Prop16Area.Meas.Psi` of the
  circle-average approximations of `∫ openBump · e^{−γY} dμ_{h^𝕍}`;
* `muOfMod_ball_eq`: pathwise, on the a.s. event where `μ_{h^𝕍}` is the vague limit of its
  approximations and does not charge `∂K` (`ae_muHU_null`), every ball mass of `muOfMod` is
  `triMass` (monotone convergence, `LQGMeas.iSup_openBump`, `Prop16Area.Meas.integral_eq_Psi`);
* **`prob_muOfMod_eq`**: for any measurable set `S` of rational ball-mass functions,
  `P[ballMassQ (muOfMod W γ K Y) ∈ S] = P'[ballMassQ (muOfMod W' γ K Y') ∈ S]` for any two white
  noises (joint law `map_wn_mod_eq`, S3TrInv2).

Own elementary glue (DG use the equality in law implicitly); no N4-type vague-limit
characterization of `muTr` is needed: the measure is determined by `(W, Y|_e)` pathwise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3 SupTail QuantumZipper

/-- the circle vector of a white-noise vector: `wnCircVec W ω = triCirc (wnVec W ω)` -/
def triCirc (w : WNSpace → ℝ) : CircIdx → ℝ := fun j =>
  Real.sqrt Real.pi * w (measKerL2 openSquare (Ioi 0) (circleUnif j.1.1 j.1.2))

lemma measurable_triCirc : Measurable triCirc :=
  measurable_pi_iff.2 fun _ => (measurable_pi_apply _).const_mul _

/-- the field sample of `h^𝕍` as a function of `p = (w, y)` -/
def triField (p : (WNSpace → ℝ) × (ℕ → ℝ)) : FieldSample := circExt (triCirc p.1)

lemma measurable_triField : Measurable triField :=
  measurable_circExt.comp (measurable_triCirc.comp measurable_fst)

/-- the cut-off integrand `openBump_U,n · e^{−γ Y}`, `Y = triExt e y` -/
def triG (γ : ℝ) (e : ℕ → ℂ) (U : Set ℂ) (n : ℕ) (p : (WNSpace → ℝ) × (ℕ → ℝ)) (z : ℂ) : ℝ :=
  LQGMeas.openBump U n z * Real.exp (γ * -triExt e p.2 z)

lemma measurable_triG (γ : ℝ) (e : ℕ → ℂ) (U : Set ℂ) (n : ℕ) :
    Measurable fun q : ((WNSpace → ℝ) × (ℕ → ℝ)) × ℂ => triG γ e U n q.1 q.2 :=
  ((LQGMeas.continuous_openBump U n).measurable.comp measurable_snd).mul
    (Real.measurable_exp.comp ((((measurable_triExt e).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).neg).const_mul γ))

/-- the mass of `U` under `e^{−γY} μ_{h^𝕍}`, as a functional of `(w, y)` -/
def triMass (γ : ℝ) (e : ℕ → ℂ) (U : Set ℂ) (p : (WNSpace → ℝ) × (ℕ → ℝ)) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (Prop16Area.Meas.Psi γ triField (triG γ e U n) p)

lemma measurable_triMass (γ : ℝ) (e : ℕ → ℂ) (U : Set ℂ) : Measurable (triMass γ e U) :=
  Measurable.iSup fun n => ENNReal.measurable_ofReal.comp
    (Prop16Area.Meas.measurable_Psi γ measurable_triField (measurable_triG γ e U n))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- **pathwise identification of the masses of `muOfMod`** on the good event -/
theorem muOfMod_eq_triMass (W : WNSpace → Ω → ℝ) {γ : ℝ} {K : Set ℂ}
    (hKU : K ⊆ openSquare) {e : ℕ → ℂ} (hKe : interior K ⊆ closure (range e))
    {Y : ℂ → Ω → ℝ} {ω : Ω} (hYc : Continuous fun z => Y z ω)
    (hvag : IsVagueLimitOn openSquare (areaApprox γ (wnField W ω)) (muHU W γ ω))
    (hfr : muHU W γ ω (frontier K) = 0) {B : Set ℂ} (hB : IsOpen B) (hBb : Bornology.IsBounded B) :
    muOfMod W γ K Y ω B = triMass γ e (B ∩ interior K) (wnVec W ω, fun i => Y (e i) ω) := by
  set μ := muHU W γ ω
  set U := B ∩ interior K with hU
  set p : (WNSpace → ℝ) × (ℕ → ℝ) := (wnVec W ω, fun i => Y (e i) ω)
  have hUo : IsOpen U := hB.inter isOpen_interior
  have hUb : Bornology.IsBounded U := hBb.subset inter_subset_left
  have hUS : U ⊆ openSquare := inter_subset_right.trans (interior_subset.trans hKU)
  have hUc : Uᶜ.Nonempty := ⟨0, fun h => by have := hUS h; simp [openSquare] at this⟩
  set f : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (γ * -Y z ω))
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul hYc.neg)).measurable
  -- step 1: `muOfMod(B) = ∫⁻_U f dμ` (the frontier of `K` is `μ`-null)
  have h1 : muOfMod W γ K Y ω B = ∫⁻ z in U, f z ∂μ := by
    unfold muOfMod
    rw [withDensity_apply _ hB.measurableSet, Measure.restrict_restrict hB.measurableSet]
    congr 1
    refine Measure.restrict_congr_set (ae_eq_set.2 ⟨?_, ?_⟩)
    · refine measure_mono_null (fun z hz => ?_) hfr
      obtain ⟨⟨hzB, hzK⟩, hzU⟩ := hz
      exact ⟨subset_closure hzK, fun hzi => hzU ⟨hzB, hzi⟩⟩
    · rw [sdiff_eq_empty.2 (inter_subset_inter_right _ interior_subset), measure_empty]
  -- step 2: monotone convergence through the cut-offs
  have h2 : ∫⁻ z in U, f z ∂μ =
      ⨆ n : ℕ, ∫⁻ z, ENNReal.ofReal (LQGMeas.openBump U n z) * f z ∂μ := by
    rw [← lintegral_iSup (f := fun n z => ENNReal.ofReal (LQGMeas.openBump U n z) * f z)
      (fun n => (ENNReal.measurable_ofReal.comp
      (LQGMeas.continuous_openBump U n).measurable).mul hfm)
      (fun m n hmn z => mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (LQGMeas.openBump_mono U z hmn)) _), ← lintegral_indicator hUo.measurableSet]
    congr 1
    funext z
    rw [← ENNReal.iSup_mul, LQGMeas.iSup_openBump hUo hUc z]
    by_cases hz : z ∈ U
    · simp [indicator_of_mem hz]
    · simp [indicator_of_notMem hz]
  -- step 3: each cut-off integral is `Psi`
  have hg : ∀ n, triG γ e U n p = fun z => LQGMeas.openBump U n z * Real.exp (γ * -Y z ω) := by
    intro n; funext z
    simp only [triG]
    by_cases hz : z ∈ U
    · rw [show triExt e p.2 z = Y z ω from triExt_eq hYc (hKe hz.2)]
    · have : LQGMeas.openBump U n z = 0 := by
        by_contra h
        exact hz (LQGMeas.tsupport_openBump_subset U n (subset_tsupport _ h))
      rw [this, zero_mul, zero_mul]
  have h3 : ∀ n, ∫⁻ z, ENNReal.ofReal (LQGMeas.openBump U n z) * f z ∂μ =
      ENNReal.ofReal (Prop16Area.Meas.Psi γ triField (triG γ e U n) p) := by
    intro n
    have hc : Continuous (triG γ e U n p) := by
      rw [hg n]
      exact (LQGMeas.continuous_openBump U n).mul
        (Real.continuous_exp.comp (continuous_const.mul hYc.neg))
    have hcs : HasCompactSupport (triG γ e U n p) := by
      rw [hg n]; exact (LQGMeas.hasCompactSupport_openBump hUb n).mul_right
    have hV : tsupport (triG γ e U n p) ⊆ openSquare := by
      rw [hg n]
      exact tsupport_mul_subset_left.trans ((LQGMeas.tsupport_openBump_subset U n).trans hUS)
    have hgood : p ∈ Prop16Area.Meas.goodSet γ triField (fun _ => openSquare) := ⟨μ, hvag⟩
    rw [← Prop16Area.Meas.integral_eq_Psi hgood hc hcs hV]
    change _ = ENNReal.ofReal (∫ z, triG γ e U n p z ∂μ)
    rw [ofReal_integral_eq_lintegral_ofReal
      (GoodSample.integrable_of_tsupport hvag.2.1 hc hcs hV) (ae_of_all _ fun z => ?_)]
    · congr 1; funext z
      rw [hg n]
      simp only [f]
      rw [ENNReal.ofReal_mul (LQGMeas.openBump_nonneg U n z)]
    · rw [hg n]; exact mul_nonneg (LQGMeas.openBump_nonneg U n z) (Real.exp_pos _).le
  rw [h1, h2]
  simp only [triMass, h3]

/-- the rational ball masses of `muOfMod` as a measurable functional of `(w, y)` -/
def triBallQ (γ : ℝ) (e : ℕ → ℂ) (K : Set ℂ) (p : (WNSpace → ℝ) × (ℕ → ℝ)) :
    ℚ × ℚ → ℚ → ℝ≥0∞ :=
  fun c q => triMass γ e (Metric.ball (ratPt c) q ∩ interior K) p

lemma measurable_triBallQ (γ : ℝ) (e : ℕ → ℂ) (K : Set ℂ) : Measurable (triBallQ γ e K) :=
  measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ => measurable_triMass γ e _

/-- a.s. the rational ball masses of `muOfMod` are `triBallQ` of `(W, Y|_e)` -/
theorem ae_ballMassQ_muOfMod (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ openSquare) (hK0 : volume (frontier K) = 0)
    {e : ℕ → ℂ} (hKe : interior K ⊆ closure (range e)) {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun z => Y z ω) :
    ∀ᵐ ω ∂P, ballMassQ (muOfMod W γ K Y ω) = triBallQ γ e K (wnVec W ω, fun i => Y (e i) ω) := by
  have := hW.isProbabilityMeasure
  obtain ⟨Ω₀, _, P₀, X, hP₀, hX⟩ := GMCIdent5.exists_zeroGFF_openSquare
  have hfK : frontier K ⊆ K := hK.isClosed.frontier_subset
  filter_upwards [ae_isVagueLimitOn_wn hX hW hγ hγ2, ae_muHU_null hW hγ hγ2
    (hK.of_isClosed_subset isClosed_frontier hfK) (hfK.trans hKU) hK0] with ω hv hf
  funext c q
  exact muOfMod_eq_triMass W hKU hKe (hYc ω) hv hf Metric.isOpen_ball
    Metric.isBounded_ball

/-- **The law of the LQG measure `muOfMod` does not depend on the white noise**: for two white
noises `W`, `W'` (any probability spaces) and continuous modifications `Y`, `Y'` on `K` whose
circle averages are the same functional `Φ` of the noise, every measurable event of the
rational ball masses has the same probability. -/
theorem prob_muOfMod_eq {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {W' : WNSpace → Ω' → ℝ} (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ openSquare)
    (hK0 : volume (frontier K) = 0) (hne : (interior K).Nonempty)
    {Φ : ℂ → ℝ → (WNSpace → ℝ) → ℝ} (hΦ : ∀ z r, Measurable (Φ z r))
    {Y : ℂ → Ω → ℝ} (hY : IsDGMod P K (fun z r ω => Φ z r (wnVec W ω)) Y)
    {Y' : ℂ → Ω' → ℝ} (hY' : IsDGMod P' K (fun z r ω => Φ z r (wnVec W' ω)) Y')
    {S : Set (ℚ × ℚ → ℚ → ℝ≥0∞)} (hS : MeasurableSet S) :
    P {ω | ballMassQ (muOfMod W γ K Y ω) ∈ S} =
      P' {ω | ballMassQ (muOfMod W' γ K Y' ω) ∈ S} := by
  obtain ⟨e, ρ, -, hKe, hρ⟩ := exists_triDense hne
  have hT : MeasurableSet (triBallQ γ e K ⁻¹' S) := measurable_triBallQ γ e K hS
  have hm : Measurable fun ω => (wnVec W ω, fun i => Y (e i) ω) :=
    (measurable_wnVec hW).prodMk (measurable_pi_iff.2 fun i => hY.2.1 (e i))
  have hm' : Measurable fun ω => (wnVec W' ω, fun i => Y' (e i) ω) :=
    (measurable_wnVec hW').prodMk (measurable_pi_iff.2 fun i => hY'.2.1 (e i))
  have e1 : {ω | ballMassQ (muOfMod W γ K Y ω) ∈ S} =ᵐ[P]
      (fun ω => (wnVec W ω, fun i => Y (e i) ω)) ⁻¹' (triBallQ γ e K ⁻¹' S) := by
    filter_upwards [ae_ballMassQ_muOfMod hW hγ hγ2 hK hKU hK0 hKe hY.1] with ω hω
    simp only [mem_preimage, hω]
  have e2 : {ω | ballMassQ (muOfMod W' γ K Y' ω) ∈ S} =ᵐ[P']
      (fun ω => (wnVec W' ω, fun i => Y' (e i) ω)) ⁻¹' (triBallQ γ e K ⁻¹' S) := by
    filter_upwards [ae_ballMassQ_muOfMod hW' hγ hγ2 hK hKU hK0 hKe hY'.1] with ω hω
    simp only [mem_preimage, hω]
  rw [measure_congr e1, measure_congr e2, ← Measure.map_apply hm hT, ← Measure.map_apply hm' hT,
    map_wn_mod_eq hW hW' hρ hΦ hY hY']

end DG
end LQGMetric
