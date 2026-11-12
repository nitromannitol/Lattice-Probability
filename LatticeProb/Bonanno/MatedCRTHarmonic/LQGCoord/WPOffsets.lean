/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCoord.WPOffsets at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.WPModulus
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ScaleKolm

/-!
For a window `(S, δ)` and a test
function `f`, with `L` the dyadic limit of the normalized masses (`WMassLimit`):

* `pathwise_bound_wMass`, `lintegral_sup_level_le`: for a level-`n` dyadic offset `a ∈ [1,2]`,
  `|wMass (a ε) − L| ≤ ∫ |f| wDens(2ε) chainT_m H + Σ_{grid of level m} |wMass (c ε) − L|`, whose
  expectation is `≤ M δ^{2+γ²/2} (C₁ θ^m + (2^m + 1) C₂ 2^{-βk})` uniformly in `n`;
* `lintegral_tsum_supG_le`: summing over the scales `ε = δ 2^{-k}` with `m = ⌊βk/2⌋`,
  `E Σ_k sup_{dyadic a} |wMass (a δ 2^{-k}) − L| ≤ M δ^{2+γ²/2} sumC γ` (`sumC` depends only on `γ`);
* `ae_tendsto_wMass` (**all offsets**): almost surely `wMass γ X δ f s → L` as `s → 0⁺`;
* `lintegral_wMassSup_le` (**supremum over all small radii**, for `f ≥ 0`): a measurable `W*` with
  `wMass s ≤ W*` for all `0 < s ≤ δ/2` on the good event and `E W* ≤ M δ^{2+γ²/2} (π/16 + sumC γ)`.

On the good event `GoodCirc` (joint continuity of the circle averages, a.s. by `ScaleKolm`), the
masses are continuous in the radius, which passes from dyadic offsets to all offsets.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric LQGMetric.CircleAvg QuantumZipper QuantumZipper.AllOffsets

/-! ## The good event -/

/-- joint continuity of the circle averages on `(0, ∞) × ℂ` -/
def GoodCirc (h : DistC) : Prop :=
  ContinuousOn (fun p : ℝ × ℂ => circleAvg h p.1 p.2) (Ioi 0 ×ˢ univ)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}

lemma ae_goodCirc (hX : IsWholePlaneGFF X P) : ∀ᵐ ω ∂P, GoodCirc (X ω) :=
  (ae_tendsto_mollAvgS_circleAvg hX).mono fun _ h => h.1

omit [MeasurableSpace Ω] in
lemma continuousOn_wDens_of_good {ω : Ω} (hg : GoodCirc (X ω)) (γ δ : ℝ) :
    ContinuousOn (fun p : ℝ × ℂ => wDens γ X δ p.1 p.2 ω) (Ioi 0 ×ˢ univ) := by
  unfold wDens cInc
  refine ContinuousOn.mul ?_ ?_
  · exact continuousOn_fst.rpow_const fun p hp => Or.inl (ne_of_gt hp.1)
  · exact Real.continuous_exp.comp_continuousOn ((hg.sub continuousOn_const).const_smul γ)

omit [MeasurableSpace Ω] in
lemma exists_bound_wDens_of_good {ω : Ω} (hg : GoodCirc (X ω)) (γ δ : ℝ) {a b : ℝ}
    (ha : 0 < a) (R : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ s ∈ Icc a b, ∀ z ∈ closedBall (0 : ℂ) R, wDens γ X δ s z ω ≤ B := by
  have hK : IsCompact (Icc a b ×ˢ closedBall (0 : ℂ) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_wDens_of_good hg γ δ).mono fun p hp => ⟨ha.trans_le hp.1.1, mem_univ _⟩)
  refine ⟨max B 0, le_max_right _ _, fun s hs z hz => ?_⟩
  have := hB (s, z) ⟨hs, hz⟩
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

variable {S : Set ℂ} {δ : ℝ} {f : ℂ → ℝ} {M : ℝ}

omit [MeasurableSpace Ω] in
lemma integrable_fDens_of_good {ω : Ω} (hg : GoodCirc (X ω)) (γ : ℝ) (hW : Win S δ)
    (hf : WinFun S f M) {s : ℝ} (hs : 0 < s) :
    Integrable (fun z => f z * wDens γ X δ s z ω) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_wDens_of_good hg γ δ (a := s) (b := s) hs (δ / 4)
  have hmeas : AEStronglyMeasurable (fun z => f z * wDens γ X δ s z ω) volume := by
    have hc : Continuous fun z => wDens γ X δ s z ω :=
      continuousOn_univ.1 ((continuousOn_wDens_of_good hg γ δ).comp
        (continuous_const.prodMk continuous_id).continuousOn fun z _ => ⟨hs, mem_univ _⟩)
    exact (hf.meas.mul hc.measurable).aestronglyMeasurable
  refine Integrable.mono' ((integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const (C := M * B) (measure_closedBall_lt_top (x := (0 : ℂ)) (r := δ / 4)).ne))
    hmeas (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ S
  · have hzb : z ∈ closedBall (0 : ℂ) (δ / 4) := hW.subset hz
    rw [indicator_of_mem hzb, Real.norm_eq_abs, abs_mul, abs_of_pos (wDens_pos γ δ hs z ω)]
    exact mul_le_mul (hf.bdd z) (hB s ⟨le_rfl, le_rfl⟩ z hzb) (wDens_pos γ δ hs z ω).le
      hf.M_nonneg
  · rw [hf.zero z hz, zero_mul, norm_zero]
    exact indicator_nonneg (fun _ _ => mul_nonneg hf.M_nonneg hB0) _

omit [MeasurableSpace Ω] in
/-- on the good event the masses are continuous in the radius -/
lemma continuousOn_wMass_of_good {ω : Ω} (hg : GoodCirc (X ω)) (γ : ℝ) (hW : Win S δ)
    (hf : WinFun S f M) : ContinuousOn (fun s => wMass γ X δ f s ω) (Ioi 0) := by
  intro s₀ hs₀
  have hs₀' : 0 < s₀ := hs₀
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨B, hB0, hB⟩ := exists_bound_wDens_of_good hg γ δ (a := s₀ / 2) (b := 2 * s₀)
    (by positivity) (δ / 4)
  have hnhds : Icc (s₀ / 2) (2 * s₀) ∈ 𝓝 s₀ := Icc_mem_nhds (by linarith) (by linarith)
  refine continuousAt_of_dominated (bound := (closedBall (0 : ℂ) (δ / 4)).indicator
    fun _ => M * B) ?_ ?_ ?_ ?_
  · filter_upwards [hnhds] with s hs
    exact (integrable_fDens_of_good hg γ hW hf (by linarith [hs.1])).aestronglyMeasurable
  · filter_upwards [hnhds] with s hs
    refine Eventually.of_forall fun z => ?_
    have hsp : 0 < s := by linarith [hs.1]
    by_cases hz : z ∈ S
    · have hzb : z ∈ closedBall (0 : ℂ) (δ / 4) := hW.subset hz
      rw [indicator_of_mem hzb, Real.norm_eq_abs, abs_mul, abs_of_pos (wDens_pos γ δ hsp z ω)]
      exact mul_le_mul (hf.bdd z) (hB s hs z hzb) (wDens_pos γ δ hsp z ω).le hf.M_nonneg
    · rw [hf.zero z hz, zero_mul, norm_zero]
      exact indicator_nonneg (fun _ _ => mul_nonneg hf.M_nonneg hB0) _
  · exact (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (C := M * B) (measure_closedBall_lt_top (x := (0 : ℂ))).ne)
  · refine Eventually.of_forall fun z => ?_
    have hc : ContinuousAt (fun s => wDens γ X δ s z ω) s₀ := by
      have := (continuousOn_wDens_of_good hg γ δ).continuousAt
        (x := (s₀, z)) (prod_mem_nhds (Ioi_mem_nhds hs₀') univ_mem)
      have hcz : ContinuousAt (fun s : ℝ => (s, z)) s₀ :=
        (continuous_id.prodMk continuous_const).continuousAt
      exact ContinuousAt.comp (f := fun s : ℝ => (s, z)) (x := s₀) this hcz
    exact continuousAt_const.mul hc

/-! ## The pathwise bound -/

omit [MeasurableSpace Ω] in
theorem pathwise_bound_wMass {ω : Ω} (hg : GoodCirc (X ω)) (γ : ℝ) (hW : Win S δ)
    (hf : WinFun S f M) (L : ℝ) {ε : ℝ} (hε : 0 < ε) (m d : ℕ) {i : ℕ}
    (hi : i ≤ 2 ^ (m + d)) :
    ENNReal.ofReal |wMass γ X δ f (dpt (m + d) i * ε) ω - L| ≤
      (∫⁻ z, ENNReal.ofReal (|f z| * (wDens γ X δ (2 * ε) z ω *
        chainT m (m + d) (fun a => bandH γ X z ε a ω)))) +
      ∑ l ∈ Finset.range (2 ^ m + 1), ENNReal.ofReal |wMass γ X δ f (dpt m l * ε) ω - L| := by
  have ha : 0 < dpt (m + d) i := by linarith [dpt_ge_one (m + d) i]
  have ha' : 0 < dpt m (i / 2 ^ d) := by linarith [dpt_ge_one m (i / 2 ^ d)]
  have hil : i / 2 ^ d ≤ 2 ^ m :=
    Nat.div_le_of_le_mul (by rw [pow_add] at hi; rw [mul_comm]; exact hi)
  have h1 := mul_pos ha hε
  have h2 := mul_pos ha' hε
  have hint1 := integrable_fDens_of_good hg γ hW hf h1
  have hint2 := integrable_fDens_of_good hg γ hW hf h2
  have hmod : ENNReal.ofReal |wMass γ X δ f (dpt (m + d) i * ε) ω -
      wMass γ X δ f (dpt m (i / 2 ^ d) * ε) ω| ≤
      ∫⁻ z, ENNReal.ofReal (|f z| * (wDens γ X δ (2 * ε) z ω *
        chainT m (m + d) (fun a => bandH γ X z ε a ω))) := by
    rw [wMass, wMass, ← integral_sub hint1 hint2]
    have hi2 : Integrable (fun z => |f z * wDens γ X δ (dpt (m + d) i * ε) z ω -
        f z * wDens γ X δ (dpt m (i / 2 ^ d) * ε) z ω|) := (hint1.sub hint2).abs
    refine (ENNReal.ofReal_le_ofReal (abs_integral_le_integral_abs)).trans ?_
    rw [ofReal_integral_eq_lintegral_ofReal hi2 (ae_of_all _ fun _ => abs_nonneg _)]
    refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
    rw [wDens_offset_eq γ δ hε ha z ω, wDens_offset_eq γ δ hε ha' z ω, ← mul_sub, ← mul_sub,
      abs_mul, abs_mul, abs_of_pos (wDens_pos (X := X) γ δ (by positivity : (0 : ℝ) < 2 * ε) z ω)]
    have hc : |bandH γ X z ε (dpt (m + d) i) ω - bandH γ X z ε (dpt m (i / 2 ^ d)) ω| ≤
        chainT m (m + d) (fun b => bandH γ X z ε b ω) :=
      chain_bound (fun b => bandH γ X z ε b ω) m d i hi
    have hd0 := (wDens_pos (X := X) γ δ (by positivity : (0 : ℝ) < 2 * ε) z ω).le
    calc |f z| * (wDens γ X δ (2 * ε) z ω *
          |bandH γ X z ε (dpt (m + d) i) ω - bandH γ X z ε (dpt m (i / 2 ^ d)) ω|)
        ≤ |f z| * (wDens γ X δ (2 * ε) z ω *
          chainT m (m + d) (fun b => bandH γ X z ε b ω)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hd0) (abs_nonneg _)
      _ = _ := rfl
  have hgrid : ENNReal.ofReal |wMass γ X δ f (dpt m (i / 2 ^ d) * ε) ω - L| ≤
      ∑ l ∈ Finset.range (2 ^ m + 1), ENNReal.ofReal |wMass γ X δ f (dpt m l * ε) ω - L| :=
    Finset.single_le_sum (f := fun l => ENNReal.ofReal |wMass γ X δ f (dpt m l * ε) ω - L|)
      (fun _ _ => bot_le) (Finset.mem_range.2 (by omega))
  calc ENNReal.ofReal |wMass γ X δ f (dpt (m + d) i * ε) ω - L|
      ≤ ENNReal.ofReal (|wMass γ X δ f (dpt (m + d) i * ε) ω -
          wMass γ X δ f (dpt m (i / 2 ^ d) * ε) ω| +
          |wMass γ X δ f (dpt m (i / 2 ^ d) * ε) ω - L|) :=
        ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ ≤ _ := ENNReal.ofReal_add_le.trans (add_le_add hmod hgrid)

/-! ## The expectation at a fixed level -/

lemma measurable_bandH_joint (hX : IsWholePlaneGFF X P) (γ ε a : ℝ) :
    Measurable (fun p : Ω × ℂ => bandH γ X p.2 ε a p.1) := by
  have h1 : Measurable fun p : Ω × ℂ => circleAvg (X p.1) (a * ε) p.2 :=
    measurable_circleAvg.comp (f := fun p : Ω × ℂ => (X p.1, a * ε, p.2))
      ((hX.measurable.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
  have h2 : Measurable fun p : Ω × ℂ => circleAvg (X p.1) (2 * ε) p.2 :=
    measurable_circleAvg.comp (f := fun p : Ω × ℂ => (X p.1, 2 * ε, p.2))
      ((hX.measurable.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
  have h : Measurable fun p : Ω × ℂ => bandΦ X p.2 ε a p.1 := h1.sub h2
  exact measurable_const.mul (Real.measurable_exp.comp (h.const_mul γ))

lemma measurable_chainT_band (hX : IsWholePlaneGFF X P) (γ ε : ℝ) (m n : ℕ) :
    Measurable (fun p : Ω × ℂ => chainT m n (fun a => bandH γ X p.2 ε a p.1)) := by
  have hH : ∀ a, Measurable (fun p : Ω × ℂ => bandH γ X p.2 ε a p.1) :=
    measurable_bandH_joint hX γ ε
  unfold chainT incr
  exact Finset.measurable_sum _ fun j _ => measurable_const.add
    ((Finset.measurable_sum _ fun l _ => ((hH _).sub (hH _)).pow_const 4).div_const _)

lemma Win.volume_le_ofReal (hW : Win S δ) : volume S ≤ ENNReal.ofReal (π * (δ / 4) ^ 2) := by
  rw [← ofReal_measureReal hW.volume_lt_top.ne]
  exact ENNReal.ofReal_le_ofReal hW.volumeReal_le

lemma wConstG_nonneg {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : 0 ≤ wConstG γ := by
  unfold wConstG
  have := wq_lt_one hγ hγ2
  exact mul_nonneg (wConst_nonneg γ) (add_nonneg (by positivity)
    (div_nonneg zero_le_one (by linarith)))

/-- **The level bound**: for `k ≥ 2` and every level `m + e`,
`E sup_i |wMass (dpt (m+e) i · δ2^{-k}) − L| ≤ M δ^{2+γ²/2} ((π/16) C θ^m + (2^m+1) C' q^k)`. -/
theorem lintegral_sup_level_le (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hW : Win S δ) (hf : WinFun S f M) {L : Ω → ℝ} (hL : WMassLimit γ X P δ f M L) {k : ℕ}
    (hk : 2 ≤ k) (m e : ℕ) :
    ∫⁻ ω, ⨆ i : Fin (2 ^ (m + e) + 1),
        ENNReal.ofReal |wMass γ X δ f (dpt (m + e) i * wRad δ k) ω - L ω| ∂P ≤
      ENNReal.ofReal (M * δ ^ (2 + γ ^ 2 / 2) *
        (π / 16 * modConst * θm ^ m + (2 ^ m + 1) * (wConstG γ * wq γ ^ k))) := by
  have := hX.gaussian.isProbabilityMeasure
  have hδ := hW.pos
  have hM0 := hf.M_nonneg
  set ε := wRad δ k with hεd
  have hε : 0 < ε := wRad_pos hδ k
  have h2ε : 2 * ε ≤ δ / 2 := two_mul_wRad_le_half hδ hk
  set Mod : Ω → ℝ≥0∞ := fun ω => ∫⁻ z, ENNReal.ofReal (|f z| * (wDens γ X δ (2 * ε) z ω *
    chainT m (m + e) (fun a => bandH γ X z ε a ω))) with hMod
  set Gr : Ω → ℝ≥0∞ := fun ω => ∑ l ∈ Finset.range (2 ^ m + 1),
    ENNReal.ofReal |wMass γ X δ f (dpt m l * ε) ω - L ω| with hGr
  have hpt : ∀ᵐ ω ∂P, (⨆ i : Fin (2 ^ (m + e) + 1),
      ENNReal.ofReal |wMass γ X δ f (dpt (m + e) i * ε) ω - L ω|) ≤ Mod ω + Gr ω := by
    filter_upwards [ae_goodCirc hX] with ω hg
    exact iSup_le fun i => pathwise_bound_wMass hg γ hW hf (L ω) hε m e (i := i)
      (Nat.lt_succ_iff.1 i.2)
  refine (lintegral_mono_ae hpt).trans ?_
  have hFm : Measurable (fun p : Ω × ℂ => ENNReal.ofReal (|f p.2| *
      (wDens γ X δ (2 * ε) p.2 p.1 * chainT m (m + e) (fun a => bandH γ X p.2 ε a p.1)))) :=
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp
      (hf.meas.comp measurable_snd)).mul
      ((measurable_wDens hX γ δ _).mul (measurable_chainT_band hX γ ε m (m + e))))
  have hModm : Measurable Mod := hFm.lintegral_prod_right'
  rw [lintegral_add_left' hModm.aemeasurable]
  set c₁ := δ ^ (γ ^ 2 / 2) * (modConst * θm ^ m) with hc₁
  have hc₁0 : 0 ≤ c₁ := mul_nonneg (Real.rpow_nonneg hδ.le _)
    (mul_nonneg modConst_nonneg (pow_nonneg θm_pos.le _))
  have hModb : ∫⁻ ω, Mod ω ∂P ≤ ENNReal.ofReal (M * (π * (δ / 4) ^ 2) * c₁) := by
    simp only [hMod]
    rw [lintegral_lintegral_swap hFm.aemeasurable]
    have hpt2 : ∀ z, ∫⁻ ω, ENNReal.ofReal (|f z| * (wDens γ X δ (2 * ε) z ω *
        chainT m (m + e) (fun a => bandH γ X z ε a ω))) ∂P ≤
        S.indicator (fun _ => ENNReal.ofReal M) z * ENNReal.ofReal c₁ := by
      intro z
      simp_rw [ENNReal.ofReal_mul (abs_nonneg (f z))]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      by_cases hz : z ∈ S
      · rw [indicator_of_mem hz]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hf.bdd z))
          (lintegral_wDens_chainT_le hX hγ hγ2 hε (hW.norm_add_le hz h2ε) m (m + e))
      · simp [hf.zero z hz]
    refine (lintegral_mono hpt2).trans ?_
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_const hW.meas]
    calc ENNReal.ofReal M * volume S * ENNReal.ofReal c₁
        ≤ ENNReal.ofReal M * ENNReal.ofReal (π * (δ / 4) ^ 2) * ENNReal.ofReal c₁ := by
          gcongr; exact hW.volume_le_ofReal
      _ = ENNReal.ofReal (M * (π * (δ / 4) ^ 2) * c₁) := by
          rw [← ENNReal.ofReal_mul hM0, ← ENNReal.ofReal_mul (by positivity)]
  have hGrb : ∫⁻ ω, Gr ω ∂P ≤
      ENNReal.ofReal ((2 ^ m + 1) * (wConstG γ * M * δ ^ (2 + γ ^ 2 / 2) * wq γ ^ k)) := by
    have hmem : ∀ l ∈ Finset.range (2 ^ m + 1), dpt m l ∈ Icc (1 : ℝ) 2 := fun l hl =>
      ⟨dpt_ge_one m l, dpt_le_two (by have := Finset.mem_range.1 hl; omega)⟩
    have hael : ∀ l ∈ Finset.range (2 ^ m + 1), AEMeasurable (fun ω =>
        ENNReal.ofReal |wMass γ X δ f (dpt m l * ε) ω - L ω|) P := fun l _ =>
      (continuous_abs.measurable.comp_aemeasurable
        ((measurable_wMass hX γ hf δ _).aemeasurable.sub hL.aemeas)).ennreal_ofReal
    simp only [hGr]
    rw [lintegral_finsetSum' _ hael]
    refine (Finset.sum_le_sum fun l hl => hL.offset hX hγ hγ2 hW hf hk (hmem l hl)).trans
      (le_of_eq ?_)
    have hC0 : 0 ≤ (2 : ℝ) ^ m + 1 := by positivity
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul hC0,
      show ((2 : ℝ) ^ m + 1) = ((2 ^ m + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  refine (add_le_add hModb hGrb).trans (le_of_eq ?_)
  have hD : δ ^ (2 + γ ^ 2 / 2) = δ ^ 2 * δ ^ (γ ^ 2 / 2) := by
    rw [Real.rpow_add hδ, Real.rpow_two]
  rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg (by positivity)
    (mul_nonneg (mul_nonneg (mul_nonneg (wConstG_nonneg hγ hγ2) hM0)
      (Real.rpow_nonneg hδ.le _)) (pow_nonneg (wq_pos γ).le _)))]
  congr 1
  rw [hc₁, hD]
  ring

/-! ## Summation over the scales -/

/-- the supremum over all dyadic offsets at scale `δ 2^{-k}` -/
def supG (γ : ℝ) (X : Ω → DistC) (δ : ℝ) (f : ℂ → ℝ) (L : Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (i : Fin (2 ^ n + 1)), ENNReal.ofReal |wMass γ X δ f (dpt n i * wRad δ k) ω - L ω|

omit [MeasurableSpace Ω] in
lemma level_mono (γ : ℝ) (X : Ω → DistC) (δ : ℝ) (f : ℂ → ℝ) (L : Ω → ℝ) (k : ℕ) (ω : Ω) :
    Monotone (fun n : ℕ => ⨆ i : Fin (2 ^ n + 1),
      ENNReal.ofReal |wMass γ X δ f (dpt n i * wRad δ k) ω - L ω|) := by
  refine monotone_nat_of_le_succ fun n => iSup_le fun i => ?_
  have hi : 2 * (i : ℕ) < 2 ^ (n + 1) + 1 := by have := i.2; rw [pow_succ]; omega
  refine le_iSup_of_le (⟨2 * i, hi⟩ : Fin (2 ^ (n + 1) + 1)) (le_of_eq ?_)
  rw [dpt_double n i]

/-- the summand of the scale series (depends only on `γ`) -/
def bndC (γ : ℝ) (k : ℕ) : ℝ :=
  π / 16 * modConst * θm ^ (⌊AreaExist.areaRate γ * k / 2⌋₊) +
    (2 ^ (⌊AreaExist.areaRate γ * k / 2⌋₊) + 1) *
      (wConstG γ * exp (-AreaExist.areaRate γ * (k * log 2)))

lemma bndC_nonneg {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (k : ℕ) : 0 ≤ bndC γ k := by
  unfold bndC
  have := wConstG_nonneg hγ hγ2
  have := modConst_nonneg
  have := θm_pos
  positivity

lemma summable_bndC {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : Summable (bndC γ) :=
  AreaOffsets.summable_bndβ (AreaExist.areaRate_pos hγ hγ2)
    (mul_nonneg (by positivity) modConst_nonneg) (wConstG_nonneg hγ hγ2)

/-- the constant of the summed bound (depends only on `γ`) -/
def sumC (γ : ℝ) : ℝ := ∑' k, bndC γ (k + 2)

lemma sumC_nonneg {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : 0 ≤ sumC γ :=
  tsum_nonneg fun _ => bndC_nonneg hγ hγ2 _

lemma wq_pow_eq (γ : ℝ) (k : ℕ) :
    wq γ ^ k = exp (-AreaExist.areaRate γ * (k * log 2)) := by
  rw [wq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num),
    Real.log_inv]
  congr 1; ring

theorem lintegral_supG_le (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hW : Win S δ) (hf : WinFun S f M) {L : Ω → ℝ} (hL : WMassLimit γ X P δ f M L) {k : ℕ}
    (hk : 2 ≤ k) :
    ∫⁻ ω, supG γ X δ f L k ω ∂P ≤ ENNReal.ofReal (M * δ ^ (2 + γ ^ 2 / 2) * bndC γ k) := by
  set m := ⌊AreaExist.areaRate γ * k / 2⌋₊
  have hmeas : ∀ n, AEMeasurable (fun ω => ⨆ i : Fin (2 ^ n + 1), ENNReal.ofReal
      |wMass γ X δ f (dpt n i * wRad δ k) ω - L ω|) P :=
    fun n => AEMeasurable.iSup fun i =>
      (continuous_abs.measurable.comp_aemeasurable
        ((measurable_wMass hX γ hf δ _).aemeasurable.sub hL.aemeas)).ennreal_ofReal
  show ∫⁻ ω, ⨆ n : ℕ, (⨆ i : Fin (2 ^ n + 1), ENNReal.ofReal
      |wMass γ X δ f (dpt n i * wRad δ k) ω - L ω|) ∂P ≤ _
  rw [lintegral_iSup' hmeas (ae_of_all _ fun ω => level_mono γ X δ f L k ω)]
  refine iSup_le fun n => ?_
  obtain ⟨e, he⟩ : ∃ e, max n m = m + e := ⟨max n m - m, by omega⟩
  refine (lintegral_mono fun ω => level_mono γ X δ f L k ω (show n ≤ m + e by omega)).trans
    ((lintegral_sup_level_le hX hγ hγ2 hW hf hL hk m e).trans (le_of_eq ?_))
  congr 1
  rw [bndC, wq_pow_eq]

theorem lintegral_tsum_supG_le (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hW : Win S δ) (hf : WinFun S f M) {L : Ω → ℝ}
    (hL : WMassLimit γ X P δ f M L) :
    ∫⁻ ω, ∑' k, supG γ X δ f L (k + 2) ω ∂P ≤
      ENNReal.ofReal (M * δ ^ (2 + γ ^ 2 / 2) * sumC γ) := by
  have hGm : ∀ k, AEMeasurable (supG γ X δ f L k) P := fun k =>
    AEMeasurable.iSup fun n => AEMeasurable.iSup fun i =>
      (continuous_abs.measurable.comp_aemeasurable
        ((measurable_wMass hX γ hf δ _).aemeasurable.sub hL.aemeas)).ennreal_ofReal
  have hMD : 0 ≤ M * δ ^ (2 + γ ^ 2 / 2) :=
    mul_nonneg hf.M_nonneg (Real.rpow_nonneg hW.pos.le _)
  have hsum : Summable fun k => M * δ ^ (2 + γ ^ 2 / 2) * bndC γ (k + 2) :=
    ((summable_nat_add_iff 2).2 (summable_bndC hγ hγ2)).mul_left _
  rw [lintegral_tsum fun k => hGm _, sumC, ← tsum_mul_left,
    ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hMD (bndC_nonneg hγ hγ2 _)) hsum]
  exact ENNReal.tsum_le_tsum fun k => lintegral_supG_le hX hγ hγ2 hW hf hL (by omega)

/-! ## All offsets -/

omit [MeasurableSpace Ω] in
/-- on the good event, every offset `a ∈ [1, 2]` is controlled by the dyadic supremum -/
theorem ofReal_abs_wMass_offset_le {ω : Ω} (hg : GoodCirc (X ω)) (γ : ℝ) (hW : Win S δ)
    (hf : WinFun S f M) (L : Ω → ℝ) (k : ℕ) {a : ℝ} (ha : a ∈ Icc (1 : ℝ) 2) :
    ENNReal.ofReal |wMass γ X δ f (a * wRad δ k) ω - L ω| ≤ supG γ X δ f L k ω := by
  have hε := wRad_pos hW.pos k
  have hφc : ContinuousOn (fun b : ℝ => wMass γ X δ f (b * wRad δ k) ω) (Ioi 0) :=
    (continuousOn_wMass_of_good hg γ hW hf).comp (continuous_id.mul continuous_const).continuousOn
      fun b hb => mul_pos hb hε
  set an : ℕ → ℕ := fun n => ⌊(a - 1) * 2 ^ n⌋₊ with han
  have hy0 : ∀ n : ℕ, 0 ≤ (a - 1) * 2 ^ n := fun n =>
    mul_nonneg (by linarith [ha.1]) (by positivity)
  have han_le : ∀ n, an n ≤ 2 ^ n := fun n =>
    Nat.floor_le_of_le (by push_cast; nlinarith [ha.2, pow_pos (two_pos (α := ℝ)) n])
  have hconv : Tendsto (fun n => dpt n (an n)) atTop (𝓝 a) := by
    have hup : ∀ n, dpt n (an n) ≤ a := fun n => by
      have h1 : (an n : ℝ) ≤ (a - 1) * 2 ^ n := Nat.floor_le (hy0 n)
      unfold dpt
      have : (an n : ℝ) / 2 ^ n ≤ a - 1 := by
        rw [div_le_iff₀ (by positivity)]; exact h1
      linarith
    have hlow : ∀ n, a - (1 / 2) ^ n ≤ dpt n (an n) := fun n => by
      have h1 : (a - 1) * 2 ^ n - 1 < (an n : ℝ) := by
        have := Nat.lt_floor_add_one ((a - 1) * 2 ^ n); linarith
      unfold dpt
      have h2 : a - 1 - (1 / 2) ^ n ≤ (an n : ℝ) / 2 ^ n := by
        have hpw : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
        rw [le_div_iff₀ (by positivity), sub_mul, hpw]
        linarith
      linarith
    have hl : Tendsto (fun n : ℕ => a - (1 / 2 : ℝ) ^ n) atTop (𝓝 a) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_sub a
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlow hup
  have hbd : ∀ n, ENNReal.ofReal |wMass γ X δ f (dpt n (an n) * wRad δ k) ω - L ω| ≤
      supG γ X δ f L k ω := fun n =>
    le_iSup₂_of_le (f := fun (n : ℕ) (i : Fin (2 ^ n + 1)) => ENNReal.ofReal
      |wMass γ X δ f (dpt n i * wRad δ k) ω - L ω|) n
      ⟨an n, Nat.lt_succ_of_le (han_le n)⟩ le_rfl
  have ha0 : (0 : ℝ) < a := by linarith [ha.1]
  have hlim : Tendsto (fun n => ENNReal.ofReal |wMass γ X δ f (dpt n (an n) * wRad δ k) ω -
      L ω|) atTop (𝓝 (ENNReal.ofReal |wMass γ X δ f (a * wRad δ k) ω - L ω|)) := by
    have h1 := ((hφc.continuousAt (Ioi_mem_nhds ha0)).tendsto.comp hconv)
    exact (ENNReal.continuous_ofReal.tendsto _).comp (((h1.sub_const (L ω)).abs))
  exact le_of_tendsto' hlim hbd

lemma exists_dyadic_offset {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hsδ : s ≤ δ) :
    ∃ n : ℕ, (2 : ℝ) ^ n ≤ δ / s ∧ δ / s < 2 ^ (n + 1) ∧
      s / wRad δ (n + 1) ∈ Icc (1 : ℝ) 2 := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ δ / s by
    rw [le_div_iff₀ hs]; linarith) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨n, h1, h2, ?_, ?_⟩
  · rw [le_div_iff₀ (wRad_pos hδ _), one_mul, wRad, inv_pow]
    rw [div_lt_iff₀ hs] at h2
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  · rw [div_le_iff₀ (wRad_pos hδ _), wRad, inv_pow, pow_succ]
    rw [le_div_iff₀ hs] at h1
    field_simp
    linarith

/-- **Convergence along all radii** (Sheffield–Wang Thm 1.1 for the whole-plane GFF, on a
window): almost surely `wMass γ X δ f s → L` as `s → 0⁺`. -/
theorem ae_tendsto_wMass (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hW : Win S δ) (hf : WinFun S f M) {L : Ω → ℝ} (hL : WMassLimit γ X P δ f M L) :
    ∀ᵐ ω ∂P, Tendsto (fun s => wMass γ X δ f s ω) (𝓝[>] 0) (𝓝 (L ω)) := by
  have hδ := hW.pos
  have hGm : ∀ k, AEMeasurable (supG γ X δ f L k) P := fun k =>
    AEMeasurable.iSup fun n => AEMeasurable.iSup fun i =>
      (continuous_abs.measurable.comp_aemeasurable
        ((measurable_wMass hX γ hf δ _).aemeasurable.sub hL.aemeas)).ennreal_ofReal
  have hint : ∫⁻ ω, ∑' k, supG γ X δ f L (k + 2) ω ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_tsum_supG_le hX hγ hγ2 hW hf hL)
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum fun k => hGm (k + 2)) hint
  filter_upwards [hae, ae_goodCirc hX] with ω hω hg
  have hG0 : Tendsto (fun k => supG γ X δ f L (k + 2) ω) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  have hev : ∀ᶠ k in atTop, supG γ X δ f L (k + 2) ω < ENNReal.ofReal η :=
    hG0.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hη))
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  refine ⟨wRad δ (K + 2), wRad_pos hδ _, fun s hs hsd => ?_⟩
  have hs0 : 0 < s := hs
  rw [Real.dist_eq, sub_zero, abs_of_pos hs0] at hsd
  have hsδ : s ≤ δ := hsd.le.trans (by
    unfold wRad; exact mul_le_of_le_one_right hδ.le (pow_le_one₀ (by norm_num) (by norm_num)))
  obtain ⟨n, -, hn2, hn3⟩ := exists_dyadic_offset hδ hs0 hsδ
  have h5 : (2 : ℝ) ^ (K + 2) ≤ δ / s := by
    rw [le_div_iff₀ hs0]
    have : s < δ * (2 : ℝ)⁻¹ ^ (K + 2) := hsd
    rw [inv_pow, lt_mul_inv_iff₀ (by positivity)] at this
    linarith
  have hKn : K + 2 ≤ n + 1 := by
    have h6 : (2 : ℝ) ^ (K + 2) < 2 ^ (n + 1) := h5.trans_lt hn2
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h6
    omega
  have hsa : s = s / wRad δ (n + 1) * wRad δ (n + 1) := by
    rw [div_mul_cancel₀ _ (wRad_pos hδ _).ne']
  have hb := ofReal_abs_wMass_offset_le hg γ hW hf L (n + 1) hn3
  rw [← hsa] at hb
  have hK' := hK (n + 1 - 2) (by omega)
  rw [show n + 1 - 2 + 2 = n + 1 by omega] at hK'
  rw [Real.dist_eq]
  exact (ENNReal.ofReal_lt_ofReal_iff hη).1 (hb.trans_lt hK')

/-! ## The supremum over all small radii -/

/-- a measurable upper bound for `sup_{0 < s ≤ δ/2} wMass s` -/
def wMassSup (γ : ℝ) (X : Ω → DistC) (δ : ℝ) (f : ℂ → ℝ) (L : Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal |L ω| + ∑' k, supG γ X δ f L (k + 2) ω

omit [MeasurableSpace Ω] in
theorem ofReal_wMass_le_wMassSup {ω : Ω} (hg : GoodCirc (X ω)) (γ : ℝ) (hW : Win S δ)
    (hf : WinFun S f M) (L : Ω → ℝ) {s : ℝ} (hs : 0 < s) (hsδ : s ≤ δ / 2) :
    ENNReal.ofReal |wMass γ X δ f s ω| ≤ wMassSup γ X δ f L ω := by
  have hδ := hW.pos
  obtain ⟨n, -, hn1, hn2⟩ := exists_dyadic_offset hδ hs (by linarith)
  have hn : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    subst h0
    rw [div_lt_iff₀ hs] at hn1
    norm_num at hn1
    linarith
  have hsa : s = s / wRad δ (n + 1) * wRad δ (n + 1) := by
    rw [div_mul_cancel₀ _ (wRad_pos hδ _).ne']
  have hb := ofReal_abs_wMass_offset_le hg γ hW hf L (n + 1) hn2
  rw [← hsa] at hb
  have h1 : supG γ X δ f L (n + 1) ω ≤ ∑' k, supG γ X δ f L (k + 2) ω := by
    have := ENNReal.le_tsum (f := fun k => supG γ X δ f L (k + 2) ω) (n - 1)
    rwa [show n - 1 + 2 = n + 1 by omega] at this
  calc ENNReal.ofReal |wMass γ X δ f s ω|
      ≤ ENNReal.ofReal (|L ω| + |wMass γ X δ f s ω - L ω|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := abs_sub_abs_le_abs_sub (wMass γ X δ f s ω) (L ω)
        linarith
    _ ≤ ENNReal.ofReal |L ω| + ENNReal.ofReal |wMass γ X δ f s ω - L ω| := ENNReal.ofReal_add_le
    _ ≤ wMassSup γ X δ f L ω := add_le_add le_rfl (hb.trans h1)

/-- `E ofReal |wMass s| ≤ M · vol(S) · δ^{γ²/2}` -/
lemma lintegral_ofReal_abs_wMass_le (hX : IsWholePlaneGFF X P) (γ : ℝ) (hW : Win S δ)
    (hf : WinFun S f M) {s : ℝ} (hs : 0 < s) (hsδ : s ≤ δ / 2) :
    ∫⁻ ω, ENNReal.ofReal |wMass γ X δ f s ω| ∂P ≤
      ENNReal.ofReal (M * (π * (δ / 4) ^ 2) * δ ^ (γ ^ 2 / 2)) := by
  have := hX.gaussian.isProbabilityMeasure
  have hδ := hW.pos
  have hFm : Measurable (fun p : Ω × ℂ => ENNReal.ofReal (|f p.2| * wDens γ X δ s p.2 p.1)) :=
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp
      (hf.meas.comp measurable_snd)).mul (measurable_wDens hX γ δ s))
  have hpt : ∀ ω, ENNReal.ofReal |wMass γ X δ f s ω| ≤
      ∫⁻ z, ENNReal.ofReal (|f z| * wDens γ X δ s z ω) := by
    intro ω
    rw [← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    congr 1; funext z
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_pos (wDens_pos γ δ hs z ω)]
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_lintegral_swap hFm.aemeasurable]
  have hpt2 : ∀ z, ∫⁻ ω, ENNReal.ofReal (|f z| * wDens γ X δ s z ω) ∂P ≤
      S.indicator (fun _ => ENNReal.ofReal M) z * ENNReal.ofReal (δ ^ (γ ^ 2 / 2)) := by
    intro z
    simp_rw [ENNReal.ofReal_mul (abs_nonneg (f z))]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz]
      obtain ⟨hi, he⟩ := integral_wDens hX γ hs (hW.norm_add_le hz hsδ) (P := P)
      rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω =>
        (wDens_pos γ δ hs z ω).le), he]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hf.bdd z)) le_rfl
    · simp [hf.zero z hz]
  refine (lintegral_mono hpt2).trans ?_
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_const hW.meas]
  calc ENNReal.ofReal M * volume S * ENNReal.ofReal (δ ^ (γ ^ 2 / 2))
      ≤ ENNReal.ofReal M * ENNReal.ofReal (π * (δ / 4) ^ 2) * ENNReal.ofReal (δ ^ (γ ^ 2 / 2)) := by
        gcongr; exact hW.volume_le_ofReal
    _ = _ := by rw [← ENNReal.ofReal_mul hf.M_nonneg, ← ENNReal.ofReal_mul (by
          have := hf.M_nonneg; positivity)]

/-- **The supremum bound**: `E wMassSup ≤ M δ^{2+γ²/2} (π/16 + sumC γ)`. -/
theorem lintegral_wMassSup_le (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hW : Win S δ) (hf : WinFun S f M) {L : Ω → ℝ} (hL : WMassLimit γ X P δ f M L) :
    ∫⁻ ω, wMassSup γ X δ f L ω ∂P ≤
      ENNReal.ofReal (M * δ ^ (2 + γ ^ 2 / 2) * (π / 16 + sumC γ)) := by
  have hδ := hW.pos
  have hM0 := hf.M_nonneg
  have hLm : AEMeasurable (fun ω => ENNReal.ofReal |L ω|) P :=
    (continuous_abs.measurable.comp_aemeasurable hL.aemeas).ennreal_ofReal
  -- Fatou for the limit
  have hk : ∀ k, 1 ≤ k → wRad δ k ≤ δ / 2 := fun k hk => wRad_le_half hδ hk
  have hFatou : ∫⁻ ω, ENNReal.ofReal |L ω| ∂P ≤
      ENNReal.ofReal (M * (π * (δ / 4) ^ 2) * δ ^ (γ ^ 2 / 2)) := by
    have hmeas : ∀ k, AEMeasurable (fun ω => ENNReal.ofReal |wMass γ X δ f (wRad δ (k + 1)) ω|)
        P := fun k =>
      (continuous_abs.measurable.comp (measurable_wMass hX γ hf δ _)).ennreal_ofReal.aemeasurable
    have h1 := lintegral_liminf_le' (u := (atTop : Filter ℕ)) hmeas
    have h2 : ∫⁻ ω, ENNReal.ofReal |L ω| ∂P = ∫⁻ ω, liminf (fun k => ENNReal.ofReal
        |wMass γ X δ f (wRad δ (k + 1)) ω|) atTop ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hL.tendsto] with ω h
      have h' : Tendsto (fun k => wMass γ X δ f (wRad δ (k + 1)) ω) atTop (𝓝 (L ω)) :=
        (tendsto_add_atTop_iff_nat (f := fun k => wMass γ X δ f (wRad δ k) ω) 1).2 h
      exact ((ENNReal.continuous_ofReal.tendsto _).comp (h'.abs)).liminf_eq.symm
    rw [h2]
    refine h1.trans ?_
    refine (liminf_le_liminf (Eventually.of_forall fun k =>
      lintegral_ofReal_abs_wMass_le hX γ hW hf (wRad_pos hδ _) (hk _ (by omega)))).trans ?_
    rw [liminf_const]
  have hGm : ∀ k, AEMeasurable (supG γ X δ f L k) P := fun k =>
    AEMeasurable.iSup fun n => AEMeasurable.iSup fun i =>
      (continuous_abs.measurable.comp_aemeasurable
        ((measurable_wMass hX γ hf δ _).aemeasurable.sub hL.aemeas)).ennreal_ofReal
  show ∫⁻ ω, (ENNReal.ofReal |L ω| + ∑' k, supG γ X δ f L (k + 2) ω) ∂P ≤ _
  rw [lintegral_add_left' hLm]
  refine (add_le_add hFatou (lintegral_tsum_supG_le hX hγ hγ2 hW hf hL)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg (mul_nonneg hM0
    (Real.rpow_nonneg hδ.le _)) (sumC_nonneg hγ hγ2))]
  congr 1
  rw [Real.rpow_add hδ, Real.rpow_two]
  ring

end MatedCRTHarmonic.LQGCoord
