/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCoord.WPLimit at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.WPMass

/-!
# Dyadic limits of the normalized masses, with `L¹` rates along every offset

For a window
`(S, δ)` and a test function `f`, the normalized masses `wMass γ X δ f s` along the dyadic radii
`wRad δ k = δ 2^{-k}` converge almost surely to a limit `L` (`exists_wMass_limit`), with
`E|wMass (wRad δ k) − L| ≤ C M δ^{2+γ²/2} q^k`, and for every offset `c ∈ [1, 2]`
`E|wMass (c · wRad δ k) − L| ≤ C' M δ^{2+γ²/2} q^k` (`WMassLimit.offset`), `q = 2^{-β} < 1`.
Proof: the two-radius rate (`integral_abs_wMass_sub_le`) at the pairs `(δ 2^{-k-1}, δ 2^{-k})`
(summable) and `(δ 2^{-k}, c δ 2^{-k})`, and the generic lemma `exists_ae_limit_of_summable`
(summable `L¹` increments give an a.s. limit with the tail bound). Own elementary glue.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal Real

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric LQGMetric.CircleAvg QuantumZipper

/-- **A.s. limits from summable `L¹` increments**, with the tail bound. -/
theorem exists_ae_limit_of_summable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {G : ℕ → Ω → ℝ} (hG : ∀ k, AEMeasurable (G k) P) {b : ℕ → ℝ} (hb0 : ∀ k, 0 ≤ b k)
    (hb : Summable b)
    (hstep : ∀ k, ∫⁻ ω, ENNReal.ofReal |G (k + 1) ω - G k ω| ∂P ≤ ENNReal.ofReal (b k)) :
    ∃ L : Ω → ℝ, AEMeasurable L P ∧ (∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (L ω))) ∧
      ∀ k, ∫⁻ ω, ENNReal.ofReal |G k ω - L ω| ∂P ≤ ENNReal.ofReal (∑' j, b (k + j)) := by
  set d : ℕ → Ω → ℝ := fun j ω => |G (j + 1) ω - G j ω| with hd
  have hdm : ∀ j, AEMeasurable (fun ω => ENNReal.ofReal (d j ω)) P := fun j =>
    (continuous_abs.measurable.comp_aemeasurable ((hG (j + 1)).sub (hG j))).ennreal_ofReal
  have hsum : ∫⁻ ω, ∑' j, ENNReal.ofReal (d j ω) ∂P ≠ ⊤ := by
    rw [lintegral_tsum hdm]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hstep)
    rw [← ENNReal.ofReal_tsum_of_nonneg hb0 hb]
    exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ ω ∂P, ∑' j, ENNReal.ofReal (d j ω) ≠ ⊤ :=
    (ae_lt_top' (AEMeasurable.ennreal_tsum hdm) hsum).mono fun ω h => h.ne
  have hsumm : ∀ᵐ ω ∂P, Summable fun j => d j ω := by
    filter_upwards [hae] with ω h
    have := ENNReal.summable_toReal h
    simpa [hd, ENNReal.toReal_ofReal (abs_nonneg _)] using this
  have hdist : ∀ ω j, dist (G j ω) (G j.succ ω) ≤ d j ω := fun ω j => by
    rw [Real.dist_eq, abs_sub_comm]
  set L : Ω → ℝ := fun ω => limUnder atTop fun k => G k ω
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (L ω)) := by
    filter_upwards [hsumm] with ω h
    exact (cauchySeq_of_dist_le_of_summable (fun j => d j ω) (hdist ω) h).tendsto_limUnder
  refine ⟨L, aemeasurable_of_tendsto_metrizable_ae' hG hconv, hconv, fun k => ?_⟩
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal |G k ω - L ω| ≤ ∑' j, ENNReal.ofReal (d (k + j) ω) := by
    filter_upwards [hsumm, hconv] with ω hs ht
    have h1 := dist_le_tsum_of_dist_le_of_tendsto (fun j => d j ω) (hdist ω) hs ht k
    rw [Real.dist_eq] at h1
    have hs' : Summable fun j => d (k + j) ω := by
      have := (summable_nat_add_iff k).2 hs
      simpa only [add_comm] using this
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => abs_nonneg _) hs']
    exact ENNReal.ofReal_le_ofReal h1
  refine (lintegral_mono_ae hpt).trans ?_
  have hb' : Summable fun j => b (k + j) := by
    have := (summable_nat_add_iff k).2 hb
    simpa only [add_comm] using this
  rw [lintegral_tsum fun j => hdm (k + j),
    ENNReal.ofReal_tsum_of_nonneg (fun j => hb0 _) hb']
  exact ENNReal.tsum_le_tsum fun j => hstep (k + j)

/-! ## Dyadic radii -/

/-- the dyadic radii `δ 2^{-k}` -/
def wRad (δ : ℝ) (k : ℕ) : ℝ := δ * (2 : ℝ)⁻¹ ^ k

lemma wRad_pos {δ : ℝ} (hδ : 0 < δ) (k : ℕ) : 0 < wRad δ k := by unfold wRad; positivity

lemma wRad_succ (δ : ℝ) (k : ℕ) : wRad δ (k + 1) = wRad δ k / 2 := by
  unfold wRad; rw [pow_succ]; ring

lemma wRad_le_half {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : 1 ≤ k) : wRad δ k ≤ δ / 2 := by
  unfold wRad
  have : (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  rw [pow_one] at this
  nlinarith

lemma two_mul_wRad_le_half {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : 2 ≤ k) :
    2 * wRad δ k ≤ δ / 2 := by
  have h := wRad_le_half hδ (show 1 ≤ k - 1 by omega)
  have e : wRad δ k = wRad δ (k - 1) / 2 := by
    rw [← wRad_succ]; congr 1; omega
  rw [e]; linarith

/-- the geometric ratio `q = 2^{-β}` -/
def wq (γ : ℝ) : ℝ := (2 : ℝ)⁻¹ ^ AreaExist.areaRate γ

lemma wq_pos (γ : ℝ) : 0 < wq γ := by unfold wq; positivity

lemma wq_lt_one {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : wq γ < 1 :=
  Real.rpow_lt_one (by norm_num) (by norm_num) (AreaExist.areaRate_pos hγ hγ2)

lemma wRad_div_rpow {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) (k : ℕ) :
    (wRad δ k / δ) ^ AreaExist.areaRate γ = wq γ ^ k := by
  rw [wRad, mul_div_cancel_left₀ _ hδ.ne', wq, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]

/-! ## Limits of the masses -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
variable {S : Set ℂ} {δ : ℝ} {f : ℂ → ℝ} {M : ℝ}

lemma measurable_wMass (hX : IsWholePlaneGFF X P) (γ : ℝ) (hf : WinFun S f M) (δ s : ℝ) :
    Measurable (wMass γ X δ f s) := by
  have h : StronglyMeasurable (Function.uncurry fun (ω : Ω) (z : ℂ) => f z * wDens γ X δ s z ω) :=
    ((hf.meas.comp measurable_snd).mul (measurable_wDens hX γ δ s)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := volume)).measurable

/-- the step bound in `lintegral` form -/
lemma lintegral_wMass_step_le (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hW : Win S δ) (hf : WinFun S f M) {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ ω, ENNReal.ofReal |wMass γ X δ f (wRad δ (k + 1)) ω - wMass γ X δ f (wRad δ k) ω| ∂P ≤
      ENNReal.ofReal (wConst γ * M * δ ^ (2 + γ ^ 2 / 2) * wq γ ^ k) := by
  have hδ := hW.pos
  have h1 := wRad_pos hδ (k + 1)
  have h2 := wRad_le_half hδ hk
  have h12 : wRad δ (k + 1) ≤ wRad δ k := by rw [wRad_succ]; linarith [wRad_pos hδ k]
  have h21 : wRad δ k ≤ 2 * wRad δ (k + 1) := by rw [wRad_succ]; linarith
  have hb := integral_abs_wMass_sub_le (P := P) hX hγ hγ2 hW hf h1 h12 h21 h2
  rw [wRad_div_rpow hδ] at hb
  have hi : Integrable (fun ω => |wMass γ X δ f (wRad δ k) ω -
      wMass γ X δ f (wRad δ (k + 1)) ω|) P :=
    ((integrable_wMass hX γ hW hf (wRad_pos hδ k) h2).sub
      (integrable_wMass hX γ hW hf h1 (by rw [wRad_succ]; linarith))).abs
  simp_rw [abs_sub_comm (wMass γ X δ f (wRad δ (k + 1)) _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hb

/-- the limit of the masses along `wRad δ (k + 1)`, with its rates -/
structure WMassLimit (γ : ℝ) (X : Ω → DistC) (P : Measure Ω) (δ : ℝ) (f : ℂ → ℝ) (M : ℝ)
    (L : Ω → ℝ) : Prop where
  aemeas : AEMeasurable L P
  tendsto : ∀ᵐ ω ∂P, Tendsto (fun k => wMass γ X δ f (wRad δ k) ω) atTop (𝓝 (L ω))
  rate : ∀ k, 1 ≤ k → ∫⁻ ω, ENNReal.ofReal |wMass γ X δ f (wRad δ k) ω - L ω| ∂P ≤
    ENNReal.ofReal (wConst γ * M * δ ^ (2 + γ ^ 2 / 2) * wq γ ^ k / (1 - wq γ))

theorem exists_wMass_limit (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hW : Win S δ) (hf : WinFun S f M) : ∃ L, WMassLimit γ X P δ f M L := by
  have hδ := hW.pos
  have hC0 : 0 ≤ wConst γ * M * δ ^ (2 + γ ^ 2 / 2) :=
    mul_nonneg (mul_nonneg (wConst_nonneg γ) hf.M_nonneg) (Real.rpow_nonneg hδ.le _)
  have hq0 := wq_pos γ
  have hq1 := wq_lt_one hγ hγ2
  have hb0 : ∀ k : ℕ, 0 ≤ wConst γ * M * δ ^ (2 + γ ^ 2 / 2) * wq γ ^ (k + 1) :=
    fun k => mul_nonneg hC0 (pow_nonneg hq0.le _)
  have hb : Summable fun k : ℕ => wConst γ * M * δ ^ (2 + γ ^ 2 / 2) * wq γ ^ (k + 1) := by
    have := (summable_geometric_of_lt_one hq0.le hq1).mul_left
      (wConst γ * M * δ ^ (2 + γ ^ 2 / 2) * wq γ)
    refine this.congr fun k => ?_
    rw [pow_succ]; ring
  have hstep : ∀ k : ℕ, ∫⁻ ω, ENNReal.ofReal |wMass γ X δ f (wRad δ (k + 1 + 1)) ω -
      wMass γ X δ f (wRad δ (k + 1)) ω| ∂P ≤
      ENNReal.ofReal (wConst γ * M * δ ^ (2 + γ ^ 2 / 2) * wq γ ^ (k + 1)) :=
    fun k => lintegral_wMass_step_le hX hγ hγ2 hW hf (k := k + 1) (by omega)
  obtain ⟨L, hLm, hLt, hLr⟩ := exists_ae_limit_of_summable
    (G := fun k => wMass γ X δ f (wRad δ (k + 1)))
    (fun k => (measurable_wMass hX γ hf δ _).aemeasurable) hb0 hb hstep
  refine ⟨L, ⟨hLm, ?_, fun k hk => ?_⟩⟩
  · filter_upwards [hLt] with ω h
    exact (tendsto_add_atTop_iff_nat (f := fun k => wMass γ X δ f (wRad δ k) ω) 1).1 h
  · have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have h := hLr (k - 1)
    simp only [hk1] at h
    refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    have : (fun j => wConst γ * M * δ ^ (2 + γ ^ 2 / 2) * wq γ ^ (k - 1 + j + 1)) =
        fun j => wConst γ * M * δ ^ (2 + γ ^ 2 / 2) * wq γ ^ k * wq γ ^ j := by
      funext j
      rw [show k - 1 + j + 1 = k + j by omega, pow_add]; ring
    rw [this, tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
    ring

/-- the constant of the offset rate -/
def wConstG (γ : ℝ) : ℝ := wConst γ * (2 ^ AreaExist.areaRate γ + 1 / (1 - wq γ))

/-- **The offset rate**: `E|wMass (c δ 2^{-k}) − L| ≤ wConstG γ · M · δ^{2+γ²/2} · q^k` for every
offset `c ∈ [1, 2]` and `k ≥ 2`. -/
theorem WMassLimit.offset {γ : ℝ} {L : Ω → ℝ} (hL : WMassLimit γ X P δ f M L)
    (hX : IsWholePlaneGFF X P) (hγ : 0 < γ) (hγ2 : γ < 2) (hW : Win S δ) (hf : WinFun S f M)
    {k : ℕ} (hk : 2 ≤ k) {c : ℝ} (hc : c ∈ Icc (1 : ℝ) 2) :
    ∫⁻ ω, ENNReal.ofReal |wMass γ X δ f (c * wRad δ k) ω - L ω| ∂P ≤
      ENNReal.ofReal (wConstG γ * M * δ ^ (2 + γ ^ 2 / 2) * wq γ ^ k) := by
  have hδ := hW.pos
  have hr := wRad_pos hδ k
  have hc1 : 1 ≤ c := hc.1
  have hc2 : c ≤ 2 := hc.2
  have hcr : c * wRad δ k ≤ δ / 2 := by
    have := two_mul_wRad_le_half hδ hk; nlinarith
  have hq0 := wq_pos γ
  have hq1 := wq_lt_one hγ hγ2
  set C := wConst γ * M * δ ^ (2 + γ ^ 2 / 2) with hC
  have hC0 : 0 ≤ C := mul_nonneg (mul_nonneg (wConst_nonneg γ) hf.M_nonneg)
    (Real.rpow_nonneg hδ.le _)
  -- the cross term
  have hcross := integral_abs_wMass_sub_le (P := P) hX hγ hγ2 hW hf hr
    (le_mul_of_one_le_left hr.le hc1) (mul_le_mul_of_nonneg_right hc2 hr.le) hcr
  have hβ0 : 0 ≤ AreaExist.areaRate γ := (AreaExist.areaRate_pos hγ hγ2).le
  have hcq : (c * wRad δ k / δ) ^ AreaExist.areaRate γ ≤
      2 ^ AreaExist.areaRate γ * wq γ ^ k := by
    rw [mul_div_assoc, Real.mul_rpow (by linarith) (div_pos hr hδ).le, wRad_div_rpow hδ]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by linarith) hc2 hβ0)
      (pow_nonneg hq0.le _)
  have hi : Integrable (fun ω => |wMass γ X δ f (c * wRad δ k) ω - wMass γ X δ f (wRad δ k) ω|)
      P := ((integrable_wMass hX γ hW hf (by positivity) hcr).sub
        (integrable_wMass hX γ hW hf hr ((le_mul_of_one_le_left hr.le hc1).trans hcr))).abs
  have h1 : ∫⁻ ω, ENNReal.ofReal |wMass γ X δ f (c * wRad δ k) ω -
      wMass γ X δ f (wRad δ k) ω| ∂P ≤ ENNReal.ofReal (C * (2 ^ AreaExist.areaRate γ *
        wq γ ^ k)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hcross.trans (mul_le_mul_of_nonneg_left hcq hC0))
  have h2 := hL.rate k (by omega)
  have hmeas1 : AEMeasurable (fun ω => ENNReal.ofReal |wMass γ X δ f (c * wRad δ k) ω -
      wMass γ X δ f (wRad δ k) ω|) P :=
    (continuous_abs.measurable.comp ((measurable_wMass hX γ hf δ _).sub
      (measurable_wMass hX γ hf δ _))).ennreal_ofReal.aemeasurable
  calc ∫⁻ ω, ENNReal.ofReal |wMass γ X δ f (c * wRad δ k) ω - L ω| ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal |wMass γ X δ f (c * wRad δ k) ω - wMass γ X δ f (wRad δ k) ω| +
          ENNReal.ofReal |wMass γ X δ f (wRad δ k) ω - L ω|) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ = (∫⁻ ω, ENNReal.ofReal |wMass γ X δ f (c * wRad δ k) ω -
          wMass γ X δ f (wRad δ k) ω| ∂P) +
        ∫⁻ ω, ENNReal.ofReal |wMass γ X δ f (wRad δ k) ω - L ω| ∂P :=
        lintegral_add_left' hmeas1 _
    _ ≤ ENNReal.ofReal (C * (2 ^ AreaExist.areaRate γ * wq γ ^ k)) +
        ENNReal.ofReal (C * wq γ ^ k / (1 - wq γ)) := add_le_add h1 h2
    _ = ENNReal.ofReal (wConstG γ * M * δ ^ (2 + γ ^ 2 / 2) * wq γ ^ k) := by
        rw [← ENNReal.ofReal_add (by positivity) (div_nonneg (by positivity)
          (by linarith))]
        congr 1
        rw [wConstG, hC]
        field_simp

end MatedCRTHarmonic.LQGCoord
