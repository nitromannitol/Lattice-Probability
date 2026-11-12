/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.HeatDirR2c at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirR2b

/-!
# DGo (3.10) on a square: the assembly (task P2-HEAT2, packet R2)

Ding–Goswami, arXiv:1610.09998, `Watabiki_final.tex`, (3.10) (DGo:606, proof DGo:618–700):
`max_{v ∈ 𝒰_ε} Var(Δ_δ(v)) = O_{𝒰,ε}(1)` for `δ < ε/4`, with `𝒰 = D = (a, a+L)²`.

* `abs_dirCircFun_sub_phiKernel_le` — the pointwise split of DGo's
  `Δ_δ(v) = √π(G_{v;1} + G_{v;2} + G_{v;3} + G_{v;4})` (DGo:621–628) in kernel form:
  `|K^D_{δ,v} − k_{δ,1,v}| ≤ K e^{−cs} 1_D + g₂ + |g₄| + g₆`.
* **`dgo_var_bound`** — (3.10): `‖√π (K^D_{δ,v} − k_{δ,1,v})‖² ≤ σ²` uniformly in
  `δ ∈ (0, ε/4)` and `v` with `B̄_ε(v) ⊆ D`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Real Set Function Metric
open scoped ENNReal Interval

namespace LQGMetric
namespace DGo
namespace HeatDir

open HeatSq

variable {a L δ ε : ℝ} {v : ℂ}

/-- the constant of the envelope `K e^{−cs} 1_D(z)` -/
def envK (L ε : ℝ) : ℝ :=
  (smallConst (ε / 2) L + π⁻¹) * Real.exp (2 * DDDF.P29WN.rateC L) + decayConst L 1 ^ 2

/-- the envelope `1_{s>0} K e^{−cs} 1_D(z)` of the `s ≥ 1` part and of `p^D − p` inside `D` -/
def envFun (a L ε : ℝ) (q : ℝ × ℂ) : ℝ :=
  (Ioi 0).indicator (fun s => envK L ε * Real.exp (-DDDF.P29WN.rateC L * s)) q.1 *
    (sqOpen a L).indicator (fun _ => (1 : ℝ)) q.2

lemma envK_nonneg (L ε : ℝ) : 0 ≤ envK L ε := by
  have := smallConst_nonneg (ε / 2) L
  unfold envK; positivity

lemma envFun_nonneg (q : ℝ × ℂ) : 0 ≤ envFun a L ε q :=
  mul_nonneg (indicator_nonneg (fun s _ => by have := envK_nonneg L ε; positivity) _)
    (indicator_nonneg (fun _ _ => zero_le_one) _)

lemma memLp_envFun (hL : 0 < L) : MemLp (envFun a L ε) 2 (volume : Measure (ℝ × ℂ)) :=
  memLp_expInd (by unfold DDDF.P29WN.rateC; positivity) (envK L ε) a L

/-- `|(2π)⁻¹ ∫_{(0,2π]} f| ≤ C` when `|f| ≤ C` -/
lemma abs_avg_le {f : ℝ → ℝ} {C : ℝ} (h : ∀ θ, |f θ| ≤ C) :
    |(2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), f θ| ≤ C := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  rw [abs_mul, abs_of_pos (inv_pos.2 h2π), ← Real.norm_eq_abs]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) (2 * π))
    (f := f) (C := C) measure_Ioc_lt_top fun θ _ => by rw [Real.norm_eq_abs]; exact h θ
  rw [Real.volume_real_Ioc_of_le h2π.le, sub_zero] at hb
  calc (2 * π)⁻¹ * ‖∫ θ in Ioc 0 (2 * π), f θ‖ ≤ (2 * π)⁻¹ * (C * (2 * π)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C := by field_simp

/-- **The pointwise split** of `Δ_δ(v)`'s kernel (DGo:621–628). -/
theorem abs_dirCircFun_sub_phiKernel_le (hL : 0 < L) (hδ : 0 < δ) (hδε : δ < ε / 4)
    (hB : closedBall v ε ⊆ sqOpen a L) (s : ℝ) (z : ℂ) :
    |dirCircFun a L δ v (s, z) - WhiteNoise.phiKernel δ 1 v (s, z)| ≤
      envFun a L ε (s, z) + freeCircFun (δ ^ 2) δ v (s, z) + |g4Fun δ v (s, z)| +
        g6Fun ε v (s, z) := by
  have hε : 0 < ε := by linarith
  set c := DDDF.P29WN.rateC L
  have hc : 0 < c := by unfold c DDDF.P29WN.rateC; positivity
  set M0 := smallConst (ε / 2) L
  have hM0 : 0 ≤ M0 := smallConst_nonneg (ε / 2) L
  set K1 := decayConst L 1 ^ 2
  have hK1 : 0 ≤ K1 := sq_nonneg _
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hE0 : 0 ≤ envFun a L ε (s, z) := envFun_nonneg _
  have hF0 := freeCircFun_nonneg (T := δ ^ 2) (δ := δ) (v := v) (s, z)
  have hG0 : 0 ≤ g6Fun ε v (s, z) := indicator_nonneg (fun q hq =>
    heatKernel_nonneg _ (by have := hq.1.1; positivity) _ _) _
  have hg40 := abs_nonneg (g4Fun δ v (s, z))
  set A := (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), circHeat δ v (s, z) θ
  have hphi0 : s ∉ Icc (δ ^ 2) (1 ^ 2) → WhiteNoise.phiKernel δ 1 v (s, z) = 0 := fun h => by
    unfold WhiteNoise.phiKernel; exact indicator_of_notMem (fun h' => h h'.1) _
  have hphi1 : s ∈ Icc (δ ^ 2) 1 → WhiteNoise.phiKernel δ 1 v (s, z) = heatKernel (s / 2) v z :=
    fun h => by
      unfold WhiteNoise.phiKernel
      rw [indicator_of_mem (show ((s, z) : ℝ × ℂ) ∈ Icc (δ ^ 2) (1 ^ 2) ×ˢ (univ : Set ℂ) from
        ⟨by rwa [one_pow], trivial⟩)]
  rcases le_or_gt s 0 with hs | hs
  · rw [dirCircFun_of_nonpos hs, hphi0 (fun h => by nlinarith [h.1]), sub_zero, abs_zero]
    positivity
  by_cases hz : z ∈ sqOpen a L
  swap
  · have hD : dirCircFun a L δ v (s, z) = 0 := by
      unfold dirCircFun; exact indicator_of_notMem (fun h => hz h.2) _
    rw [hD, zero_sub, abs_neg]
    by_cases hI : s ∈ Icc (δ ^ 2) 1
    · rw [hphi1 hI, abs_of_nonneg (heatKernel_nonneg _ (by positivity) _ _)]
      have : g6Fun ε v (s, z) = heatKernel (s / 2) v z := by
        unfold g6Fun
        rw [indicator_of_mem (show ((s, z) : ℝ × ℂ) ∈ Ioc 0 1 ×ˢ (closedBall v ε)ᶜ from
          ⟨⟨hs, hI.2⟩, fun h => hz (hB h)⟩)]
      linarith
    · rw [hphi0 (fun h => hI (by rwa [one_pow] at h)), abs_zero]; positivity
  have hDd : dirCircFun a L δ v (s, z) =
      (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), sqDirKernel a L (s / 2) (circleMap v δ θ) z := by
    unfold dirCircFun
    rw [indicator_of_mem (show ((s, z) : ℝ × ℂ) ∈ Ioi 0 ×ˢ sqOpen a L from ⟨hs, hz⟩),
      intervalIntegral.integral_of_le h2π.le]
  have hE : envFun a L ε (s, z) = envK L ε * Real.exp (-c * s) := by
    simp only [envFun, indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs), indicator_of_mem hz,
      mul_one, c]
  have hA0 : 0 ≤ A := mul_nonneg (by positivity)
    (setIntegral_nonneg measurableSet_Ioc fun θ _ => circHeat_nonneg hs θ)
  rcases le_or_gt s 2 with hs2 | hs2
  · have hdiff : |dirCircFun a L δ v (s, z) - A| ≤ M0 := by
      have hm : Measurable fun θ => sqDirKernel a L (s / 2) (circleMap v δ θ) z :=
        measurable_sqDirKernel_comp hL (half_pos hs) (continuous_circleMap v δ).measurable
          measurable_const
      have hf : IntegrableOn (fun θ => sqDirKernel a L (s / 2) (circleMap v δ θ) z)
          (Ioc 0 (2 * π)) :=
        Integrable.mono' (integrableOn_const (C := decayConst L (s / 2) ^ 2)
          measure_Ioc_lt_top.ne) hm.aestronglyMeasurable (Filter.Eventually.of_forall fun θ => by
            rw [Real.norm_eq_abs]
            exact DDDF.P29WN.abs_sqDirKernel_le_const hL (half_pos hs) _ _)
      rw [hDd, ← mul_sub, ← integral_sub hf (integrableOn_circHeat (s, z))]
      refine abs_avg_le fun θ => ?_
      obtain ⟨hre, him⟩ := circle_margin hB hδ hδε θ
      exact abs_sqDirKernel_sub_heat_le hL (half_pos hε) (half_pos hs) (by linarith) hre him hz
    have hEM : M0 + π⁻¹ ≤ envFun a L ε (s, z) := by
      rw [hE]
      have h1 : 1 ≤ Real.exp (2 * c) * Real.exp (-c * s) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
      have h0 : 0 ≤ M0 + π⁻¹ := by positivity
      unfold envK
      nlinarith [Real.exp_pos (-c * s), Real.exp_pos (2 * c)]
    have hπ0 : 0 ≤ π⁻¹ := by positivity
    rcases lt_or_ge s (δ ^ 2) with hsδ | hsδ
    · rw [hphi0 (fun h => by linarith [h.1]), sub_zero]
      have hF : freeCircFun (δ ^ 2) δ v (s, z) = A := by
        unfold freeCircFun
        rw [indicator_of_mem (show ((s, z) : ℝ × ℂ) ∈ Ioc 0 (δ ^ 2) ×ˢ (univ : Set ℂ) from
          ⟨⟨hs, hsδ.le⟩, trivial⟩)]
      have := abs_sub_abs_le_abs_sub (dirCircFun a L δ v (s, z)) A
      rw [abs_of_nonneg hA0] at this
      linarith
    rcases le_or_gt s 1 with hs1 | hs1
    · rw [hphi1 ⟨hsδ, hs1⟩]
      have hg : g4Fun δ v (s, z) = A - heatKernel (s / 2) v z := by
        unfold g4Fun
        rw [indicator_of_mem (show ((s, z) : ℝ × ℂ) ∈ Icc (δ ^ 2) 1 ×ˢ (univ : Set ℂ) from
          ⟨⟨hsδ, hs1⟩, trivial⟩)]
      have := abs_sub_le (dirCircFun a L δ v (s, z)) A (heatKernel (s / 2) v z)
      rw [hg]
      linarith
    · rw [hphi0 (fun h => by nlinarith [h.2]), sub_zero]
      have hAπ : A ≤ π⁻¹ := by
        refine (le_abs_self A).trans (abs_avg_le fun θ => ?_)
        rw [abs_of_nonneg (circHeat_nonneg hs θ)]
        refine (heatKernel_le_inv_time (half_pos hs) _ _).trans ?_
        rw [show (2 * π)⁻¹ * (s / 2)⁻¹ = π⁻¹ * s⁻¹ by field_simp]
        exact mul_le_of_le_one_right hπ0 (inv_le_one_of_one_le₀ hs1.le)
      have := abs_sub_abs_le_abs_sub (dirCircFun a L δ v (s, z)) A
      rw [abs_of_nonneg hA0] at this
      linarith
  · rw [hphi0 (fun h => by nlinarith [h.2]), sub_zero, hDd]
    have hb : |(2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), sqDirKernel a L (s / 2) (circleMap v δ θ) z| ≤
        K1 * Real.exp (-c * s) := abs_avg_le fun θ => by
      have := DDDF.P29WN.abs_sqDirKernel_le_exp (a := a) hL (s := s / 2) (by linarith)
        (circleMap v δ θ) z
      rwa [show -(2 * DDDF.P29WN.rateC L) * (s / 2) = -c * s by ring] at this
    have hK : K1 * Real.exp (-c * s) ≤ envFun a L ε (s, z) := by
      rw [hE]
      have := smallConst_nonneg (ε / 2) L
      unfold envK
      have : 0 ≤ (smallConst (ε / 2) L + π⁻¹) * Real.exp (2 * c) := by positivity
      nlinarith [Real.exp_pos (-c * s)]
    linarith

/-- **DGo (3.10) on the square `D = (a, a+L)²`** (DGo:606, proof DGo:618–700): for every `ε > 0`
there is `σ²` with `‖√π (K^D_{δ,v} − k_{δ,1,v})‖² ≤ σ²` (i.e. `Var(ĥ^D_δ(v) − η_δ(v)) ≤ σ²`) for all
`δ ∈ (0, ε/4)` and all `v` with `B̄_ε(v) ⊆ D`. -/
theorem dgo_var_bound (a L : ℝ) : ∀ ε > 0, ∃ σ2 : ℝ, ∀ δ ∈ Ioo 0 (ε / 4), ∀ v : ℂ,
    closedBall v ε ⊆ sqOpen a L →
      ‖Real.sqrt Real.pi • (dirCircKernel a L δ v - WhiteNoise.phiKernelL2 δ 1 v)‖ ^ 2 ≤ σ2 := by
  intro ε hε
  by_cases hL : 0 < L
  swap
  · refine ⟨0, fun δ _ v hB => absurd (hB (mem_closedBall_self hε.le)) fun hv => hL ?_⟩
    obtain ⟨h1, h2, -, -⟩ := hv; linarith
  set C1 := (∫⁻ q, ENNReal.ofReal (envFun a L ε q ^ 2)).toReal
  have hC1 : ∫⁻ q, ENNReal.ofReal (envFun a L ε q ^ 2) ≠ ⊤ :=
    ((memLp_envFun (a := a) (ε := ε) hL).integrable_sq).lintegral_lt_top.ne
  have hC10 : 0 ≤ C1 := ENNReal.toReal_nonneg
  set B := 4 * (C1 + (2 * π)⁻¹ * (2 + 2 * Real.log 2) + 1 / π + (π * ε ^ 2)⁻¹)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hB0 : 0 ≤ B := by positivity
  refine ⟨π * B, fun δ hδ v hB => ?_⟩
  have hδ0 := hδ.1
  rw [norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt Real.pi_pos.le]
  refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
  have hBδ : closedBall v δ ⊆ sqOpen a L :=
    (closedBall_subset_closedBall (by linarith [hδ.2])).trans hB
  have hae : (⇑(dirCircKernel a L δ v - WhiteNoise.phiKernelL2 δ 1 v) : ℝ × ℂ → ℝ) =ᵐ[volume]
      fun q => dirCircFun a L δ v q - WhiteNoise.phiKernel δ 1 v q := by
    filter_upwards [Lp.coeFn_sub (dirCircKernel a L δ v) (WhiteNoise.phiKernelL2 δ 1 v),
      coeFn_dirCircKernel hL hδ0 hBδ, WhiteNoise.coeFn_phiKernelL2 δ 1 hδ0 v] with q h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  rw [DDDF.P29WN.sq_norm_eq_integral hae]
  refine DDDF.P29WN.integral_sq_le_of_lintegral hB0 ?_
  have hpt : ∀ q : ℝ × ℂ,
      ENNReal.ofReal ((dirCircFun a L δ v q - WhiteNoise.phiKernel δ 1 v q) ^ 2) ≤
      4 * (ENNReal.ofReal (envFun a L ε q ^ 2) + ENNReal.ofReal (freeCircFun (δ ^ 2) δ v q ^ 2) +
        ENNReal.ofReal (g4Fun δ v q ^ 2) + ENNReal.ofReal (g6Fun ε v q ^ 2)) := by
    rintro ⟨s, z⟩
    have h := abs_dirCircFun_sub_phiKernel_le hL hδ0 hδ.2 hB s z
    have e0 : 0 ≤ envFun a L ε (s, z) := envFun_nonneg _
    have f0 := freeCircFun_nonneg (T := δ ^ 2) (δ := δ) (v := v) (s, z)
    have g0 : 0 ≤ g6Fun ε v (s, z) := indicator_nonneg (fun q hq =>
      heatKernel_nonneg _ (by have := hq.1.1; positivity) _ _) _
    set X := dirCircFun a L δ v (s, z) - WhiteNoise.phiKernel δ 1 v (s, z)
    set e := envFun a L ε (s, z)
    set f := freeCircFun (δ ^ 2) δ v (s, z)
    set g := g4Fun δ v (s, z)
    set k := g6Fun ε v (s, z)
    have hsq : X ^ 2 ≤ 4 * (e ^ 2 + f ^ 2 + g ^ 2 + k ^ 2) := by
      have h1 := pow_le_pow_left₀ (abs_nonneg _) h 2
      rw [sq_abs] at h1
      have hg2 : |g| ^ 2 = g ^ 2 := sq_abs g
      nlinarith [sq_nonneg (e - f), sq_nonneg (e - |g|), sq_nonneg (e - k), sq_nonneg (f - |g|),
        sq_nonneg (f - k), sq_nonneg (|g| - k)]
    calc ENNReal.ofReal (X ^ 2) ≤ ENNReal.ofReal (4 * (e ^ 2 + f ^ 2 + g ^ 2 + k ^ 2)) :=
          ENNReal.ofReal_le_ofReal hsq
      _ = _ := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity)]
          norm_num
  have hmF : Measurable fun q => ENNReal.ofReal (freeCircFun (δ ^ 2) δ v q ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_freeCircFun.pow_const 2)
  have hmG : Measurable fun q => ENNReal.ofReal (g4Fun δ v q ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_g4Fun.pow_const 2)
  have hmH : Measurable fun q => ENNReal.ofReal (g6Fun ε v q ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_g6Fun.pow_const 2)
  calc ∫⁻ q, ENNReal.ofReal ((dirCircFun a L δ v q - WhiteNoise.phiKernel δ 1 v q) ^ 2)
      ≤ ∫⁻ q, 4 * (ENNReal.ofReal (envFun a L ε q ^ 2) +
          ENNReal.ofReal (freeCircFun (δ ^ 2) δ v q ^ 2) +
          ENNReal.ofReal (g4Fun δ v q ^ 2) + ENNReal.ofReal (g6Fun ε v q ^ 2)) := lintegral_mono hpt
    _ = 4 * ((∫⁻ q, ENNReal.ofReal (envFun a L ε q ^ 2)) +
          (∫⁻ q, ENNReal.ofReal (freeCircFun (δ ^ 2) δ v q ^ 2)) +
          (∫⁻ q, ENNReal.ofReal (g4Fun δ v q ^ 2)) + ∫⁻ q, ENNReal.ofReal (g6Fun ε v q ^ 2)) := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_add_right _ hmH,
          lintegral_add_right _ hmG, lintegral_add_right _ hmF]
    _ ≤ 4 * (ENNReal.ofReal C1 + ENNReal.ofReal ((2 * π)⁻¹ * (2 + 2 * Real.log 2)) +
          ENNReal.ofReal (1 / π) + ENNReal.ofReal ((π * ε ^ 2)⁻¹)) := by
        rw [ENNReal.ofReal_toReal hC1]
        exact mul_le_mul' le_rfl (add_le_add (add_le_add (add_le_add le_rfl
          (lintegral_freeCircFun_sq_le hδ0 v)) (lintegral_g4Fun_sq_le hδ0 v))
          (lintegral_g6Fun_sq_le hε v))
    _ = ENNReal.ofReal B := by
        have e1 : ENNReal.ofReal B = 4 * ENNReal.ofReal (C1 + (2 * π)⁻¹ * (2 + 2 * Real.log 2) +
            1 / π + (π * ε ^ 2)⁻¹) := by
          simp only [B]; rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
        rw [e1, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add hC10 (by positivity)]

/-- **DGo (3.10), white-noise form**: `Var(ĥ^D_δ(v) − η_δ(v)) ≤ σ²` with
`ĥ^D_δ(v) = √π W(K^D_{δ,v})` and `η_δ(v) = phi W δ 1 v`, for every white noise `W`. -/
theorem dgo_var_bound_W {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WhiteNoise.WNSpace → Ω → ℝ} (hW : WhiteNoise.IsWhiteNoise P W) (a L : ℝ) :
    ∀ ε > 0, ∃ σ2 : ℝ, ∀ δ ∈ Ioo 0 (ε / 4), ∀ v : ℂ, closedBall v ε ⊆ sqOpen a L →
      ProbabilityTheory.variance (fun ω => Real.sqrt Real.pi * W (dirCircKernel a L δ v) ω -
        WhiteNoise.phi W δ 1 v ω) P ≤ σ2 := by
  intro ε hε
  obtain ⟨σ2, hσ⟩ := dgo_var_bound a L ε hε
  refine ⟨σ2, fun δ hδ v hB => ?_⟩
  have h := hW.hasLaw ![dirCircKernel a L δ v, WhiteNoise.phiKernelL2 δ 1 v]
    ![Real.sqrt Real.pi, -Real.sqrt Real.pi]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have e : (fun ω => Real.sqrt Real.pi * W (dirCircKernel a L δ v) ω +
      -Real.sqrt Real.pi * W (WhiteNoise.phiKernelL2 δ 1 v) ω) =
      fun ω => Real.sqrt Real.pi * W (dirCircKernel a L δ v) ω - WhiteNoise.phi W δ 1 v ω := by
    funext ω; simp only [WhiteNoise.phi]; ring
  rw [e] at h
  rw [h.variance_eq, ProbabilityTheory.variance_id_gaussianReal,
    Real.coe_toNNReal _ (sq_nonneg _)]
  have e2 : Real.sqrt Real.pi • dirCircKernel a L δ v +
      -Real.sqrt Real.pi • WhiteNoise.phiKernelL2 δ 1 v =
      Real.sqrt Real.pi • (dirCircKernel a L δ v - WhiteNoise.phiKernelL2 δ 1 v) := by
    rw [neg_smul, ← sub_eq_add_neg, smul_sub]
  rw [e2]
  exact hσ δ hδ v hB

end HeatDir
end DGo
end LQGMetric
