/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3Eta9B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta9A
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L4FineHP
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2BridgeLemmas
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3VarBdry

/-!
# The field events behind DZZ l. 1193–1195 (P2-DZZETA2, step (1), probabilistic part)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`): (eq-tilde-h-eta-assump) l. 1100–1103 (from
Lemma 2.7, `lem-tilde-h-eta`, l. 548–576, **uniform up to `∂𝕍`**: the maximum is over `v ∈ 𝕍`),
the event `Ẽ_{δ,α}` (Definition.tilde-E, l. 1105–1107) and `𝓔_{δ,α}` (eq-def-E-delta-alpha, l. 864).

* `etaCV hW n`: a continuous version of `η_{2^{-n}}` (`exists_continuous_etaInf`).
* `tildeEtaEvent hW δ`: the event of (eq-tilde-h-eta-assump) with the threshold `√(log δ⁻¹)`:
  `|h̃_{2^{-j}}(v) − η_{2^{-j}}(v)| < √(log δ⁻¹)` for **all** `v ∈ 𝕍`, `j ≥ 0` (continuous versions);
  `highProb_tildeEtaEvent`: it has high probability (`dzz_lemma27_uncond`).
* `ae_etaCV_center`, `ae_etaCV_split`: the null sets where the versions disagree (dyadic centres;
  a.e. `z`, by Fubini, for the band split `η_{2^{-n}} = η_{2^{-p}} + η^{2^{-p}}_{2^{-n}}`).
* `etaCV_ge_of_nbrFine`: on DZZ's `𝓔_{δ,α}` at all finer centres (`nbrFineEvent`, P2-DZZ3B), the
  bound `η_{2^{-m-j}}(z) ≥ η_s(c_B) − α√L log L` holds at **every** `z` near `c_B` (limit along the
  centres of `boxAt N z`, continuity of `etaCV`).
* `dens_compare_real`: the pointwise algebra of the density comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent GMCIdent3 GMCIdent4 SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- a continuous version of `η_{2^{-n}}` -/
def etaCV (hW : IsWhiteNoise P W) (n : ℕ) : ℂ → Ω → ℝ :=
  (exists_continuous_etaInf hW (δ := (2 : ℝ)⁻¹ ^ n) (by positivity)).choose

lemma etaCV_spec (hW : IsWhiteNoise P W) (n : ℕ) :
    (∀ ω, Continuous fun x => etaCV hW n x ω) ∧ (∀ x, Measurable (etaCV hW n x)) ∧
      ∀ x, etaCV hW n x =ᵐ[P] etaInf W ((2 : ℝ)⁻¹ ^ n) x :=
  (exists_continuous_etaInf hW (δ := (2 : ℝ)⁻¹ ^ n) (by positivity)).choose_spec

lemma measurable_etaCV_uncurry (hW : IsWhiteNoise P W) (n : ℕ) :
    Measurable fun p : ℂ × Ω => etaCV hW n p.1 p.2 :=
  measurable_uncurry_of_continuous_of_measurable (etaCV_spec hW n).1 (etaCV_spec hW n).2.1

lemma mem_ferniqueBox_of_dzzV {z : ℂ} (hz : z ∈ dzzV) : z ∈ ferniqueBox 0 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  simp only [ferniqueBox, Complex.mem_reProdIm, Complex.zero_re, Complex.zero_im, zero_add,
    mem_Icc]
  exact ⟨⟨h1, h2⟩, h3, h4⟩

/-- **(eq-tilde-h-eta-assump)** (DZZ l. 1100–1103) with threshold `√(log δ⁻¹)`, for all `v ∈ 𝕍` -/
def tildeEtaEvent (hW : IsWhiteNoise P W) (δ : ℝ) : Set Ω :=
  {ω | ∀ v ∈ dzzV, ∀ j : ℕ, |coarseVer hW j v ω - etaCV hW j v ω| < Real.sqrt (Real.log δ⁻¹)}

universe u

/-- **DZZ Lemma 2.7 ⇒ (eq-tilde-h-eta-assump) w.h.p.** -/
theorem highProb_tildeEtaEvent {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) :
    HighProb P (fun δ => tildeEtaEvent hW δ) := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := dzz_lemma27_uncond.{u}
  set Z : ℕ → ℂ → Ω → ℝ := fun j x ω => coarseVer hW j x ω - etaCV hW j x ω with hZ
  have hZc : ∀ j ω, Continuous fun x => Z j x ω := fun j ω =>
    ((coarseVer_spec hW j).1 ω).sub ((etaCV_spec hW j).1 ω)
  have hZae : ∀ j x, Z j x =ᵐ[P] fun ω => tildeHInf W ((1 / 2 : ℝ) ^ j) x ω -
      etaInf W ((1 / 2 : ℝ) ^ j) x ω := by
    intro j x
    filter_upwards [(coarseVer_spec hW j).2.2 x, (etaCV_spec hW j).2.2 x] with ω h1 h2
    simp only [hZ, h1, h2, one_div]
  -- `δ ≤ δ₁ := min (1/2) (C^{-2C})` gives `C δ^{1/C} ≤ δ^{1/(2C)}`
  set δ₁ : ℝ := min (1 / 2) ((C ^ (2 * C))⁻¹) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min (by norm_num) (inv_pos.2 (Real.rpow_pos_of_pos hC0 _))
  refine ⟨1 / (2 * C), by positivity, δ₁, hδ₁0, fun δ ⟨hδ0, hδ1⟩ => ?_⟩
  have hδ2 : δ < 1 / 2 := hδ1.trans_le (min_le_left _ _)
  have hL0 : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hδ0, by linarith⟩)
  have hsub : (tildeEtaEvent hW δ)ᶜ ⊆
      {ω | ∃ v ∈ ferniqueBox 0 1, ∃ j : ℕ, Real.sqrt (Real.log δ⁻¹) ≤ |Z j v ω|} := by
    intro ω hω
    simp only [tildeEtaEvent, mem_compl_iff, mem_setOf_eq, not_forall, not_lt] at hω
    obtain ⟨v, hv, j, hj⟩ := hω
    exact ⟨v, mem_ferniqueBox_of_dzzV hv, j, hj⟩
  have hb := hC hW Z hZc hZae (Real.sqrt (Real.log δ⁻¹)) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt hL0] at hb
  have he : Real.exp (-Real.log δ⁻¹ / C) = δ ^ (1 / C) := by
    rw [Real.rpow_def_of_pos hδ0, Real.log_inv]; ring_nf
  have hsplit : δ ^ (1 / C) = δ ^ (1 / (2 * C)) * δ ^ (1 / (2 * C)) := by
    rw [← Real.rpow_add hδ0]; congr 1; field_simp; ring
  have hCd : C * δ ^ (1 / (2 * C)) ≤ 1 := by
    have h1 : δ ≤ (C ^ (2 * C))⁻¹ := hδ1.le.trans (min_le_right _ _)
    have h2 : δ ^ (1 / (2 * C)) ≤ ((C ^ (2 * C))⁻¹) ^ (1 / (2 * C)) :=
      Real.rpow_le_rpow hδ0.le h1 (by positivity)
    rw [Real.inv_rpow (Real.rpow_nonneg hC0.le _), ← Real.rpow_mul hC0.le,
      show 2 * C * (1 / (2 * C)) = 1 by field_simp, Real.rpow_one] at h2
    calc C * δ ^ (1 / (2 * C)) ≤ C * C⁻¹ := mul_le_mul_of_nonneg_left h2 hC0.le
      _ = 1 := mul_inv_cancel₀ hC0.ne'
  have hreal : P.real (tildeEtaEvent hW δ)ᶜ ≤ δ ^ (1 / (2 * C)) := by
    refine (measureReal_mono hsub).trans (hb.trans ?_)
    rw [he, hsplit, ← mul_assoc]
    have := Real.rpow_nonneg hδ0.le (1 / (2 * C))
    nlinarith
  rw [← ofReal_measureReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- the versions agree at all dyadic centres, a.s. -/
lemma ae_etaCV_center (hW : IsWhiteNoise P W) :
    ∀ᵐ ω ∂P, ∀ (p : ℕ) (b : DyBox), etaCV hW p b.center ω = etaInf W ((2 : ℝ)⁻¹ ^ p) b.center ω := by
  rw [ae_all_iff]; intro p
  rw [ae_all_iff]; intro b
  exact (etaCV_spec hW p).2.2 b.center

/-- the band split `η_{2^{-n}} = η_{2^{-p}} + η^{2^{-p}}_{2^{-n}}` for the versions, a.s. for a.e. `z` -/
lemma ae_etaCV_split (hW : IsWhiteNoise P W) :
    ∀ᵐ ω ∂P, ∀ p n : ℕ, p ≤ n → ∀ᵐ z ∂(volume : Measure ℂ),
      etaCV hW n z ω = etaVer W ((2 : ℝ)⁻¹ ^ p) n z ω + etaCV hW p z ω := by
  have hP := hW.isProbabilityMeasure
  rw [ae_all_iff]; intro p
  rw [ae_all_iff]; intro n
  by_cases hpn : p ≤ n
  swap
  · exact Eventually.of_forall fun ω h => absurd h hpn
  have hle : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ p := pow_le_pow_of_le_one (by norm_num) (by norm_num) hpn
  have hm1 := measurable_etaCV_uncurry hW n
  have hm2 : Measurable fun q : ℂ × Ω => etaVer W ((2 : ℝ)⁻¹ ^ p) n q.1 q.2 + etaCV hW p q.1 q.2 :=
    (measurable_etaVer hW _ n).add (measurable_etaCV_uncurry hW p)
  have h : ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume : Measure ℂ),
      etaCV hW n z ω = etaVer W ((2 : ℝ)⁻¹ ^ p) n z ω + etaCV hW p z ω := by
    refine (Measure.ae_ae_comm (μ := (volume : Measure ℂ)) (ν := P)
      (p := fun z ω => etaCV hW n z ω = etaVer W ((2 : ℝ)⁻¹ ^ p) n z ω + etaCV hW p z ω)
      (measurableSet_eq_fun hm1 hm2)).1 (Eventually.of_forall fun z => ?_)
    filter_upwards [(etaCV_spec hW n).2.2 z, (etaCV_spec hW p).2.2 z,
      etaVer_ae_eq hW ((2 : ℝ)⁻¹ ^ p) n z,
      etaInf_eq_add_eta_ae hW (ε' := (2 : ℝ)⁻¹ ^ n) (by positivity) hle z] with ω h1 h2 h3 h4
    rw [h1, h2, h3, h4, add_comm]
    rfl
  filter_upwards [h] with ω hω _
  exact hω

/-- **η at every `z` near `c_B`** on `nbrFineGen` (with the versions agreeing at the centres):
`η_{2^{-m-j}}(z) ≥ η_s(c_B) − T` for `‖z − c_B‖ < 8 s`. -/
lemma etaCV_ge_of_nbrFine (hW : IsWhiteNoise P W) {X Y T : ℝ} {ω : Ω}
    (hω : ω ∈ nbrFineGen W X Y T)
    (hc : ∀ (p : ℕ) (b : DyBox), etaCV hW p b.center ω = etaInf W ((2 : ℝ)⁻¹ ^ p) b.center ω)
    {B : DyBox} {j : ℕ} (hm : (2 : ℝ) ^ B.n ≤ X) (hj : (2 : ℝ) ^ j ≤ Y) {z : ℂ} (hz : z ∈ dzzV)
    (hzB : ‖z - B.center‖ < 8 * B.side) :
    etaInf W B.side B.center ω - T ≤ etaCV hW (B.n + j) z ω := by
  have hz' := mem_ferniqueBox_of_dzzV hz
  set c : ℕ → ℂ := fun N => (DyBox.boxAt N z).center with hcdef
  have hcN : ∀ N, ‖z - c N‖ ≤ (2 : ℝ)⁻¹ ^ N := fun N => DyBox.norm_sub_center_boxAt_le hz' N
  have htc : Tendsto c atTop (𝓝 z) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num))
    rw [norm_sub_rev]; exact hcN N
  have ht : Tendsto (fun N => etaCV hW (B.n + j) (c N) ω) atTop (𝓝 (etaCV hW (B.n + j) z ω)) :=
    ((etaCV_spec hW (B.n + j)).1 ω).continuousAt.tendsto.comp htc
  have hgap : 0 < 8 * B.side - ‖z - B.center‖ := by linarith
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one hgap (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ge_of_tendsto ht (eventually_atTop.2 ⟨max N₀ (B.n + j), fun N hN => ?_⟩)
  have hN1 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN2 : B.n + j ≤ N := (le_max_right _ _).trans hN
  have hpow : (2 : ℝ)⁻¹ ^ N ≤ (2 : ℝ)⁻¹ ^ N₀ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hN1
  have h8 : ‖B.center - (DyBox.boxAt N z).center‖ ≤ 8 * B.side := by
    calc ‖B.center - (DyBox.boxAt N z).center‖ ≤ ‖B.center - z‖ + ‖z - (DyBox.boxAt N z).center‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖z - B.center‖ + (2 : ℝ)⁻¹ ^ N := by rw [norm_sub_rev B.center z]; exact add_le_add le_rfl (hcN N)
      _ ≤ 8 * B.side := by linarith
  have h := hω B.n j hm hj B (DyBox.boxAt N z) rfl hN2 h8
  rw [hcdef]; simp only
  rw [hc (B.n + j) (DyBox.boxAt N z)]
  have := (abs_le.1 h).2
  linarith

/-- **the pointwise algebra of the density comparison** (DZZ l. 1193–1195): with
`h̃_n ≥ η_n − T₁`, `η_n = η^{δ̂}_n + η_{δ̂}`, `η_{δ̂}(z) ≥ η_s(c_B) − T₂`,
`Var h̃_n ≤ Var η^{δ̂}_n + Var η_s(c_B) + V`, `m₀ ≤ M_{γ,s}(B) = s² e^{γη_s(c_B) − γ²/2 Var}` and
`c_A ≤ e^{−γ(T₁+T₂) − γ²/2 V}`:
`c_A m₀ s^{-2} e^{γ η^{δ̂}_n − γ²/2 Var η^{δ̂}_n} ≤ e^{γ h̃_n − γ²/2 Var h̃_n}`. -/
lemma dens_compare_real {γ cv yn ev yp eB tv bv vB T₁ T₂ V m₀ s cA : ℝ} (hγ : 0 < γ)
    (h1 : yn - T₁ ≤ cv) (h2 : yn = ev + yp) (h3 : eB - T₂ ≤ yp) (h4 : tv ≤ bv + vB + V)
    (hs : 0 < s) (h7 : m₀ ≤ s ^ 2 * Real.exp (γ * eB - γ ^ 2 / 2 * vB)) (hcA0 : 0 ≤ cA)
    (h8 : cA ≤ Real.exp (-(γ * (T₁ + T₂)) - γ ^ 2 / 2 * V)) :
    cA * m₀ / s ^ 2 * Real.exp (γ * ev - γ ^ 2 / 2 * bv) ≤
      Real.exp (γ * cv - γ ^ 2 / 2 * tv) := by
  have hs2 : 0 < s ^ 2 := by positivity
  by_cases hm : m₀ ≤ 0
  · have : cA * m₀ / s ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hcA0 hm) hs2.le
    exact (mul_nonpos_of_nonpos_of_nonneg this (Real.exp_pos _).le).trans (Real.exp_pos _).le
  push Not at hm
  have hm' : m₀ / s ^ 2 ≤ Real.exp (γ * eB - γ ^ 2 / 2 * vB) := by
    rw [div_le_iff₀ hs2]; linarith [mul_comm (s ^ 2) (Real.exp (γ * eB - γ ^ 2 / 2 * vB))]
  have hA : cA * m₀ / s ^ 2 ≤ Real.exp (-(γ * (T₁ + T₂)) - γ ^ 2 / 2 * V) *
      Real.exp (γ * eB - γ ^ 2 / 2 * vB) := by
    rw [mul_div_assoc]
    exact mul_le_mul h8 hm' (div_pos hm hs2).le (Real.exp_pos _).le
  refine (mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have e1 : γ * (yn - T₁) ≤ γ * cv := mul_le_mul_of_nonneg_left h1 hγ.le
  have e3 : γ * (eB - T₂) ≤ γ * yp := mul_le_mul_of_nonneg_left h3 hγ.le
  have e4 : γ ^ 2 / 2 * tv ≤ γ ^ 2 / 2 * (bv + vB + V) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  rw [h2] at e1
  nlinarith

end DZZ
end LQGMetric
