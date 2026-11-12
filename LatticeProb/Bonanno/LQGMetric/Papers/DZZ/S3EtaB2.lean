/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3EtaB2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3EtaB1

/-!
# (eq-M-tilde-B-bound) at `M^W` (P2-DZZETA2, step (2))

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` (eq-M-tilde-B-bound), l. 1116–1119): on
`{M_{γ,s}(B) ≤ δ²} ∩ Ẽ_{δ,α}`, for every box `B̃ ∈ 𝓑(B,t) ∪ 𝓑_∂(B_large,t)`,
`M_γ(B̃) ≤ e^{2αγ√L log L} δ² s^{−2} M̃_{γ,ε²s,η}(B̃)` (`M_γ = M^W = wickQArea γ W`,
`ε = 2^{-kL37}`, `ε² s = 2^{-(n_B + 2 kL37)}`).

* `L32TildeMUpper P γ W ν`: the statement, for all dyadic boxes `B` of side `≥ δ^{C_mc}`
  (DZZ: `1 ≤ m ≤ C_mc log₂ δ⁻¹`) and all dyadic boxes `B̃` within distance `3 s` of `c_B` (this
  contains both of DZZ's families: `B_large` has side `2s` and the boxes have side `ts ≤ s`).
* **`l32TildeMUpper_wickQArea`**: it holds for `ν = wickQArea γ W`, on the event
  `wickGoodU ∩ (eq-tilde-h-eta-assump) ∩ 𝓔_{δ,α}` (DZZ's `Ẽ_{δ,α}`, l. 1105–1107), with
  `α = 128 C_mc + A`. Proof: the mirror image of `l32TildeMLower_wickQArea` (upper bounds of the
  fields, lower bound of the variance), and the limit step `ae_wickQArea_le_of_closed`.

DZZ give no proof of (eq-M-tilde-B-bound); this is the comparison of the approximating densities
that it abbreviates (DV entry proposed in the report).
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

lemma isClosed_closedBox_eta (b : DyBox) : IsClosed b.closedBox :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
    (isClosed_le Complex.continuous_im continuous_const)))

lemma closedBox_sub_dzzV_eta (b : DyBox) : b.closedBox ⊆ dzzV := by
  intro z ⟨h1, h2, h3, h4⟩
  have hs := DyBox.side_pos' b
  have hj : (b.j : ℝ) + 1 ≤ 2 ^ b.n := by exact_mod_cast b.hj
  have hk : (b.k : ℝ) + 1 ≤ 2 ^ b.n := by exact_mod_cast b.hk
  have e : (2 : ℝ) ^ b.n * b.side = 1 := by
    unfold DyBox.side; rw [inv_pow, mul_inv_cancel₀ (by positivity)]
  have hj0 : (0 : ℝ) ≤ b.j := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ b.k := Nat.cast_nonneg _
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- **η at every `z` near `c_B`**, upper bound (mirror of `etaCV_ge_of_nbrFine`) -/
lemma etaCV_le_of_nbrFine (hW : IsWhiteNoise P W) {X Y T : ℝ} {ω : Ω}
    (hω : ω ∈ nbrFineGen W X Y T)
    (hc : ∀ (p : ℕ) (b : DyBox), etaCV hW p b.center ω = etaInf W ((2 : ℝ)⁻¹ ^ p) b.center ω)
    {B : DyBox} {j : ℕ} (hm : (2 : ℝ) ^ B.n ≤ X) (hj : (2 : ℝ) ^ j ≤ Y) {z : ℂ} (hz : z ∈ dzzV)
    (hzB : ‖z - B.center‖ < 8 * B.side) :
    etaCV hW (B.n + j) z ω ≤ etaInf W B.side B.center ω + T := by
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
  refine le_of_tendsto ht (eventually_atTop.2 ⟨max N₀ (B.n + j), fun N hN => ?_⟩)
  have hN1 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN2 : B.n + j ≤ N := (le_max_right _ _).trans hN
  have hpow : (2 : ℝ)⁻¹ ^ N ≤ (2 : ℝ)⁻¹ ^ N₀ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hN1
  have h8 : ‖B.center - (DyBox.boxAt N z).center‖ ≤ 8 * B.side := by
    calc ‖B.center - (DyBox.boxAt N z).center‖ ≤ ‖B.center - z‖ + ‖z - (DyBox.boxAt N z).center‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖z - B.center‖ + (2 : ℝ)⁻¹ ^ N := by
          rw [norm_sub_rev B.center z]; exact add_le_add le_rfl (hcN N)
      _ ≤ 8 * B.side := by linarith
  have h := hω B.n j hm hj B (DyBox.boxAt N z) rfl hN2 h8
  rw [hcdef]; simp only
  rw [hc (B.n + j) (DyBox.boxAt N z)]
  have := (abs_le.1 h).1
  linarith

/-- variance bookkeeping, lower bound (mirror of `tildeVar_le_split`) -/
lemma tildeVar_ge_split (hW : IsWhiteNoise P W) {b₁ : ℝ}
    (hb : ∀ (n : ℕ) (v : ℂ), |tildeVar ((1 / 2 : ℝ) ^ n) v - etaVar ((1 / 2 : ℝ) ^ n) v| ≤ b₁)
    (B : DyBox) {j n : ℕ} (hn : B.n + j ≤ n) {z : ℂ} (hz : ‖z - B.center‖ ≤ 5 * B.side) :
    etaBVar ((2 : ℝ)⁻¹ ^ (B.n + j)) n z + etaVar B.side B.center -
      (b₁ + 2 * Real.sqrt (1076 * 5) * Real.sqrt (Real.log B.side⁻¹ + 4)) ≤
      tildeVar ((2 : ℝ)⁻¹ ^ n) z := by
  set δh : ℝ := (2 : ℝ)⁻¹ ^ (B.n + j)
  have hs := DyBox.side_pos' B
  have hs1 : B.side ≤ 1 := by unfold DyBox.side; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hδh0 : 0 < δh := by positivity
  have hδhs : δh ≤ B.side := by
    unfold DyBox.side; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hnδ : (2 : ℝ)⁻¹ ^ n ≤ δh := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h1 := (abs_le.1 (hb n z)).1
  rw [one_div] at h1
  have h2 := etaVar_split (ε := δh) (ε' := (2 : ℝ)⁻¹ ^ n) (by positivity) hnδ z
  have h3 := etaVar_split (ε := B.side) (ε' := δh) hδh0 hδhs z
  have h4 := etaBandVar_nonneg δh B.side z
  have h5 := etaVar_sub_le hW hs hs1 B.center z
  have h6 : Real.sqrt (1076 * ‖B.center - z‖ / B.side) ≤ Real.sqrt (1076 * 5) := by
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ hs, norm_sub_rev]; nlinarith
  have h7 : 0 ≤ Real.sqrt (Real.log B.side⁻¹ + 4) := Real.sqrt_nonneg _
  have h8 := mul_le_mul_of_nonneg_right h6 h7
  have e2 : etaBVar δh n z = Real.pi * ‖etaKernelL2 (Ioo (((2 : ℝ)⁻¹ ^ n) ^ 2) (δh ^ 2)) z‖ ^ 2 :=
    rfl
  have e3 : etaBandVar δh B.side z = Real.pi * ‖etaKernelL2 (Ioo (δh ^ 2) (B.side ^ 2)) z‖ ^ 2 :=
    rfl
  rw [← e2] at h2
  rw [← e3] at h3
  nlinarith

/-- **the pointwise algebra of (eq-M-tilde-B-bound)** -/
lemma dens_compare_real_upper {γ cv yn ev yp eB tv bv vB T₁ T₂ V δ s cA : ℝ} (hγ : 0 < γ)
    (h1 : cv ≤ yn + T₁) (h2 : yn = ev + yp) (h3 : yp ≤ eB + T₂) (h4 : bv + vB - V ≤ tv)
    (hs : 0 < s) (h7 : s ^ 2 * Real.exp (γ * eB - γ ^ 2 / 2 * vB) ≤ δ ^ 2)
    (h8 : Real.exp (γ * (T₁ + T₂) + γ ^ 2 / 2 * V) ≤ cA) :
    Real.exp (γ * cv - γ ^ 2 / 2 * tv) ≤
      cA * δ ^ 2 / s ^ 2 * Real.exp (γ * ev - γ ^ 2 / 2 * bv) := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hm' : Real.exp (γ * eB - γ ^ 2 / 2 * vB) ≤ δ ^ 2 / s ^ 2 := by
    rw [le_div_iff₀ hs2]; linarith [mul_comm (s ^ 2) (Real.exp (γ * eB - γ ^ 2 / 2 * vB))]
  have hA : Real.exp (γ * (T₁ + T₂) + γ ^ 2 / 2 * V) * Real.exp (γ * eB - γ ^ 2 / 2 * vB) ≤
      cA * δ ^ 2 / s ^ 2 := by
    rw [mul_div_assoc]
    exact mul_le_mul h8 hm' (Real.exp_pos _).le ((Real.exp_pos _).le.trans h8)
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le)
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have e1 : γ * cv ≤ γ * (yn + T₁) := mul_le_mul_of_nonneg_left h1 hγ.le
  have e3 : γ * yp ≤ γ * (eB + T₂) := mul_le_mul_of_nonneg_left h3 hγ.le
  have e4 : γ ^ 2 / 2 * (bv + vB - V) ≤ γ ^ 2 / 2 * tv :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  rw [h2] at e1
  nlinarith

/-- the full-measure set for (eq-M-tilde-B-bound) -/
def wickGoodU (hW : IsWhiteNoise P W) (γ : ℝ) : Set Ω :=
  {ω | (∀ (p : ℕ) (b : DyBox), etaCV hW p b.center ω = etaInf W ((2 : ℝ)⁻¹ ^ p) b.center ω) ∧
    (∀ p n : ℕ, p ≤ n → ∀ᵐ z ∂(volume : Measure ℂ),
      etaCV hW n z ω = etaVer W ((2 : ℝ)⁻¹ ^ p) n z ω + etaCV hW p z ω) ∧
    (∀ (b' : DyBox) (p : ℕ) (c : ℝ), (∀ᶠ m in atTop, ∀ᶠ n in atTop,
      ∀ᵐ z ∂(volume.restrict (nbhdSq b'.closedBox m)),
        wickDensC hW γ n z ω ≤ ENNReal.ofReal c * etaDens W γ ((2 : ℝ)⁻¹ ^ p) n z ω) →
      wickQArea γ W ω b'.closedBox ≤ ENNReal.ofReal c * etaChaos W γ ((2 : ℝ)⁻¹ ^ p) b'.closedBox ω)}

theorem ae_wickGoodU (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ω ∈ wickGoodU hW γ := by
  have h3 : ∀ᵐ ω ∂P, ∀ (b' : DyBox) (p : ℕ) (c : ℝ), (∀ᶠ m in atTop, ∀ᶠ n in atTop,
      ∀ᵐ z ∂(volume.restrict (nbhdSq b'.closedBox m)),
        wickDensC hW γ n z ω ≤ ENNReal.ofReal c * etaDens W γ ((2 : ℝ)⁻¹ ^ p) n z ω) →
      wickQArea γ W ω b'.closedBox ≤ ENNReal.ofReal c * etaChaos W γ ((2 : ℝ)⁻¹ ^ p) b'.closedBox ω := by
    rw [ae_all_iff]; intro b'; rw [ae_all_iff]; intro p
    exact ae_wickQArea_le_of_closed hW hγ hγ2 _ (isClosed_closedBox_eta b')
      (closedBox_sub_dzzV_eta b')
  filter_upwards [ae_etaCV_center hW, ae_etaCV_split hW, h3] with ω h1 h2 h3
  exact ⟨h1, h2, h3⟩

end DZZ
end LQGMetric
