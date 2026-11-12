/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3EtaB3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3EtaB2

/-!
# (eq-M-tilde-B-bound) at `M^W`: the statement and its proof (P2-DZZETA2, step (2))

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` (eq-M-tilde-B-bound), l. 1116–1119), see `S3EtaB2`.
With (Eq.LQG-tildeM) (l. 1122–1125) = `measure_etaChaos_ge_le` (Markov, `E M̃ ≤ Leb`) this is the
input of `𝓔_{B'_i, open}` and of (eq-B-good-Psi) in DZZ's proof of the upper bound of Prop 3.2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent GMCIdent3 GMCIdent4 SupTail

/-- **DZZ (eq-M-tilde-B-bound)** (l. 1116–1119) on a high-probability event: for every dyadic box
`B` of side `s ≥ δ^{C_mc}` with `M_{γ,s}(B) ≤ δ²` and every dyadic box `B̃` within distance `3s` of
`c_B`: `ν(B̃) ≤ e^{2αγ√L log L} δ² s^{−2} M̃_{γ,ε²s,η}(B̃)`, `ε² s = 2^{-(n_B + 2 kL37)}`. -/
def L32TildeMUpper {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (W : WNSpace → Ω → ℝ) (ν : Ω → Measure ℂ) : Prop :=
  ∃ α : ℝ, ∃ G : ℝ → Set Ω, HighProb P G ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
    ∀ B : DyBox, δ ^ dzzCmc γ ≤ B.side → ∀ ω ∈ G δ, approxLQG γ W ω B ≤ δ ^ 2 →
      ∀ b' : DyBox, (∀ z ∈ b'.closedBox, ‖z - B.center‖ ≤ 3 * B.side) →
        ν ω b'.closedBox ≤
          ENNReal.ofReal (Real.exp (2 * α * γ * Real.sqrt (Real.log δ⁻¹) *
            Real.log (Real.log δ⁻¹)) * δ ^ 2 / B.side ^ 2) *
          etaChaos W γ ((2 : ℝ)⁻¹ ^ (B.n + 2 * kL37 γ δ)) b'.closedBox ω

universe u

/-- **DZZ (eq-M-tilde-B-bound) at `M^W`** -/
theorem l32TildeMUpper_wickQArea {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    L32TildeMUpper P γ W (wickQArea γ W) := by
  set Cm := dzzCmc γ with hCmdef
  have hCm1 : 1 ≤ Cm := by have := l31theta_pos hγ hγ2; rw [hCmdef]; unfold dzzCmc; linarith
  obtain ⟨b₁, hb₁0, hb₁⟩ := dzz_var_compare
  set α : ℝ := 128 * Cm with hαdef
  have hα0 : 0 < α := by positivity
  set A : ℝ := 1 + (b₁ + 14 + 2 * Cm + 2 * Real.sqrt (1076 * 5) * Real.sqrt (Cm + 4)) with hAdef
  refine ⟨α + A, fun δ => wickGoodU hW γ ∩ (tildeEtaEvent hW δ ∩ nbrFineEvent W Cm α δ),
    highProb_inter_ae ((highProb_tildeEtaEvent hW).inter
      (nbrFineEvent_highProb hW (by linarith) hα0)) (ae_wickGoodU hW hγ hγ2),
    Real.exp (-33), Real.exp_pos _, fun δ ⟨hδ0, hδ1⟩ B hs ω ⟨hgood, hE27, hnbr⟩ happ b' hb' => ?_⟩
  set L := Real.log δ⁻¹ with hLdef
  have hL33 : 33 ≤ L := by
    rw [hLdef, Real.log_inv, le_neg]
    exact ((Real.log_lt_iff_lt_exp hδ0).2 hδ1).le
  set q := kL37 γ δ with hqdef
  set jj := 2 * q with hjj
  set p := B.n + jj with hp
  have hs0 := DyBox.side_pos' B
  have hsinv : B.side⁻¹ ≤ δ ^ (-Cm) := by
    rw [Real.rpow_neg hδ0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hδ0 _) hs
  have h2m : (2 : ℝ) ^ B.n ≤ δ ^ (-Cm) := by
    refine le_trans (le_of_eq ?_) hsinv
    unfold DyBox.side; rw [inv_pow, inv_inv]
  have hlogs : Real.log B.side⁻¹ ≤ Cm * L := by
    have := Real.log_le_log (inv_pos.2 hs0) hsinv
    rw [Real.log_rpow hδ0] at this
    rw [hLdef, Real.log_inv δ]; linarith
  have hK : (2 : ℝ) ^ q ≤ 4 * Cm * L := by
    have hN : ⌊4 * dzzCmc γ * Real.log δ⁻¹⌋₊ ≠ 0 := by
      have : (1 : ℝ) ≤ 4 * dzzCmc γ * Real.log δ⁻¹ := by nlinarith
      exact (Nat.floor_pos.2 this).ne'
    have h1 := Nat.pow_log_le_self 2 hN
    have h2 : ((2 ^ q : ℕ) : ℝ) ≤ (⌊4 * dzzCmc γ * Real.log δ⁻¹⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (Nat.floor_le (by positivity))
  have h2j : (2 : ℝ) ^ jj ≤ (α * L) ^ 2 := by
    have e : (2 : ℝ) ^ jj = ((2 : ℝ) ^ q) ^ 2 := by rw [hjj, mul_comm, pow_mul]
    rw [e, hαdef]
    have h0 : (0 : ℝ) ≤ 2 ^ q := by positivity
    nlinarith
  have hexpo := expo_asymp (α := α) (b₁ := b₁) (K := 1) (S := Real.log B.side⁻¹) hγ hγ2 hα0.le
    hb₁0 hCm1 (le_trans (Real.exp_one_lt_d9.le.trans (by norm_num)) hL33) le_rfl (by nlinarith)
    hlogs
  simp only [one_pow, mul_one] at hexpo
  have hlog1024 : 0 ≤ Real.log 1024 := Real.log_nonneg (by norm_num)
  have h8 : Real.exp (γ * (Real.sqrt L + α * Real.sqrt L * Real.log L) + γ ^ 2 / 2 *
      (b₁ + 2 * Real.sqrt (1076 * 5) * Real.sqrt (Real.log B.side⁻¹ + 4))) ≤
      Real.exp (2 * (α + A) * γ * Real.sqrt L * Real.log L) := by
    refine Real.exp_le_exp.2 ?_
    have hin : b₁ + 2 * Real.sqrt (1076 * 5) * Real.sqrt (Real.log B.side⁻¹ + 4) ≤
        b₁ + Real.log 1024 +
          2 * Real.sqrt (1076 * 5) * Real.sqrt (Real.log B.side⁻¹ + 4) := by linarith
    have : γ ^ 2 / 2 * (b₁ + 2 * Real.sqrt (1076 * 5) * Real.sqrt (Real.log B.side⁻¹ + 4)) ≤
        γ ^ 2 / 2 * (b₁ + Real.log 1024 +
          2 * Real.sqrt (1076 * 5) * Real.sqrt (Real.log B.side⁻¹ + 4)) :=
      mul_le_mul_of_nonneg_left hin (by positivity)
    rw [hAdef]; linarith
  -- the comparison on `B̃`, on its neighbourhoods
  refine hgood.2.2 b' p _ ?_
  obtain ⟨m₀, hm₀⟩ := exists_nat_one_div_lt hs0
  refine eventually_atTop.2 ⟨m₀, fun m hm => eventually_atTop.2 ⟨p, fun n hn => ?_⟩⟩
  filter_upwards [ae_restrict_of_ae (hgood.2.1 p n hn),
    ae_restrict_mem (isOpen_nbhdSq b'.closedBox m).measurableSet] with z hz hzU
  have hzV : z ∈ dzzV := openSquare_subset_dzzV hzU.2
  obtain ⟨w, hw, hdw⟩ := Metric.mem_thickening_iff.1 hzU.1
  have hmm : 1 / ((m : ℝ) + 1) ≤ 1 / ((m₀ : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
  have hnorm' : ‖z - B.center‖ < 4 * B.side := by
    have := hb' w hw
    calc ‖z - B.center‖ ≤ ‖z - w‖ + ‖w - B.center‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < 1 / ((m : ℝ) + 1) + 3 * B.side := by rw [← dist_eq_norm]; linarith
      _ ≤ 4 * B.side := by linarith
  have hnorm : ‖z - B.center‖ ≤ 5 * B.side := by linarith
  have h1 : coarseVer hW n z ω ≤ etaCV hW n z ω + Real.sqrt L := by
    have := (abs_lt.1 (hE27 z hzV n)).2; linarith
  have h3 := etaCV_le_of_nbrFine hW hnbr hgood.1 h2m h2j hzV (by linarith)
  have h4 := tildeVar_ge_split hW hb₁ B (j := jj) hn hnorm
  have h7 : B.side ^ 2 *
      Real.exp (γ * etaInf W B.side B.center ω - γ ^ 2 / 2 * etaVar B.side B.center) ≤ δ ^ 2 :=
    happ
  have hc0 : 0 ≤ Real.exp (2 * (α + A) * γ * Real.sqrt (Real.log δ⁻¹) *
      Real.log (Real.log δ⁻¹)) * δ ^ 2 / B.side ^ 2 := by positivity
  unfold etaDens wickDensC
  rw [← ENNReal.ofReal_mul hc0]
  refine ENNReal.ofReal_le_ofReal ?_
  exact dens_compare_real_upper hγ h1 hz h3 h4 hs0 h7 h8

end DZZ
end LQGMetric
