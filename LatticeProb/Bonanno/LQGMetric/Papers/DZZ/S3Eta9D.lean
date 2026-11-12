/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3Eta9D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta9C

/-!
# DZZ l. 1193–1195 at `M^W`: `L32TildeMLower P γ W (wickQArea γ W)` (P2-DZZETA2)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1193–1195): on a high-probability event, for every
dyadic box `B` (side `s ≥ δ'^{C_mc}`), every `S ∈ 𝒮_B` inside `𝕍` and every square `S̃_{i_j}` of
side `ε s'`,
`M_γ(S̃) ≥ e^{−2αγ√L log L} δ'² s^{−2} M̃_{γ,ε²s',η}(S̃)` (here `M_γ = M^W = wickQArea γ W`).

The event is `wickGood ∩ (eq-tilde-h-eta-assump) ∩ 𝓔_{δ,α}` (finer-centre form `nbrFineEvent`,
`α = 128 C_mc`), i.e. DZZ's `Ẽ_{δ,α}` (l. 1105–1107); DZZ also intersect with `Ẽ_{δ',α}`, which is
not needed. Proof (DZZ's "similarly to (eq-M-tilde-B-bound)", made explicit): for `n ≥ p`
(`2^{-p} = δ̂ = ε² s'`) and a.e. `z ∈ S̃`,
`γh̃_n(z) − γ²/2 Var ≥ γη^{δ̂}_n(z) − γ²/2 Var + log(M_{γ,s}(B)/s²) − γ(√L + α√L log L) − γ²/2 V`
(`dens_compare_real`, `tildeVar_le_split`, `etaCV_ge_of_nbrFine`), `V = O(√L)` (`expo_asymp`), and
the limit step `ae_ofReal_mul_etaChaos_le` (both measures are limits of their approximations,
(eq-def-M-eta) l. 1209–1213 and (eq-def-tilde-M) l. 677–683).

**`l32TildeMLower_wickQArea`**, hence (with P2-DZZETA) `l32BallCover_dzzMuIn`: DZZ's
(eq-Euclidean-Ball-covering) at `μIn` (P-3 of D97).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent GMCIdent3 GMCIdent4 SupTail

lemma highProb_inter_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω}
    {G : Set Ω} (hE : HighProb P E) (hG : ∀ᵐ ω ∂P, ω ∈ G) : HighProb P (fun δ => G ∩ E δ) := by
  obtain ⟨c, hc, δ₀, hδ₀, h⟩ := hE
  refine ⟨c, hc, δ₀, hδ₀, fun δ hδ => ?_⟩
  have h0 : P Gᶜ = 0 := ae_iff.1 hG
  rw [compl_inter]
  exact (measure_union_le _ _).trans (by rw [h0, zero_add]; exact h δ hδ)

lemma side_div_eq {B : DyBox} {q : ℕ} :
    B.side / 1024 / ((2 : ℝ) ^ q) ^ 2 = (2 : ℝ)⁻¹ ^ (B.n + (10 + 2 * q)) := by
  unfold DyBox.side
  rw [inv_pow, inv_pow, pow_add, pow_add, pow_mul]
  field_simp
  ring_nf
  rw [pow_mul']; norm_num

universe u

/-- **DZZ l. 1193–1195 at `M^W`** -/
theorem l32TildeMLower_wickQArea {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    L32TildeMLower P γ W (wickQArea γ W) := by
  set Cm := dzzCmc γ with hCmdef
  have hCm1 : 1 ≤ Cm := by have := l31theta_pos hγ hγ2; rw [hCmdef]; unfold dzzCmc; linarith
  obtain ⟨b₁, hb₁0, hb₁⟩ := dzz_var_compare
  set α : ℝ := 128 * Cm with hαdef
  have hα0 : 0 < α := by positivity
  set A : ℝ := 1 + (b₁ + 14 + 2 * Cm + 2 * Real.sqrt (1076 * 5) * Real.sqrt (Cm + 4)) with hAdef
  refine ⟨α + A, fun δ => wickGood hW γ ∩ (tildeEtaEvent hW δ ∩ nbrFineEvent W Cm α δ),
    highProb_inter_ae ((highProb_tildeEtaEvent hW).inter
      (nbrFineEvent_highProb hW (by linarith) hα0)) (ae_wickGood hW hγ hγ2),
    Real.exp (-33), Real.exp_pos _, fun δ ⟨hδ0, hδ1⟩ B a b ha hb hs hSV => ?_⟩
  set L := Real.log δ⁻¹ with hLdef
  have hL33 : 33 ≤ L := by
    rw [hLdef, Real.log_inv, le_neg]
    exact ((Real.log_lt_iff_lt_exp hδ0).2 hδ1).le
  obtain ⟨hk2, -, hk64⟩ := kP32_facts hγ hγ2 hL33
  set q := kL37 γ δ with hqdef
  set k := kP32 γ δ with hkdef
  set jj := 10 + 2 * q with hjj
  set p := B.n + jj with hp
  have hk1 : 1 ≤ k := Nat.one_le_two_pow
  have hδh : B.side / 1024 / (2 * (k : ℝ)) ^ 2 = (2 : ℝ)⁻¹ ^ p := by rw [hk2]; exact side_div_eq
  -- parameter facts
  have hs0 := DyBox.side_pos' B
  have hpU : δ ≤ p32Up δ := by
    unfold p32Up; exact le_mul_of_one_le_right hδ0.le (Real.one_le_exp (by positivity))
  have hδCm : δ ^ Cm ≤ B.side :=
    (Real.rpow_le_rpow hδ0.le hpU (by linarith)).trans hs
  have hsinv : B.side⁻¹ ≤ δ ^ (-Cm) := by
    rw [Real.rpow_neg hδ0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hδ0 _) hδCm
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
    have e : (2 : ℝ) ^ jj = 1024 * ((2 : ℝ) ^ q) ^ 2 := by
      rw [hjj, pow_add, pow_mul]; norm_num; rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e, hαdef]
    have h0 : (0 : ℝ) ≤ 2 ^ q := by positivity
    nlinarith
  have hratio : B.side / (2 : ℝ)⁻¹ ^ p = 1024 * ((2 : ℝ) ^ q) ^ 2 := by
    rw [← hδh, hk2]; field_simp
  have hcA0 : 0 ≤ Real.exp (-(2 * (α + A) * γ * Real.sqrt L * Real.log L)) := (Real.exp_pos _).le
  have hexpo := expo_asymp (α := α) (b₁ := b₁) (S := Real.log B.side⁻¹) hγ hγ2 hα0.le hb₁0 hCm1
    (le_trans (Real.exp_one_lt_d9.le.trans (by norm_num)) hL33) (by linarith) hK hlogs
  have h8 : Real.exp (-(2 * (α + A) * γ * Real.sqrt L * Real.log L)) ≤
      Real.exp (-(γ * (Real.sqrt L + α * Real.sqrt L * Real.log L)) - γ ^ 2 / 2 *
        (b₁ + Real.log (B.side / (2 : ℝ)⁻¹ ^ p) +
          2 * Real.sqrt (1076 * 5) * Real.sqrt (Real.log B.side⁻¹ + 4))) := by
    refine Real.exp_le_exp.2 ?_
    rw [hratio]
    rw [hAdef]; linarith
  -- the comparison on one square
  intro ω ⟨hgood, hE27, hnbr⟩ hm₀ i j hi hj
  have hS : evenSq (sqCorner B a b) (B.side / 1024 / (2 * k)) i j ⊆ dzzV :=
    (evenSq_subset_sqSB B a b hk1 hi hj).trans hSV
  refine hgood.2.2 B a b k i j hS _ ?_
  rw [hδh]
  refine eventually_atTop.2 ⟨p, fun n hn => ?_⟩
  filter_upwards [ae_restrict_of_ae (hgood.2.1 p n hn),
    ae_restrict_mem (measurableSet_evenSq _ _ _ _)] with z hz hzS
  have hzV : z ∈ dzzV := hS hzS
  have hnorm := norm_sub_center_le_of_sqSB ha hb (evenSq_subset_sqSB B a b hk1 hi hj hzS)
  have h1 : etaCV hW n z ω - Real.sqrt L ≤ coarseVer hW n z ω := by
    have := (abs_lt.1 (hE27 z hzV n)).1; linarith
  have h3 := etaCV_ge_of_nbrFine hW hnbr hgood.1 h2m h2j hzV (by linarith)
  have h4 := tildeVar_le_split hW hb₁ B (j := jj) hn hnorm
  have h7 : p32Up δ ^ 2 ≤ B.side ^ 2 *
      Real.exp (γ * etaInf W B.side B.center ω - γ ^ 2 / 2 * etaVar B.side B.center) := hm₀
  have hc0 : 0 ≤ Real.exp (-(2 * (α + A) * γ * Real.sqrt (Real.log δ⁻¹) *
      Real.log (Real.log δ⁻¹))) * p32Up δ ^ 2 / B.side ^ 2 := by positivity
  unfold etaDens wickDensC
  rw [← ENNReal.ofReal_mul hc0]
  refine ENNReal.ofReal_le_ofReal ?_
  have key := dens_compare_real hγ h1 hz h3 h4 hs0 h7 hcA0 h8
  convert key using 3

/-- **P-3 of D97 closed**: DZZ's (eq-Euclidean-Ball-covering) for `μIn` -/
theorem l32BallCover_dzzMuIn_eta {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    L32BallCover P γ W (dzzMuIn γ W) :=
  l32BallCover_dzzMuIn_of_lower hW hγ hγ2 (l32TildeMLower_wickQArea hW hγ hγ2)

end DZZ
end LQGMetric
