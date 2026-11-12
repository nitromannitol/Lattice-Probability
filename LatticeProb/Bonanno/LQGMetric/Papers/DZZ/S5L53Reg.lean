/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53Reg at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Adapt
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105U2

/-!
# a.s. regularity of `M^W` on `𝕍°` and DG Lemma 3.12's DZZ input without `hreg` (P2-DZZ53)

The adapter `dzzL53Whp_dzzMuIn` (S5Adapt) takes the hypothesis `hreg`: a.s. the Wick chaos
`wickQArea γ W ω = CR^{−γ²/2} M_γ` is finite on compact subsets of `𝕍° = (0,1)²` and has no
atoms there. DZZ use it implicitly (finiteness of `D̃_δ(u,v)`, DZZ l. 121). Here it is proved
for a white noise `W`:

* finiteness: `M_γ` is a.s. the vague limit on `𝕍°` of its circle-average approximations
  (`GMCIdent3.ae_isVagueLimitOn_wn`, which includes finiteness on compacts), and
  `CR^{−γ²/2} ≤ e^b` on a compact (`wickArea_le_of_compact`);
* no atoms: DG Lemma 3.8, upper half (`DG.dgL38Upper_muHU`, Ding–Gwynne arXiv:1807.01072,
  DG:1112–1150): with probability `≥ 1 − Cε^p` every ball `B(z, ε^β)`, `z ∈ B̄(u,R)`, has mass
  `≤ ε`; so `P(∃ z ∈ B̄(u,R), M_γ{z} > 1/n) ≤ Cε^p` for all small `ε`, i.e. `= 0`. Countably
  many rational balls cover `𝕍°`. Own elementary deduction from DG L3.8.

Main results: `ae_wickQArea_reg` (= `hreg`) and `dzzL53Whp_dzzMuIn_wn` (DG L3.12's DZZ input
from DZZ Lemma 5.3 and Proposition 3.17 only).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- a.s. `M_γ` has no atom in `B̄(u,R)` when `B̄(u,2R) ⊆ 𝕍°` (DG Lemma 3.8, upper half) -/
theorem ae_muHU_noAtom_ball (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {u : ℂ} {R : ℝ} (hR : 0 < R) (hKU : closedBall u (2 * R) ⊆ openSquare) :
    ∀ᵐ ω ∂P, ∀ z ∈ closedBall u R, DG.muHU W γ ω {z} = 0 := by
  have hβ : 2 / (2 - γ) ^ 2 < 2 / (2 - γ) ^ 2 + 1 := by linarith
  obtain ⟨p, C, ε₀, hp, hε₀, hb⟩ :=
    DG.dgL38Upper_muHU (P := P) hW hγ hγ2 hR hKU hβ
  set β := 2 / (2 - γ) ^ 2 + 1
  -- the events `A n = {∃ z, M{z} > 1/n}` are null
  have hA : ∀ n : ℕ, P {ω | ∃ z ∈ closedBall u R, ((n : ℝ≥0∞))⁻¹ < DG.muHU W γ ω {z}} = 0 := by
    intro n
    have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε ^ p)) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun ε : ℝ => ε ^ p) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun ε : ℝ => ε ^ p) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ p)) :=
          (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.mono_left
            nhdsWithin_le_nhds
        rwa [Real.zero_rpow hp.ne'] at this
      have h1 : Tendsto (fun ε : ℝ => C * ε ^ p) (𝓝[>] 0) (𝓝 (C * 0)) := h0.const_mul C
      rw [mul_zero] at h1
      simpa using ENNReal.tendsto_ofReal h1
    refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
    have hn : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < ε₀ ∧ ε ≤ 1 / ((n : ℝ) + 1) ∧ 0 < ε := by
      have hpos : (0 : ℝ) < min ε₀ (1 / ((n : ℝ) + 1)) := lt_min hε₀ (by positivity)
      filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
      exact ⟨hε.2.trans_le (min_le_left _ _), (hε.2.trans_le (min_le_right _ _)).le, hε.1⟩
    filter_upwards [hn] with ε ⟨hε₀', hεn, hε⟩
    refine (measure_mono fun ω hω => ?_).trans (hb ε hε hε₀')
    obtain ⟨z, hz, hlt⟩ := hω
    simp only [mem_ofPred_eq]
    intro hall
    have h1 : DG.muHU W γ ω {z} ≤ ENNReal.ofReal ε :=
      (measure_mono (singleton_subset_iff.2 (mem_ball_self (Real.rpow_pos_of_pos hε β)))).trans
        (hall z hz)
    have h2 : ENNReal.ofReal ε ≤ ((n : ℝ≥0∞))⁻¹ := by
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hn0)]
        refine ENNReal.ofReal_le_ofReal (hεn.trans ?_)
        rw [one_div]
        exact inv_anti₀ (by exact_mod_cast hn0) (by linarith)
    exact absurd (hlt.trans_le (h1.trans h2)) (lt_irrefl _)
  have hU := measure_iUnion_null hA
  rw [← compl_mem_ae_iff] at hU
  filter_upwards [hU] with ω hω z hz
  simp only [compl_iUnion, mem_iInter, mem_compl_iff, mem_ofPred_eq, not_exists, not_and,
    not_lt] at hω
  by_contra hne
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hne
  exact absurd (hω n z hz) (not_le.2 hn)

/-- a.s. `M_γ` has no atom in `𝕍°` -/
theorem ae_muHU_noAtom (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ x ∈ openSquare, DG.muHU W γ ω {x} = 0 := by
  have hall : ∀ᵐ ω ∂P, ∀ (c : ℚ × ℚ) (q : ℚ), 0 < (q : ℝ) →
      closedBall (ratPt c) (2 * q) ⊆ openSquare →
        ∀ z ∈ closedBall (ratPt c) q, DG.muHU W γ ω {z} = 0 := by
    rw [ae_all_iff]; intro c; rw [ae_all_iff]; intro q
    by_cases h : 0 < (q : ℝ) ∧ closedBall (ratPt c) (2 * q) ⊆ openSquare
    · filter_upwards [ae_muHU_noAtom_ball hW hγ hγ2 h.1 h.2] with ω hω _ _ z hz using hω z hz
    · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ h
  filter_upwards [hall] with ω hω x hx
  obtain ⟨r, hr, hrx⟩ := Metric.isOpen_iff.1 isOpen_openSquare' x hx
  obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (show (0 : ℝ) < r / 4 by positivity)
  obtain ⟨c, hc⟩ := exists_ratPt_dist_lt x (show (0 : ℝ) < q from hq0)
  refine hω c q hq0 (fun z hz => hrx ?_) x (mem_closedBall.2 (dist_comm x _ ▸ hc.le))
  rw [mem_ball]
  have := dist_triangle z (ratPt c) x
  rw [mem_closedBall] at hz
  linarith

/-- **`hreg` of `dzzL53Whp_dzzMuIn`**: a.s. `M^W = CR^{−γ²/2} M_γ` is finite on compact subsets of
`𝕍°` and has no atoms there. -/
theorem ae_wickQArea_reg (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, (∀ K, IsCompact K → K ⊆ openSquare → wickQArea γ W ω K < ⊤) ∧
      ∀ x ∈ openSquare, wickQArea γ W ω {x} = 0 := by
  obtain ⟨Ω₀, _, P₀, X, hP₀, hX⟩ := GMCIdent5.exists_zeroGFF_openSquare
  filter_upwards [GMCIdent3.ae_isVagueLimitOn_wn hX hW hγ hγ2, ae_muHU_noAtom hW hγ hγ2]
    with ω hv hat
  refine ⟨fun K hK hKU => ?_, fun x hx => ?_⟩
  · obtain ⟨b, hb⟩ := wickArea_le_of_compact γ hK hKU
    refine (hb _ K hK.isClosed.measurableSet subset_rfl).trans_lt ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hv.2.1 K hK hKU)
  · exact withDensity_absolutelyContinuous _ _ (hat x hx)

end DZZ
end LQGMetric
