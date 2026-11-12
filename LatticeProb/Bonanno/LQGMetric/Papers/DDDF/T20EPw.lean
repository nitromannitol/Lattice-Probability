/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20EPw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EParam

/-!
# DDDF Theorem 20, Step 4: the pathwise gluing bound with crossing lengths (task P2-DDDFT20e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1103–1105 and 1117–1119: `glue_box` with
near-optimal long crossings (`exists_good_path`) and `δ → 0` gives
`L(g) ≤ L(γ, f) + Σ_{e ∈ circR} L(e, f)` (`T20E.glue_rect`), `L(e, f)` the crossing length
`mrectLen` of the long rectangle `e`. Also: the arithmetic of the parameters
(`exists_lin_le_two_pow`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LQGMetric
namespace DDDF
namespace T20E

open LFPP

variable {ξ : ℝ}

/-- a near-optimal long crossing -/
lemma exists_good_path {f : ℂ → ℝ} (hf : Continuous f) (K : ℕ) (e : Circle × ℂ) {δ : ℝ}
    (hδ : 0 < δ) : ∃ p : ℝ → ℂ, LAdm K e p ∧ lfppLen ξ f p ≠ ⊤ ∧
      (lfppLen ξ f p).toReal ≤ T20B.mrectLen ξ f K e.1 e.2 3 1 + δ := by
  set L := crossLenIn ξ f (T20D.RL K e) (T20B.mot K e.1 e.2 '' (rectAB 3 1).side₁)
    (T20B.mot K e.1 e.2 '' (rectAB 3 1).side₂)
  have hL : L ≠ ⊤ := T20D.crossLenIn_mot_ne_top K e.1 e.2 (by norm_num) (by norm_num) hf
  have hlt : L < L + ENNReal.ofReal δ := ENNReal.lt_add_right hL (by simpa using hδ)
  have hL' : (⨅ P ∈ {P | AdmPath (T20D.RL K e) (T20B.mot K e.1 e.2 '' (rectAB 3 1).side₁)
      (T20B.mot K e.1 e.2 '' (rectAB 3 1).side₂) P}, lfppLen ξ f P) < L + ENNReal.ofReal δ := by
    rw [← crossLenIn_eq_biInf]; exact hlt
  obtain ⟨p, hp⟩ := iInf_lt_iff.1 hL'
  obtain ⟨hpa, hp'⟩ := iInf_lt_iff.1 hp
  have hfin : lfppLen ξ f p ≠ ⊤ := ne_top_of_lt hp'
  refine ⟨p, hpa, hfin, ?_⟩
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hL, ENNReal.ofReal_ne_top⟩) hp'.le
  rwa [ENNReal.toReal_add hL ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hδ.le] at this

/-- **The gluing bound with crossing lengths.** -/
theorem glue_rect {f g : ℂ → ℝ} (hf : Continuous f) {Fr : Set ℂ} (hfg : ∀ x ∈ Fr, g x = f x)
    {K : ℕ} {i₁ i₂ j₁ j₂ : ℤ} (hx : BoxOK K i₁ i₂) (hy : BoxOK K j₁ j₂)
    (hfar : ∀ x ∈ (rectAB 1 1).toSet, x ∈ outBox K i₁ i₂ j₁ j₂ → x ∈ Fr)
    {γ : ℝ → ℂ} (hγ : AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ γ)
    (hγf : lfppLen ξ f γ ≠ ⊤) :
    (rectLen ξ g (rectAB 1 1)).toReal ≤
      (lfppLen ξ f γ).toReal + ∑ e ∈ circR K i₁ i₂ j₁ j₂, T20B.mrectLen ξ f K e.1 e.2 3 1 := by
  classical
  set R := circR K i₁ i₂ j₁ j₂
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := ε / ((R.card : ℝ) + 1)
  have hδ : 0 < δ := by positivity
  have hch := fun e => exists_good_path (ξ := ξ) hf K e hδ
  set pc : Circle × ℂ → ℝ → ℂ := fun e => (hch e).choose
  have h1 := glue_box hfg hx hy hfar hγ hγf (pc := pc) (fun e _ => (hch e).choose_spec.1)
    (fun e _ => (hch e).choose_spec.2.1)
  have h2 : ∑ e ∈ R, (lfppLen ξ f (pc e)).toReal ≤
      ∑ e ∈ R, T20B.mrectLen ξ f K e.1 e.2 3 1 + R.card * δ := by
    have := Finset.sum_le_sum fun e (_ : e ∈ R) => (hch e).choose_spec.2.2
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have h3 : (R.card : ℝ) * δ ≤ ε := by
    simp only [δ]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- `c K + d ≤ 2^K` for large `K` -/
lemma exists_lin_le_two_pow (c d : ℝ) : ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → c * K + d ≤ 2 ^ K := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
  have hc : (0 : ℝ) < |c| + |d| + 1 := by positivity
  have hev := h.eventually (gt_mem_nhds (inv_pos.2 hc))
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hev
  refine ⟨max K₀ 1, fun K hK => ?_⟩
  have h1 := hK₀ K (le_of_max_le_left hK)
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast le_of_max_le_right hK
  have h2 : (0 : ℝ) < 2 ^ K := by positivity
  rw [pow_one, div_lt_iff₀ h2] at h1
  have h3 : (K : ℝ) * (|c| + |d| + 1) < 2 ^ K := by
    calc (K : ℝ) * (|c| + |d| + 1) < ((|c| + |d| + 1)⁻¹ * 2 ^ K) * (|c| + |d| + 1) :=
          mul_lt_mul_of_pos_right h1 hc
      _ = 2 ^ K := by field_simp
  have : c * K + d ≤ K * (|c| + |d| + 1) := by
    nlinarith [le_abs_self c, le_abs_self d, abs_nonneg c, abs_nonneg d]
  linarith

end T20E
end DDDF
end LQGMetric
