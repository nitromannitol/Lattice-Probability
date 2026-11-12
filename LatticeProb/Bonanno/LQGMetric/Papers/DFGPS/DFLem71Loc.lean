/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.DFLem71Loc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.DFLem71Chain

/-!
# DF Lemma 7.1: localization of near-optimal paths, moduli on compact sets

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:1040–1048, proof of Lemma 2.12):
"if `sup_{u,v ∈ S_r} D(u, v) ≤ D(S_r, ∂S_{r'}) / (2C)` with `C > sup ‖f^n‖_∞`, then each path of
near-minimal `e^{ξ f}·D`-length between two points of `S_r(0)` is contained in `S_{r'}(0)`"
(`dfl71_loc`, with Euclidean balls and the factor `e^{2|ξ|M}`, DEV-DFGPS-6). The cost of a path
leaving `B_{r'}(0)` is at least `e^{−|ξ|M} D(B̄_r, ∂B_{r'})` (`le_weylCost_of_exit` and the exit
lemma), while `e^{ξ g}·D(z, w) ≤ e^{|ξ|M} sup D`.

Also: DF's "modulus of continuity of `f`" (DF:1307) measured in the metric `D` on a compact set
(`dfl71_modulus`), and the positive distance between a closed ball and a larger sphere
(`dfl71_sphere_gap`), which keeps short `D`-paths inside a compact set (DF's `r^{-1}(R(·))`
bound, DF:1305).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.DFGPS

open MetricGeometry

theorem dfl71_abs_le {ξ M : ℝ} {g : C(ℂ, ℝ)} (hg : ∀ z, |g z| ≤ M) (x : ℂ) :
    -(|ξ| * M) ≤ ξ * g x ∧ ξ * g x ≤ |ξ| * M := by
  have : |ξ * g x| ≤ |ξ| * M := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hg x) (abs_nonneg ξ)
  exact abs_le.1 this

/-- **Localization** (DFGPS T:1040–1048): near-optimal paths for `e^{ξ g}·D'` between points of
`B̄_R(0)` stay in `B_{r'}(0)`, and their `D'`-length is bounded. -/
theorem dfl71_loc {D' : ContMetric} (hD' : D'.IsLength) {ξ M : ℝ} {g : C(ℂ, ℝ)}
    (hg : ∀ z, |g z| ≤ M) {R r' s' d' η₀ : ℝ} (hRr : R < r') (hη₀ : 0 < η₀)
    (hs : ∀ u ∈ closedBall (0 : ℂ) R, ∀ v ∈ closedBall (0 : ℂ) R, D'.1 (u, v) ≤ s')
    (hd : ∀ u ∈ closedBall (0 : ℂ) R, ∀ y ∈ sphere (0 : ℂ) r', d' ≤ D'.1 (u, y))
    (hgap : Real.exp (2 * |ξ| * M) * s' + Real.exp (|ξ| * M) * η₀ < d')
    {z w : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) (hw : w ∈ closedBall (0 : ℂ) R) :
    ∃ (L : ℝ) (P : ℝ → ℂ), 0 ≤ L ∧ ContinuousOn (D'.pt ∘ P) (Icc 0 L) ∧
      HasUnitSpeedOn (D'.pt ∘ P) (Icc 0 L) ∧ P 0 = z ∧ P L = w ∧
      (∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g (P t)))) <
        weylScale ξ g D' z w + ENNReal.ofReal η₀ ∧
      L ≤ Real.exp (|ξ| * M) * (Real.exp (|ξ| * M) * s' + η₀) ∧
      ∀ t ∈ Icc 0 L, P t ∈ ball (0 : ℂ) r' := by
  set A := |ξ| * M with hAdef
  have hA := dfl71_abs_le (ξ := ξ) hg
  have h2A : Real.exp (2 * |ξ| * M) = Real.exp A * Real.exp A := by
    rw [← Real.exp_add]; congr 1; rw [hAdef]; ring
  have hs0 : 0 ≤ s' := (dist_nonneg (x := D'.pt z) (y := D'.pt z)).trans (hs z hz z hz)
  have hW : weylScale ξ g D' z w ≤ ENNReal.ofReal (Real.exp A * s') :=
    (weylScale_mem_Icc_of_isLength hD' (fun x => (hA x).1) (fun x => (hA x).2)).2.trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hs z hz w hw) (Real.exp_pos _).le))
  have hWt : weylScale ξ g D' z w ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hW
  have hlt : weylScale ξ g D' z w < weylScale ξ g D' z w + ENNReal.ofReal η₀ :=
    ENNReal.lt_add_right hWt (ENNReal.ofReal_pos.2 hη₀).ne'
  have hlt' := hlt
  conv_lhs at hlt' => rw [weylScale]
  simp only [iInf_lt_iff] at hlt'
  obtain ⟨L, P, hL, hc, hu, h0, h1, hcost⟩ := hlt'
  have hcost' : (∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g (P t)))) <
      ENNReal.ofReal (Real.exp A * s' + η₀) := by
    refine hcost.trans_le ?_
    rw [ENNReal.ofReal_add (by positivity) hη₀.le]
    gcongr
  have hpos : 0 < Real.exp A * s' + η₀ := by positivity
  refine ⟨L, P, hL, hc, hu, h0, h1, hcost, ?_, ?_⟩
  · -- length bound
    have hlow : ENNReal.ofReal (Real.exp (-A) * L) ≤
        ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g (P t))) := by
      calc ENNReal.ofReal (Real.exp (-A) * L)
          = ∫⁻ _ in Icc 0 L, ENNReal.ofReal (Real.exp (-A)) := by
            rw [setLIntegral_const, Real.volume_Icc, sub_zero,
              ENNReal.ofReal_mul (Real.exp_pos _).le]
        _ ≤ _ := setLIntegral_mono' measurableSet_Icc fun t _ =>
            ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hA _).1)
    have := (ENNReal.ofReal_lt_ofReal_iff hpos).1 (hlow.trans_lt hcost')
    have hE : Real.exp A * Real.exp (-A) = 1 := by rw [← Real.exp_add]; simp
    calc L = Real.exp A * (Real.exp (-A) * L) := by rw [← mul_assoc, hE, one_mul]
      _ ≤ Real.exp A * (Real.exp A * s' + η₀) :=
          mul_le_mul_of_nonneg_left this.le (Real.exp_pos _).le
  · -- localization
    intro t ht
    by_contra hnot
    have hzb : z ∈ ball (0 : ℂ) r' :=
      mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hz) hRr)
    have hexit := le_weylCost_of_exit hL hc hu isOpen_ball (a := -A)
      (fun x _ => (hA x).1) ⟨t, ht, hnot⟩
    rw [h0] at hexit
    have hinf := dfl71_le_infEDist_compl_ball hD' hzb (hd z hz)
    have hd0 : 0 ≤ d' := by
      have : 0 ≤ Real.exp (2 * |ξ| * M) * s' + Real.exp (|ξ| * M) * η₀ := by positivity
      linarith
    have key : ENNReal.ofReal (Real.exp (-A) * d') <
        ENNReal.ofReal (Real.exp A * s' + η₀) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact ((mul_le_mul_of_nonneg_left hinf zero_le).trans hexit).trans_lt hcost'
    have k2 := (ENNReal.ofReal_lt_ofReal_iff hpos).1 key
    have hE : Real.exp A * Real.exp (-A) = 1 := by rw [← Real.exp_add]; simp
    have k3 : d' < Real.exp A * (Real.exp A * s' + η₀) := by
      calc d' = Real.exp A * (Real.exp (-A) * d') := by rw [← mul_assoc, hE, one_mul]
        _ < _ := mul_lt_mul_of_pos_left k2 (Real.exp_pos _)
    rw [h2A] at hgap
    nlinarith

/-- DF's modulus of continuity (DF:1307), measured with the metric `D` on a compact set. -/
theorem dfl71_modulus (D : ContMetric) (f : C(ℂ, ℝ)) {K : Set ℂ} (hK : IsCompact K) {θ : ℝ}
    (hθ : 0 < θ) : ∃ δ > 0, ∀ u ∈ K, ∀ q ∈ K, D.1 (u, q) ≤ δ → |f u - f q| ≤ θ := by
  have hS : IsCompact (D.pt '' K) := hK.image (continuous_weylPt D)
  have hF : Continuous fun x : D.Space => f (weylToC D x) := f.continuous.comp (continuous_weylToC D)
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous hF.continuousOn) θ hθ
  refine ⟨δ / 2, half_pos hδ, fun u hu q hq huq => ?_⟩
  have := h (D.pt u) ⟨u, hu, rfl⟩ (D.pt q) ⟨q, hq, rfl⟩ (by
    show D.1 (u, q) < δ
    linarith)
  rw [Real.dist_eq] at this
  exact this.le

/-- The `D`-distance from `B̄_ρ(0)` to the sphere `∂B_{ρ'}(0)`, `ρ < ρ'`, is positive. -/
theorem dfl71_sphere_gap (D : ContMetric) {ρ ρ' : ℝ} (hρ : ρ < ρ') :
    ∃ d₁ > 0, ∀ u ∈ closedBall (0 : ℂ) ρ, ∀ y ∈ sphere (0 : ℂ) ρ', d₁ ≤ D.1 (u, y) := by
  by_cases hne : (closedBall (0 : ℂ) ρ ×ˢ sphere (0 : ℂ) ρ').Nonempty
  · obtain ⟨p, hp, hmin⟩ := ((isCompact_closedBall _ _).prod (isCompact_sphere _ _)).exists_isMinOn
      hne D.1.continuous.continuousOn
    refine ⟨D.1 p, ?_, fun u hu y hy => hmin (mk_mem_prod hu hy)⟩
    rcases (dist_nonneg (x := D.pt p.1) (y := D.pt p.2)).eq_or_lt with h | h
    · exfalso
      have heq : p.1 = p.2 := D.2.eq_of_eq_zero p.1 p.2 h.symm
      have h1 := mem_closedBall_zero_iff.1 hp.1
      have h2 := mem_sphere_zero_iff_norm.1 hp.2
      rw [heq] at h1; linarith
    · exact h
  · refine ⟨1, one_pos, fun u hu y hy => absurd ⟨(u, y), mk_mem_prod hu hy⟩ hne⟩

end LQGMetric.DFGPS
