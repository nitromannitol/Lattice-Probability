/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P17 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17A
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L4Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.17: reduction to the approximate-LFPP lower bound (eqn-lfpp-lower-show)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, Prop 3.17
(`prop-lfpp-lower0`, DG:1515–1521), proof DG:1523–1532: "By Proposition 3.16, it suffices to
prove a lower bound for approximate `ε^β`-Liouville graph distances, i.e. … (eqn-lfpp-lower-show)
`D̂^{ε^β}(K, ∂U) ≥ ε^{β(1 − 2/d − γ²/(2d)) + ζ}`. Note that the error term
`ε^β e^{(γ/d) ĥ_{ε^β}(v_{S_z})}` coming from the left side of (3.33) does not pose a problem
here: indeed, Lemma 3.5 shows that with polynomially high probability … this term is at most
`ε^{β(1 − 2γ/d)}` uniformly over all `z ∈ 𝕊` and we have `1 − 2γ/d > 1 − 2/d − γ²/(2d)`."

Here (with `δ = ε^β`, which only reparametrizes the statement):
* `DGP316For` is the body of `Blueprint.DGProp3_16` for a fixed coupling;
* `DGP317Show` is (eqn-lfpp-lower-show) for the white noise `W` (`D̂(K,∂U)` read pointwise:
  `δ^{λ+ζ} ≤ D̂^δ(z, w; 𝕊)` for `z ∈ K`, `w ∈ ∂U`) — DG Steps 1–3 (DG:1533–1591), open;
* `DGP317For` is Prop 3.17 for the coupling, with `D^δ(K, ∂U)` = `p17SetDist` (paths in `Ū`;
  `h^{𝕊(1)}_δ` is only defined on `𝕊`);
* `dg_prop317_of_coupling`, `dgProp3_17_of`: P3.16 + L3.5 (`dg_lemma35`, proved) +
  (eqn-lfpp-lower-show) ⇒ P3.17.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint WhiteNoise DDDF

variable {Ω : Type} [MeasurableSpace Ω]

/-- the body of `Blueprint.DGProp3_16` (DG:1432–1437) for a given coupling -/
def DGP316For (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hc : ℝ → ℂ → Ω → ℝ) : Prop :=
  ∀ ζ ∈ Ioo (0 : ℝ) 1, ∀ ξ : ℝ, 0 < ξ → ∃ p K δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧
    ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ¬ ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
        δ ^ ζ * (dgApproxLFPP ξ δ (fun x => phiVer W P δ 1 x ω) z w -
            δ ^ (1 - ζ) * Real.exp (ξ * dgMaxSq δ (fun x => phiVer W P δ 1 x ω) z)) ≤
          dgLFPP ξ (fun x => hc δ x ω) closedUnitSquare z w ∧
        dgLFPP ξ (fun x => hc δ x ω) closedUnitSquare z w ≤
          δ ^ (-ζ) * dgApproxLFPP ξ δ (fun x => phiVer W P δ 1 x ω) z w} ≤
        ENNReal.ofReal (K * δ ^ p)

/-- **DG (eqn-lfpp-lower-show)** (DG:1527–1530), at `δ = ε^β` -/
def DGP317Show (P : Measure Ω) (W : WNSpace → Ω → ℝ) (γ : ℝ) : Prop :=
  ∀ K U : Set ℂ, IsCompact K → IsOpen U → K ⊆ U → U ⊆ closedUnitSquare →
    ∀ ζ ∈ Ioo (0 : ℝ) 1, ∃ p C δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ¬ ∀ z ∈ K, ∀ w ∈ frontier U, δ ^ (dgLambda γ + ζ) ≤
        dgApproxLFPP (xiGamma γ) δ (fun x => phiVer W P δ 1 x ω) z w} ≤
        ENNReal.ofReal (C * δ ^ p)

/-- **DG Proposition 3.17** (DG:1515–1521) for a coupling `(W, h^{𝕊(1)})` -/
def DGP317For (P : Measure Ω) (hc : ℝ → ℂ → Ω → ℝ) (γ : ℝ) : Prop :=
  ∀ K U : Set ℂ, IsCompact K → IsOpen U → K ⊆ U → U ⊆ closedUnitSquare →
    ∀ ζ ∈ Ioo (0 : ℝ) 1, ∃ p C δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ¬ ENNReal.ofReal (δ ^ (dgLambda γ + ζ)) ≤
        p17SetDist (xiGamma γ) (fun x => hc δ x ω) K U} ≤ ENNReal.ofReal (C * δ ^ p)

lemma p17_isClosed_sq : IsClosed closedUnitSquare := by
  have : closedUnitSquare = Complex.re ⁻¹' Icc 0 1 ∩ Complex.im ⁻¹' Icc 0 1 := by
    ext z; simp [closedUnitSquare, and_assoc]
  rw [this]
  exact (isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Icc.preimage Complex.continuous_im)

lemma p17_center_mem {m : ℕ} {k : ℤ × ℤ} (hk : k ∈ dgIdx m) : dgCenter m k ∈ closedUnitSquare := by
  obtain ⟨h1, h2, h3, h4⟩ := hk
  have hm : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  have e : (2 : ℝ)⁻¹ ^ m * (2 : ℝ) ^ m = 1 := by rw [← mul_pow]; norm_num
  have c2 : ((k.1 : ℝ) + 1) ≤ (2 : ℝ) ^ m := by exact_mod_cast (Int.add_one_le_iff.2 h2)
  have c4 : ((k.2 : ℝ) + 1) ≤ (2 : ℝ) ^ m := by exact_mod_cast (Int.add_one_le_iff.2 h4)
  have c1 : (0 : ℝ) ≤ k.1 := by exact_mod_cast h1
  have c3 : (0 : ℝ) ≤ k.2 := by exact_mod_cast h3
  simp only [closedUnitSquare, dgCenter, mem_ofPred_eq]
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · nlinarith
  · nlinarith

/-- pure exponent arithmetic of DG:1527–1532 -/
lemma p17_arith {δ lam ζ ζ₁ ζ₂ b g g₂ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (hg : g ≤ b - (lam + ζ₂))
    (hδg : δ ^ g ≤ 1 / 2) (hg₂ : g₂ ≤ ζ - ζ₁ - ζ₂) (hδg₂ : δ ^ g₂ ≤ 1 / 2) :
    δ ^ (lam + ζ) ≤ δ ^ ζ₁ * (δ ^ (lam + ζ₂) - δ ^ b) := by
  have h0 := hδ.1
  have hb : δ ^ b ≤ δ ^ (lam + ζ₂) / 2 := by
    have : δ ^ b = δ ^ (lam + ζ₂) * δ ^ (b - (lam + ζ₂)) := by rw [← Real.rpow_add h0]; ring_nf
    rw [this]
    have := (Real.rpow_le_rpow_of_exponent_ge h0 hδ.2.le hg).trans hδg
    nlinarith [Real.rpow_pos_of_pos h0 (lam + ζ₂)]
  have h2 : δ ^ (lam + ζ) = δ ^ ζ₁ * δ ^ (lam + ζ₂) * δ ^ (ζ - ζ₁ - ζ₂) := by
    rw [← Real.rpow_add h0, ← Real.rpow_add h0]; ring_nf
  have h3 := (Real.rpow_le_rpow_of_exponent_ge h0 hδ.2.le hg₂).trans hδg₂
  rw [h2]
  have p1 := Real.rpow_pos_of_pos h0 ζ₁
  have p2 := Real.rpow_pos_of_pos h0 (lam + ζ₂)
  have : δ ^ ζ₁ * δ ^ (lam + ζ₂) * δ ^ (ζ - ζ₁ - ζ₂) ≤ δ ^ ζ₁ * δ ^ (lam + ζ₂) * (1 / 2) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  nlinarith

lemma p17_half {δ g : ℝ} (hg : 0 < g) (hδ : 0 < δ) (hδ' : δ ≤ (1 / 2 : ℝ) ^ (1 / g)) :
    δ ^ g ≤ 1 / 2 := by
  calc δ ^ g ≤ ((1 / 2 : ℝ) ^ (1 / g)) ^ g := Real.rpow_le_rpow hδ.le hδ' hg.le
    _ = 1 / 2 := by rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hg.ne', Real.rpow_one]

/-- **DG Prop 3.17 from P3.16, L3.5 and (eqn-lfpp-lower-show)** (DG:1523–1532), for a coupling -/
theorem dg_prop317_of_coupling {P : Measure Ω} {W : WNSpace → Ω → ℝ} {hz : Ω → DistC}
    {hc : ℝ → ℂ → Ω → ℝ} (hcpl : IsDGCoupling P W hz hc) (h316 : DGP316For P W hc) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hshow : DGP317Show P W γ) : DGP317For P hc γ := by
  intro K U hK hU hKU hUS ζ hζ
  set ξ := xiGamma γ
  have hξ : 0 < ξ := xiGamma_pos hγ
  have hQ : 2 < Q γ := by
    unfold Q
    have : 2 / γ + γ / 2 - 2 = (2 - γ) ^ 2 / (2 * γ) := by field_simp; ring
    have : 0 < (2 - γ) ^ 2 / (2 * γ) := by positivity
    linarith
  have hlam : dgLambda γ = 1 - ξ * Q γ := DFGPS.L36.dgLambda_eq hγ
  set ζ₁ := min (ζ / 3) (ξ * (Q γ - 2) / 8) with hζ₁d
  set ζ₃ := (Q γ - 2) / 4 with hζ₃d
  set ζ₂ := min ζ₁ (ξ * (Q γ - 2) / 4) with hζ₂d
  have hζ₃ : 0 < ζ₃ := by rw [hζ₃d]; linarith
  have hζ₁ : 0 < ζ₁ := by rw [hζ₁d]; exact lt_min (by linarith [hζ.1]) (by nlinarith)
  have hζ₁3 : ζ₁ ≤ ζ / 3 := min_le_left _ _
  have hζ₁8 : ζ₁ ≤ ξ * (Q γ - 2) / 8 := min_le_right _ _
  have hζ₂ : 0 < ζ₂ := lt_min hζ₁ (by nlinarith)
  obtain ⟨p1, C1, d1, hp1, hd1, hb1⟩ := h316 ζ₁ ⟨hζ₁, by linarith [hζ.2]⟩ ξ hξ
  obtain ⟨K3, d3, hd3, hb3⟩ := dg_lemma35 hcpl.2.1 (U := closedUnitSquare)
    ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun z hz => by
      obtain ⟨a, b, c, d⟩ := hz
      rw [mem_closedBall_zero_iff]
      refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
      rw [abs_of_nonneg a, abs_of_nonneg c]; linarith) hζ₃
  obtain ⟨p2, C2, d2, hp2, hd2, hb2⟩ := hshow K U hK hU hKU hUS ζ₂
    ⟨hζ₂, (min_le_left _ _).trans_lt (by linarith [hζ.2])⟩
  set g := ξ * (Q γ - 2) / 4 with hgd
  have hg : 0 < g := by rw [hgd]; nlinarith
  set g₂ := ζ₁ with hg₂d
  have hg₂ : 0 < g₂ := hζ₁
  set δ₁ := min (min (min d1 d2) (min d3 1)) (min ((1 / 2 : ℝ) ^ (1 / g)) ((1 / 2 : ℝ) ^ (1 / g₂)))
  have hδ₁ : 0 < δ₁ := lt_min (lt_min (lt_min hd1 hd2) (lt_min hd3 one_pos))
    (lt_min (by positivity) (by positivity))
  refine ⟨min (min p1 p2) ζ₃, |C1| + |C2| + |K3|, δ₁, lt_min (lt_min hp1 hp2) hζ₃, hδ₁,
    fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδδ⟩ := hδ
  have hδ1' : δ < d1 := hδδ.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hδ2' : δ < d2 := hδδ.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hδ3' : δ < d3 := hδδ.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hδ1 : δ < 1 := hδδ.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hδg : δ ^ g ≤ 1 / 2 := p17_half hg hδ0 (hδδ.le.trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hδg₂ : δ ^ g₂ ≤ 1 / 2 := p17_half hg₂ hδ0 (hδδ.le.trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  set E1 := {ω | ¬ ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
        δ ^ ζ₁ * (dgApproxLFPP ξ δ (fun x => phiVer W P δ 1 x ω) z w -
            δ ^ (1 - ζ₁) * Real.exp (ξ * dgMaxSq δ (fun x => phiVer W P δ 1 x ω) z)) ≤
          dgLFPP ξ (fun x => hc δ x ω) closedUnitSquare z w ∧
        dgLFPP ξ (fun x => hc δ x ω) closedUnitSquare z w ≤
          δ ^ (-ζ₁) * dgApproxLFPP ξ δ (fun x => phiVer W P δ 1 x ω) z w}
  set E2 := {ω | ¬ ∀ z ∈ K, ∀ w ∈ frontier U, δ ^ (dgLambda γ + ζ₂) ≤
        dgApproxLFPP ξ δ (fun x => phiVer W P δ 1 x ω) z w}
  set E3 := {ω | ∃ z ∈ closedUnitSquare, (2 + ζ₃) * Real.log δ⁻¹ < |phiVer W P δ 1 z ω|}
  have hsub : {ω | ¬ ENNReal.ofReal (δ ^ (dgLambda γ + ζ)) ≤
      p17SetDist ξ (fun x => hc δ x ω) K U} ⊆ E1 ∪ E2 ∪ E3 := by
    intro ω hω
    by_contra hn
    simp only [mem_union, not_or] at hn
    obtain ⟨⟨n1, n2⟩, n3⟩ := hn
    simp only [E1, E2, E3, mem_ofPred_eq, not_not, not_exists, not_and, not_lt] at n1 n2 n3
    apply hω
    have hUc : closure U ⊆ closedUnitSquare := closure_minimal hUS p17_isClosed_sq
    refine p17SetDist_ge hUc fun z hz w hw => ?_
    have hzS : z ∈ closedUnitSquare := hUS (hKU hz)
    have hwS : w ∈ closedUnitSquare := hUc (frontier_subset_closure hw)
    have hL : 0 ≤ Real.log δ⁻¹ := (Real.log_pos ((one_lt_inv₀ hδ0).2 hδ1)).le
    have hM : dgMaxSq δ (fun x => phiVer W P δ 1 x ω) z ≤ (2 + ζ₃) * Real.log δ⁻¹ :=
      Real.iSup_le (fun k => (le_abs_self _).trans (n3 _ (p17_center_mem k.2.1)))
        (by positivity)
    have herr : δ ^ (1 - ζ₁) * Real.exp (ξ * dgMaxSq δ (fun x => phiVer W P δ 1 x ω) z) ≤
        δ ^ (1 - ζ₁ - ξ * (2 + ζ₃)) := by
      have e : δ ^ (1 - ζ₁ - ξ * (2 + ζ₃)) =
          δ ^ (1 - ζ₁) * Real.exp (ξ * ((2 + ζ₃) * Real.log δ⁻¹)) := by
        rw [Real.rpow_sub hδ0, div_eq_mul_inv]
        congr 1
        rw [Real.rpow_def_of_pos hδ0, Real.log_inv, ← Real.exp_neg]
        congr 1
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hM hξ.le))
        (Real.rpow_nonneg hδ0.le _)
    have h1 := (n1 z hzS w hwS).1
    have h2 := n2 z hz w hw
    refine le_trans ?_ h1
    refine (p17_arith (ζ₁ := ζ₁) (ζ₂ := ζ₂) (b := 1 - ζ₁ - ξ * (2 + ζ₃)) ⟨hδ0, hδ1⟩ ?_ hδg ?_
      hδg₂).trans ?_
    · rw [hlam, hgd, hζ₃d]; nlinarith [min_le_right ζ₁ (ξ * (Q γ - 2) / 4), hζ₁8]
    · rw [hg₂d]; linarith [min_le_left ζ₁ (ξ * (Q γ - 2) / 4), hζ₁3]
    · exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hδ0.le _)
  have hpow : ∀ q : ℝ, min (min p1 p2) ζ₃ ≤ q → δ ^ q ≤ δ ^ (min (min p1 p2) ζ₃) :=
    fun q hq => Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le hq
  have hδp := Real.rpow_nonneg hδ0.le (min (min p1 p2) ζ₃)
  calc P _ ≤ P (E1 ∪ E2 ∪ E3) := measure_mono hsub
    _ ≤ P E1 + P E2 + P E3 := (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (C1 * δ ^ p1) + ENNReal.ofReal (C2 * δ ^ p2) +
          ENNReal.ofReal (K3 * δ ^ ζ₃) :=
        add_le_add (add_le_add (hb1 δ ⟨hδ0, hδ1'⟩) (hb2 δ ⟨hδ0, hδ2'⟩)) (hb3 δ ⟨hδ0, hδ3'⟩)
    _ ≤ ENNReal.ofReal (|C1| * δ ^ (min (min p1 p2) ζ₃)) +
          ENNReal.ofReal (|C2| * δ ^ (min (min p1 p2) ζ₃)) +
          ENNReal.ofReal (|K3| * δ ^ (min (min p1 p2) ζ₃)) :=
        add_le_add (add_le_add
          (ENNReal.ofReal_le_ofReal (mul_le_mul (le_abs_self _)
            (hpow _ ((min_le_left _ _).trans (min_le_left _ _)))
            (Real.rpow_nonneg hδ0.le _) (abs_nonneg _)))
          (ENNReal.ofReal_le_ofReal (mul_le_mul (le_abs_self _)
            (hpow _ ((min_le_left _ _).trans (min_le_right _ _)))
            (Real.rpow_nonneg hδ0.le _) (abs_nonneg _))))
          (ENNReal.ofReal_le_ofReal (mul_le_mul (le_abs_self _) (hpow _ (min_le_right _ _))
            (Real.rpow_nonneg hδ0.le _) (abs_nonneg _)))
    _ = ENNReal.ofReal ((|C1| + |C2| + |K3|) * δ ^ (min (min p1 p2) ζ₃)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- **DG Proposition 3.17** for the coupling of `Blueprint.DGProp3_16`, from P3.16, DG L3.5 and
(eqn-lfpp-lower-show) for every white noise. -/
theorem dgProp3_17_of (h316 : DGProp3_16)
    (hshow : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ),
      IsWhiteNoise P W → ∀ γ : ℝ, 0 < γ → γ < 2 → DGP317Show P W γ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : WNSpace → Ω → ℝ)
      (hz : Ω → DistC) (hc : ℝ → ℂ → Ω → ℝ), IsDGCoupling P W hz hc ∧
        ∀ γ : ℝ, 0 < γ → γ < 2 → DGP317For P hc γ := by
  obtain ⟨Ω, _, P, W, hz, hc, hcpl, h⟩ := h316
  exact ⟨Ω, _, P, W, hz, hc, hcpl, fun γ hγ hγ2 =>
    dg_prop317_of_coupling hcpl h hγ hγ2 (hshow P W hcpl.2.1 γ hγ hγ2)⟩

end LQGMetric.DG
