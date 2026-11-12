/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108P2E at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108P2D

/-!
# CONF Lemma 3.3, Step 1: from `G^U` to the `D_h` event (D108 packet P2)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`literature/src/1905.00381/confluence-final.tex`, Step 1 of Lemma 3.3 (C:1200–1205): "By
condition 3 in the definition of `E^U_r(z)` and Axiom III, if `E^U_r(z) ∩ G^U` occurs then
(3.10) `max_V sup_{u,v} D_h(u,v;V_{δr/4}) ≤ (c/100) 𝔠_r e^{ξh_r(z)}`", using
`D_{h|_U} = e^{ξ𝔥^U}·D_{h̊^U}` (C:1197).

* `zb_step1_of` : a.s., for the field `Y = (h − h_ρ(w)) − f_n` of Remark 1.2 and every open
  `W ⊆ V`: if the harmonic part satisfies `𝔥^U ≤ (h − h_ρ(w))_r(z) + A` on `W`, then
  `diam(K; D_h(·,·;W)) ≤ e^{ξ(A + h_r(z))} diam(K; D_Y(·,·;W))`.

Own routine argument (Weyl scaling by `min(f_n, m)`, `m = (h − h_ρ(w))_r(z) + A`, and by the
constant `h_ρ(w)`; `LM.t17_internal_le_of_le`), the mirror image of `zb_312_of`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

lemma p2_addConst_addConst_neg (k : DistC) (a : ℝ) : addConst (addConst k (-a)) a = k := by
  simp only [addConst, addFun, add_assoc, ← p2_ofCont_add]
  have e : ContinuousMap.const ℂ (-a) + ContinuousMap.const ℂ a = 0 := by ext; simp
  rw [e]
  have : ofCont 0 = 0 := by ext φ; simp [ofCont]
  rw [this, add_zero]

/-- **CONF Lemma 3.3, Step 1, analytic core** (C:1200–1205). -/
theorem zb_step1_of {γ : ℝ} (hγ : 0 < γ) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {ρ : ℝ} {w : ℂ}
    {U : Set ℂ} {hU : IsOpen U} {X : Ω → DistC} {V : Set ℂ} {Y : Ω → DistC}
    {fn : Ω → C(ℂ, ℝ)} (hYdef : ∀ ω, Y ω = addFun (recField h ρ w ω) (-(fn ω)))
    (hfnb : ∀ ω, ∃ M, ∀ x, |fn ω x| ≤ M)
    (hfnV : ∀ ω (𝔥 : ℂ → ℝ), InnerProductSpace.HarmonicOnNhd 𝔥 U →
      (∀ φ : TestOn (toOpens U hU),
        restrictTo (toOpens U hU) (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) →
      EqOn ⇑(fn ω) 𝔥 V)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (A : ℝ) :
    ∀ᵐ ω ∂P, ∀ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 U →
      (∀ φ : TestOn (toOpens U hU),
        restrictTo (toOpens U hU) (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) →
      ∀ W : Set ℂ, IsOpen W → W ⊆ V →
      (∀ u ∈ W, 𝔥 u ≤ circleAvg (recField h ρ w ω) r z + A) → ∀ K : Set ℂ,
      internalDiam (D (h ω)) K W ≤
        ENNReal.ofReal (Real.exp (xiGamma γ * (A + circleAvg (h ω) r z))) *
          internalDiam (D (Y ω)) K W := by
  set ξ := xiGamma γ
  have hξ : 0 ≤ ξ := (GM.xiGamma_pos hγ).le
  set g' : Ω → DistC := recField h ρ w with hg'
  have hg'G : IsWholePlaneGFF g' P := isWholePlaneGFF_recField hh ρ w
  filter_upwards [hD.length P g' (GM.Tight.isGFFPlusCont_of_wp hg'G),
    hD.weyl P g' (GM.Tight.isGFFPlusCont_of_wp hg'G),
    CircleAvg.ae_circleAvg_addConst hh z hr] with ω hl hw hca
  intro 𝔥 h𝔥 hT W hWo hWV hup K
  set hρ := circleAvg (h ω) ρ w
  set m := circleAvg (g' ω) r z + A with hm
  have hgm : circleAvg (g' ω) r z = circleAvg (h ω) r z - hρ := by
    rw [hg', recField, hca]; ring
  have hfV := hfnV ω 𝔥 h𝔥 hT
  obtain ⟨M, hM⟩ := hfnb ω
  set ft : C(ℂ, ℝ) := fn ω ⊓ ContinuousMap.const ℂ m with hft
  have hftW : ∀ x ∈ W, ξ * (-(fn ω)) x = ξ * (-ft) x := by
    intro x hx
    have : fn ω x ≤ m := by rw [hfV (hWV hx)]; exact hup x hx
    simp [hft, ContinuousMap.inf_apply, min_eq_left this]
  have ha2 : ∀ x, -(ξ * m) ≤ ξ * (-ft) x := by
    intro x
    have : ft x ≤ m := by simp [hft, ContinuousMap.inf_apply]
    simp only [ContinuousMap.neg_apply]; nlinarith
  have hb2 : ∀ x, ξ * (-ft) x ≤ ξ * max M (-m) := by
    intro x
    have h1 : -M ≤ fn ω x := (abs_le.1 (hM x)).1
    have : min (-M) m ≤ ft x := by
      simp only [hft, ContinuousMap.inf_apply, ContinuousMap.const_apply]
      exact min_le_min h1 le_rfl
    have h3 : -ft x ≤ max M (-m) := by
      rcases le_total (-M) m with hle | hle
      · rw [min_eq_left hle] at this; exact (by linarith : -ft x ≤ M).trans (le_max_left _ _)
      · rw [min_eq_right hle] at this; exact (by linarith : -ft x ≤ -m).trans (le_max_right _ _)
    simp only [ContinuousMap.neg_apply]; nlinarith
  -- `D_{g'}(·,·;W) ≤ e^{ξm} D_Y(·,·;W)` and `D_h = e^{ξh_ρ} D_{g'}`
  have hcmp : ∀ u v : ℂ, (D (h ω)).internal W u v ≤
      ENNReal.ofReal (Real.exp (ξ * hρ) * Real.exp (ξ * m)) * (D (Y ω)).internal W u v := by
    intro u v
    have e1 : (D (Y ω)).internal W u v = (D (addFun (g' ω) (-ft))).internal W u v := by
      rw [hYdef ω]
      exact internal_weyl_eq_of_internal_eq hWo (fun a b => (hw _ a b).symm)
        (fun a b => (hw _ a b).symm) (fun _ _ _ _ => rfl) hftW u v
    have e2 : (D (g' ω)).internal W u v ≤
        ENNReal.ofReal (Real.exp (ξ * m)) * (D (addFun (g' ω) (-ft))).internal W u v := by
      refine LM.t17_internal_le_of_le (Real.exp_pos _) (fun x y => ?_) W u v
      have := (dist_addFun_mem_Icc_of_weyl hl hw ha2 hb2 x y).1
      have hpos : 0 < Real.exp (-(ξ * m)) := Real.exp_pos _
      calc (D (g' ω)).1 (x, y) = Real.exp (ξ * m) * (Real.exp (-(ξ * m)) * (D (g' ω)).1 (x, y)) := by
            rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
        _ ≤ Real.exp (ξ * m) * (D (addFun (g' ω) (-ft))).1 (x, y) := by gcongr
    have e3 : D (h ω) = (D (g' ω)).smulPos (Real.exp (ξ * hρ)) (Real.exp_pos _) := by
      have hk : addConst (g' ω) hρ = h ω := p2_addConst_addConst_neg (h ω) hρ
      apply Subtype.ext
      ext p
      show (D (h ω)).1 (p.1, p.2) = _
      rw [← hk, dist_addConst_of_weyl hl hw hρ]; rfl
    rw [e3, ContMetric.internal_smulPos, e1, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
    gcongr
  have hk : Real.exp (ξ * hρ) * Real.exp (ξ * m) = Real.exp (ξ * (A + circleAvg (h ω) r z)) := by
    rw [← Real.exp_add, hm, hgm]; ring_nf
  unfold internalDiam
  refine iSup₂_le fun u hu => iSup₂_le fun v hv => (hcmp u v).trans ?_
  rw [hk]
  gcongr
  exact le_iSup₂_of_le u hu (le_iSup₂_of_le v hv le_rfl)

end LQGMetric.CONF
