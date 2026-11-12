/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_12 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_12Ae
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_12Moll
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Nodes

/-!
# DFGPS Lemma 2.12 (`lem-weyl-scaling`)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) Lemma 2.12, T:1026–1031, proof
T:1035–1048. Following the paper:

1. `f^{*,n}_{ε_n} := fⁿ * p_{ε_n²/2} → f` locally uniformly (T:1036–1037;
   `tendstoUniformlyOn_heatMollify_seq`, L2_12Moll.lean);
2. `D^{ε_n}_{h+fⁿ} = e^{ξ f^{*,n}_{ε_n}} · D^{ε_n}_h` (T:1038; `lfppDistE_addFun_eq_weylScale`);
3. localization (eqn-square-bdy-weyl) from Lemma 2.10 (T:1039–1046; `ae_isLength_agree`,
   `loc_of_agree`);
4. "the same proof as in [DF, Lemma 7.1]" (T:1047–1048): `dfLem7_1`, applied to
   `Dⁿ := 𝔞_{ε_n}⁻¹ D^{ε_n}_h` (a length metric) and `D_h`.

`D_h` is a length metric a.s. by DFGPS Lemma 2.5 (`lem2_5_lim`) applied to its law; the node
`Lem2_12` does not assume it. `𝔞_{ε_n} > 0` for large `n` since `D_h(0,1) > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry LFPP

/-- `C D` is a length metric if `D` is (as `ContMetric.isLength_smulPos`, GM/S1/StrongWeak.lean) -/
theorem isLength_smul_L212 {C : ℝ} (hC : 0 < C) {D : ContMetric} (hD : D.IsLength) :
    (D.smul C hC).IsLength := by
  intro x y ε hε
  let f : D.Space → (D.smul C hC).Space := fun z => z
  have hf : ∀ a b, edist (f a) (f b) = ENNReal.ofReal C * edist a b :=
    fun a b => D.edist_smul C hC a b
  have hfc : Continuous f :=
    (show LipschitzWith (Real.toNNReal C) f from fun a b => (hf a b).le).continuous
  let x' : D.Space := x
  let y' : D.Space := y
  obtain ⟨γ, hγ⟩ := hD x' y' (ε / C) (div_pos hε hC)
  refine ⟨γ.map hfc, ?_⟩
  calc MetricGeometry.pathLength (γ.map hfc) = ENNReal.ofReal C * MetricGeometry.pathLength γ :=
        MetricGeometry.pathLength_map_of_edist_eq hf hfc γ
    _ ≤ ENNReal.ofReal C * (edist x' y' + ENNReal.ofReal (ε / C)) := by gcongr
    _ = edist (f x') (f y') + ENNReal.ofReal ε := by
        rw [mul_add, ← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ _ hC.ne', ← hf]

/-- **DFGPS Lemma 2.12** (`lem-weyl-scaling`, T:1026–1048), given DFGPS Lemma 2.8. -/
theorem lem2_12 (h28 : Lem2_8) : Lem2_12 := by
  intro γ hγ hγ2 Ω _ P _ h Dh εn hh hεp hε0 hconv
  set ξ := xiGamma γ
  have hcS : ∀ᵐ ω ∂P, ∀ n, TendstoLocallyUniformly
      (fun (k : ℕ) (z : ℂ) => h ω (heatTrunc (εn n ^ 2 / 2) z k)) (heatMollify (εn n) (h ω)) atTop ∧
      Continuous (heatMollify (εn n) (h ω)) := ae_all_iff.2 fun n =>
    hh.ae_tendstoLocallyUniformly_heatMollify (εn n) (hεp n).ne'
  filter_upwards [ae_isLength_agree h28 hγ hγ2 P h Dh εn hh hεp hε0 hconv, hconv, hcS]
    with ω hω hcv hc
  intro fn f M hfnM hfM hfconv R hR
  set a : ℕ → ℝ := fun n => aEpsDF ξ (εn n)
  -- `𝔞_{ε_n} > 0` for large `n`
  have hpos : ∀ᶠ n in atTop, 0 < a n := by
    have h01 : ((0 : ℂ), (1 : ℂ)) ∈ closedBall (0 : ℂ) 1 ×ˢ closedBall (0 : ℂ) 1 :=
      ⟨mem_closedBall_self zero_le_one, by simp⟩
    have ht := (hcv 1 one_pos).tendsto_at h01
    have hD0 : 0 < (Dh ω).1 (0, 1) := by
      refine lt_of_le_of_ne (dist_nonneg (x := (Dh ω).pt 0) (y := (Dh ω).pt 1)) fun h0 => ?_
      exact one_ne_zero ((Dh ω).2.eq_of_eq_zero 0 1 h0.symm).symm
    filter_upwards [ht.eventually (lt_mem_nhds hD0)] with n hn
    refine lt_of_le_of_ne (aEpsDF_nonneg_sq _ _) fun h0 => ?_
    simp only [a, ← h0, inv_zero, zero_mul] at hn
    exact lt_irrefl _ hn
  -- the metrics `Dⁿ = 𝔞_{ε_n}⁻¹ D^{ε_n}_h` and the functions `f^{*,n}_{ε_n}`
  set Dn : ℕ → ContMetric := fun n => if ha : 0 < a n then
    (lfppDistCM ξ (εn n) (h ω) (hc n).2).smul (a n)⁻¹ (inv_pos.2 ha)
    else lfppDistCM ξ (εn n) (h ω) (hc n).2
  have hDn : ∀ n (ha : 0 < a n),
      Dn n = (lfppDistCM ξ (εn n) (h ω) (hc n).2).smul (a n)⁻¹ (inv_pos.2 ha) := by
    intro n ha; simp only [Dn, ha, ↓reduceDIte]
  have hDnlen : ∀ n, (Dn n).IsLength := by
    intro n
    by_cases ha : 0 < a n
    · rw [hDn n ha]; exact isLength_smul_L212 _ (isLength_lfppDistCM _ _ _ _)
    · simp only [Dn, ha, ↓reduceDIte]; exact isLength_lfppDistCM _ _ _ _
  set gn : ℕ → C(ℂ, ℝ) := fun n => mollCont (εn n) (hεp n).ne' (fn n) M (hfnM n)
  have hgM : ∀ n z, |gn n z| ≤ M := fun n z =>
    abs_heatMollify_ofCont_le (fn n) (hfnM n) (hεp n).ne' z
  have hgconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(gn n)) ⇑f atTop
      (closedBall 0 R) := fun R hR =>
    tendstoUniformlyOn_heatMollify_seq (fun n => (hεp n).ne') hε0 hfnM hfM hfconv hR
  have hDconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑(Dh ω).1 atTop
      (closedBall 0 R ×ˢ closedBall 0 R) := by
    intro R hR
    refine (hcv R hR).congr ?_
    filter_upwards [hpos] with n hn p _
    rw [hDn n hn, ContMetric.smul_apply, lfppDistCM_coe]
  have hloc := loc_of_agree hω.2 (Real.exp (2 * |ξ| * M))
  have key := (dfLem7_1 ξ M Dn (Dh ω) gn f hDnlen hω.1 hDconv hgconv hgM hfM hloc).2.2 R hR
  refine key.congr ?_
  filter_upwards [hpos] with n hn p _
  beta_reduce
  rw [hDn n hn, weylScale_smul, ← lfppDistE_addFun_eq_weylScale ξ (hεp n).ne' (hc n).1 (hc n).2,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hn.le)]
  rfl

end LQGMetric.DFGPS
