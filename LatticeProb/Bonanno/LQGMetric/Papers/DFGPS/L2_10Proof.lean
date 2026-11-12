/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_10Proof at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_10ProofCut
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_10ProofScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.10 (`lem-square-bdy-dist`, T:943–990): proof

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`), proof of Lemma 2.10, T:951–966:
(i)–(ii) for the normalized whole-plane GFF `ĥ`, Lemma 2.8 on `S_1(0)` gives (2.11)
(`lem2_10_unit`, `sqBdyEvent_of_mem_sqG`); (iii) by Lemma 2.6 (scaling, `lem2_6`, and
`h^r =ᵈ h`, `measure_sqBdyEvent_eq_of_map_eq`) this gives (2.12) for every `r`; (iv) for
`h = ĥ + f` the metrics are bi-Lipschitz with constants `e^{±ξ‖f‖_∞}`
(`LFPP.lfppDistE_addFun_mem_bounds`); with `P[e^{ξ‖f‖_∞} ≤ A]` close to `1` and `A²C` in place of
`C` one gets (2.10).

Reading: the paper's `ĥ` is `h − f` normalized; we use `ĥ := (h − f)^{(1)} = (h−f) − (h−f)_1(0)` as
the reference normalized GFF and compare `h` with `h − f` directly (`h − f` and `ĥ` differ by a
constant, which does not affect the event; Lemma 2.6's identity holds for `h − f` itself). The
paper's "with `1−2(1−p)` in place of `p`" is run with `p' = (1+p)/2` and `P[e^{|ξ|‖f‖} > A] ≤
(1−p)/2`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

/-- **DFGPS T:963–966** (deterministic part): if `|f| ≤ M` and `e^{|ξ|M} ≤ A`, the event of (2.10)
for `g` with constant `A²C` implies the event for `g + f` with constant `C`. -/
theorem sqBdyEvent_addFun {ξ ε C r R A M : ℝ} (hε : ε ≠ 0) (hC : 0 < C) {g : DistC}
    (hconv : ∀ z, Tendsto (fun n : ℕ => g (heatTrunc (ε ^ 2 / 2) z n)) atTop
      (𝓝 (heatMollify ε g z))) (f : C(ℂ, ℝ)) (hM : ∀ w, |f w| ≤ M)
    (hA : Real.exp (|ξ| * M) ≤ A) (hE : sqBdyEvent ξ ε (A ^ 2 * C) r R g) :
    sqBdyEvent ξ ε C r R (addFun g f) := by
  set e := Real.exp (|ξ| * M)
  have he : 0 < e := Real.exp_pos _
  set K := ENNReal.ofReal e
  have hK0 : K ≠ 0 := by simp [K, he]
  have hKt : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have b := lfppDistE_addFun_mem_bounds ξ hε hconv f hM
  unfold sqBdyEvent at hE ⊢
  set Sg := ⨆ u ∈ sqC r 0, ⨆ v ∈ sqC r 0, lfppDistE ξ ε g u v
  set Ig := ⨅ u ∈ sqC r 0, ⨅ v ∈ frontier (sqC (R * r) 0), lfppDistE ξ ε g u v
  set Ih := ⨅ u ∈ sqC r 0, ⨅ v ∈ frontier (sqC (R * r) 0), lfppDistE ξ ε (addFun g f) u v
  have h1 : (⨆ u ∈ sqC r 0, ⨆ v ∈ sqC r 0, lfppDistE ξ ε (addFun g f) u v) ≤ K * Sg :=
    iSup₂_le fun u hu => iSup₂_le fun v hv => (b u v).1.trans (by
      gcongr
      exact le_iSup₂_of_le (f := fun u _ => ⨆ v ∈ sqC r 0, lfppDistE ξ ε g u v) u hu
        (le_iSup₂_of_le (f := fun v _ => lfppDistE ξ ε g u v) v hv le_rfl))
  have h2 : Ig ≤ K * Ih := by
    have : K * Ih = ⨅ u ∈ sqC r 0, ⨅ v ∈ frontier (sqC (R * r) 0),
        K * lfppDistE ξ ε (addFun g f) u v := by
      simp only [Ih, ENNReal.mul_iInf_of_ne hK0 hKt]
    rw [this]
    exact le_iInf₂ fun u hu => le_iInf₂ fun v hv =>
      iInf₂_le_of_le (f := fun u _ => ⨅ v ∈ frontier (sqC (R * r) 0), lfppDistE ξ ε g u v) u hu
        (iInf₂_le_of_le (f := fun v _ => lfppDistE ξ ε g u v) v hv (b u v).2)
  have hA0 : 0 < A := he.trans_le hA
  have h3 : K * K * ENNReal.ofReal (A ^ 2 * C)⁻¹ ≤ ENNReal.ofReal C⁻¹ := by
    rw [← ENNReal.ofReal_mul he.le, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_inv, ← mul_assoc]
    refine mul_le_of_le_one_left (inv_nonneg.2 hC.le) ?_
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    nlinarith
  calc _ ≤ K * Sg := h1
    _ < K * (ENNReal.ofReal (A ^ 2 * C)⁻¹ * Ig) := (ENNReal.mul_lt_mul_iff_right hK0 hKt).2 hE
    _ ≤ K * (ENNReal.ofReal (A ^ 2 * C)⁻¹ * (K * Ih)) := by gcongr
    _ = K * K * ENNReal.ofReal (A ^ 2 * C)⁻¹ * Ih := by ring
    _ ≤ ENNReal.ofReal C⁻¹ * Ih := by gcongr

/-- `h^r = h(r·) − h_r(0)` is a normalized whole-plane GFF -/
theorem isNormalizedWPGFF_fieldScale {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → DistC} (hg : IsWholePlaneGFF g P) {r : ℝ} (hr : 0 < r) :
    IsNormalizedWPGFF (fun ω => fieldScale r (g ω)) P := by
  refine ⟨isWholePlaneGFF_fieldScale hg hr, ?_⟩
  filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero (hg.affineComp hr 0),
    CircleAvg.ae_circleAvg_affineComp hg hr 0] with ω h1 h2
  simp only [fieldScale]
  rw [h1, h2]
  ring

theorem map_fieldScale_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → DistC}
    (hg : IsWholePlaneGFF g P) {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    P.map (fun ω => fieldScale r (g ω)) = P.map (fun ω => fieldScale r' (g ω)) := by
  have h1 := isNormalizedWPGFF_fieldScale hg hr
  have h2 := isNormalizedWPGFF_fieldScale hg hr'
  exact GFFLaw.map_eq_of_normalized_ae (GFFLaw.integral_bumpTest 0 0)
    (measurable_circleAvg_left 1 0) h1.1 h2.1 (CircleAvg.ae_circleAvg_addConst_one_zero h1.1)
    (CircleAvg.ae_circleAvg_addConst_one_zero h2.1) h1.2 h2.2

theorem isGFFPlusBddCont_of_normalizedWP {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → DistC} (hg : IsNormalizedWPGFF g P) : IsGFFPlusBddCont g P := by
  have e : ofCont 0 = 0 := by ext φ; simp [ofCont]
  refine ⟨hg.1.measurable, fun _ => 0, measurable_const, fun _ => ⟨0, by simp⟩, ?_⟩
  simpa [e] using hg.1

/-- a deterministic `A` with `P[e^{|ξ| sup|f|} > A]` small -/
theorem exists_measure_exp_supAbs_gt_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → C(ℂ, ℝ)} (hf : Measurable f) (ξ : ℝ) {δ : ℝ}
    (hδ : 0 < δ) : ∃ A : ℝ, P {ω | A < Real.exp (|ξ| * supAbs (f ω))} ≤ ENNReal.ofReal δ := by
  set B : ℕ → Set Ω := fun n => {ω | (n : ℝ) < Real.exp (|ξ| * supAbs (f ω))}
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    measurableSet_lt measurable_const (Real.measurable_exp.comp
      ((measurable_supAbs hf).const_mul _))
  have hT := tendsto_measure_iInter_atTop (μ := P) (fun n => (hBm n).nullMeasurableSet)
    (fun i j hij ω (hω : (j : ℝ) < _) => show (i : ℝ) < _ from
      lt_of_le_of_lt (Nat.cast_le.2 hij) hω) ⟨0, measure_ne_top _ _⟩
  have h0 : (⋂ n, B n) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun ω hω => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp (|ξ| * supAbs (f ω)))
    exact absurd (mem_iInter.1 hω n) (not_lt.2 hn.le)
  rw [h0, measure_empty] at hT
  obtain ⟨n, hn⟩ := (hT.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ))).exists
  exact ⟨n, hn.le⟩

/-- **DFGPS Lemma 2.10** (`lem-square-bdy-dist`, T:943–990), from Lemma 2.8. -/
theorem lem2_10 (h28 : Lem2_8) : Lem2_10 := by
  intro γ hγ hγ2 Ω _ P _ h hh p hp C hC
  obtain ⟨hhm, f, hf, hfb, hg⟩ := id hh
  set ξ := xiGamma γ
  set g : Ω → DistC := fun ω => h ω - ofCont (f ω)
  set G : Ω → DistC := fun ω => fieldScale 1 (g ω)
  have hGn : IsNormalizedWPGFF G P := isNormalizedWPGFF_fieldScale hg one_pos
  have hδ : 0 < (1 - p) / 2 := by linarith [hp.2]
  obtain ⟨A, hAP⟩ := exists_measure_exp_supAbs_gt_le (P := P) hf ξ hδ
  have hA0 : 0 < max A 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set A' := max A 1
  have hAP' : P {ω | A' < Real.exp (|ξ| * supAbs (f ω))} ≤ ENNReal.ofReal ((1 - p) / 2) :=
    (measure_mono fun ω (hω : A' < _) => show A < _ from (le_max_left _ _).trans_lt hω).trans hAP
  have hC' : 0 < A' ^ 2 * C := by positivity
  obtain ⟨R₀, hR₀⟩ := lem2_10_unit h28 hγ hγ2 P G (isGFFPlusBddCont_of_normalizedWP hGn) hC'
    (p := (1 + p) / 2) (by linarith [hp.2])
  set s := innSide R₀
  have hs : 0 < s := innSide_pos R₀
  refine ⟨1 / s, one_lt_one_div hs ((innSide_le_half R₀).trans_lt (by norm_num)), fun r hr => ?_⟩
  set ρ := r / s
  have hρ : 0 < ρ := div_pos hr hs
  have hrs : ρ * s = r := div_mul_cancel₀ r hs.ne'
  have htend : Tendsto (fun ε => ε / ρ) (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun ε hε =>
      div_pos hε hρ⟩
    simpa using ((tendsto_id (x := 𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds).div_const ρ
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [htend.eventually hR₀, self_mem_nhdsWithin] with ε hε hε0
  have hε0' : (0 : ℝ) < ε := hε0
  have hερ : ε / ρ ≠ 0 := (div_pos hε0' hρ).ne'
  -- (ii) internal metric → whole-plane metric
  have k1 : P {ω | lfppSqC ξ (ε / ρ) (G ω) sq1 ∈ sqG (A' ^ 2 * C) R₀} ≤
      P {ω | sqBdyEvent ξ (ε / ρ) (A' ^ 2 * C) s (1 / s) (G ω)} := by
    refine measure_mono_ae ?_
    filter_upwards [hGn.1.ae_tendstoLocallyUniformly_heatMollify (ε / ρ) hερ] with ω hω hmem
    exact sqBdyEvent_of_mem_sqG hC' hω.2 hmem
  -- (iii) scaling: law of `h^ρ` and Lemma 2.6
  have k2 : P {ω | sqBdyEvent ξ (ε / ρ) (A' ^ 2 * C) s (1 / s) (G ω)} =
      P {ω | sqBdyEvent ξ (ε / ρ) (A' ^ 2 * C) s (1 / s) (fieldScale ρ (g ω))} :=
    measure_sqBdyEvent_eq_of_map_eq hGn.1 (isWholePlaneGFF_fieldScale hg hρ)
      (map_fieldScale_eq hg one_pos hρ) ξ hερ _ _ _
  have k3 : P {ω | sqBdyEvent ξ (ε / ρ) (A' ^ 2 * C) s (1 / s) (fieldScale ρ (g ω))} =
      P {ω | sqBdyEvent ξ ε (A' ^ 2 * C) r (1 / s) (g ω)} := by
    refine measure_congr ?_
    filter_upwards [lem2_6 hg ξ hε0' hρ] with ω hω
    refine propext ?_
    rw [← hrs]
    refine sqBdyEvent_scale hρ ?_ ENNReal.ofReal_ne_top hω
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos (inv_pos.2 hρ) (Real.exp_pos _)
  -- (iv) adding `f`
  have k4 : P {ω | sqBdyEvent ξ ε (A' ^ 2 * C) r (1 / s) (g ω)} ≤
      P {ω | sqBdyEvent ξ ε C r (1 / s) (h ω)} +
        P {ω | A' < Real.exp (|ξ| * supAbs (f ω))} := by
    refine (measure_mono_ae ?_).trans (measure_union_le _ _)
    filter_upwards [hg.ae_tendstoLocallyUniformly_heatMollify ε hε0'.ne'] with ω hω hE
    by_cases hb : A' < Real.exp (|ξ| * supAbs (f ω))
    · exact Or.inr hb
    · left
      obtain ⟨M, hM⟩ := hfb ω
      have := sqBdyEvent_addFun hε0'.ne' hC
        (fun x => (tendstoLocallyUniformlyOn_univ.2 hω.1).tendsto_at (mem_univ x)) (f ω)
        (abs_le_supAbs hM) (not_lt.1 hb) hE
      have e : addFun (g ω) (f ω) = h ω := sub_add_cancel _ _
      rwa [e] at this
  have hsum : ENNReal.ofReal ((1 + p) / 2) = ENNReal.ofReal p + ENNReal.ofReal ((1 - p) / 2) := by
    rw [← ENNReal.ofReal_add hp.1.le hδ.le]; ring_nf
  have := hε.trans (k1.trans (k2.trans k3).le |>.trans (k4.trans (add_le_add_right hAP' _)))
  rw [hsum] at this
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top this

end LQGMetric.DFGPS
