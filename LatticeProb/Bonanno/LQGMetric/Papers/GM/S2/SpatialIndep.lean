/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndep at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepAsm5
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepShift
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.Defs

/-!
# GM Lemma 2.7 (spatial independence)

Source: GM = Gwynne–Miller, *Existence and uniqueness of the Liouville quantum gravity metric for
`γ ∈ (0,2)`*, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`, Lemma 2.7
(`lem-spatial-ind`, l. 964–971) and its proof (l. 972–1004). Cited results, taken as hypotheses:
LM Lemma 2.1 (Markov property, `Blueprint.LMLem2_1`) and MQ Lemma 4.1 with general radii
(`Blueprint.MQLem4_1Gen`, decision D41).

The proof follows GM:
1. (bookkeeping) translate by `a` so that `U = ⋃_{z} B_{1+s}(z − a)` misses `∂𝔻`, and normalize
   (`isNormalized_shift`, `aeEventIn_shift`);
2. (GM l. 974–975) Markov decomposition `h' = 𝔥 + h̊` on `U` (`LMLem2_1`), with `𝔥` a.s. equal to
   an `h'|_{ℂ∖U}`-measurable `G`, and `h̊|_{B_{1+s}(z)}` mutually independent;
3. (GM l. 979–988) the good event `{𝔐_z ≤ A}` read off `W_z = G − h'_{1+s}(z)` (`goodD`), with
   `P[bad] ≤ min(p/4, (1−q)/4)` uniformly (`exists_good_const`, `prob_not_goodD_le`);
4. (GM l. 989–998) on the good event, MQ Lemma 4.1 + Remark 4.2 (`rn_bounds_of_rep`);
5. (GM l. 999–1004) conclusion by `frozen_union_bound` (GM (2.13); GM's `1 − p̃^{#}` at l. 1002
   should read `1 − (1 − p̃)^{#}`, GA-8b in `DEVIATIONS.md`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric InnerProductSpace

namespace LQGMetric.GM

open Blueprint

/-- **GM Lemma 2.7** (l. 964–1004). -/
theorem gm_L2_7 (hLM21 : Blueprint.LMLem2_1) (hMQ : Blueprint.MQLem4_1Gen) : L2_7 := by
  intro s p q hs hp hp1 hq hq1
  generalize hRdef : 1 + s = R
  have hR : 0 < R := by rw [← hRdef]; linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = s / 4 := ⟨_, rfl⟩
  obtain ⟨ρ₁, hρ₁def⟩ : ∃ ρ₁ : ℝ, ρ₁ = 1 / R := ⟨_, rfl⟩
  obtain ⟨ρ₂, hρ₂def⟩ : ∃ ρ₂ : ℝ, ρ₂ = (1 + s / 2) / R := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδR : δ < R := by rw [hδdef, ← hRdef]; linarith
  have hρ₁ : 0 < ρ₁ := by rw [hρ₁def]; positivity
  have hρ₁R : ρ₁ * R = 1 := by rw [hρ₁def]; field_simp
  have hρ₂R : ρ₂ * R = 1 + s / 2 := by rw [hρ₂def]; field_simp
  have hρ₁₂ : ρ₁ < ρ₂ := by
    rw [hρ₁def, hρ₂def]; exact div_lt_div_of_pos_right (by linarith) hR
  have hρ₂1 : ρ₂ < 1 := by rw [hρ₂def, div_lt_one hR, ← hRdef]; linarith
  have hρ₂0 : 0 ≤ ρ₂ := by rw [hρ₂def]; positivity
  have hρδ : ρ₂ * R + δ < R := by rw [hρ₂R, hδdef, ← hRdef]; linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (p / 4) ((1 - q) / 4) / 3 := ⟨_, rfl⟩
  have hε : 0 < ε := by
    rw [hεdef]; exact div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  obtain ⟨A, hA, hosc, hoff, hzv⟩ := exists_good_const hδ hδR hρ₂1 hR hε
  obtain ⟨c, -, hc⟩ := exists_MQSpec hMQ hρ₁ hρ₁₂ hρ₂1 hA
  obtain ⟨n₀, hn₀⟩ := frozen_union_bound (c := c) hp hq1
  refine ⟨n₀, ?_⟩
  intro Ω _ P _ h hh Z hZ hsep E hE hpE
  classical
  -- 1. translation and normalization
  set a : ℂ := (((∑ z ∈ Z, ‖z‖) + R + 2 : ℝ) : ℂ) with ha
  set k : Ω → ℝ := fun ω => -circleAvg (affineComp 1 a (h ω)) 1 0 with hk
  set h' : Ω → DistC := fun ω => addConst (affineComp 1 a (h ω)) (k ω) with hh'def
  have hN : IsNormalizedWPGFF h' P := isNormalized_shift hh a
  have hh' : IsWholePlaneGFF h' P := hN.1
  -- 2. the Markov decomposition on `U`
  obtain ⟨hh0, hz, hdec, hharm, ⟨G, hGF, hhG⟩, -, hzbU, -, hind⟩ :=
    hLM21 P h' hN (unionO Z a R) (disjoint_unionO_sphere hR)
  have hFle := fieldSigmaClosed_le_gm hh'.measurable ((unionO Z a R : Set ℂ)ᶜ)
  have hGm : Measurable G := hGF.mono hFle le_rfl
  have hindG : Indep (MeasurableSpace.comap hz inferInstance)
      (MeasurableSpace.comap G inferInstance) P :=
    indep_of_indep_of_le_right hind hGF.comap_le
  have hdecG : ∀ᵐ ω ∂P, h' ω = G ω + hz ω := by
    filter_upwards [hhG] with ω hω; rw [hdec, hω]
  -- 3. the pieces
  let x : {z // z ∈ Z} → ℂ := fun i => (i : ℂ) - a
  have hBU : ∀ i : {z // z ∈ Z}, ball (x i) R ⊆ (unionO Z a R : Set ℂ) :=
    fun i y hy => ballO_le_unionO (a := a) (R := R) i.2 hy
  have hzbi : ∀ i : {z // z ∈ Z}, IsZeroBoundaryGFF (ballO (x i) R)
      (fun ω => restrictTo (ballO (x i) R) (hz ω)) P := fun i =>
    isZeroBoundaryGFF_restrict_component (ballO_le_unionO i.2) (isOpen_unionO_diff hsep i.2) hzbU
  have h1R : ∀ i : {z // z ∈ Z}, ballO (x i) 1 ≤ ballO (x i) R := fun i =>
    ball_subset_ball (by rw [← hRdef]; linarith)
  let Y : ∀ i : {z // z ∈ Z}, Ω → DistOn (ballO (x i) 1) :=
    fun i ω => restrictTo (ballO (x i) 1) (hz ω)
  have hYeq : ∀ i, Y i = distRes (ballO (x i) 1) (ballO (x i) R) ∘
      fun ω => restrictTo (ballO (x i) R) (hz ω) := fun i => by
    funext ω; exact (distRes_restrictTo (h1R i) (hz ω)).symm
  have hY : ∀ i, Measurable (Y i) := fun i => by
    rw [hYeq i]; exact (measurable_distRes _ _).comp (hzbi i).measurable
  have hYi : iIndepFun Y P := by
    have := (iIndepFun_restrictTo_of_zeroBoundary isBounded_unionO
      (fun i : {z // z ∈ Z} => ballO (x i) R) (fun i => ballO_le_unionO i.2)
      (fun i j hij => disjoint_ball_shift hsep i.2 j.2 (fun h => hij (Subtype.ext h)))
      (fun i => isOpen_unionO_diff hsep i.2) hzbU).comp
      (fun i => distRes (ballO (x i) 1) (ballO (x i) R)) (fun i => measurable_distRes _ _)
    convert this using 1
    funext i; exact hYeq i
  -- the frozen harmonic parts `W_z = G − h'_{1+s}(z)`
  let W : Ω → {z // z ∈ Z} → DistC := fun ω i => addConst (G ω) (-circleAvg (h' ω) R (x i))
  have hWF : Measurable[fieldSigmaClosed h' ((unionO Z a R : Set ℂ)ᶜ)] W := by
    have hcm : ∀ i, Measurable[fieldSigmaClosed h' ((unionO Z a R : Set ℂ)ᶜ)]
        fun ω => -circleAvg (h' ω) R (x i) := fun i =>
      (measurable_circleAvg_fieldSigmaClosed h' R (x i)
        (sphere_subset_compl_unionO hsep hR i.2)).neg
    exact @measurable_addConst_pi Ω (fieldSigmaClosed h' ((unionO Z a R : Set ℂ)ᶜ)) _ G
      (fun i ω => -circleAvg (h' ω) R (x i)) hGF hcm
  have hW : Measurable W := hWF.mono hFle le_rfl
  have hWY : IndepFun W (fun ω i => Y i ω) P :=
    indepFun_pi_of_indep_comap hind hWF (f := fun i T => restrictTo (ballO (x i) 1) T)
      (fun i => measurable_restrictTo _)
  -- the events
  have hE' : ∀ i : {z // z ∈ Z}, ∃ S : Set (DistOn (ballO (x i) 1)), MeasurableSet S ∧
      E i =ᵐ[P] (fun ω => restrictTo (ballO (x i) 1)
        (addConst (h' ω) (-circleAvg (h' ω) R (x i)))) ⁻¹' S := fun i => by
    have := hE i i.2
    rw [← hRdef] at this ⊢
    exact exists_preimage_of_aeEventIn (aeEventIn_shift hh (by rw [← hRdef] at hR; exact hR)
      (i : ℂ) a k this)
  choose S hS hES using hE'
  let T : ∀ i : {z // z ∈ Z}, Set (({z // z ∈ Z} → DistC) × DistOn (ballO (x i) 1)) :=
    fun i => {pr | pr.2 + restrictTo (ballO (x i) 1) (pr.1 i) ∈ S i}
  have hT : ∀ i, MeasurableSet (T i) := fun i => measurableSet_shiftSet i _ (hS i)
  have hEq : ∀ i : {z // z ∈ Z}, E i =ᵐ[P] {ω | (W ω, Y i ω) ∈ T i} := by
    intro i
    refine eventuallyEqSet_iff.2 ?_
    filter_upwards [eventuallyEqSet_iff.1 (hES i), hdecG] with ω h1 hω
    rw [h1]
    show restrictTo (ballO (x i) 1) (addConst (h' ω) (-circleAvg (h' ω) R (x i))) ∈ S i ↔
      restrictTo (ballO (x i) 1) (hz ω) + restrictTo (ballO (x i) 1) (W ω i) ∈ S i
    have : addConst (h' ω) (-circleAvg (h' ω) R (x i)) = hz ω + W ω i := by
      show addConst (h' ω) (-circleAvg (h' ω) R (x i)) =
        hz ω + addConst (G ω) (-circleAvg (h' ω) R (x i))
      rw [← addConst_add_left, ← hω]
    rw [this, restrictTo_add_gm]
  have hpE' : ∀ i : {z // z ∈ Z}, ENNReal.ofReal p ≤ P {ω | (W ω, Y i ω) ∈ T i} := fun i => by
    rw [← measure_congr (hEq i)]; exact hpE i i.2
  -- 4. the good sets and the bound on their complements
  obtain ⟨Sd, hSdc, hSdd⟩ := TopologicalSpace.exists_countable_dense ℂ
  let Good : {z // z ∈ Z} → Set ({z // z ∈ Z} → DistC) :=
    fun i => {w | goodD δ hδ.le Sd (x i) (ρ₂ * R) A (w i)}
  have hGood : ∀ i, MeasurableSet (Good i) := fun i => by
    show MeasurableSet ((fun f : {z // z ∈ Z} → DistC => f i) ⁻¹'
      {T : DistC | goodD δ hδ.le Sd (x i) (ρ₂ * R) A T})
    exact measurable_pi_apply i (measurableSet_goodD hδ.le hSdc (x i) (ρ₂ * R) A)
  have hbad : ∀ i, P (W ⁻¹' (Good i)ᶜ) ≤ ENNReal.ofReal (min (p / 4) ((1 - q) / 4)) := by
    intro i
    have hρ : 0 ≤ ρ₂ * R := by positivity
    have h0 := prob_not_goodD_le (P := P) (h' := h') (G := G) hdec hhG hharm (A := A) hδ
      (hBU i) hρδ hρ Sd
    have h1 := prob_oscEv_le hh' hzbU hindG hdecG hGm (z := x i) hR hρ₂0 hρ₂1 (hBU i)
      (half_pos hA)
    have h2 := hoff P h' hh' (x i)
    have hI := integral_radProf_pos hδ
    have h3 := prob_zbPair_ge_le hδ hδR (hzbi i) (t := A * (∫ y, radProf δ y) / 4)
      (by positivity)
    calc P (W ⁻¹' (Good i)ᶜ) ≤ _ := (measure_mono fun ω hω => hω).trans h0
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε :=
          add_le_add (add_le_add (h1.trans (hosc (x i))) h2)
            (h3.trans (ENNReal.ofReal_le_ofReal hzv))
      _ = ENNReal.ofReal (min (p / 4) ((1 - q) / 4)) := by
          rw [← ENNReal.ofReal_add hε.le hε.le, ← ENNReal.ofReal_add (by positivity) hε.le,
            hεdef]
          congr 1; ring
  -- 5. the Radon–Nikodym bounds on the good sets
  set ht : Ω → DistC := fun ω => h' ω - G ω with htdef
  have htm : Measurable ht := measurable_distOn_iff.2 fun φ => by
    show Measurable fun ω => h' ω φ - G ω φ
    exact ((measurable_distOn_apply φ).comp hh'.measurable).sub
      ((measurable_distOn_apply φ).comp hGm)
  have hthz : ∀ᵐ ω ∂P, ht ω = hz ω := by
    filter_upwards [hdecG] with ω hω
    simp only [htdef]; rw [hω, add_sub_cancel_left]
  let aa : {z // z ∈ Z} → ENNReal := fun i => (P.map (Y i)) (S i)
  have hrn : ∀ i, ∀ᵐ w ∂(P.map W), w ∈ Good i →
      (P.map (Y i)) {b | (w, b) ∈ T i} ^ 2 ≤ ENNReal.ofReal c * aa i ∧
        aa i ^ 2 ≤ ENNReal.ofReal c * (P.map (Y i)) {b | (w, b) ∈ T i} := by
    intro i
    have hf : Measurable fun w : {z // z ∈ Z} → DistC => (P.map (Y i)) (Prod.mk w ⁻¹' T i) :=
      measurable_measure_prodMk_left (hT i)
    have hmeas : MeasurableSet {w : {z // z ∈ Z} → DistC | w ∈ Good i →
        ((P.map (Y i)) (Prod.mk w ⁻¹' T i) ^ 2 ≤ ENNReal.ofReal c * aa i ∧
          aa i ^ 2 ≤ ENNReal.ofReal c * (P.map (Y i)) (Prod.mk w ⁻¹' T i))} :=
      MeasurableSet.imp (hGood i) ((measurableSet_le (hf.pow_const 2) measurable_const).inter
        (measurableSet_le measurable_const (hf.const_mul _)))
    refine (ae_map_iff hW.aemeasurable hmeas).2 ?_
    filter_upwards [hhG, hharm] with ω hω hωh hgood
    obtain ⟨g, hg, hrep⟩ := hωh
    rw [hω] at hrep
    obtain ⟨hrepW, hbd⟩ := pointwise_good hg hrep hδ (hBU i) hρδ hSdd hgood
    exact rn_bounds_of_rep hc hR hρ₁R htm hthz (hzbi i) (hg.mono (hBU i)) hbd hrepW (hS i)
  -- 6. conclusion (GM l. 999–1004)
  have hcard : n₀ ≤ Fintype.card {z // z ∈ Z} := by rw [Fintype.card_coe]; exact hZ
  have hfin := hn₀ P W Y hcard hW hY hWY hYi T hT Good hGood hbad aa hrn hpE'
  refine hfin.trans (measure_mono_ae ?_)
  have hall := ae_all_iff.2 fun i => eventuallyEqSet_iff.1 (hEq i)
  filter_upwards [hall] with ω hω hex
  obtain ⟨i, hi⟩ := hex
  exact mem_iUnion₂.2 ⟨i, i.2, (hω i).2 hi⟩

end LQGMetric.GM
