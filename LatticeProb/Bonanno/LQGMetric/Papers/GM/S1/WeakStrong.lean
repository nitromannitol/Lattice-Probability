/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S1.WeakStrong at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Dilate
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Eq115
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgKolm
import LatticeProb.Bonanno.LQGMetric.Analysis.Multiplicative
import LatticeProb.Bonanno.LQGMetric.Blueprint.GMWeakUniqueness
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSScaling

/-!
# GM Lemma 1.10: every weak γ-LQG metric is strong

Source: Gwynne–Miller, arXiv:1905.00383v3 (GM), `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 1.10, l. 486–535; blueprint `blueprint/M1.md` §3 rows 10–16.

* `gm_s1_9` (l. 507): GM Theorem 1.9 (`Blueprint.GMWeakUniqueness`) applied to `D^{(b)}` and `D`
  (same `𝔠_r` by `gm_s1_8`) gives `D^{(b)} = 𝔨_b D`.
* `gm_s1_10` (l. 515–517): continuity of `b ↦ 𝔨_b` at `1`. GM: `h(·/b) − h_{1/b}(0) =ᵈ h` and
  Weyl scaling give `𝔨_b e^{−ξ h_{1/b}(0)} D_h(0, 1/b) =ᵈ D_h(0,1)`; with the continuous version of
  `(r, z) ↦ h_r(z)` (`CircleAvg.exists_continuous_version_circleAvg`) the left side converges
  pointwise as `b → 1`, and `tendsto_one_of_map_eq` (own elementary argument from the
  distribution-function lemma `Analysis.measure_eq_zero_of_Iic_div_invariant`, which is the core
  of GM's "it is easy to see") forces `𝔨_b → 1`.
* `gm_s1_11` (l. 507–519): `𝔨_b = b^β` (multiplicativity from `gm_s1_9_comp`, `gm_s1_9_unique`;
  Cauchy equation `gm_s1_11_cauchy`).
* `gm_s1_12` (l. 520–529), `gm_s1_13` (l. 529, `Blueprint.DFGPSScaling`), `gm_s1_14`
  (l. 530–534), `gm_l1_10` (Lemma 1.10).
Sign convention: blueprint BP-M1-3 (`𝔨_b = b^β`, `𝔠_r = r^β`, `β = ξQ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace GM

/-! ### `Z_n → Z` a.s. and `k_n Z_n =ᵈ Z > 0` force `k_n → 1` -/

section Core

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : Ω → ℝ} {Zn : ℕ → Ω → ℝ} {k : ℕ → ℝ}

omit [IsProbabilityMeasure P] in
lemma prob_le_eq_of_law {n : ℕ} (hZ : AEMeasurable Z P) (hZn : AEMeasurable (Zn n) P)
    (hlaw : P.map (fun ω => k n * Zn n ω) = P.map Z) (t : ℝ) :
    P {ω | k n * Zn n ω ≤ t} = P {ω | Z ω ≤ t} := by
  have := congrArg (fun ν : Measure ℝ => ν (Iic t)) hlaw
  rwa [Measure.map_apply_of_aemeasurable (hZn.const_mul _) measurableSet_Iic,
    Measure.map_apply_of_aemeasurable hZ measurableSet_Iic] at this

omit [IsProbabilityMeasure P] in
lemma map_Iic_eq (hZ : AEMeasurable Z P) (t : ℝ) : P.map Z (Iic t) = P {ω | Z ω ≤ t} := by
  rw [Measure.map_apply_of_aemeasurable hZ measurableSet_Iic]; rfl

omit [IsProbabilityMeasure P] in
lemma map_Iic_zero (hZ : AEMeasurable Z P) (hpos : ∀ᵐ ω ∂P, 0 < Z ω) : P.map Z (Iic 0) = 0 := by
  rw [map_Iic_eq hZ]
  have := ae_iff.1 hpos
  simpa only [not_lt] using this

lemma false_of_ge {c : ℝ} (hc : 1 < c) (hZ : AEMeasurable Z P)
    (hZn : ∀ n, AEMeasurable (Zn n) P) (hpos : ∀ᵐ ω ∂P, 0 < Z ω)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Zn n ω) atTop (𝓝 (Z ω))) (hk : ∀ n, c ≤ k n)
    (hlaw : ∀ n, P.map (fun ω => k n * Zn n ω) = P.map Z) : False := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hsupp := map_Iic_zero hZ hpos
  have h2 : ∀ t, 0 ≤ t → P {ω | Z ω ≤ t} ≤ P {ω | Z ω ≤ t / c} := by
    intro t ht
    let B : ℕ → Set Ω := fun N => ⋃ n, {ω | Zn (n + N) ω ≤ t / c}
    have hB : Antitone B := fun N M hNM => iUnion_subset fun n =>
      subset_iUnion_of_subset (n + (M - N)) fun ω hω => by
        simpa only [mem_setOf_eq, show n + (M - N) + N = n + M by omega] using hω
    have h1 : ∀ N, P {ω | Z ω ≤ t} ≤ P (B N) := fun N => by
      rw [← prob_le_eq_of_law hZ (hZn N) (hlaw N)]
      refine measure_mono fun ω hω => mem_iUnion.2 ⟨0, ?_⟩
      simp only [mem_setOf_eq, zero_add] at hω ⊢
      by_cases h0 : 0 ≤ Zn N ω
      · rw [le_div_iff₀ hc0]; nlinarith [hk N]
      · linarith [div_nonneg ht hc0.le]
    have hI : P (⋂ N, B N) = ⨅ N, P (B N) := hB.measure_iInter (fun N =>
      .iUnion fun n => nullMeasurableSet_le (hZn _) aemeasurable_const) ⟨0, measure_ne_top _ _⟩
    refine (le_iInf h1).trans (hI ▸ measure_mono_ae ?_)
    filter_upwards [hlim] with ω hω hmem
    simp only [mem_iInter, mem_iUnion, mem_setOf_eq, B] at hmem
    show Z ω ≤ t / c
    by_contra hgt
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hω.eventually (lt_mem_nhds (not_le.1 hgt)))
    obtain ⟨n, hn⟩ := hmem N
    exact absurd hn (not_le.2 (hN _ (Nat.le_add_left N n)))
  have hinv : ∀ t, P.map Z (Iic t) = P.map Z (Iic (t / c)) := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · rw [map_Iic_eq hZ, map_Iic_eq hZ]
      exact le_antisymm (h2 t ht) (measure_mono fun ω hω => le_trans hω (div_le_self ht hc.le))
    · rw [measure_mono_null (Iic_subset_Iic.2 ht.le) hsupp,
        measure_mono_null (Iic_subset_Iic.2 (div_neg_of_neg_of_pos ht hc0).le) hsupp]
  exact IsProbabilityMeasure.ne_zero _ (Analysis.measure_eq_zero_of_Iic_div_invariant hsupp hc hinv)

lemma false_of_le {c : ℝ} (hc0 : 0 < c) (hc : c < 1) (hZ : AEMeasurable Z P)
    (hZn : ∀ n, AEMeasurable (Zn n) P) (hpos : ∀ᵐ ω ∂P, 0 < Z ω)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Zn n ω) atTop (𝓝 (Z ω))) (hk : ∀ n, 0 < k n ∧ k n ≤ c)
    (hlaw : ∀ n, P.map (fun ω => k n * Zn n ω) = P.map Z) : False := by
  have hsupp := map_Iic_zero hZ hpos
  have h2 : ∀ t, 0 ≤ t → P {ω | Z ω < t / c} ≤ P {ω | Z ω ≤ t} := by
    intro t ht
    let C : ℕ → Set Ω := fun N => ⋂ n, {ω | Zn (n + N) ω ≤ t / c}
    have hC : Monotone C := fun N M hNM => subset_iInter fun n =>
      iInter_subset_of_subset (n + (M - N)) fun ω hω => by
        simpa only [mem_setOf_eq, show n + (M - N) + N = n + M by omega] using hω
    have h1 : ∀ N, P (C N) ≤ P {ω | Z ω ≤ t} := fun N => by
      rw [← prob_le_eq_of_law hZ (hZn N) (hlaw N)]
      refine measure_mono fun ω hω => ?_
      have hω := mem_iInter.1 hω 0
      simp only [mem_setOf_eq, zero_add] at hω ⊢
      by_cases h0 : 0 ≤ Zn N ω
      · rw [le_div_iff₀ hc0] at hω; nlinarith [hk N]
      · nlinarith [(hk N).1]
    have hU : P (⋃ N, C N) = ⨆ N, P (C N) := hC.measure_iUnion
    refine (measure_mono_ae ?_).trans (hU ▸ iSup_le h1)
    filter_upwards [hlim] with ω hω hlt
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hω.eventually (gt_mem_nhds (show Z ω < t / c from hlt)))
    exact mem_iUnion.2 ⟨N, mem_iInter.2 fun n => (hN _ (Nat.le_add_left N n)).le⟩
  set d : ℝ := 2 / (1 + c) with hd
  have hd1 : 1 < d := by rw [hd, lt_div_iff₀ (by linarith)]; linarith
  have hdc : d * c < 1 := by rw [hd, div_mul_eq_mul_div, div_lt_one (by linarith)]; linarith
  have hd0 : 0 < d := zero_lt_one.trans hd1
  have hinv : ∀ s, P.map Z (Iic s) = P.map Z (Iic (s / d)) := by
    intro s
    rcases le_or_gt s 0 with hs | hs
    · rw [measure_mono_null (Iic_subset_Iic.2 hs) hsupp,
        measure_mono_null (Iic_subset_Iic.2 (div_nonpos_of_nonpos_of_nonneg hs hd0.le)) hsupp]
    · rw [map_Iic_eq hZ, map_Iic_eq hZ]
      have ht : 0 < s / d := div_pos hs hd0
      refine le_antisymm ((measure_mono fun ω (hω : Z ω ≤ s) => ?_).trans (h2 _ ht.le))
        (measure_mono fun ω hω => le_trans hω (div_le_self hs.le hd1.le))
      show Z ω < s / d / c
      rw [div_div]
      exact lt_of_le_of_lt hω ((lt_div_iff₀ (mul_pos hd0 hc0)).2 (by nlinarith))
  exact IsProbabilityMeasure.ne_zero _ (Analysis.measure_eq_zero_of_Iic_div_invariant hsupp hd1 hinv)

/-- If `Z_n → Z` a.s., `Z > 0` a.s. and `k_n Z_n` has the law of `Z` (`k_n > 0`), then
`k_n → 1` (own elementary argument; GM l. 515–517 "it is easy to see"). -/
theorem tendsto_one_of_map_eq (hZ : AEMeasurable Z P) (hZn : ∀ n, AEMeasurable (Zn n) P)
    (hpos : ∀ᵐ ω ∂P, 0 < Z ω) (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Zn n ω) atTop (𝓝 (Z ω)))
    (hk : ∀ n, 0 < k n) (hlaw : ∀ n, P.map (fun ω => k n * Zn n ω) = P.map Z) :
    Tendsto k atTop (𝓝 1) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · by_contra hne
    obtain ⟨φ, hφm, hφ⟩ := extraction_of_frequently_atTop (not_eventually.1 hne)
    exact false_of_le (Zn := fun n => Zn (φ n)) (k := fun n => k (φ n)) (c := max a (1 / 2))
      (lt_max_of_lt_right (by norm_num)) (max_lt ha (by norm_num)) hZ (fun n => hZn _) hpos
      (by filter_upwards [hlim] with ω hω using hω.comp hφm.tendsto_atTop)
      (fun n => ⟨hk _, (not_lt.1 (hφ n)).trans (le_max_left _ _)⟩) (fun n => hlaw _)
  · by_contra hne
    obtain ⟨φ, hφm, hφ⟩ := extraction_of_frequently_atTop (not_eventually.1 hne)
    exact false_of_ge (Zn := fun n => Zn (φ n)) (k := fun n => k (φ n)) ha hZ (fun n => hZn _)
      hpos (by filter_upwards [hlim] with ω hω using hω.comp hφm.tendsto_atTop)
      (fun n => not_lt.1 (hφ n)) (fun n => hlaw _)

end Core

/-! ### Field and scaling facts -/

lemma affineComp_one_zero (g : DistC) : affineComp 1 0 g = g := by
  refine DFunLike.ext _ _ fun φ => ?_
  have e : testAffinePull 1 0 φ = φ := TestFunction.ext fun x => by
    rw [testAffinePull_apply _ _ one_ne_zero]; simp
  rw [GFFInv.affineComp_apply, e]; simp

lemma affineComp_inv_self {r : ℝ} (hr : r ≠ 0) (g : DistC) :
    affineComp r⁻¹ 0 (affineComp r 0 g) = g := by
  rw [affineComp_comp (inv_ne_zero hr) hr, mul_inv_cancel₀ hr]; simpa using affineComp_one_zero g

/-! ### GM.S1.9–S1.14 and Lemma 1.10 -/

variable {γ : ℝ}

/-- **GM.S1.9** (GM l. 507): GM Theorem 1.9 for `D̃ = D^{(b)}` gives `D^{(b)} = 𝔨_b D`. -/
theorem gm_s1_9 (hγ : 0 < γ) (hγ2 : γ < 2) (h19 : Blueprint.GMWeakUniqueness)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {b : ℝ} (hb : 0 < b) :
    ∃ k : ℝ, 0 < k ∧ EqSmulAS (dilateMetric b hb D) D k :=
  h19 γ hγ hγ2 _ D c (gm_s1_8 hD hb) hD

/-- **GM.S1.10** (GM l. 515–517): `b ↦ 𝔨_b` is continuous at `1`. -/
theorem gm_s1_10 (_hγ : 0 < γ) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (hex : ExistsNormalizedGFF) (k : ℝ → ℝ)
    (hk : ∀ b (hb : 0 < b), 0 < k b ∧ EqSmulAS (dilateMetric b hb D) D (k b)) :
    ContinuousAt k 1 := by
  obtain ⟨Ω, _, P, _, h, hh⟩ := hex
  obtain ⟨H, hHc, hHe⟩ := CircleAvg.exists_continuous_version_circleAvg hh.1
  have hc := isGFFPlusCont_of_isWholePlaneGFF hh.1
  have hDv : ∀ p : ℂ × ℂ, Measurable fun d : DistC => (D d).1 p := fun p =>
    (continuous_eval_const p).measurable.comp
      (measurable_subtype_coe.comp hD.measurable)
  let Zf : ℝ → Ω → ℝ := fun b ω =>
    Real.exp (-xiGamma γ * H b⁻¹ 0 ω) * (D (h ω)).1 (0, ((b⁻¹ : ℝ) : ℂ))
  have hZe : ∀ b, 0 < b → Zf b =ᵐ[P] fun ω => Real.exp (-xiGamma γ *
      (circleAvg (h ω) b⁻¹ 0 - circleAvg (h ω) 1 0)) * (D (h ω)).1 (0, ((b⁻¹ : ℝ) : ℂ)) :=
    fun b hb => by
      filter_upwards [hHe b⁻¹ (inv_pos.2 hb) 0] with ω hω
      simp only [Zf, hω]
  have hZm : ∀ b, 0 < b → AEMeasurable (Zf b) P := fun b hb =>
    (((((measurable_circleAvg_left _ 0).comp hh.1.measurable).sub
      ((measurable_circleAvg_left 1 0).comp hh.1.measurable)).const_mul _).exp.mul
        ((hDv _).comp hh.1.measurable)).aemeasurable.congr (hZe b hb).symm
  have hZ1 : Zf 1 =ᵐ[P] fun ω => (D (h ω)).1 (0, 1) := by
    filter_upwards [hZe 1 one_pos] with ω hω
    rw [hω]; simp
  have hlaw : ∀ b (hb : 0 < b), P.map (fun ω => k b * Zf b ω) = P.map (Zf 1) := by
    intro b hb
    let g : Ω → DistC := fun ω =>
      addConst (affineComp b⁻¹ 0 (h ω)) (-(circleAvg (h ω) b⁻¹ 0))
    have hgm : Measurable g := ((hh.1.affineComp (inv_pos.2 hb) 0).addConst
      ((measurable_circleAvg_left _ 0).comp hh.1.measurable).neg).measurable
    have hg : P.map g = P.map h := CircleAvg.map_affine_sub_circleAvg hh (inv_pos.2 hb) 0
    have e1 : (fun ω => k b * Zf b ω) =ᵐ[P] fun ω => (D (g ω)).1 (0, 1) := by
      filter_upwards [hZe b hb, hh.2, hD.ae_dist_addConst
        (isGFFPlusCont_affineComp hc (inv_pos.2 hb) 0), (hk b hb).2 P h hc] with ω e1 e2 e3 e4
      have e5 := e4 0 ((b⁻¹ : ℝ) : ℂ)
      rw [dilateMetric, ContMetric.rescale_apply, mul_zero, ← Complex.ofReal_mul,
        mul_inv_cancel₀ hb.ne', Complex.ofReal_one] at e5
      show _ = (D (addConst _ _)).1 (0, 1)
      rw [e3, e5, e1, e2, sub_zero, show xiGamma γ * -circleAvg (h ω) b⁻¹ 0 =
        -xiGamma γ * circleAvg (h ω) b⁻¹ 0 by ring]
      ring
    rw [Measure.map_congr e1, Measure.map_congr hZ1]
    change P.map ((fun d : DistC => (D d).1 (0, 1)) ∘ g) =
      P.map ((fun d : DistC => (D d).1 (0, 1)) ∘ h)
    rw [← Measure.map_map (hDv _) hgm, hg, Measure.map_map (hDv _) hh.1.measurable]
  have hpos : ∀ᵐ ω ∂P, 0 < Zf 1 ω := ae_of_all _ fun ω => by
    refine mul_pos (Real.exp_pos _) ?_
    have : (0 : ℂ) ≠ ((1⁻¹ : ℝ) : ℂ) := by simp
    exact dist_pos.2 (show (D (h ω)).pt 0 ≠ (D (h ω)).pt _ from this)
  have hseq : ∀ v : ℕ → ℝ, (∀ n, 0 < v n) → Tendsto v atTop (𝓝 1) →
      Tendsto (fun n => k (v n)) atTop (𝓝 1) := by
    intro v hv hv1
    have hvi : Tendsto (fun n => (v n)⁻¹) atTop (𝓝 1⁻¹) := hv1.inv₀ one_ne_zero
    refine tendsto_one_of_map_eq (Z := Zf 1) (Zn := fun n => Zf (v n)) (hZm 1 one_pos)
      (fun n => hZm _ (hv n)) hpos (ae_of_all _ fun ω => ?_) (fun n => (hk _ (hv n)).1)
      (fun n => hlaw _ (hv n))
    have hH : Tendsto (fun n => H (v n)⁻¹ 0 ω) atTop (𝓝 (H 1⁻¹ 0 ω)) := by
      have := ((hHc ω).continuousWithinAt (x := ((1 : ℝ)⁻¹, (0 : ℂ)))
        ⟨by norm_num, mem_univ _⟩).tendsto.comp (tendsto_nhdsWithin_iff.2
          ⟨hvi.prodMk_nhds tendsto_const_nhds, Eventually.of_forall fun n =>
            ⟨inv_pos.2 (hv n), mem_univ _⟩⟩)
      exact this
    have hDt : Tendsto (fun n => (D (h ω)).1 (0, (((v n)⁻¹ : ℝ) : ℂ))) atTop
        (𝓝 ((D (h ω)).1 (0, ((1⁻¹ : ℝ) : ℂ)))) :=
      ((D (h ω)).1.continuous.tendsto _).comp (tendsto_const_nhds.prodMk_nhds
        ((Complex.continuous_ofReal.tendsto _).comp hvi))
    exact ((Real.continuous_exp.tendsto _).comp (hH.const_mul _)).mul hDt
  have hk1 : k 1 = 1 := tendsto_nhds_unique tendsto_const_nhds
    (hseq (fun _ => 1) (fun _ => one_pos) tendsto_const_nhds)
  rw [ContinuousAt, hk1, tendsto_nhds_iff_seq_tendsto]
  intro u hu
  have hv1 : Tendsto (fun n => max (u n) (1 / 2)) atTop (𝓝 1) := by
    have h2 := hu.max (tendsto_const_nhds (x := (1 / 2 : ℝ)))
    rwa [max_eq_left (by norm_num : (1 / 2 : ℝ) ≤ 1)] at h2
  refine (hseq _ (fun n => lt_of_lt_of_le (by norm_num) (le_max_right _ _)) hv1).congr' ?_
  filter_upwards [hu.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))] with n hn
  show k (max (u n) (1 / 2)) = k (u n)
  rw [max_eq_left hn.le]

/-- **GM.S1.9–S1.11** (GM l. 507–519): `𝔨_b = b^β`. If no normalized GFF exists, every
`EqSmulAS` statement is vacuous (`β = 0`). -/
theorem gm_s1_11 (hγ : 0 < γ) (hγ2 : γ < 2) (h19 : Blueprint.GMWeakUniqueness)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) :
    ∃ β : ℝ, ∀ {b : ℝ} (hb : 0 < b), EqSmulAS (dilateMetric b hb D) D (b ^ β) := by
  by_cases hex : ExistsNormalizedGFF
  · choose kf hkf using fun b (hb : 0 < b) => gm_s1_9 hγ hγ2 h19 hD hb
    let K : ℝ → ℝ := fun b => if hb : 0 < b then kf b hb else 1
    have hK : ∀ b (hb : 0 < b), 0 < K b ∧ EqSmulAS (dilateMetric b hb D) D (K b) :=
      fun b hb => by simp only [K, dif_pos hb]; exact hkf b hb
    have hmul : ∀ b₁ b₂, 0 < b₁ → 0 < b₂ → K (b₁ * b₂) = K b₁ * K b₂ := by
      intro b₁ b₂ h₁ h₂
      refine gm_s1_9_unique hex (hK _ (mul_pos h₁ h₂)).2 ?_
      rw [← gm_s1_9_comp D h₁ h₂]
      intro Ω _ P _ h hh
      filter_upwards [(hK b₁ h₁).2 P _ (isGFFPlusCont_affineComp hh (inv_pos.2 h₂) 0),
        (hK b₂ h₂).2 P h hh] with ω e1 e2 u v
      have e3 := e2 u v
      simp only [dilateMetric, ContMetric.rescale_apply] at e3
      show (dilateMetric b₁ h₁ D (affineComp b₂⁻¹ 0 (h ω))).1 ((b₂ : ℂ) * u, (b₂ : ℂ) * v) = _
      rw [e1, e3]
      ring
    obtain ⟨β, hβ⟩ := gm_s1_11_cauchy K (fun b hb => (hK b hb).1) hmul
      (gm_s1_10 hγ hD hex K hK)
    exact ⟨β, fun {b} hb => hβ b hb ▸ (hK b hb).2⟩
  · refine ⟨0, fun {b} hb => ?_⟩
    intro Ω _ P _ h hh
    exfalso
    obtain ⟨-, f, -, hg⟩ := hh
    exact hex ⟨Ω, _, P, inferInstance, _, hg.addConst
      ((measurable_circleAvg_left 1 0).comp hg.measurable).neg, by
        filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hg] with ω hω
        rw [hω]
        simp only [Pi.neg_apply, Function.comp_apply]
        ring⟩

/-- **GM.S1.12** (GM l. 520–529): `b^{−β} e^{−ξ h_b(0)} D_h(b·, b·) = D_{h(b·) − h_b(0)} =ᵈ D_{h°}`,
so `D` is a weak metric with `𝔠_r = r^β`. -/
theorem gm_s1_12 (_hγ : 0 < γ) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (β : ℝ)
    (hβ : ∀ {b : ℝ} (hb : 0 < b), EqSmulAS (dilateMetric b hb D) D (b ^ β)) :
    IsWeakLQGMetric γ D (fun r => r ^ β) where
  measurable := hD.measurable
  length := hD.length
  locality := hD.locality
  weyl := hD.weyl
  translation := hD.translation
  tightness := by
    refine tightAcrossScales_of_ae_eq hD.measurable (fun r hr => Real.rpow_pos_of_pos hr _)
      (rpow_ratio_bounds β) ?_
    intro Ω _ P _ h hh r hr
    have hf := isGFFPlusCont_of_isWholePlaneGFF (hh.affineComp hr 0)
    filter_upwards [hβ hr P _ hf, hD.ae_dist_addConst hf] with ω h1 h2
    ext ⟨u, v⟩
    have h1' := h1 u v
    simp only [dilateMetric, ContMetric.rescale_apply, affineComp_inv_self hr.ne'] at h1'
    simp only [ContinuousMap.smul_apply, ContinuousMap.comp_apply, smul_eq_mul, scaleArgs,
      ContinuousMap.coe_mk]
    rw [h1', h2, show xiGamma γ * -circleAvg (h ω) r 0 = -xiGamma γ * circleAvg (h ω) r 0 by ring]
    have := (Real.rpow_pos_of_pos hr β).ne'
    field_simp

/-- **GM.S1.13** (GM l. 529): DFGPS Theorem 1.5 for `𝔠_r = r^β` forces `β = ξQ`. -/
theorem gm_s1_13 (hγ : 0 < γ) (hγ2 : γ < 2) (h15 : Blueprint.DFGPSScaling)
    {D : DistC → ContMetric} {β : ℝ} (hD : IsWeakLQGMetric γ D (fun r => r ^ β)) :
    β = xiGamma γ * Q γ := by
  have key : ∀ ζ : ℝ, 0 < ζ → xiGamma γ * Q γ - ζ ≤ β ∧ β ≤ xiGamma γ * Q γ + ζ := by
    intro ζ hζ
    obtain ⟨δ₀, hδ₀, H⟩ := h15 γ hγ hγ2 D _ hD ζ hζ
    have hm : 0 < min δ₀ (1 / 2) := lt_min hδ₀ (by norm_num)
    have hδ0 : 0 < min δ₀ (1 / 2) / 2 := half_pos hm
    have hδ1 : min δ₀ (1 / 2) / 2 < 1 := by
      linarith [half_lt_self hm, min_le_right δ₀ (1 / 2)]
    obtain ⟨l, u⟩ := H _ ⟨hδ0, (half_lt_self hm).trans_le (min_le_left _ _)⟩ 1 one_pos
    simp only [mul_one, Real.one_rpow, div_one] at l u
    exact ⟨(Real.rpow_le_rpow_left_iff_of_base_lt_one hδ0 hδ1).1 u,
      (Real.rpow_le_rpow_left_iff_of_base_lt_one hδ0 hδ1).1 l⟩
  refine le_antisymm (le_of_forall_pos_le_add fun ζ hζ => (key ζ hζ).2)
    (le_of_forall_pos_le_add fun ζ hζ => by linarith [(key ζ hζ).1])

/-- **GM.S1.14** (GM l. 530–534): Axiom IV′ and `D^{(r)} = r^{ξQ} D` give Axiom IV. -/
theorem gm_s1_14 (_hγ : 0 < γ) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c)
    (hβ : ∀ {b : ℝ} (hb : 0 < b), EqSmulAS (dilateMetric b hb D) D (b ^ (xiGamma γ * Q γ))) :
    IsStrongLQGMetric γ D where
  measurable := hD.measurable
  length := hD.length
  locality := hD.locality
  weyl := hD.weyl
  coord P _ h hh r hr z := by
    have hF := isGFFPlusCont_affineComp hh hr z
    filter_upwards [hD.translation P h hh z, hβ hr P _ hF, hD.ae_dist_addConst hF]
      with ω h1 h2 h3 u v
    have e : affineComp r⁻¹ 0 (affineComp r z (h ω)) = affineComp 1 z (h ω) := by
      rw [affineComp_comp (inv_ne_zero hr.ne') hr.ne', mul_inv_cancel₀ hr.ne']
      simp
    have h2' := h2 u v
    simp only [dilateMetric, ContMetric.rescale_apply, e] at h2'
    rw [h3, ← h1 ((r : ℂ) * u) ((r : ℂ) * v), h2', Real.rpow_def_of_pos hr,
      show Real.log r * (xiGamma γ * Q γ) = xiGamma γ * (Q γ * Real.log r) by ring]

/-- **GM Lemma 1.10** (GM l. 486–535): every weak γ-LQG metric is strong (given GM Theorem 1.9
and DFGPS Theorem 1.5 as Blueprint hypotheses). -/
theorem gm_l1_10 (hγ : 0 < γ) (hγ2 : γ < 2) (h19 : Blueprint.GMWeakUniqueness)
    (h15 : Blueprint.DFGPSScaling) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) : IsStrongLQGMetric γ D := by
  obtain ⟨β, hβ⟩ := gm_s1_11 hγ hγ2 h19 hD
  have hβ' := gm_s1_13 hγ hγ2 h15 (gm_s1_12 hγ hD β hβ)
  subst hβ'
  exact gm_s1_14 hγ hD hβ


end GM
end LQGMetric
