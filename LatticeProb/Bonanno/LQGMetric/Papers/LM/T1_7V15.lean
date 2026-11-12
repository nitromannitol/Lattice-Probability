/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V15 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V14
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V9

/-!
# LM Theorem 1.7, Steps 1–2 per field: the Efron–Stein integrand bounded by the resampling bounds

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.7 (l. 1011–1055; D107 §3(i)–(ii)). With `Φ` and the
jointly measurable conditional law `K` of `t17v_es_avg`: for `ν`-a.e. `d` and `t17Λ`-a.e. `θ`, the
Efron–Stein integrand `t17ES` at `(θ, d)` is at most `∑_S b_S` for every family `b` bounding
`(F(D^S) − F(d))_+²` over all `D^S` compatible with `d` at `S` (`T17Compat`).

The exceptional set is the zero set of a jointly measurable function of `(θ, d)` (kernel
measurability), so the quantifiers "a.e. `θ`, a.e. `d`" of `t17v_resample_kernel` can be exchanged
(Tonelli, `Measure.ae_ae_comm`; D107 §1.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric.LM

/-- **Steps 1–2, per field, a.e. `d` and a.e. `θ`** -/
theorem t17v_ES_le (ν : Measure ContMetric) [IsProbabilityMeasure ν]
    (hL : ∀ᵐ d ∂ν, d.IsLength) {C : ℝ} (hC : 0 ≤ C)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : ℂ, p.2.1 (z, w) ≤ C * p.1.1 (z, w)) {ε R : ℝ}
    {F : ContMetric → ℝ} (hFm : Measurable F)
    {Φ : (ℝ × ℝ) × (t17Box ε R → ℕ → ℝ≥0∞) → ℝ} (hΦ : Measurable Φ)
    (K : Kernel ((ℝ × ℝ) × (t17Box ε R → ℕ → ℝ≥0∞)) ContMetric) [IsMarkovKernel K]
    (hslice : ∀ᵐ θ ∂t17Λ, (ν.map (t17Y ε θ (t17Box ε R))) ⊗ₘ
        (K.comap (fun y => (θ, y)) (measurable_const.prodMk measurable_id)) =
      ν.map fun d => (t17Y ε θ (t17Box ε R) d, d))
    (hΦF : ∀ᵐ θ ∂t17Λ, ∀ᵐ d ∂ν, F d = Φ (θ, t17Y ε θ (t17Box ε R) d))
    (hprod : ∀ᵐ θ ∂(volume : Measure (ℝ × ℝ)), ν.map (t17Y ε θ (t17Box ε R)) =
      Measure.pi fun k : t17Box ε R => ν.map (t17eEnc (t17Square ε θ k))) :
    ∀ᵐ d ∂ν, ∀ᵐ θ ∂t17Λ, ∀ b : t17Box ε R → ℝ,
      (∀ (k : t17Box ε R) (d'' : ContMetric), T17Compat C ε θ (t17Box ε R) d d'' k →
        max (F d'' - F d) 0 ^ 2 ≤ b k) →
      t17ES ε R F Φ ν θ d ≤ ∑ k, ENNReal.ofReal (b k) := by
  set p := TopologicalSpace.denseSeq (ℂ × ℂ)
  obtain ⟨M, hM, hML, hνM⟩ := t17v_measurable_length_subset ν hL
  have hY := t17v_measurable_Y ε (t17Box ε R)
  have hev : ∀ n, Measurable fun d : ContMetric => d.1 (p n) := fun n =>
    (continuous_eval_const _).measurable.comp measurable_subtype_coe
  -- resampled coordinates and the good set of `D^S`
  set yS : (t17Box ε R) → ((ℝ × ℝ) × ContMetric) × ContMetric → (t17Box ε R) → ℕ → ℝ≥0∞ := fun k q =>
    Function.update (t17Y ε q.1.1 (t17Box ε R) q.1.2) k (t17Y ε q.1.1 (t17Box ε R) q.2 k) with hySdef
  have hyS : ∀ k, Measurable (yS k) := fun k =>
    (t17v_measurable_update k).comp ((hY.comp measurable_fst).prodMk
      (hY.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  set T : (t17Box ε R) → Set ((((ℝ × ℝ) × ContMetric) × ContMetric) × ContMetric) := fun k =>
    {t | t.2 ∈ M ∧ (∀ n, t.2.1 (p n) ≤ C ^ 2 * t.1.1.2.1 (p n)) ∧
      (∀ n, t.1.1.2.1 (p n) ≤ C ^ 2 * t.2.1 (p n)) ∧ t17Y ε t.1.1.1 (t17Box ε R) t.2 = yS k t.1 ∧
      F t.2 = Φ (t.1.1.1, yS k t.1)} with hTdef
  have hT : ∀ k, MeasurableSet (T k) := by
    intro k
    have hB1 : MeasurableSet {t : (((ℝ × ℝ) × ContMetric) × ContMetric) × ContMetric |
        ∀ n, t.2.1 (p n) ≤ C ^ 2 * t.1.1.2.1 (p n)} := by
      have : {t : (((ℝ × ℝ) × ContMetric) × ContMetric) × ContMetric |
          ∀ n, t.2.1 (p n) ≤ C ^ 2 * t.1.1.2.1 (p n)} = ⋂ n, {t | t.2.1 (p n) ≤
            C ^ 2 * t.1.1.2.1 (p n)} := by ext; simp
      rw [this]
      exact MeasurableSet.iInter fun n => measurableSet_le ((hev n).comp measurable_snd)
        (measurable_const.mul ((hev n).comp
          (measurable_snd.comp (measurable_fst.comp measurable_fst))))
    have hB2 : MeasurableSet {t : (((ℝ × ℝ) × ContMetric) × ContMetric) × ContMetric |
        ∀ n, t.1.1.2.1 (p n) ≤ C ^ 2 * t.2.1 (p n)} := by
      have : {t : (((ℝ × ℝ) × ContMetric) × ContMetric) × ContMetric |
          ∀ n, t.1.1.2.1 (p n) ≤ C ^ 2 * t.2.1 (p n)} = ⋂ n, {t | t.1.1.2.1 (p n) ≤
            C ^ 2 * t.2.1 (p n)} := by ext; simp
      rw [this]
      exact MeasurableSet.iInter fun n => measurableSet_le
        ((hev n).comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))
        (measurable_const.mul ((hev n).comp measurable_snd))
    have hθ3 : Measurable fun t : (((ℝ × ℝ) × ContMetric) × ContMetric) × ContMetric => t.1.1.1 :=
      measurable_fst.comp (measurable_fst.comp measurable_fst)
    exact (measurable_snd hM).inter (hB1.inter (hB2.inter ((measurableSet_eq_fun
      (hY.comp (hθ3.prodMk measurable_snd)) ((hyS k).comp measurable_fst)).inter
      (measurableSet_eq_fun (hFm.comp measurable_snd)
        (hΦ.comp (hθ3.prodMk ((hyS k).comp measurable_fst)))))))
  -- the bad mass at `(θ, d)`
  set Kq : (t17Box ε R) → Kernel (((ℝ × ℝ) × ContMetric) × ContMetric) ContMetric := fun k =>
    K.comap (fun q => (q.1.1, yS k q)) ((measurable_fst.comp measurable_fst).prodMk (hyS k))
  have hKq : ∀ k, IsMarkovKernel (Kq k) := fun k => by simp only [Kq]; infer_instance
  have hbadq : ∀ k, Measurable fun q : ((ℝ × ℝ) × ContMetric) × ContMetric =>
      Kq k q (Prod.mk q ⁻¹' (T k)ᶜ) := fun k =>
    (Kq k).measurable_kernel_prodMk_left (hT k).compl
  set bad : (ℝ × ℝ) × ContMetric → ℝ≥0∞ := fun x =>
    ∑ k, ∫⁻ d', Kq k (x, d') (Prod.mk (x, d') ⁻¹' (T k)ᶜ) ∂ν with hbaddef
  have hbad : Measurable bad :=
    Finset.measurable_sum _ fun k _ => (hbadq k).lintegral_prod_right'
  -- for a.e. `θ`, `bad (θ, ·) = 0` `ν`-a.e. (`t17v_resample_kernel`)
  set Rel : ContMetric → ContMetric → Prop := fun d d'' => d'' ∈ M ∧
    (∀ n, d''.1 (p n) ≤ C ^ 2 * d.1 (p n)) ∧ (∀ n, d.1 (p n) ≤ C ^ 2 * d''.1 (p n))
  have hR : ∀ π : Measure (ContMetric × ContMetric), π.map Prod.fst = ν → π.map Prod.snd = ν →
      ∀ᵐ q ∂π, Rel q.1 q.2 := by
    intro π h1 h2
    have hl : ∀ᵐ q ∂π, q.2 ∈ M := ae_of_ae_map measurable_snd.aemeasurable (h2 ▸ hνM)
    have hb1 := t17e_bilip_measure hC hcopy h1 h2
    have hs1 : (π.map Prod.swap).map Prod.fst = ν := by
      rw [Measure.map_map measurable_fst measurable_swap]; exact h2
    have hs2 : (π.map Prod.swap).map Prod.snd = ν := by
      rw [Measure.map_map measurable_snd measurable_swap]; exact h1
    have hb2 := ae_of_ae_map measurable_swap.aemeasurable (t17e_bilip_measure hC hcopy hs1 hs2)
    filter_upwards [hl, hb1, hb2] with q hq1 hq2 hq3
    exact ⟨hq1, fun n => hq2 _ _, fun n => hq3 _ _⟩
  have hθd : ∀ᵐ θ ∂t17Λ, ∀ᵐ d ∂ν, bad (θ, d) = 0 := by
    filter_upwards [hslice, hΦF, t17Λ_ae hprod] with θ hs hf hp
    have hYθ : Measurable (t17Y ε θ (t17Box ε R)) := measurable_t17Y ε θ (t17Box ε R)
    have hΦθ : Measurable fun y : (t17Box ε R) → ℕ → ℝ≥0∞ => Φ (θ, y) :=
      hΦ.comp (measurable_const.prodMk measurable_id)
    have hFθ : F =ᵐ[ν] (fun y : (t17Box ε R) → ℕ → ℝ≥0∞ => Φ (θ, y)) ∘ t17Y ε θ (t17Box ε R) := hf
    have hex := t17v_resample_kernel (ι := (t17Box ε R)) (E := ℕ → ℝ≥0∞) ν (Y := t17Y ε θ (t17Box ε R)) hYθ hp
      (F := F) (Φ := fun y => Φ (θ, y)) hΦθ hFm hFθ
      (K.comap (fun y => (θ, y)) (measurable_const.prodMk measurable_id)) hs Rel hR
    filter_upwards [hex] with d hd
    refine Finset.sum_eq_zero fun k _ => ?_
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hd k] with d' hd'
    simp only [Pi.zero_apply]
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    simp only [Kq, Kernel.comap_apply] at hd' ⊢
    filter_upwards [hd'] with d'' ⟨⟨h1, h2, h3⟩, h4, h5⟩
    simp only [mem_preimage, mem_compl_iff, not_not, hTdef, hySdef, mem_ofPred_eq]
    exact ⟨h1, h2, h3, h4, h5⟩
  -- exchange the quantifiers
  have hG : MeasurableSet {x : (ℝ × ℝ) × ContMetric | bad (x.1, x.2) = 0} :=
    measurableSet_eq_fun hbad measurable_const
  have hswap := (Measure.ae_ae_comm (μ := t17Λ) (ν := ν)
    (p := fun θ d => bad (θ, d) = 0) hG).1 hθd
  filter_upwards [hswap, hνM] with d hdG hdM
  filter_upwards [hdG] with θ hθG b hb
  have hd := hML hdM
  unfold t17ES
  refine Finset.sum_le_sum fun k _ => ?_
  have hk : ∫⁻ d', Kq k ((θ, d), d') (Prod.mk ((θ, d), d') ⁻¹' (T k)ᶜ) ∂ν = 0 :=
    (Finset.sum_eq_zero_iff.1 hθG) k (Finset.mem_univ k)
  have hk' := (lintegral_eq_zero_iff ((hbadq k).comp (measurable_const.prodMk measurable_id))).1 hk
  have hint : ∀ᵐ d' ∂ν, ENNReal.ofReal (max (Φ (θ, Function.update (t17Y ε θ (t17Box ε R) d) k
      (t17Y ε θ (t17Box ε R) d' k)) - F d) 0 ^ 2) ≤ ENNReal.ofReal (b k) := by
    filter_upwards [hk'] with d' hd'
    have hae : ∀ᵐ d'' ∂K (θ, yS k ((θ, d), d')), (((θ, d), d'), d'') ∈ T k := by
      have := measure_eq_zero_iff_ae_notMem.1 hd'
      simp only [Kq, Kernel.comap_apply] at this
      filter_upwards [this] with d'' h
      simpa using h
    obtain ⟨d'', h1, h2, h3, h4, h5⟩ := @Filter.Eventually.exists _ _ _ (by infer_instance) hae
    refine ENNReal.ofReal_le_ofReal ?_
    have hΦe : Φ (θ, Function.update (t17Y ε θ (t17Box ε R) d) k (t17Y ε θ (t17Box ε R) d' k)) = F d'' := h5.symm
    rw [hΦe]
    refine hb k d'' ⟨hML h1, t17v_le_of_dense h2, t17v_le_of_dense h3, fun j hj hjk => ?_⟩
    have hjk' : (⟨j, hj⟩ : (t17Box ε R)) ≠ k := fun h => hjk (by rw [← h])
    have henc : t17eEnc (t17Square ε θ j) d'' = t17eEnc (t17Square ε θ j) d := by
      have := congrFun h4 ⟨j, hj⟩
      simp only [hySdef] at this
      rwa [Function.update_of_ne hjk'] at this
    exact t17v_internal_eq_of_enc hd (hML h1) (t17_isOpen_square ε θ j) henc
  calc ∫⁻ d', ENNReal.ofReal (max (Φ (θ, Function.update (t17Y ε θ (t17Box ε R) d) k
        (t17Y ε θ (t17Box ε R) d' k)) - F d) 0 ^ 2) ∂ν
      ≤ ∫⁻ _, ENNReal.ofReal (b k) ∂ν := lintegral_mono_ae hint
    _ = ENNReal.ofReal (b k) := by rw [lintegral_const, measure_univ, mul_one]

end LQGMetric.LM
