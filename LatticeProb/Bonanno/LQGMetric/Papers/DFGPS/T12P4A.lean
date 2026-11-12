/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P4A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P3B
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20Conv
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Bdd
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_12Ae
import LatticeProb.Bonanno.LQGMetric.Metric.WeylMetric

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2: Weyl scaling for the glued metric `patchT` (P-3b, deterministic part)

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
Step 1 (T:1349–1356: Weyl scaling of the limit from Lemma 2.12), Step 2 (T:1358–1374) and Step 3
(T:1376–1385: unbounded `f` by locality, "since D_h(·,·;O) is determined by h|_O"). Items 1–5 of
`handoff/P2-DFT12b.md` §3:

* `exists_subseq_ae_lfppC` — item 1: convergence in probability (`TendstoInProbLU`) gives a.s.
  locally uniform convergence along a subsequence (Borel–Cantelli on the squares `B̄_{m+1}²`).
* `mollify_close_addFun`, `eventually_mollify_close` — item 2: the GFF case of Lemma 2.1
  (eqn-localized-approx) transfers to `g + f` for bounded continuous `f` (T:735–738, as in
  `lem2_1_approx_of_gff`).
* `truncLim_addFun_eq_weyl`, `patchT_addFun_eq_weyl_bdd` — items 3–4 (deterministic): if the
  global LFPP of `g + f` converges to `e^{ξ f}·D` for every bounded `f`, then
  `truncLim W (g + f) = truncD W (e^{ξ f}·D)` and `patchT (g + f) = e^{ξ f}·D`.
* `truncLim_addFun_congr`, `patchT_addFun_eq_weyl` — item 5: all continuous `f` (Step 3).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open Blueprint MetricGeometry LFPP

/-! ### Item 1: a.s. convergence along a subsequence -/

/-- **convergence in probability ⇒ a.s. convergence along a subsequence** (Borel–Cantelli via
`exists_subseq_ae_tendsto_all`), for the rescaled global LFPP of a GFF plus a bounded continuous
function -/
theorem exists_subseq_ae_lfppC {ξ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hgff : IsGFFPlusBddCont h P)
    {Y : Ω → C(ℂ × ℂ, ℝ)} {εn : ℕ → ℝ} (hεp : ∀ n, 0 < εn n)
    (hT : TendstoInProbLU P (fun n ω => (aEpsDF ξ (εn n))⁻¹ • lfppDist ξ (εn n) (h ω)) atTop
      (fun ω => Y ω)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂P,
      (∀ R : ℝ, 0 < R → TendstoUniformlyOn
        (fun n p => (aEpsDF ξ (εn (ns n)))⁻¹ * lfppDist ξ (εn (ns n)) (h ω) p)
        (fun p => Y ω p) atTop (closedBall 0 R ×ˢ closedBall 0 R)) ∧
      Tendsto (fun n => lfppC ξ (εn (ns n)) (h ω)) atTop (𝓝 (Y ω)) := by
  let K : ℕ → Set (ℂ × ℂ) := fun m => L220.sqR ((m : ℝ) + 1)
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (heatMollify (εn n) (h ω)) :=
    ae_all_iff.2 fun n => (hgff.ae_tendstoLocallyUniformly_heatMollify _ (hεp n).ne').mono
      fun ω hω => hω.2
  have hval : ∀ ω, (∀ n, Continuous (heatMollify (εn n) (h ω))) → ∀ n p,
      lfppC ξ (εn n) (h ω) p = (aEpsDF ξ (εn n))⁻¹ * lfppDist ξ (εn n) (h ω) p := by
    intro ω hω n p
    rw [lfppC_apply_of_continuous (hω n) p]; rfl
  let f : ∀ m, ℕ → Ω → C(K m, ℝ) := fun m n ω => (lfppC ξ (εn n) (h ω)).restrict (K m)
  let g : ∀ m, Ω → C(K m, ℝ) := fun m ω => (Y ω).restrict (K m)
  have hTm : ∀ m, TendstoInMeasure P (f m) atTop (g m) := by
    intro m e he
    rcases eq_or_ne e ⊤ with rfl | htop
    · simp only [top_le_iff, edist_ne_top, ofPred_false, measure_empty, tendsto_const_nhds]
    have hδ : 0 < e.toReal := ENNReal.toReal_pos he.ne' htop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hT ((m : ℝ) + 1) (by positivity) e.toReal hδ) (fun _ => zero_le) fun n => measure_mono_ae ?_
    filter_upwards [hc] with ω hω hmem
    change e ≤ edist (f m n ω) (g m ω) at hmem
    rw [ENNReal.ofReal_toReal htop]
    refine hmem.trans ?_
    set S := ⨆ p ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) ×ˢ closedBall (0 : ℂ) ((m : ℝ) + 1),
      edist (((aEpsDF ξ (εn n))⁻¹ • lfppDist ξ (εn n) (h ω)) p) (Y ω p) with hS
    rcases eq_or_ne S ⊤ with hS' | hS'
    · rw [hS']; exact le_top
    rw [edist_dist, ← ENNReal.ofReal_toReal hS']
    refine ENNReal.ofReal_le_ofReal ((ContinuousMap.dist_le ENNReal.toReal_nonneg).2 fun p => ?_)
    have h1 : edist (((aEpsDF ξ (εn n))⁻¹ • lfppDist ξ (εn n) (h ω)) p.1) (Y ω p.1) ≤ S :=
      le_iSup₂ (f := fun p (_ : p ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) ×ˢ
        closedBall (0 : ℂ) ((m : ℝ) + 1)) =>
          edist (((aEpsDF ξ (εn n))⁻¹ • lfppDist ξ (εn n) (h ω)) p) (Y ω p)) p.1 p.2
    have h2 : f m n ω p = ((aEpsDF ξ (εn n))⁻¹ • lfppDist ξ (εn n) (h ω)) p.1 := by
      show lfppC ξ (εn n) (h ω) p.1 = _
      rw [hval ω hω n p.1]; rfl
    rw [dist_edist, h2]
    exact ENNReal.toReal_mono hS' h1
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_tendsto_all (μ := P) (ι := ℕ) hTm
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae, hc] with ω hω hcω
  have hU : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n p => lfppC ξ (εn (ns n)) (h ω) p)
      (fun p => Y ω p) atTop (closedBall 0 R ×ˢ closedBall 0 R) := by
    intro R _
    obtain ⟨m, hm⟩ := exists_nat_ge R
    have hsub : closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R ⊆ K m :=
      prod_mono (closedBall_subset_closedBall (by linarith))
        (closedBall_subset_closedBall (by linarith))
    refine (Metric.tendstoUniformlyOn_iff.2 fun η hη => ?_).mono hsub
    have := (tendsto_iff_dist_tendsto_zero.1 (hω m)).eventually (gt_mem_nhds hη)
    filter_upwards [this] with n hn p hp
    rw [dist_comm]
    exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist (f := f m (ns n) ω) (g := g m ω)
      ⟨p, hp⟩) hn
  refine ⟨fun R hR => (hU R hR).congr (Eventually.of_forall fun n p _ => ?_),
    tendsto_contMap_of_tendstoUniformlyOn_balls hU⟩
  exact hval ω hcω (ns n) p

/-! ### Item 2: Lemma 2.1 for `g + f` -/

/-- **(eqn-localized-approx) for `g + f`** (T:735–738, the argument of `lem2_1_approx_of_gff`):
the GFF form of Lemma 2.1 at a fixed field `g` transfers to `g + f` for bounded continuous `f` -/
theorem mollify_close_addFun {g : DistC} {U : Set ℂ} (f : C(ℂ, ℝ)) {M : ℝ} (hM : ∀ w, |f w| ≤ M)
    (hg : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∀ z ∈ closure U,
      (∃ L : ℝ, Tendsto (fun n : ℕ => g (heatTrunc (ε ^ 2 / 2) z n)) atTop (𝓝 L)) ∧
      |heatMollify ε g z - locMollify ε hε g z| ≤ δ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∀ z ∈ closure U,
      |heatMollify ε (addFun g f) z - locMollify ε hε (addFun g f) z| ≤ δ := by
  intro δ hδ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), M * (2 * Real.exp (-(1 / (8 * ε)))) ≤ δ / 2 := by
    have : Tendsto (fun ε : ℝ => M * (2 * Real.exp (-(1 / (8 * ε))))) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_exp_neg_inv_eight.const_mul 2).const_mul M
    exact this.eventually (ge_mem_nhds (by linarith))
  filter_upwards [hg (δ / 2) (by linarith), hsmall] with ε h1 h2 hε z hz
  obtain ⟨⟨L, hL⟩, hb⟩ := h1 hε z hz
  rw [addFun, heatMollify_add_ofCont _ f M hM hε z hL]
  have hloc : locMollify ε hε (g + ofCont f) z = locMollify ε hε g z + locMollify ε hε (ofCont f) z := by
    unfold locMollify; rfl
  rw [hloc]
  have hf := abs_heatMollify_sub_locMollify_ofCont_le f M hM ε hε z
  calc |heatMollify ε g z + heatMollify ε (ofCont f) z -
        (locMollify ε hε g z + locMollify ε hε (ofCont f) z)|
      = |(heatMollify ε g z - locMollify ε hε g z) +
          (heatMollify ε (ofCont f) z - locMollify ε hε (ofCont f) z)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hb (hf.trans h2)
    _ = δ := by ring

/-- the `𝓝[>] 0` form of Lemma 2.1 along a sequence `ε_k → 0` -/
theorem eventually_mollify_close {g : DistC} {U : Set ℂ} {εs : ℕ → ℝ} (hεs : ∀ k, 0 < εs k)
    (hε0 : Tendsto εs atTop (𝓝 0))
    (hg : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∀ z ∈ closure U,
      |heatMollify ε g z - locMollify ε hε g z| ≤ δ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop, ∀ z ∈ closure U,
      |locMollify (εs k) (hεs k) g z - heatMollify (εs k) g z| ≤ δ := by
  intro δ hδ
  have ht : Tendsto εs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε0, Eventually.of_forall hεs⟩
  filter_upwards [ht.eventually (hg δ hδ)] with k hk z hz
  rw [abs_sub_comm]
  exact hk (hεs k) z hz

/-! ### Items 3–4: bounded `f` (deterministic) -/

/-- `h*_ε` of `g + f` is continuous when the truncations of `g` converge locally uniformly -/
theorem continuous_heatMollify_addFun {ε : ℝ} (hε : 0 < ε) {g : DistC}
    (hg : TendstoLocallyUniformly (fun (n : ℕ) (z : ℂ) => g (heatTrunc (ε ^ 2 / 2) z n))
      (heatMollify ε g) atTop ∧ Continuous (heatMollify ε g))
    (f : C(ℂ, ℝ)) {M : ℝ} (hM : ∀ w, |f w| ≤ M) : Continuous (heatMollify ε (addFun g f)) := by
  rw [heatMollify_addFun hε.ne' (fun z => hg.1.tendsto_comp hg.2.continuousAt tendsto_const_nhds) f M hM]
  exact hg.2.add (continuous_heatMollify_ofCont f M hM ε hε.ne')

/-- **Items 2–3 (deterministic)**: if the LFPP of `g + f` converges to `e^{ξ f}·D` and Lemma 2.1
holds for `g` near `W̄`, then `truncLim W (g + f) = truncD W (e^{ξ f}·D)` -/
theorem truncLim_addFun_eq_weyl {ξ : ℝ} {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}
    (hε0 : Tendsto εs atTop (𝓝 0)) {g : DistC} {D : ContMetric} (hD : D.IsLength)
    (hcont : ∀ k, TendstoLocallyUniformly
      (fun (n : ℕ) (z : ℂ) => g (heatTrunc (εs k ^ 2 / 2) z n)) (heatMollify (εs k) g) atTop ∧
      Continuous (heatMollify (εs k) g))
    (f : C(ℂ, ℝ)) {M : ℝ} (hM : ∀ w, |f w| ≤ M)
    (hA : Tendsto (fun k => lfppC ξ (εs k) (addFun g f)) atTop (𝓝 (weylMetric ξ f D hD).1))
    (W : dyadicDomainsC) {U : Set ℂ} (hWU : closure (W : Set ℂ) ⊆ closure U)
    (hg : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∀ z ∈ closure U,
      (∃ L : ℝ, Tendsto (fun n : ℕ => g (heatTrunc (ε ^ 2 / 2) z n)) atTop (𝓝 L)) ∧
      |heatMollify ε g z - locMollify ε hε g z| ≤ δ) :
    truncLim ξ εs hεs W (addFun g f) = truncD W (weylMetric ξ f D hD).1 := by
  refine truncLim_eq_of_mollify W (fun k => continuous_heatMollify_addFun (hεs k) (hcont k) f hM)
    hA fun δ hδ => ?_
  filter_upwards [eventually_mollify_close hεs hε0 (mollify_close_addFun f hM hg) δ hδ] with k hk
    z hz
  exact hk z (hWU hz)

/-- a length-metric version of `patchT_eq` through the internal metrics on the squares -/
theorem patchT_eq_of_internal {ξ : ℝ} {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k} (D : ContMetric)
    (hD : D.IsLength) (g : DistC)
    (h : ∀ n z w, tChainInf (sqWd n) (truncLim ξ εs hεs (sqWd n) g) z w = D.internal (sqW n) z w) :
    patchT ξ εs hεs g = D := by
  have hF : ∀ p, patchF ξ εs hεs g p = D.1 p := fun p => by
    refine Tendsto.limUnder_eq ?_
    refine (tendsto_internal_sqW_toReal D hD p.1 p.2).congr fun n => ?_
    rw [h n]
  have e : (fun a => patchF ξ εs hεs g (Qd a)) = D.1 ∘ Qd := funext fun a => hF (Qd a)
  rw [patchT, e, contQ_comp, toContMetric_coe]

/-! ### Item 5: unbounded `f` (Step 3, T:1376–1385) -/

/-- `truncLim W (g + f)` depends only on `f` near `W̄` (eqn-localized-property) -/
theorem truncLim_addFun_congr {ξ : ℝ} {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}
    (hε0 : Tendsto εs atTop (𝓝 0)) (W : dyadicDomainsC) {g : DistC} {f f' : C(ℂ, ℝ)} {R : ℝ}
    (hWR : closure (W : Set ℂ) ⊆ closedBall 0 R) (hff : ∀ z ∈ ball (0 : ℂ) (R + 1), f z = f' z) :
    truncLim ξ εs hεs W (addFun g f) = truncLim ξ εs hεs W (addFun g f') := by
  unfold truncLim limUnder
  rw [Filter.map_congr (m₁ := fun k => truncW W (L217.locSqC ξ (εs k) (hεs k) (addFun g f)
    (closure W))) (m₂ := fun k => truncW W (L217.locSqC ξ (εs k) (hεs k) (addFun g f')
    (closure W))) ?_]
  filter_upwards [hε0.eventually (gt_mem_nhds one_pos)] with k hk
  congr 1
  have hEq : EqOn (L217.locMollifyC (εs k) (hεs k) (addFun g f))
      (L217.locMollifyC (εs k) (hεs k) (addFun g f')) (closure (W : Set ℂ)) := by
    intro z hz
    show (g + ofCont f) (locTest (εs k) (hεs k) z) = (g + ofCont f') (locTest (εs k) (hεs k) z)
    simp only [add_apply, ofCont_apply]
    congr 2
    funext x
    by_cases hx : x ∈ tsupport (locTest (εs k) (hεs k) z : ℂ → ℝ)
    · have hx' := tsupport_locTest_subset (εs k) (hεs k) z hx
      have hz' := hWR hz
      rw [mem_closedBall] at hx' hz'
      rw [dist_zero_right] at hz'
      have hs : Real.sqrt (εs k) < 1 := by
        rw [Real.sqrt_lt' one_pos]; simpa using hk
      rw [hff x (by
        rw [mem_ball, dist_zero_right]
        calc ‖x‖ ≤ ‖z‖ + dist x z := by
              rw [dist_eq_norm]; linarith [norm_sub_norm_le x z, norm_sub_rev x z]
          _ < R + 1 := by linarith)]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  unfold L217.locSqC unionMetricMap
  congr 1
  funext p
  rw [lfppDOn_congr hEq]

/-- **Item 5 (Step 3, T:1376–1385)**: Weyl scaling of `patchT` for every continuous `f`, from the
bounded case and locality (`truncLim_addFun_congr`): on `sqW n` replace `f` by a bounded
continuous `f̃` equal to `f` near `sqW n`; the internal metrics of `e^{ξ f̃}·D` and `e^{ξ f}·D` on
`sqW n` agree (`weylScaleOn_congr`). -/
theorem patchT_addFun_eq_weyl {ξ : ℝ} {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}
    (hε0 : Tendsto εs atTop (𝓝 0)) {g : DistC} {D : ContMetric} (hD : D.IsLength)
    (hB : ∀ f : C(ℂ, ℝ), (∃ M, ∀ w, |f w| ≤ M) → ∀ W : dyadicDomainsC,
      truncLim ξ εs hεs W (addFun g f) = truncD W (weylMetric ξ f D hD).1)
    (f : C(ℂ, ℝ)) : patchT ξ εs hεs (addFun g f) = weylMetric ξ f D hD := by
  refine patchT_eq_of_internal _ (weylMetric_isLength hD) _ fun n z w => ?_
  set W := sqWd n
  obtain ⟨R, hR⟩ := W.2.1.isBounded.closure.subset_closedBall (0 : ℂ)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (R + 1)).exists_bound_of_continuousOn
    f.continuous.continuousOn
  set C' := max C 0
  let f' : C(ℂ, ℝ) := ⟨fun z => max (-C') (min C' (f z)), by fun_prop⟩
  have hbd : ∀ w, |f' w| ≤ C' := fun w => by
    have h0 : 0 ≤ C' := le_max_right _ _
    refine abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hff : ∀ z ∈ ball (0 : ℂ) (R + 1), f z = f' z := fun z hz => by
    have h1 := hC z (ball_subset_closedBall hz)
    rw [Real.norm_eq_abs, abs_le] at h1
    have h2 : C ≤ C' := le_max_left _ _
    show f z = max (-C') (min C' (f z))
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  have hWb : (W : Set ℂ) ⊆ ball (0 : ℂ) (R + 1) := fun x hx => by
    have := hR (subset_closure hx)
    rw [mem_closedBall] at this; rw [mem_ball]; linarith
  have hWo : IsOpen (W : Set ℂ) := W.2.1.isOpen
  rw [truncLim_addFun_congr hε0 W hR hff, hB f' ⟨C', hbd⟩ W,
    ← internal_eq_tChainInf _ (weylMetric_isLength hD) W]
  show (weylMetric ξ f' D hD).internal (W : Set ℂ) z w = (weylMetric ξ f D hD).internal (W : Set ℂ) z w
  rw [weylMetric_internal hD hWo, weylMetric_internal hD hWo]
  exact weylScaleOn_congr fun x hx => by rw [← hff x (hWb hx)]

end LQGMetric.DFGPS.T12
