/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39H5
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas4
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9, packet J6 (part 1): a.s. finiteness of `σ^ε_{s,𝕣}` and `𝓕_t` trivial for `t ≤ 0`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`.

* `t39j6_rho_top_succ`, `t39j6_rho_top_mono`: `ρ^n_r(z) = ∞` stays `∞` (definition (3.13), C:1258);
* **`t39j6_rho_ae_ne_top`**: for `r > 0` and `z ∈ (r/4)ℤ²`, a.s. `ρ^n_r(z) < ∞` for every `n`.
  Source: CONF Lemma 3.5 (C:1276–1282, `CONFLem3_5At`) with `K = {0}`, `𝕫 = z`, `ε = 2^{-i}`,
  `𝕣' = 2^i r` (so `ε𝕣' = r` and `z ∈ (ε𝕣'/4)ℤ² ∩ B_{ε𝕣'}(z)`): `P[ρ^{⌊η log 2^i⌋}_r(z) = ∞] ≤ C₀ 4^{-i}`,
  and `ρ^n = ∞ ⇒ ρ^{n'} = ∞` for `n' ≥ n`. This is the a.s. finiteness CONF uses tacitly when it
  writes `σ^ε_{s,𝕣}` as a radius (C:1295) (D119 S5; own short argument from L3.5, no source spells it out);
* `t39j6_rho_ae_ne_top_dyadic`: the same simultaneously for all dyadic `ε = 2^{-j}` and all grid points;
* **`t39j6_confSigma_ne_top`** (deterministic): `𝓑^•_s` bounded and all `ρ` finite ⇒ `σ^ε_{s,𝕣} < ∞`
  (finitely many grid points in `B_{ε𝕣}(𝓑^•_s)`, so `R^ε_𝕣(𝓑^•_s) < ∞`; a bounded set lies in some `𝓑^•_{s'}`);
* **`t39j6_confSigma_ae_ne_top`**: a.s., `σ^{2^{-j}}_{s,𝕣} < ∞` for all `j` and all `s`;
* `t39j6_filledBallSigma_nonpos`: `𝓕_t` is trivial for `t ≤ 0` (`𝓑^•_s = ∅` for `s ≤ 0`), and
  **`t39j6_stop_nonneg`**: a filled-ball stopping time which is a.s. positive is surely `≥ 0`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace CONF

open Blueprint GM

section Rho
variable {Ω : Type} [MeasurableSpace Ω]

/-- `ρ^n = ∞ ⇒ ρ^{n+1} = ∞` -/
theorem t39j6_rho_top_succ (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (P : Measure Ω)
    (h : Ω → DistC) (p : CONFParams) (r : ℝ) (z : ℂ) (n : ℕ) (ω : Ω)
    (hn : confRho ξ cc D P h p r z n ω = ⊤) : confRho ξ cc D P h p r z (n + 1) ω = ⊤ := by
  simp only [confRho, hn]
  refine iInf_eq_top.2 fun k => iInf_eq_top.2 fun hk => ?_
  exfalso
  rw [ENNReal.mul_top (by norm_num)] at hk
  exact ENNReal.ofReal_ne_top (top_le_iff.1 hk)

theorem t39j6_rho_top_mono (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (P : Measure Ω)
    (h : Ω → DistC) (p : CONFParams) (r : ℝ) (z : ℂ) (ω : Ω) {n m : ℕ} (hnm : n ≤ m)
    (hn : confRho ξ cc D P h p r z n ω = ⊤) : confRho ξ cc D P h p r z m ω = ⊤ := by
  induction m, hnm using Nat.le_induction with
  | base => exact hn
  | succ m _ ih => exact t39j6_rho_top_succ ξ cc D P h p r z m ω ih

/-- `n ≤ ⌊η log 2^i⌋` for large `i` -/
theorem t39j6_confN_large (p : CONFParams) (hη : 0 < p.η) (n : ℕ) :
    ∀ᶠ i : ℕ in atTop, n ≤ confN p ((2 : ℝ)⁻¹ ^ i) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨i₀, hi₀⟩ := exists_nat_ge ((n : ℝ) / (p.η * Real.log 2))
  refine eventually_atTop.2 ⟨i₀, fun i hi => ?_⟩
  have e : Real.log ((2 : ℝ)⁻¹ ^ i)⁻¹ = i * Real.log 2 := by
    rw [inv_pow, inv_inv, Real.log_pow]
  unfold confN
  rw [e]
  refine Nat.le_floor ?_
  have h1 : (n : ℝ) ≤ p.η * Real.log 2 * i₀ := by
    rwa [div_le_iff₀ (mul_pos hη hl), mul_comm] at hi₀
  have h2 : (i₀ : ℝ) ≤ i := by exact_mod_cast hi
  nlinarith [mul_pos hη hl]

/-- **a.s. finiteness of `ρ^n_r(z)`** for `z ∈ (r/4)ℤ²`, from CONF Lemma 3.5 (C:1276) -/
theorem t39j6_rho_ae_ne_top {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ gridPts (r / 4)) :
    ∀ᵐ ω ∂P, ∀ n, confRho (xiGamma γ) c D P h p r z n ω ≠ ⊤ := by
  obtain ⟨C₀, ε₀, -, hε₀, HK⟩ := H35 {0} isCompact_singleton
  rw [ae_all_iff]
  intro n
  rw [ae_iff]
  simp only [ne_eq, not_not]
  set S := {ω | confRho (xiGamma γ) c D P h p r z n ω = ⊤}
  have hbound : ∀ᶠ i : ℕ in atTop, P S ≤ ENNReal.ofReal (C₀ * ((2 : ℝ)⁻¹ ^ i) ^ 2) := by
    have hsmall : ∀ᶠ i : ℕ in atTop, (2 : ℝ)⁻¹ ^ i < ε₀ :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
        (gt_mem_nhds hε₀)
    filter_upwards [hsmall, t39j6_confN_large p hη n] with i hi hNi
    have hεpos : 0 < (2 : ℝ)⁻¹ ^ i := by positivity
    have hR' : 0 < (2 : ℝ) ^ i * r := by positivity
    have hεR : (2 : ℝ)⁻¹ ^ i * ((2 : ℝ) ^ i * r) = r := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow, one_mul]
    have hP := HK P h hh z ((2 : ℝ) ^ i * r) hR' ((2 : ℝ)⁻¹ ^ i) ⟨hεpos, hi⟩
    rw [hεR] at hP
    refine (measure_mono fun ω hω => ?_).trans hP
    refine ⟨z, ⟨hz, ?_⟩, ?_⟩
    · rw [mem_thickening_iff]
      exact ⟨z, ⟨0, rfl, by simp⟩, by simpa using hr⟩
    · rw [t39j6_rho_top_mono _ _ _ _ _ _ _ _ ω hNi hω]
      exact ENNReal.ofReal_lt_top
  have hlim : Tendsto (fun i : ℕ => ENNReal.ofReal (C₀ * ((2 : ℝ)⁻¹ ^ i) ^ 2)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num)).pow 2).const_mul C₀
    simpa using this
  exact le_antisymm (ge_of_tendsto hlim hbound) zero_le

/-- the same for all dyadic `ε = 2^{-j}` (scale `ε𝕣`) and all grid points of `(ε𝕣/4)ℤ²` -/
theorem t39j6_rho_ae_ne_top_dyadic {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ ω ∂P, ∀ (j : ℕ), ∀ z ∈ gridPts ((2 : ℝ)⁻¹ ^ j * R / 4), ∀ n,
      confRho (xiGamma γ) c D P h p ((2 : ℝ)⁻¹ ^ j * R) z n ω ≠ ⊤ := by
  have H : ∀ᵐ ω ∂P, ∀ (j : ℕ) (a b : ℤ), ∀ n, confRho (xiGamma γ) c D P h p
      ((2 : ℝ)⁻¹ ^ j * R) ⟨a * ((2 : ℝ)⁻¹ ^ j * R / 4), b * ((2 : ℝ)⁻¹ ^ j * R / 4)⟩ n ω ≠ ⊤ := by
    rw [ae_all_iff]; intro j
    rw [ae_all_iff]; intro a
    rw [ae_all_iff]; intro b
    exact t39j6_rho_ae_ne_top H35 hη hh (by positivity) ⟨a, b, rfl⟩
  filter_upwards [H] with ω hω j z hz n
  obtain ⟨a, b, rfl⟩ := hz
  exact hω j a b n

end Rho

section Sigma
variable {Ω : Type} [MeasurableSpace Ω]

/-- a bounded set of `ℂ` lies in `𝓑_{s'}(z; d)` for some `s' > s` -/
theorem t39j6_bounded_subset_ballM (d : ContMetric) (z₀ : ℂ) (s : ℝ) {B : Set ℂ}
    (hB : Bornology.IsBounded B) : ∃ s' : ℝ, s < s' ∧ B ⊆ ballM d z₀ s' := by
  obtain ⟨M, hM⟩ := (hB.isCompact_closure.image_of_continuousOn
    ((d.1.continuous.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn)).isBounded.subset_closedBall 0
  refine ⟨max s M + 1, by linarith [le_max_left s M], fun x hx => ?_⟩
  have hx' : d.1 (z₀, x) ∈ closedBall (0 : ℝ) M := hM ⟨x, subset_closure hx, rfl⟩
  rw [mem_closedBall, Real.dist_eq, sub_zero] at hx'
  show d.1 (z₀, x) < max s M + 1
  linarith [le_abs_self (d.1 (z₀, x)), le_max_right s M]

/-- **`σ^ε_{s,𝕣} < ∞`** when `𝓑^•_s` is bounded and every `ρ` at scale `ε𝕣` is finite -/
theorem t39j6_confSigma_ne_top (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (P : Measure Ω)
    (h : Ω → DistC) (p : CONFParams) (z₀ : ℂ) {R ε s : ℝ} (hεR : 0 < ε * R) (ω : Ω)
    (hK : Bornology.IsBounded (filledBall (D (h ω)) z₀ s))
    (hρ : ∀ z ∈ gridPts (ε * R / 4), confRho ξ cc D P h p (ε * R) z (confN p ε) ω ≠ ⊤) :
    confSigma ξ cc D P h p z₀ R ε s ω ≠ ⊤ := by
  classical
  set K := filledBall (D (h ω)) z₀ s with hKdef
  obtain ⟨B, hB⟩ := (hK.thickening (δ := ε * R)).subset_ball z₀
  set T := gridPts (ε * R / 4) ∩ thickening (ε * R) K
  have hm : 0 < ε * R / 4 := by positivity
  have hT : T.Finite := by
    exact Set.Finite.subset ((gridBox (ε * R / 4) B z₀).finite_toSet.image
      (fun k : ℤ × ℤ => (⟨k.1 * (ε * R / 4), k.2 * (ε * R / 4)⟩ : ℂ)))
      fun w hw => grid_ball_subset hm z₀ ⟨hw.1, hB hw.2⟩
  have hsup : (⨆ z ∈ T, confRho ξ cc D P h p (ε * R) z (confN p ε) ω) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑ z ∈ hT.toFinset, confRho ξ cc D P h p (ε * R) z
      (confN p ε) ω) ?_ ?_
    · exact ENNReal.sum_ne_top.2 fun z hz => hρ z ((hT.mem_toFinset.1 hz).1)
    · exact iSup₂_le fun z hz => Finset.single_le_sum (f := fun z => confRho ξ cc D P h p (ε * R)
        z (confN p ε) ω) (fun _ _ => zero_le) (hT.mem_toFinset.2 hz)
  have hRK : confRK ξ cc D P h p R ε K ω ≠ ⊤ := by
    unfold confRK
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) hsup, ENNReal.ofReal_ne_top⟩
  set ρ := confRK ξ cc D P h p R ε K ω
  obtain ⟨B', hB'⟩ := hK.subset_ball z₀
  have hnb : Bornology.IsBounded (enbhd ρ K) := by
    refine (isBounded_ball (x := z₀) (r := B' + ρ.toReal)).subset fun x hx => ?_
    obtain ⟨y, hy, hxy⟩ := Metric.infEDist_lt_iff.1 hx
    have h1 : dist x y < ρ.toReal := by
      rw [edist_dist] at hxy
      exact (ENNReal.ofReal_lt_iff_lt_toReal dist_nonneg hRK).1 hxy
    have h2 := hB' hy
    rw [mem_ball] at h2 ⊢
    linarith [dist_triangle x y z₀]
  obtain ⟨s', hs', hsub⟩ := t39j6_bounded_subset_ballM (D (h ω)) z₀ s hnb
  have hsub' : enbhd ρ K ⊆ filledBall (D (h ω)) z₀ s' :=
    hsub.trans (subset_closure.trans subset_union_left)
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := s')) ?_
  exact iInf_le_of_le s' (iInf_le_of_le hs' (iInf_le_of_le hsub' le_rfl))

/-- **a.s., `σ^{2^{-j}}_{s,𝕣} < ∞` for every `j` and every `s`** (CONF (3.17), C:1295) -/
theorem t39j6_confSigma_ae_ne_top (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {p : CONFParams}
    (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η) {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z₀ : ℂ) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ ω ∂P, ∀ (j : ℕ) (s : ℝ),
      confSigma (xiGamma γ) c D P h p z₀ R ((2 : ℝ)⁻¹ ^ j) s ω ≠ ⊤ := by
  filter_upwards [t39j6_rho_ae_ne_top_dyadic H35 hη hh hR, ae_mem_lenSet h38 hγ hγ2 hD P h hh]
    with ω hρ hlen j s
  exact t39j6_confSigma_ne_top _ _ D P h p z₀ (by positivity) ω
    (gm_filledBall_isBounded_of_lenSet hlen z₀ s) fun z hz => hρ j z hz _

end Sigma

section Trivial
variable {Ω : Type} [MeasurableSpace Ω]

/-- `𝓑^•_s(z; d) = ∅` for `s ≤ 0` -/
theorem t39j6_filledBall_nonpos (d : ContMetric) (z₀ : ℂ) {s : ℝ} (hs : s ≤ 0) :
    filledBall d z₀ s = ∅ := by
  have hb : ballM d z₀ s = ∅ := by
    ext x
    simp only [ballM, mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
    exact hs.trans (dist_nonneg (x := d.pt z₀) (y := d.pt x))
  simp only [filledBall, hb, closure_empty, empty_union, compl_empty, notMem_empty,
    not_false_eq_true, true_and, connectedComponentIn_univ]
  ext x
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
  exact fun hb' => NormedSpace.unbounded_univ ℝ ℂ
    (hb'.subset (isPreconnected_univ.subset_connectedComponent (mem_univ x)))

/-- the restriction of a distribution to an empty open set is `0` -/
theorem t39j6_restrictTo_empty (V : TopologicalSpace.Opens ℂ) (hV : (V : Set ℂ) = ∅)
    (d : DistC) : restrictTo V d = 0 := by
  refine ContinuousLinearMap.ext fun φ => ?_
  change d (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) φ) = 0
  have hφ : TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) φ = 0 := by
    refine TestFunction.ext fun x => ?_
    have h1 := congrFun (TestFunction.monoCLM_apply (𝕜 := ℝ) (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V)
      (Ω₂ := ⊤) φ) x
    rw [h1]
    split_ifs
    · rw [φ.zero_on_compl (by simp [hV] : x ∈ (V : Set ℂ)ᶜ)]; rfl
    · rfl
  rw [hφ, map_zero]

/-- `σ(∅, h|_∅) = ⊥` -/
theorem t39j6_localSigma_empty (h : Ω → DistC) : localSigma h (fun _ => ∅) = ⊥ := by
  classical
  refine le_antisymm ((iInf_le _ 0).trans (sup_le ?_ ?_)) bot_le
  · refine MeasurableSpace.generateFrom_le fun E ⟨U, _, hE⟩ => ?_
    have : E = ∅ := by rw [hE]; simp
    rw [this]; exact @MeasurableSet.empty Ω ⊥
  · refine MeasurableSpace.generateFrom_le fun E ⟨S, F, hF, hE⟩ => ?_
    by_cases hS : dyadicHull 0 (∅ : Set ℂ) = S
    · have hS' : S = ∅ := by rw [← hS]; simp [dyadicHull]
      subst hS'
      have hc : (fun ω => restrictTo (toOpens (interior (∅ : Set ℂ)) isOpen_interior) (h ω)) =
          fun _ => 0 := funext fun ω => t39j6_restrictTo_empty _ (by simp [toOpens]) _
      have hF' : MeasurableSet[⊥] F := by
        obtain ⟨T, -, rfl⟩ := hF
        rw [hc, Set.preimage_const]
        split_ifs
        · exact @MeasurableSet.univ Ω ⊥
        · exact @MeasurableSet.empty Ω ⊥
      have e : E = F := by rw [hE]; ext ω; simp [hS]
      rw [e]; exact hF'
    · have : E = ∅ := by
        rw [hE]; ext ω; simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false]
        exact fun h' => hS h'.1
      rw [this]; exact @MeasurableSet.empty Ω ⊥

/-- **`𝓕_t` is trivial for `t ≤ 0`** -/
theorem t39j6_filledBallSigma_nonpos (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) {t : ℝ}
    (ht : t ≤ 0) : filledBallSigma D h z₀ t = ⊥ := by
  refine le_antisymm (iSup₂_le fun s hs => ?_) bot_le
  have e : (fun ω => filledBall (D (h ω)) z₀ s) = fun _ => ∅ :=
    funext fun ω => t39j6_filledBall_nonpos _ z₀ (hs.trans ht)
  rw [e, t39j6_localSigma_empty]

/-- **a filled-ball stopping time with `τ > 0` a.s. is surely `≥ 0`** -/
theorem t39j6_stop_nonneg {D : DistC → ContMetric} {h : Ω → DistC} {z₀ : ℂ} {τ : Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P] (hτ : IsFilledBallStoppingTime D h z₀ τ)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) (ω : Ω) : 0 ≤ τ ω := by
  have hm : MeasurableSet[⊥] {ω | τ ω < 0} := by
    have := hτ 0
    rwa [t39j6_filledBallSigma_nonpos D h z₀ le_rfl] at this
  rcases (MeasurableSpace.measurableSet_bot_iff (α := Ω)).1 hm with he | hu
  · by_contra hn
    have : ω ∈ {ω | τ ω < 0} := lt_of_not_ge hn
    rw [he] at this; exact this
  · have h0 : P {ω | τ ω < 0} = 0 := by
      have := ae_iff.1 (hpos.mono fun ω hω => (not_lt.2 hω.le : ¬ τ ω < 0))
      simpa using this
    rw [hu, measure_univ] at h0
    exact absurd h0 one_ne_zero

end Trivial

end CONF
end LQGMetric
