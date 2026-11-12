/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightE2Core
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC

/-!
# DFGPS Lemma 3.8 (task P2-DFA5, package DF-A5 of `blueprint/DF.md`, row 7)

DFGPS = Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage
percolation*, arXiv:1905.00380, `literature/src/1905.00380/lqg-metric-estimates-final.tex` ("T"),
Lemma 3.8 (`lem-infinite-dist`, T:1727–1731) and its proof (T:1732–1739):

"By tightness across scales, there exists `a > 0` such that for each `r > 0`,
`P[D_h(B_r(0), B_{2r}(0)) ≥ a 𝔠_r e^{ξh_r(0)}] ≥ 1/2`. By the locality of `D_h` and since
`⋂_r σ(h|_{ℂ∖B_r(0)})` is trivial, a.s. there are infinitely many `k` for which
`D_h(B_{2^k}, B_{2^{k+1}}) ≥ a 𝔠_{2^k} e^{ξh_{2^k}(0)}`. By Theorem 1.5, `𝔠_r = r^{ξQ+o_r(1)}`.
Since `t ↦ h_{e^t}(0)` is a standard linear Brownian motion, a.s. `𝔠_r e^{ξh_r(0)} → ∞`. …
Since `D_h` is a length metric, for `r ≥ 2^{k+1}` and `K ⊂ B_{2^k}(0)` compact,
`D_h(K, ∂B_r(0)) ≥ D_h(B_{2^k}(0), B_{2^{k+1}}(0))`. … any `D_h`-bounded subset of `ℂ` must be
contained in a Euclidean-bounded subset."

We follow this proof, with scales `8^j` and the annuli `𝔸_{8^j/4, 3·8^j/8}(0)` (the crossing
events of `GM.Tight.exists_crossing_event`, from the proved S2.4a = tightness across scales,
locality and Weyl scaling), and two substitutions (DEVIATIONS, proposed):
* **tail triviality (R5)** is replaced, as planned in `blueprint/DF.md` row 7, by LM Lemma 3.1
  (`Blueprint.LMLem3_1a`; Gwynne–Miller, *Local metrics of the GFF*, arXiv:1905.00379, Lemma 3.1 `lem-annulus-iterate`): for each `m` and
  `K`, applied to the radii `8^{m+K}/8^k`, it bounds the probability that none of the scales
  `8^m, …, 8^{m+K−1}` is good by `c e^{−K}`, so a.s. infinitely many scales are good
  (`ae_frequently_crossing`); no inversion is needed;
* **Brownian motion** is replaced by the Gaussian lower tail of `h_{8^n}(0) − h_1(0)` (variance
  `n log 8`, `GM.Tight.prob_exists_circleAvg_inc_le`) and Borel–Cantelli, which gives
  `𝔠_{8^n} e^{ξh_{8^n}(0)} → ∞` along the scales `8^n` (all that the proof uses).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DFGPS
namespace L38

open Blueprint GM.Tight

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

/-- `setDist` as an infimum (same proof as `GM.setDist_eq_iInf`, GM/S3/GoodAnnulusMeas). -/
lemma setDist_eq_iInf' (D : ContMetric) (A B : Set ℂ) :
    setDist D A B = ⨅ x ∈ A, ⨅ y ∈ B, ENNReal.ofReal (D.1 (x, y)) := by
  rw [setDist, MetricGeometry.setEDist_eq_iInf, iInf_image]
  refine iInf_congr fun x => iInf_congr fun _ => ?_
  rw [iInf_image]
  exact iInf_congr fun y => iInf_congr fun _ => ContMetric.edist_pt D x y

/-- **Borel–Cantelli for the circle averages**: for `a > 0`, a.s. eventually in `n`,
`h_{8^n}(0) − h_1(0) > −a n`. -/
theorem ae_eventually_circleAvg_good {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      -(a * n) < circleAvg (h ω) (8 ^ n * 1) 0 - circleAvg (h ω) 1 0 := by
  set q := Real.exp (-(a ^ 2) / (2 * Real.log 8)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    have : 0 < Real.log 8 := Real.log_pos (by norm_num)
    have : 0 < a ^ 2 := by positivity
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  set B : ℕ → Set Ω := fun n =>
    {ω | ∃ k ∈ Finset.Ico n (n + 1),
      circleAvg (h ω) (8 ^ k * 1) 0 - circleAvg (h ω) 1 0 ≤ -(a * k)} with hB
  have hPB : ∀ n, P (B n) ≤ ENNReal.ofReal (q ^ n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [pow_zero, ENNReal.ofReal_one]; exact prob_le_one
    refine (prob_exists_circleAvg_inc_le hh one_pos 0 ha.le hn (n + 1)).trans (le_of_eq ?_)
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, hq, ← Real.exp_nat_mul]
    congr 2; ring
  have hsum : (∑' n, P (B n)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hPB)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg hq0 n)
      (summable_geometric_of_lt_one hq0 hq1)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  by_contra hc
  push Not at hc
  exact hn ⟨n, Finset.mem_Ico.2 ⟨le_rfl, Nat.lt_succ_self n⟩, hc⟩

/-- **Infinitely many good scales** (T:1734, with LM Lemma 3.1 in place of tail triviality):
for events `E ρ` of `σ((h − h_ρ(0))|_{𝔸_{ρ/8, ρ/2}(0)})` with `P[E ρ] ≥ p` (LM's `p` for
`a = 1`, `b = 1/2`), a.s. `ω ∈ E (8^j)` for infinitely many `j`. -/
theorem ae_frequently_crossing (hL31 : LMLem3_1a) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsNormalizedWPGFF h P →
      ∀ E : {ρ : ℝ // 0 < ρ} → Set Ω,
      (∀ ρ, MeasurableSet[fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) ρ.1 0))
        (annulus 0 (1 / 8 * ρ.1) (1 / 2 * ρ.1))] (E ρ)) →
      (∀ ρ, ENNReal.ofReal p ≤ P (E ρ)) →
      ∀ᵐ ω ∂P, ∀ m : ℕ, ∃ j, m ≤ j ∧ ω ∈ E ⟨8 ^ j, by positivity⟩ := by
  obtain ⟨p, c₀, hp0, hp1, hc₀, hLM⟩ := hL31 (1 / 8) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) 1 one_pos (1 / 2) (by norm_num) (by norm_num)
  refine ⟨p, hp0, hp1, ?_⟩
  intro Ω _ P _ h hh E hEm hEp
  rw [ae_all_iff]
  intro m
  set S : Set Ω := {ω | ∀ j, m ≤ j → ω ∉ E ⟨8 ^ j, by positivity⟩} with hS
  have hbound : ∀ K : ℕ, 1 ≤ K → P S ≤ ENNReal.ofReal (c₀ * Real.exp (-1 * K)) := by
    intro K hK
    set rr : ℕ → ℝ := fun k => 8 ^ (m + K) / 8 ^ k with hrrdef
    have hrr : ∀ k, 0 < rr k := fun k => by positivity
    set E' : ℕ → Set Ω := fun k => E ⟨rr k, hrr k⟩ with hE'
    have hAI : AnnulusIterHyp h (1 / 8) (1 / 2) rr E' := by
      refine ⟨hrr, fun a b hab => ?_, fun k => le_of_eq ?_, fun k => hEm ⟨rr k, hrr k⟩⟩
      · show 8 ^ (m + K) / 8 ^ b ≤ (8 : ℝ) ^ (m + K) / 8 ^ a
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_right₀ (by norm_num) hab)
      · show (8 : ℝ) ^ (m + K) / 8 ^ (k + 1) / (8 ^ (m + K) / 8 ^ k) = 1 / 8
        have h8 : (8 : ℝ) ^ k ≠ 0 := by positivity
        rw [pow_succ]
        field_simp
    refine (measure_mono ?_).trans (hLM P h hh rr E' hAI (fun k => hEp _) K)
    intro ω hω
    have h0 : countOcc E' K ω = 0 := by
      classical
      unfold countOcc
      refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun k hk hkE => ?_)
      have hk := Finset.mem_Icc.1 hk
      have e : rr k = 8 ^ (m + K - k) := by
        show (8 : ℝ) ^ (m + K) / 8 ^ k = 8 ^ (m + K - k)
        rw [pow_sub₀ (8 : ℝ) (by norm_num) (by omega)]; ring
      have : E' k = E ⟨8 ^ (m + K - k), by positivity⟩ := by
        show E ⟨rr k, hrr k⟩ = _
        exact congrArg E (Subtype.ext e)
      rw [this] at hkE
      exact hω (m + K - k) (by omega) hkE
    show (countOcc E' K ω : ℝ) < 1 / 2 * K
    rw [h0]
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    push_cast; linarith
  have hT : Tendsto (fun K : ℕ => ENNReal.ofReal (c₀ * Real.exp (-1 * (K : ℝ)))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul c₀
    simpa [Function.comp_def, neg_one_mul] using this
  have hS0 : P S = 0 :=
    le_antisymm (ge_of_tendsto hT (eventually_atTop.2 ⟨1, hbound⟩)) bot_le
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hS0] with ω hω
  by_contra hc
  push Not at hc
  exact hω hc

/-- **Core of DFGPS Lemma 3.8** (T:1732–1737): a.s., for every `N` and `R` there is `ρ ≥ R`
with `D_h(x, y) ≥ N` whenever `|x| ≤ ρ` and `|y| ≥ 3ρ/2` (`ρ = 8^j/4` for a good scale `j`). -/
theorem ae_far_crossing (hT15 : DFGPSScaling) (hL31 : LMLem3_1a) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWPGFF h P) :
    ∀ᵐ ω ∂P, ∀ N R : ℝ, ∃ ρ : ℝ, R ≤ ρ ∧ ∀ x y : ℂ, ‖x‖ ≤ ρ → 3 / 2 * ρ ≤ ‖y‖ →
      N ≤ (D (h ω)).1 (x, y) := by
  set ξ := xiGamma γ with hξdef
  have hξ : 0 < ξ := GM.xiGamma_pos hγ0
  have hQ : 0 < Q γ := by unfold Q; positivity
  set κ := ξ * Q γ / 2 with hκdef
  have hκ : 0 < κ := by positivity
  obtain ⟨δ₀, hδ₀, hscal⟩ := hT15 γ hγ0 hγ2 D c hD κ hκ
  obtain ⟨p, hp0, hp1, HA⟩ := ae_frequently_crossing hL31
  obtain ⟨s, hs, Hev⟩ := exists_crossing_event hD (ε := ENNReal.ofReal (1 - p))
    (ENNReal.ofReal_pos.2 (by linarith))
  have hwp := hh.1
  choose E hEm hEc hEae using fun ρ : {ρ : ℝ // 0 < ρ} => Hev P h hwp ρ.1 ρ.2
  have hEp : ∀ ρ, ENNReal.ofReal p ≤ P (E ρ) := fun ρ => by
    have h1 : (1 : ℝ≥0∞) ≤ P (E ρ) + P (E ρ)ᶜ := by
      rw [← measure_univ (μ := P)]
      exact (measure_mono (union_compl_self (E ρ)).symm.subset).trans (measure_union_le _ _)
    have h2 : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
      rw [← ENNReal.ofReal_add hp0.le (by linarith)]; simp
    rw [← h2] at h1
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1
      (h1.trans (add_le_add le_rfl (hEc ρ).le))
  set L := Real.log 8 with hLdef
  have hL : 0 < L := Real.log_pos (by norm_num)
  set aG := κ * L / (2 * ξ) with haG
  have haG0 : 0 < aG := by positivity
  have hc1 : 0 < c 1 := hD.tightness.1 1 one_pos
  obtain ⟨m₁, hm₁⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num)).eventually (gt_mem_nhds hδ₀)).exists_forall_of_atTop
  have hEall : ∀ᵐ ω ∂P, ∀ j : ℕ, ω ∈ E ⟨8 ^ j, by positivity⟩ →
      ∀ u ∈ sphere (0 : ℂ) (8 ^ j / 4), ∀ v ∈ sphere (0 : ℂ) (3 * 8 ^ j / 8),
        ENNReal.ofReal (s * c (8 ^ j) * Real.exp (ξ * circleAvg (h ω) (8 ^ j) 0)) ≤
          (D (h ω)).internal (annulus 0 (1 / 8 * 8 ^ j) (1 / 2 * 8 ^ j)) u v :=
    ae_all_iff.2 fun j => hEae ⟨8 ^ j, by positivity⟩
  filter_upwards [HA P h hh E hEm hEp, ae_eventually_circleAvg_good P h hwp haG0, hh.2,
    hD.length P h (isGFFPlusCont_of_wp hwp), hEall] with ω hfreq hgood hnorm hlen hcross
  intro N R
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hgood
  set S := max N 0 / c 1 with hSdef
  set m : ℕ := ⌈S / (s * (κ * L / 2))⌉₊ with hmdef
  have hmS : S < s * Real.exp (κ * L / 2 * m) := by
    have h1 : S / (s * (κ * L / 2)) ≤ m := Nat.le_ceil _
    have h2 : S ≤ s * (κ * L / 2) * m := by
      rw [div_le_iff₀ (by positivity)] at h1; linarith
    have h3 := Real.add_one_le_exp (κ * L / 2 * m)
    nlinarith
  obtain ⟨m₂, hm₂⟩ := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 8)).eventually
    (eventually_ge_atTop (4 * R)) |>.exists_forall_of_atTop
  obtain ⟨j, hj, hjE⟩ := hfreq (max (max m₁ (m + 1)) (max j₀ m₂))
  have hjm₁ : m₁ ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hj
  have hjm : m + 1 ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hj
  have hjj₀ : j₀ ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hj
  have hjm₂ : m₂ ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hj
  have h8j : (0 : ℝ) < 8 ^ j := by positivity
  refine ⟨8 ^ j / 4, by linarith [hm₂ j hjm₂], fun x y hx hy => ?_⟩
  have hU : {w : ℂ | 8 ^ j / 4 ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ 3 * 8 ^ j / 8} ⊆
      (annulus 0 (1 / 8 * 8 ^ j) (1 / 2 * 8 ^ j) : Set ℂ) := fun w hw => by
    show 1 / 8 * 8 ^ j < ‖w - 0‖ ∧ ‖w - 0‖ < 1 / 2 * (8 : ℝ) ^ j
    constructor <;> linarith [hw.1, hw.2]
  have hlow := le_of_forall_internal_crossing (y := y) hlen (by linarith) hU
    (by rw [sub_zero]; exact hx) (by rw [sub_zero]; linarith) (hcross j hjE)
  refine le_trans ?_ hlow
  -- DFGPS Theorem 1.5: `𝔠_1 ≤ 8^{−jκ} 𝔠_{8^j}`
  set δ : ℝ := ((8 : ℝ) ^ j)⁻¹ with hδdef
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < δ₀ := by
    have := hm₁ j hjm₁
    rwa [one_div, inv_pow] at this
  have hsc := (hscal δ ⟨hδpos, hδlt⟩ (8 ^ j) h8j).2
  have hδr : δ * 8 ^ j = 1 := by rw [hδdef]; field_simp
  rw [hδr, show ξ * Q γ - κ = κ by rw [hκdef]; ring, div_le_iff₀ (hD.tightness.1 _ h8j),
    Real.rpow_def_of_pos hδpos, hδdef, Real.log_inv, Real.log_pow] at hsc
  have hg := hj₀ j hjj₀
  rw [mul_one] at hg
  have key := final_ineq_S24e (j := (j : ℝ)) (m := (m : ℝ)) hs hc1 hξ (by positivity)
    (by exact_mod_cast (Nat.le_succ m).trans hjm) (by rw [← hLdef] at hsc; convert hsc using 3)
    (by rw [haG] at hg; exact hg) hmS
  rw [hnorm, mul_zero, Real.exp_zero, mul_one, hSdef, div_mul_cancel₀ _ hc1.ne'] at key
  exact (le_max_left N 0).trans key.le

end L38

open Blueprint L38 in
/-- **DFGPS Lemma 3.8** (`lem-infinite-dist`, T:1727–1739), from DFGPS Theorem 1.5
(`Blueprint.DFGPSScaling`) and LM Lemma 3.1 (`Blueprint.LMLem3_1a`): a.s. `D_h(K, ∂B_r(0)) → ∞`
for every compact `K`, and every closed `D_h`-bounded set is compact. -/
theorem dfgpsLem3_8_of (hT15 : DFGPSScaling) (hL31 : LMLem3_1a) : DFGPSLem3_8 := by
  intro γ hγ0 hγ2 D c hD Ω _ P _ h hh
  filter_upwards [ae_far_crossing hT15 hL31 hγ0 hγ2 hD P h hh] with ω H
  refine ⟨fun K hK => ?_, fun A hA ⟨M, hM⟩ => ?_⟩
  · rw [ENNReal.tendsto_nhds_top_iff_nat]
    intro n
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨ρ, hRρ, hρ⟩ := H (n + 1) R
    refine eventually_atTop.2 ⟨3 / 2 * ρ, fun r hr => ?_⟩
    rw [setDist_eq_iInf']
    refine lt_of_lt_of_le (b := ENNReal.ofReal (n + 1)) ?_
      (le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal (hρ x y ?_ ?_))
    · rw [← ENNReal.ofReal_natCast]
      exact (ENNReal.ofReal_lt_ofReal_iff' ).2 ⟨by linarith, by positivity⟩
    · have := hR hx
      rw [mem_closedBall, dist_zero_right] at this
      linarith
    · rw [mem_sphere, dist_zero_right] at hy
      rw [hy]; exact hr
  · rcases A.eq_empty_or_nonempty with hA0 | ⟨u₀, hu₀⟩
    · rw [hA0]; exact isCompact_empty
    obtain ⟨ρ, hRρ, hρ⟩ := H (M + 1) ‖u₀‖
    refine Metric.isCompact_of_isClosed_isBounded hA
      ((isBounded_closedBall (x := (0 : ℂ)) (r := 3 / 2 * ρ)).subset fun u hu => ?_)
    rw [mem_closedBall, dist_zero_right]
    by_contra hc
    push Not at hc
    have := hρ u₀ u hRρ hc.le
    linarith [hM u₀ hu₀ u hu]

end DFGPS
end LQGMetric
