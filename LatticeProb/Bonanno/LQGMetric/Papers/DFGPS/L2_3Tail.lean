/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_3Tail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGMetric.Gaussian.SupTailField
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueFinite

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.3, part 1: Gaussian tails of the circle-average process on dyadic blocks

Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage percolation*
(arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Lemma 2.3 (`lem-gff-tail`),
T:751–781. Let `H` be a jointly continuous version of the circle-average process
`(r, z) ↦ h_r(z)` of a whole-plane GFF `h` (DS arXiv:0808.1560 Prop. 3.1; here
`CircleAvg.exists_continuous_version_circleAvg`).

* `blk_tail` (T:757–768, (eqn-gff-sup0)/(eqn-gff-sup-k)): for each `k`, the field
  `(r, z) ↦ H(2^k r, z) − H(2^k, 0)`, `r ∈ [1/2, 1]`, `|z| ≤ R`, satisfies
  `P(sup |·| ≥ M + u) ≤ 2 exp(−u²/(2σ²))` with `M`, `σ` depending only on `R`.
  The paper gets the `k`-uniformity from the scale invariance of the law of `h` modulo additive
  constants and the bound from Borell–TIS (AT Thm 2.1.1); we use Borell–TIS
  (`SupTail.tail_iSup_abs_le`, Adler–Taylor Thm 2.1.1) with the chaining bound for `E sup`
  (`SupTail.integral_iSup_family_le`) and check the `k`-uniformity directly on the
  (scale-invariant) covariance bound `incCov_self_le` (DEVIATIONS: DEV-DFGPS-2, DEV-DFGPS-B2a).
  We also subtract `H(2^k, 0)` instead of `H(r, 0)` (so that the radial part is a single
  Gaussian per block; see `pt_tail`).
* `pt_tail` (T:779, "t ↦ h_{e^t}(0) is a standard Brownian motion"): `H(2^k, 0) − H(1, 0)` is
  centered Gaussian with variance `k log 2`, hence `P(|·| ≥ u) ≤ 2 exp(−u²/(2(k+1)))`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace LQGMetric.DFGPS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- `H` is a jointly continuous version of the circle-average process `(r, z) ↦ h_r(z)` of `h`
(continuous on `(0, ∞) × ℂ` for every `ω`, and `H r z = h_r(z)` a.s. for each `r > 0`, `z`). -/
structure IsCircleAvgVersion (h : Ω → DistC) (P : Measure Ω) (H : ℝ → ℂ → Ω → ℝ) : Prop where
  cont : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω) (Ioi 0 ×ˢ univ)
  ae_eq : ∀ r, 0 < r → ∀ z, (fun ω => H r z ω) =ᵐ[P] fun ω => circleAvg (h ω) r z

/-- A whole-plane GFF has a jointly continuous version of its circle-average process
(DS Prop. 3.1 / HMP Prop. 2.1; `CircleAvg.exists_continuous_version_circleAvg`). -/
theorem exists_isCircleAvgVersion (hh : IsWholePlaneGFF h P) :
    ∃ H : ℝ → ℂ → Ω → ℝ, IsCircleAvgVersion h P H := by
  obtain ⟨H, hc, he⟩ := CircleAvg.exists_continuous_version_circleAvg hh
  refine ⟨fun r z ω => H r z ω + circleAvg (h ω) 1 0,
    ⟨fun ω => (hc ω).add continuousOn_const, fun r hr z => ?_⟩⟩
  filter_upwards [he r hr z] with ω hω
  simp [hω]

variable {H : ℝ → ℂ → Ω → ℝ}

lemma IsCircleAvgVersion.sub_ae_eq (hH : IsCircleAvgVersion h P H) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) (z w : ℂ) :
    (fun ω => H r z ω - H s w ω) =ᵐ[P] CircleAvg.cInc h r z s w := by
  filter_upwards [hH.ae_eq r hr z, hH.ae_eq s hs w] with ω h1 h2
  simp [CircleAvg.cInc, h1, h2]

lemma IsCircleAvgVersion.integral_sub (hh : IsWholePlaneGFF h P)
    (hH : IsCircleAvgVersion h P H) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    ∫ ω, (H r z ω - H s w ω) ∂P = 0 := by
  rw [integral_congr_ae (hH.sub_ae_eq hr hs z w)]
  exact CircleAvg.integral_cInc hh hr hs z w

lemma IsCircleAvgVersion.variance_sub (hh : IsWholePlaneGFF h P)
    (hH : IsCircleAvgVersion h P H) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    Var[fun ω => H r z ω - H s w ω; P] ≤ 2 * ((|r - s| + ‖z - w‖) / min r s) := by
  rw [variance_congr (hH.sub_ae_eq hr hs z w), (CircleAvg.map_cInc hh hr hs z w).2]
  exact CircleAvg.incCov_self_le hr hs z w

lemma IsCircleAvgVersion.integral_sq_sub (hh : IsWholePlaneGFF h P)
    (hH : IsCircleAvgVersion h P H) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    ∫ ω, (H r z ω - H s w ω) ^ 2 ∂P ≤ 2 * ((|r - s| + ‖z - w‖) / min r s) := by
  have hm : AEMeasurable (fun ω => H r z ω - H s w ω) P :=
    (CircleAvg.measurable_cInc hh r z s w).aemeasurable.congr (hH.sub_ae_eq hr hs z w).symm
  rw [← variance_of_integral_eq_zero hm (hH.integral_sub hh hr hs z w)]
  exact hH.variance_sub hh hr hs z w

lemma IsCircleAvgVersion.isGaussianProcess {T : Type*} (hh : IsWholePlaneGFF h P)
    (hH : IsCircleAvgVersion h P H) (f : T → CircleAvg.IncIdx) :
    IsGaussianProcess (fun t ω => H (f t).1.1 (f t).1.2 ω - H (f t).2.1 (f t).2.2 ω) P :=
  ((CircleAvg.isGaussianProcess_incProc hh).comp_right f).congr fun t =>
    (hH.sub_ae_eq (f t).1.1.2 (f t).2.1.2 _ _).symm

/-! ## The block field -/

/-- the parameter block `[1/2, 1] × B̄_R(0)` -/
abbrev BlkIdx (R : NNReal) : Type := {p : ℝ × ℂ // p ∈ Icc (1 / 2 : ℝ) 1 ×ˢ closedBall (0 : ℂ) R}

instance (R : NNReal) : CompactSpace (BlkIdx R) :=
  isCompact_iff_compactSpace.mp (isCompact_Icc.prod (isCompact_closedBall _ _))

instance (R : NNReal) : Nonempty (BlkIdx R) :=
  ⟨⟨(1, 0), ⟨by norm_num, by norm_num⟩, by simp⟩⟩

lemma BlkIdx.r_pos {R : NNReal} (t : BlkIdx R) : 0 < t.1.1 := by
  have := t.2.1.1; linarith

lemma BlkIdx.r_le {R : NNReal} (t : BlkIdx R) : t.1.1 ≤ 1 := t.2.1.2

lemma BlkIdx.half_le {R : NNReal} (t : BlkIdx R) : 1 / 2 ≤ t.1.1 := t.2.1.1

lemma BlkIdx.norm_le {R : NNReal} (t : BlkIdx R) : ‖t.1.2‖ ≤ R := by
  have := t.2.2; simpa using this

/-- the block field `(r, z) ↦ H(2^k r, z) − H(2^k, 0)` -/
def blk (H : ℝ → ℂ → Ω → ℝ) (k : ℕ) {R : NNReal} (t : BlkIdx R) (ω : Ω) : ℝ :=
  H (2 ^ k * t.1.1) t.1.2 ω - H (2 ^ k) 0 ω

/-- the index map of the block field into the increment process -/
def blkIdx (k : ℕ) {R : NNReal} (t : BlkIdx R) : CircleAvg.IncIdx :=
  ((⟨2 ^ k * t.1.1, mul_pos (by positivity) t.r_pos⟩, t.1.2), (⟨2 ^ k, mem_Ioi.2 (by positivity)⟩, 0))

variable (R : NNReal) (k : ℕ)

lemma blk_gaussian (hh : IsWholePlaneGFF h P) (hH : IsCircleAvgVersion h P H) :
    IsGaussianProcess (fun t : BlkIdx R => blk H k t) P :=
  hH.isGaussianProcess hh (blkIdx k)

lemma blk_centered (hh : IsWholePlaneGFF h P) (hH : IsCircleAvgVersion h P H) (t : BlkIdx R) :
    ∫ ω, blk H k t ω ∂P = 0 :=
  hH.integral_sub hh (mul_pos (by positivity) t.r_pos) (by positivity) _ _

lemma blk_cont (hH : IsCircleAvgVersion h P H) (ω : Ω) :
    Continuous fun t : BlkIdx R => blk H k t ω := by
  have hg : Continuous fun t : BlkIdx R => ((2 : ℝ) ^ k * t.1.1, t.1.2) :=
    (continuous_const.mul (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)
  exact ((hH.cont ω).comp_continuous hg fun t =>
    ⟨mul_pos (by positivity) t.r_pos, mem_univ _⟩).sub continuous_const

lemma two_pow_pos' : (0 : ℝ) < 2 ^ k := by positivity

lemma blk_var (hh : IsWholePlaneGFF h P) (hH : IsCircleAvgVersion h P H) (t : BlkIdx R) :
    Var[blk H k t; P] ≤ Real.sqrt (2 + 4 * R) ^ 2 := by
  rw [Real.sq_sqrt (by positivity)]
  have h2 := two_pow_pos' k
  have hr := t.r_pos; have hr1 := t.r_le; have hr2 := t.half_le; have hz := t.norm_le
  refine (hH.variance_sub hh (mul_pos h2 hr) h2 t.1.2 0).trans ?_
  rw [min_eq_left (by nlinarith), sub_zero, abs_of_nonpos (by nlinarith)]
  have hpos : 0 < 2 ^ k * t.1.1 := mul_pos h2 hr
  have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hR : (0 : ℝ) ≤ R := R.2
  have h3 : 1 / 2 ≤ 2 ^ k * t.1.1 := by nlinarith
  have : (-(2 ^ k * t.1.1 - 2 ^ k) + ‖t.1.2‖) / (2 ^ k * t.1.1) ≤ 1 + 2 * R := by
    rw [div_le_iff₀ hpos]; nlinarith [mul_le_mul_of_nonneg_left h3 hR]
  linarith

/-- the parameters `(r, Re z, Im z)` -/
def blkPar {R : NNReal} (t : BlkIdx R) : Fin 3 → ℝ := ![t.1.1, t.1.2.re, t.1.2.im]

lemma blkPar_diam (t t' : BlkIdx R) : ‖blkPar t - blkPar t'‖ ≤ 1 + 2 * R := by
  have hR : (0 : ℝ) ≤ R := R.2
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have hz := t.norm_le; have hz' := t'.norm_le
  have a1 := Complex.abs_re_le_norm t.1.2; have a2 := Complex.abs_re_le_norm t'.1.2
  have a3 := Complex.abs_im_le_norm t.1.2; have a4 := Complex.abs_im_le_norm t'.1.2
  have hr := t.half_le; have hr1 := t.r_le; have hr' := t'.half_le; have hr1' := t'.r_le
  have b1 := abs_le.1 a1; have b2 := abs_le.1 a2; have b3 := abs_le.1 a3; have b4 := abs_le.1 a4
  fin_cases i <;> simp only [blkPar, Pi.sub_apply, Real.norm_eq_abs, abs_le] <;>
    simp <;> constructor <;> linarith

lemma blk_incr (hh : IsWholePlaneGFF h P) (hH : IsCircleAvgVersion h P H) (t t' : BlkIdx R) :
    ∫ ω, (blk H k t ω - blk H k t' ω) ^ 2 ∂P ≤ 4 ^ 2 * ‖blkPar t - blkPar t'‖ := by
  have h2 := two_pow_pos' k
  have e : (fun ω => (blk H k t ω - blk H k t' ω) ^ 2) =
      fun ω => (H (2 ^ k * t.1.1) t.1.2 ω - H (2 ^ k * t'.1.1) t'.1.2 ω) ^ 2 := by
    funext ω; simp only [blk]; ring
  rw [e]
  refine (hH.integral_sq_sub hh (mul_pos h2 t.r_pos) (mul_pos h2 t'.r_pos) _ _).trans ?_
  have e0 : (blkPar t - blkPar t') 0 = t.1.1 - t'.1.1 := by simp [blkPar]
  have e1 : (blkPar t - blkPar t') 1 = t.1.2.re - t'.1.2.re := by simp [blkPar]
  have e2 : (blkPar t - blkPar t') 2 = t.1.2.im - t'.1.2.im := by simp [blkPar]
  have n0 := norm_le_pi_norm (blkPar t - blkPar t') 0
  have n1 := norm_le_pi_norm (blkPar t - blkPar t') 1
  have n2 := norm_le_pi_norm (blkPar t - blkPar t') 2
  rw [e0, Real.norm_eq_abs] at n0
  rw [e1, Real.norm_eq_abs] at n1
  rw [e2, Real.norm_eq_abs] at n2
  set n := ‖blkPar t - blkPar t'‖
  have hz : ‖t.1.2 - t'.1.2‖ ≤ 2 * n := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im]; linarith
  have hm : 2 ^ k / 2 ≤ min (2 ^ k * t.1.1) (2 ^ k * t'.1.1) := by
    have := t.half_le; have := t'.half_le
    exact le_min (by nlinarith) (by nlinarith)
  have hm0 : (0 : ℝ) < 2 ^ k / 2 := by positivity
  have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  rw [← mul_sub, abs_mul, abs_of_pos h2]
  have hnum : 0 ≤ 2 ^ k * |t.1.1 - t'.1.1| + ‖t.1.2 - t'.1.2‖ := by positivity
  calc 2 * ((2 ^ k * |t.1.1 - t'.1.1| + ‖t.1.2 - t'.1.2‖) / min (2 ^ k * t.1.1) (2 ^ k * t'.1.1))
      ≤ 2 * ((2 ^ k * |t.1.1 - t'.1.1| + ‖t.1.2 - t'.1.2‖) / (2 ^ k / 2)) := by
        gcongr
    _ ≤ 4 ^ 2 * n := by
        have hn : 0 ≤ n := norm_nonneg _
        have : (2 ^ k * |t.1.1 - t'.1.1| + ‖t.1.2 - t'.1.2‖) / (2 ^ k / 2) ≤ 6 * n := by
          rw [div_le_iff₀ hm0]; nlinarith
        linarith

/-- the uniform bound on `E sup` of the block field -/
def blkM (R : NNReal) : ℝ := 20 * Real.sqrt 5 * 4 * Real.sqrt ((3 + 1) * (1 + 2 * R))

lemma blk_esup (hh : IsWholePlaneGFF h P) (hH : IsCircleAvgVersion h P H) (s : ℝ)
    (hs : s = 1 ∨ s = -1) :
    Integrable (fun ω => ⨆ t : BlkIdx R, s * blk H k t ω) P ∧
      ∫ ω, (⨆ t : BlkIdx R, s * blk H k t ω) ∂P ≤ blkM R := by
  have hG : IsGaussianProcess (fun (t : BlkIdx R) ω => s * blk H k t ω) P := by
    simpa using (blk_gaussian R k hh hH).smul (fun _ => s)
  refine SupTail.integrable_iSup_of_continuous hG (fun ω => continuous_const.mul
    (blk_cont R k hH ω)) fun n t => ?_
  refine SupTail.integral_iSup_family_le hG (fun t => by
      rw [integral_const_mul, blk_centered R k hh hH, mul_zero]) (Nat.succ_pos n) t
    (blkPar (R := R)) (by norm_num) (fun i j => blkPar_diam R _ _) fun i j => ?_
  have e : (fun ω => (s * blk H k (t i) ω - s * blk H k (t j) ω) ^ 2) =
      fun ω => (blk H k (t i) ω - blk H k (t j) ω) ^ 2 := by
    funext ω
    rcases hs with rfl | rfl <;> ring
  rw [e]
  exact blk_incr R k hh hH _ _

/-- **Gaussian tail of the block supremum** (T:757–768). -/
theorem blk_tail (hh : IsWholePlaneGFF h P) (hH : IsCircleAvgVersion h P H) {u : ℝ}
    (hu : 0 ≤ u) :
    P.real {ω | blkM R + u ≤ ⨆ t : BlkIdx R, |blk H k t ω|} ≤
      2 * Real.exp (-u ^ 2 / (2 * Real.sqrt (2 + 4 * R) ^ 2)) := by
  obtain ⟨i1, e1⟩ := blk_esup R k hh hH 1 (Or.inl rfl)
  obtain ⟨i2, e2⟩ := blk_esup R k hh hH (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at i1 e1 i2 e2
  exact SupTail.tail_iSup_abs_le (blk_gaussian R k hh hH) (blk_centered R k hh hH)
    (blk_cont R k hH) i1 i2 e1 e2 (blk_var R k hh hH) hu

/-! ## The radial part at the centre -/

/-- **Gaussian tail of `H(2^k, 0) − H(1, 0)`** (variance `k log 2`; T:779). -/
theorem pt_tail (hh : IsWholePlaneGFF h P) (hH : IsCircleAvgVersion h P H) {u : ℝ}
    (hu : 0 ≤ u) :
    P.real {ω | u ≤ |H (2 ^ k) 0 ω - H 1 0 ω|} ≤
      2 * Real.exp (-u ^ 2 / (2 * Real.sqrt (k + 1) ^ 2)) := by
  have h2 := two_pow_pos' k
  set f : Unit → CircleAvg.IncIdx := fun _ => ((⟨2 ^ k, h2⟩, 0), (⟨1, mem_Ioi.2 one_pos⟩, 0))
  have hG : IsGaussianProcess (fun (_ : Unit) ω => H (2 ^ k) 0 ω - H 1 0 ω) P :=
    hH.isGaussianProcess hh f
  have h0 : ∀ t : Unit, ∫ ω, (H (2 ^ k) 0 ω - H 1 0 ω) ∂P = 0 := fun _ =>
    hH.integral_sub hh h2 one_pos _ _
  have hint : ∀ s : ℝ, Integrable (fun ω => ⨆ _ : Unit, s * (H (2 ^ k) 0 ω - H 1 0 ω)) P :=
    fun s => by
      simp only [ciSup_const]
      exact ((hG.hasGaussianLaw_eval ()).integrable).const_mul s
  have hvar : ∀ t : Unit, Var[fun ω => H (2 ^ k) 0 ω - H 1 0 ω; P] ≤ Real.sqrt (k + 1) ^ 2 := by
    intro _
    rw [Real.sq_sqrt (by positivity), variance_congr (hH.sub_ae_eq h2 one_pos 0 0),
      CircleAvg.variance_cInc_one hh h2 0, Real.log_pow, abs_of_nonneg (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have : (k : ℝ) * Real.log 2 ≤ k * 1 := by gcongr; linarith
    linarith
  have h := SupTail.tail_iSup_abs_le hG h0 (fun ω => continuous_const) (by simpa using hint 1)
    (by simpa using hint (-1)) (M := 0) (by simp only [ciSup_const]; rw [h0 ()])
    (by simp only [ciSup_const]; rw [integral_neg, h0 (), neg_zero])
    hvar hu
  simpa using h

end LQGMetric.DFGPS
