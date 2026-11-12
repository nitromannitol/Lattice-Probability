/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GffFar at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8ProofTight
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8Lim
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1PolarJoint
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8: tightness for `ε` away from `0` (step (a1), the range `[ε₁, 1)`)

DFGPS T:872–898 states tightness of the laws of `𝔞_ε⁻¹ D^ε_h(·,·;S)` for all `ε ∈ (0,1)`; the
comparison argument (T:883–891) only controls `ε` below a random threshold. For `ε ∈ [ε₁, 1)`
the paper is silent; we use a direct argument (own, in the style of D-DDDF-13): a.s.
`(ε, z) ↦ g*_ε(z)` is continuous on `(0,∞) × ℂ` (`lem2_1HeatJoint`), hence bounded by a finite
random `M` on `[ε₁, 1] × B̄_{3R}(0)`; the straight segment gives
`D^ε_g(x, y; S) ≤ e^{|ξ| M} |x − y|`, so with `𝔞_ε ≥ c > 0` on `[ε₁,1)` the metrics are
`K`-Lipschitz for one a.s. finite `K`, and `isTightMeasureSet_of_le_mul` (with the deterministic
Euclidean distance) gives tightness.

* `farSup` : the supremum of `|g*_ε(z)|` over a dense sequence of `[ε₁, 1] × B̄_R(0)`;
* `abs_heatMollify_le_farSup` : the bound on the whole compact set (continuity);
* `lem2_8_tight_far` : tightness of `{law of 𝔞_ε⁻¹ D^ε_g(·,·;S) : ε ∈ [ε₁, 1)}` given
  `𝔞_ε ≥ c > 0` there.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

/-- the compact parameter set `[ε₁, 1] × B̄_R(0)` -/
def farSet (ε₁ R : ℝ) : Set (ℝ × ℂ) := Icc ε₁ 1 ×ˢ closedBall (0 : ℂ) R

open Classical in
/-- a dense sequence of `farSet ε₁ R` (junk if empty) -/
def farSeq (ε₁ R : ℝ) : ℕ → ℝ × ℂ :=
  if h : (farSet ε₁ R).Nonempty then
    have : Nonempty (farSet ε₁ R) := h.to_subtype
    fun n => ((TopologicalSpace.exists_dense_seq (farSet ε₁ R)).choose n : ℝ × ℂ)
  else fun _ => (1, 0)

lemma farSeq_mem {ε₁ R : ℝ} (h : (farSet ε₁ R).Nonempty) (n : ℕ) : farSeq ε₁ R n ∈ farSet ε₁ R := by
  unfold farSeq; rw [dite_eq_left_of_eq_true (eq_true h)]; exact Subtype.prop _

lemma denseRange_farSeq {ε₁ R : ℝ} (h : (farSet ε₁ R).Nonempty) :
    ∃ u : ℕ → farSet ε₁ R, DenseRange u ∧ ∀ n, (u n : ℝ × ℂ) = farSeq ε₁ R n := by
  have : Nonempty (farSet ε₁ R) := h.to_subtype
  refine ⟨(TopologicalSpace.exists_dense_seq (farSet ε₁ R)).choose,
    (TopologicalSpace.exists_dense_seq (farSet ε₁ R)).choose_spec, fun n => ?_⟩
  unfold farSeq; rw [dite_eq_left_of_eq_true (eq_true h)]

/-- `sup_n |g*_{ε_n}(z_n)|` over the dense sequence -/
def farSup (ε₁ R : ℝ) (g : DistC) : ℝ := ⨆ n : ℕ, |heatMollify (farSeq ε₁ R n).1 g (farSeq ε₁ R n).2|

lemma measurable_farSup (ε₁ R : ℝ) : Measurable (farSup ε₁ R) :=
  Measurable.iSup fun n => continuous_abs.measurable.comp (measurable_heatMollify_left _ _)

lemma isCompact_farSet (ε₁ R : ℝ) : IsCompact (farSet ε₁ R) :=
  isCompact_Icc.prod (isCompact_closedBall _ _)

/-- **The bound on the compact set**, for `(ε, z) ↦ g*_ε(z)` continuous on `(0,∞) × ℂ`. -/
lemma abs_heatMollify_le_farSup {ε₁ R : ℝ} (hε₁ : 0 < ε₁) {g : DistC}
    (hg : ContinuousOn (fun p : ℝ × ℂ => heatMollify p.1 g p.2) (Ioi 0 ×ˢ univ))
    {p : ℝ × ℂ} (hp : p ∈ farSet ε₁ R) : |heatMollify p.1 g p.2| ≤ farSup ε₁ R g := by
  have hsub : farSet ε₁ R ⊆ Ioi 0 ×ˢ univ := fun q hq =>
    ⟨lt_of_lt_of_le hε₁ hq.1.1, mem_univ _⟩
  have hc : ContinuousOn (fun q : ℝ × ℂ => |heatMollify q.1 g q.2|) (farSet ε₁ R) :=
    (hg.mono hsub).abs
  obtain ⟨B, hB⟩ := (isCompact_farSet ε₁ R).exists_bound_of_continuousOn hc
  have hbdd : BddAbove (range fun n : ℕ => |heatMollify (farSeq ε₁ R n).1 g (farSeq ε₁ R n).2|) :=
    ⟨B, by
      rintro _ ⟨n, rfl⟩
      have := hB _ (farSeq_mem ⟨p, hp⟩ n)
      rwa [Real.norm_eq_abs, abs_abs] at this⟩
  obtain ⟨u, hu, hue⟩ := denseRange_farSeq ⟨p, hp⟩
  have hcl : IsClosed {q : farSet ε₁ R | |heatMollify (q : ℝ × ℂ).1 g (q : ℝ × ℂ).2| ≤
      farSup ε₁ R g} :=
    isClosed_le (continuousOn_iff_continuous_domRestrict.1 hc) continuous_const
  have hall : ∀ q : farSet ε₁ R, |heatMollify (q : ℝ × ℂ).1 g (q : ℝ × ℂ).2| ≤ farSup ε₁ R g := by
    intro q
    have hq : q ∈ closure (range u) := by rw [hu.closure_range]; exact mem_univ _
    refine (hcl.closure_subset_iff.2 ?_) hq
    rintro _ ⟨n, rfl⟩
    show |heatMollify (u n : ℝ × ℂ).1 g (u n : ℝ × ℂ).2| ≤ farSup ε₁ R g
    rw [hue n]
    exact le_ciSup hbdd n
  exact hall ⟨p, hp⟩

lemma continuous_heatMollify_of_joint {g : DistC}
    (h : ContinuousOn (fun p : ℝ × ℂ => heatMollify p.1 g p.2) (Ioi 0 ×ˢ univ)) {ε : ℝ}
    (hε : 0 < ε) : Continuous (heatMollify ε g) := by
  have hf : Continuous fun z : ℂ => ((ε, z) : ℝ × ℂ) := continuous_const.prodMk continuous_id
  have := h.comp_continuous hf fun z => ⟨hε, mem_univ _⟩
  simp only [Function.comp_def] at this
  exact this

/-- the Euclidean distance on `S × S` -/
def distC (S : Set ℂ) : C(S × S, ℝ) := ⟨fun p => dist p.1 p.2, continuous_dist⟩

/-- **Segment bound**: `𝔞_ε⁻¹ D^ε_g(x,y;S) ≤ c⁻¹ e^{|ξ| M} |x − y|`. -/
lemma lfppSqC_le_far {ξ ε c M R : ℝ} {g : DistC} (hcont : Continuous (heatMollify ε g)) {a : ℂ}
    {s : ℝ} (hs : 0 < s) (hc0 : 0 < c) (hcε : c ≤ aEpsDF ξ ε)
    (hR : closedSq a s ⊆ closedBall (0 : ℂ) R)
    (hM : ∀ u ∈ closedBall (0 : ℂ) (3 * R), |heatMollify ε g u| ≤ M)
    (p : closedSq a s × closedSq a s) :
    lfppSqC ξ ε g (closedSq a s) p ≤ (c⁻¹ * Real.exp (|ξ| * M)) * distC _ p := by
  rw [lfppSqC_apply_of_continuous hcont hs]
  have hseg : lfppDOn ξ (heatMollify ε g) (closedSq a s) p.1 p.2 ≤
      ENNReal.ofReal (Real.exp (|ξ| * M) * ‖(p.2 : ℂ) - p.1‖) := by
    refine (lfppDOn_le_segCost (convex_closedSq a s) p.1.2 p.2.2).trans
      (segCost_le fun u hu => ?_)
    have hx' := mem_closedBall_zero_iff.1 (hR p.1.2)
    have hy' := mem_closedBall_zero_iff.1 (hR p.2.2)
    have hu' : u ∈ closedBall (0 : ℂ) (3 * R) := by
      rw [mem_closedBall_zero_iff]
      rw [mem_closedBall, dist_eq_norm] at hu
      calc ‖u‖ = ‖(p.1 : ℂ) + (u - p.1)‖ := by ring_nf
        _ ≤ ‖(p.1 : ℂ)‖ + ‖u - p.1‖ := norm_add_le _ _
        _ ≤ R + ‖(p.2 : ℂ) - p.1‖ := by linarith
        _ ≤ R + (‖(p.2 : ℂ)‖ + ‖(p.1 : ℂ)‖) := by linarith [norm_sub_le (p.2 : ℂ) p.1]
        _ ≤ 3 * R := by linarith
    refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM u hu') (abs_nonneg _)
  have h1 := ENNReal.toReal_le_of_le_ofReal (by positivity) hseg
  have h2 : (aEpsDF ξ ε)⁻¹ ≤ c⁻¹ := inv_anti₀ hc0 hcε
  have hd : distC (closedSq a s) p = ‖(p.2 : ℂ) - p.1‖ := by
    show dist p.1 p.2 = _
    rw [Subtype.dist_eq, dist_eq_norm, norm_sub_rev]
  rw [hd]
  calc (aEpsDF ξ ε)⁻¹ * (lfppDOn ξ (heatMollify ε g) (closedSq a s) p.1 p.2).toReal
      ≤ c⁻¹ * (lfppDOn ξ (heatMollify ε g) (closedSq a s) p.1 p.2).toReal :=
        mul_le_mul_of_nonneg_right h2 ENNReal.toReal_nonneg
    _ ≤ c⁻¹ * (Real.exp (|ξ| * M) * ‖(p.2 : ℂ) - p.1‖) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hc0.le)
    _ = _ := by ring

/-- **Tightness for `ε ∈ [ε₁, 1)`** (whole-plane GFF, any closed square), given `𝔞_ε ≥ c > 0`
on `[ε₁, 1)`. -/
theorem lem2_8_tight_far {γ : ℝ} {a : ℂ} {s : ℝ} (hs : 0 < s) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → DistC} (hg : IsWholePlaneGFF g P)
    {ε₁ c : ℝ} (hε₁ : 0 < ε₁) (hc : 0 < c) (h𝔞 : ∀ ε ∈ Ico ε₁ 1, c ≤ aEpsDF (xiGamma γ) ε) :
    IsTightMeasureSet {μ | ∃ ε ∈ Ico ε₁ 1,
      μ = P.map fun ω => lfppSqC (xiGamma γ) ε (g ω) (closedSq a s)} := by
  have : CompactSpace (closedSq a s) := isCompact_iff_compactSpace.1 (isCompact_closedSq a hs.le)
  have hne : (closedSq a s).Nonempty := ⟨a, le_rfl, by linarith, le_rfl, by linarith⟩
  have : ConnectedSpace (closedSq a s) :=
    isConnected_iff_connectedSpace.1 ((convex_closedSq a s).isConnected hne)
  have hR : closedSq a s ⊆ closedBall (0 : ℂ) (‖a‖ + 2 * s) := closedSq_subset_closedBall a hs.le
  have hJ := lem2_1HeatJoint P g hg
  have hK : Measurable fun ω =>
      c⁻¹ * Real.exp (|xiGamma γ| * farSup ε₁ (3 * (‖a‖ + 2 * s)) (g ω)) :=
    ((((measurable_farSup _ _).comp hg.measurable).const_mul _).exp).const_mul _
  have hcont : ∀ ε, 0 < ε → ∀ᵐ ω ∂P, Continuous (heatMollify ε (g ω)) := fun ε hε => by
    filter_upwards [hJ] with ω hω
    exact continuous_heatMollify_of_joint hω.2 hε
  have hA : IsTightMeasureSet {μ | ∃ ε ∈ Ico ε₁ 1,
      μ = P.map fun _ : Ω => distC (closedSq a s)} := by
    refine (isTightMeasureSet_singleton (μ := Measure.dirac (distC (closedSq a s)))).subset ?_
    rintro μ ⟨ε, -, rfl⟩
    simp [Measure.map_const]
  have hle : ∀ ε ∈ Ico ε₁ 1, ∀ᵐ ω ∂P, ∀ p,
      lfppSqC (xiGamma γ) ε (g ω) (closedSq a s) p ≤
        c⁻¹ * Real.exp (|xiGamma γ| * farSup ε₁ (3 * (‖a‖ + 2 * s)) (g ω)) *
          distC (closedSq a s) p := by
    intro ε hε
    filter_upwards [hJ] with ω hω p
    have hε0 : 0 < ε := hε₁.trans_le hε.1
    refine lfppSqC_le_far (continuous_heatMollify_of_joint hω.2 hε0) hs hc (h𝔞 ε hε) hR (fun u hu => ?_) p
    exact abs_heatMollify_le_farSup (p := (ε, u)) hε₁ hω.2 ⟨⟨hε.1, hε.2.le⟩, hu⟩
  exact isTightMeasureSet_of_le_mul (X := closedSq a s) (Ico ε₁ 1)
    (fun _ _ => distC (closedSq a s)) (fun ε ω => lfppSqC (xiGamma γ) ε (g ω) (closedSq a s))
    _ hK hA (fun _ _ => aemeasurable_const)
    (fun ε hε => aemeasurable_lfppSqC hg.measurable (hcont ε (hε₁.trans_le hε.1)) hs)
    (fun _ _ => ae_of_all _ fun ω x => dist_self x)
    (fun ε hε => (hcont ε (hε₁.trans_le hε.1)).mono fun ω hω =>
      (lfppSqC_mem_lenPmetSet hω hs).1.1) hle

end LQGMetric.DFGPS
