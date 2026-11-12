/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11In1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3MuHat
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseLaw
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.MixedLocal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Open node 3 of P2-DG105g: the comparison tail is uniform in the white noise (P2-DG105l)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Lemma 3.11 (DG:1226):
"Combining this with (eqn-gff-compare) (applied with `A = c n^{1/2}`) … and taking a union bound
of `O_n(n²)` Euclidean balls". Here (eqn-gff-compare) (DG Lemma 3.1) is applied, after the
rescaling of DG:1243 ("the re-centered field … agrees in law with `ĥ^tr`"), to the field of the
rescaled white noise `W' = W ∘ U_{δ,c}` of each grid square. In the formalization the moduli
`hatMod`, `trMod` of `W'` are chosen modifications (`hatMod_spec`), whose tail constants a priori
depend on `W'`. We prove that the tail *probability itself* does not depend on the white noise
(DG: "agrees in law"):

* `map_wn_eq`: two white noises have the same law as processes on `WNSpace → ℝ`
  (Gaussian vectors with the same covariance, `QuantumZipper.WedgeRes.map_eq_of_gaussian_vec`,
  as in `WhiteNoise.map_phi_eq_of_cov`);
* `prob_sup_eq_of_circ`: if `Y`, `Y'` are continuous and their circle averages are a.s. a fixed
  measurable functional `Φ` of the white noise, then `P[¬ ∀ z ∈ K, |Y z| ≤ A]` is the same for
  both (the sup over `K` is a sup over a countable dense subset of `interior K`, and each value
  is the limit of the circle averages, `QuantumZipper.K3.tendsto_integral_circleUnif_zero`);
* **`hatMod_tail_uniform`, `trMod_tail_uniform`**: the tails of `hatMod hW'` and `trMod hW'`
  are bounded with the constants of `hatMod_spec hW`/`trMod_spec hW`, uniformly in `W'`;
* **`hatTr_tail_uniform`**: `P[max_K |hatMod' − trMod'| > A] ≤ c₀ e^{−c₁ A²}` uniformly in `W'`.

Own elementary glue (DG use the equality in law implicitly, DG:1243).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise QuantumZipper KilledHeat DZZ GMCIdent GMCIdent2 GMCIdent3 SupTail

/-- **Two white noises have the same law** as processes indexed by `WNSpace`. -/
theorem map_wn_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} {W : WNSpace → Ω → ℝ} {W' : WNSpace → Ω' → ℝ} (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P' W') :
    P.map (fun ω f => W f ω) = P'.map (fun ω f => W' f ω) := by
  have := hW.isProbabilityMeasure
  have := hW'.isProbabilityMeasure
  refine map_eq_of_forall_finset' (X := W) (X' := W')
    (measurable_pi_iff.mpr hW.measurable).aemeasurable
    (measurable_pi_iff.mpr hW'.measurable).aemeasurable fun I => ?_
  exact QuantumZipper.WedgeRes.map_eq_of_gaussian_vec (ι := I)
    (U := fun i => W i) (V := fun i => W' i)
    ((hW.isGaussianProcess_comp (fun f => f)).hasGaussianLaw I)
    ((hW'.isGaussianProcess_comp (fun f => f)).hasGaussianLaw I)
    (fun i => hW.measurable _) (fun i => hW'.measurable _)
    (fun i => (hW.hasLaw_single _).hasGaussianLaw.memLp_two)
    (fun i => (hW'.hasLaw_single _).hasGaussianLaw.memLp_two)
    (fun i => QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single _))
    (fun i => QuantumZipper.GFFExist.gs_integral_eq_zero (hW'.hasLaw_single _))
    (fun i j => by rw [hW.cov_eq, hW'.cov_eq])

/-- the countable test set: values of `Φ` along `r_{z,m} = ρ_z/(m+2)`, `z ∈ D` -/
def circTestSet (D : Set ℂ) (ρ : ℂ → ℝ) (Φ : ℂ → ℝ → (WNSpace → ℝ) → ℝ) (A : ℝ) :
    Set (WNSpace → ℝ) :=
  {w | ∀ z ∈ D, ∀ δ N : ℕ, ∃ m ≥ N, |Φ z (ρ z / (m + 2)) w| < A + 1 / (δ + 1)}

lemma measurableSet_circTestSet {D : Set ℂ} (hD : D.Countable) (ρ : ℂ → ℝ)
    {Φ : ℂ → ℝ → (WNSpace → ℝ) → ℝ} (hΦ : ∀ z r, Measurable (Φ z r)) (A : ℝ) :
    MeasurableSet (circTestSet D ρ Φ A) := by
  have e : circTestSet D ρ Φ A = ⋂ z ∈ D, ⋂ δ : ℕ, ⋂ N : ℕ, ⋃ m : ℕ, ⋃ (_ : m ≥ N),
      {w | |Φ z (ρ z / (m + 2)) w| < A + 1 / (δ + 1)} := by
    ext w; simp [circTestSet]
  rw [e]
  refine MeasurableSet.biInter hD fun z _ => MeasurableSet.iInter fun δ =>
    MeasurableSet.iInter fun N => MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_lt (continuous_abs.measurable.comp (hΦ _ _)) measurable_const

/-- deterministic core: for a continuous `g`, `sup_K |g| ≤ A` iff the circle averages along the
test radii pass the countable test -/
lemma forall_abs_le_iff_circ {K D : Set ℂ} (hDK : D ⊆ K) (hKD : K ⊆ closure D) {ρ : ℂ → ℝ}
    (hρ : ∀ z ∈ D, 0 < ρ z) {g : ℂ → ℝ} (hg : Continuous g) {A : ℝ}
    {a : ℂ → ℕ → ℝ} (ha : ∀ z ∈ D, ∀ m : ℕ, a z m = ∫ x, g x ∂(circleUnif z (ρ z / (m + 2)))) :
    (∀ z ∈ K, |g z| ≤ A) ↔ ∀ z ∈ D, ∀ δ N : ℕ, ∃ m ≥ N, |a z m| < A + 1 / (δ + 1) := by
  have hlim : ∀ z ∈ D, Tendsto (a z) atTop (𝓝 (g z)) := by
    intro z hz
    have hr : Tendsto (fun m : ℕ => ρ z / ((m : ℝ) + 2)) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => ?_⟩
      · exact tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      · exact div_pos (hρ z hz) (by positivity)
    have := (QuantumZipper.K3.tendsto_integral_circleUnif_zero hg z).comp hr
    exact this.congr fun m => (ha z hz m).symm
  have habs : ∀ z ∈ D, Tendsto (fun m => |a z m|) atTop (𝓝 |g z|) := fun z hz =>
    (hlim z hz).abs
  constructor
  · intro h z hz δ N
    have hlt : |g z| < A + 1 / (δ + 1) := by
      have := h z (hDK hz); have : (0 : ℝ) < 1 / (δ + 1) := by positivity
      linarith
    obtain ⟨M, hM⟩ := eventually_atTop.1 ((habs z hz).eventually (gt_mem_nhds hlt))
    exact ⟨max M N, le_max_right _ _, hM _ (le_max_left _ _)⟩
  · intro h
    have hD : ∀ z ∈ D, |g z| ≤ A := by
      intro z hz
      refine le_of_forall_pos_lt_add fun η hη => ?_
      obtain ⟨δ, hδ⟩ := exists_nat_one_div_lt hη
      by_contra hcon
      push Not at hcon
      have hlt : A + 1 / ((δ : ℝ) + 1) < |g z| := by linarith
      obtain ⟨M, hM⟩ := eventually_atTop.1 ((habs z hz).eventually (lt_mem_nhds hlt))
      obtain ⟨m, hm, hm'⟩ := h z hz δ M
      exact absurd (hM m hm) (not_lt.2 hm'.le)
    have hcl : IsClosed {z | |g z| ≤ A} := isClosed_le hg.abs continuous_const
    intro z hz
    exact (closure_minimal (fun x hx => hD x hx) hcl) (hKD hz)

/-- a.s. the bad event is the preimage of the complement of the countable test set -/
lemma ae_eq_preimage_circTestSet {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {W₀ : WNSpace → Ω₀ → ℝ} {K D : Set ℂ} (hDc : D.Countable) (hDK' : D ⊆ K)
    (hK' : K ⊆ closure D) {ρ : ℂ → ℝ} (hρ0 : ∀ z ∈ D, 0 < ρ z)
    (hr : ∀ z ∈ D, ∀ m : ℕ, 0 < ρ z / ((m : ℝ) + 2) ∧
      Metric.closedBall z (ρ z / ((m : ℝ) + 2)) ⊆ K)
    {Φ : ℂ → ℝ → (WNSpace → ℝ) → ℝ} (A : ℝ) {Y₀ : ℂ → Ω₀ → ℝ}
    (hc : ∀ ω, Continuous fun z => Y₀ z ω)
    (h : ∀ (z : ℂ) (r : ℝ), 0 < r → Metric.closedBall z r ⊆ K →
      (fun ω => ∫ x, Y₀ x ω ∂(circleUnif z r)) =ᵐ[P₀] fun ω => Φ z r (fun f => W₀ f ω)) :
    {ω | ¬ ∀ z ∈ K, |Y₀ z ω| ≤ A} =ᵐ[P₀] (fun ω f => W₀ f ω) ⁻¹' (circTestSet D ρ Φ A)ᶜ := by
  have hall : ∀ᵐ ω ∂P₀, ∀ z : D, ∀ m : ℕ,
      ∫ x, Y₀ x ω ∂(circleUnif z (ρ z / ((m : ℝ) + 2))) =
        Φ z (ρ z / ((m : ℝ) + 2)) (fun f => W₀ f ω) := by
    have : Countable D := hDc.to_subtype
    exact ae_all_iff.2 fun z => ae_all_iff.2 fun m =>
      h z _ (hr z z.2 m).1 (hr z z.2 m).2
  filter_upwards [hall] with ω hω
  simp only [eq_iff_iff]
  change (¬ ∀ z ∈ K, |Y₀ z ω| ≤ A) ↔ ¬ (fun f => W₀ f ω) ∈ circTestSet D ρ Φ A
  rw [forall_abs_le_iff_circ hDK' hK' hρ0 (hc ω)
    (a := fun z m => Φ z (ρ z / ((m : ℝ) + 2)) (fun f => W₀ f ω))
    (fun z hz m => (hω ⟨z, hz⟩ m).symm)]
  rfl

/-- **The tail of a continuous field is a functional of the white noise's law**: if the circle
averages of `Y` (inside `K`) are a.s. `Φ z r` of the white noise, the probability of
`¬ sup_K |Y| ≤ A` only depends on the law of the white noise. -/
theorem prob_sup_eq_of_circ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {W : WNSpace → Ω → ℝ} {W' : WNSpace → Ω' → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {K : Set ℂ}
    (hK : K ⊆ closure (interior K)) {Φ : ℂ → ℝ → (WNSpace → ℝ) → ℝ}
    (hΦ : ∀ z r, Measurable (Φ z r)) {Y : ℂ → Ω → ℝ} {Y' : ℂ → Ω' → ℝ}
    (hYc : ∀ ω, Continuous fun z => Y z ω) (hYc' : ∀ ω, Continuous fun z => Y' z ω)
    (hY : ∀ (z : ℂ) (r : ℝ), 0 < r → Metric.closedBall z r ⊆ K →
      (fun ω => ∫ x, Y x ω ∂(circleUnif z r)) =ᵐ[P] fun ω => Φ z r (fun f => W f ω))
    (hY' : ∀ (z : ℂ) (r : ℝ), 0 < r → Metric.closedBall z r ⊆ K →
      (fun ω => ∫ x, Y' x ω ∂(circleUnif z r)) =ᵐ[P'] fun ω => Φ z r (fun f => W' f ω))
    (A : ℝ) :
    P {ω | ¬ ∀ z ∈ K, |Y z ω| ≤ A} = P' {ω | ¬ ∀ z ∈ K, |Y' z ω| ≤ A} := by
  obtain ⟨D, hDK, hDc, hKD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (interior K)).exists_countable_dense_subset
  have hρ : ∀ z ∈ D, ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall z ρ ⊆ K := by
    intro z hz
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 isOpen_interior z (hDK hz)
    exact ⟨ε / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans
      (hb.trans interior_subset)⟩
  choose! ρ hρ0 hρK using hρ
  have hK' : K ⊆ closure D := hK.trans (closure_minimal hKD isClosed_closure)
  have hDK' : D ⊆ K := hDK.trans interior_subset
  have hr : ∀ z ∈ D, ∀ m : ℕ, 0 < ρ z / ((m : ℝ) + 2) ∧
      Metric.closedBall z (ρ z / ((m : ℝ) + 2)) ⊆ K := fun z hz m =>
    ⟨div_pos (hρ0 z hz) (by positivity), (Metric.closedBall_subset_closedBall
      (div_le_self (hρ0 z hz).le (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]))).trans
      (hρK z hz)⟩
  set S := circTestSet D ρ Φ A
  have hS : MeasurableSet S := measurableSet_circTestSet hDc ρ hΦ A
  rw [measure_congr (ae_eq_preimage_circTestSet hDc hDK' hK' hρ0 hr A hYc hY),
    measure_congr (ae_eq_preimage_circTestSet hDc hDK' hK' hρ0 hr A hYc' hY'),
    ← Measure.map_apply (measurable_pi_iff.mpr hW.measurable) hS.compl,
    ← Measure.map_apply (measurable_pi_iff.mpr hW'.measurable) hS.compl, map_wn_eq hW hW']

lemma ferniqueBox_subset_closure_interior (y : ℂ) {b : ℝ} (hb : 0 < b) :
    ferniqueBox y b ⊆ closure (interior (ferniqueBox y b)) := by
  unfold ferniqueBox
  rw [Complex.interior_reProdIm, Complex.closure_reProdIm, interior_Icc, interior_Icc,
    closure_Ioo (by linarith), closure_Ioo (by linarith)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Node 3 for `hatMod`**: the tail of `max_K |hatMod hW'|` is bounded with the constants of
`hatMod_spec hW`, uniformly over all white noises `W'` on `(Ω, P)`. -/
theorem hatMod_tail_uniform (hW : IsWhiteNoise P W) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) :
    ∃ c₀ c₁ : ℝ, 0 < c₁ ∧ ∀ (W' : WNSpace → Ω → ℝ) (hW' : IsWhiteNoise P W') (A : ℝ), 0 ≤ A →
      P {ω | ¬ ∀ z ∈ ferniqueBox y b, |hatMod hW' hb hK z ω| ≤ A} ≤
        ENNReal.ofReal (c₀ * Real.exp (-c₁ * A ^ 2)) := by
  obtain ⟨hc, -, ⟨c₀, c₁, hc₁, ht⟩, hcirc⟩ := hatMod_spec hW hb hK
  refine ⟨c₀, c₁, hc₁, fun W' hW' A hA => ?_⟩
  obtain ⟨hc', -, -, hcirc'⟩ := hatMod_spec hW' hb hK
  rw [← prob_sup_eq_of_circ hW hW' (ferniqueBox_subset_closure_interior y hb)
    (Φ := fun z r w => Real.sqrt Real.pi * w (measKerL2 openSquare (Ioi 0) (circleUnif z r)) -
      Real.sqrt Real.pi * w (hatMeasKerL2 (circleUnif z r)))
    (fun z r => ((measurable_pi_apply _).const_mul _).sub ((measurable_pi_apply _).const_mul _))
    hc hc' hcirc hcirc' A]
  exact ht A hA

/-- **Node 3 for `trMod`** -/
theorem trMod_tail_uniform (hW : IsWhiteNoise P W) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) :
    ∃ c₀ c₁ : ℝ, 0 < c₁ ∧ ∀ (W' : WNSpace → Ω → ℝ) (hW' : IsWhiteNoise P W') (A : ℝ), 0 ≤ A →
      P {ω | ¬ ∀ z ∈ ferniqueBox y b, |trMod hW' hb hK z ω| ≤ A} ≤
        ENNReal.ofReal (c₀ * Real.exp (-c₁ * A ^ 2)) := by
  obtain ⟨hc, -, ⟨c₀, c₁, hc₁, ht⟩, hcirc⟩ := trMod_spec hW hb hK
  refine ⟨c₀, c₁, hc₁, fun W' hW' A hA => ?_⟩
  obtain ⟨hc', -, -, hcirc'⟩ := trMod_spec hW' hb hK
  rw [← prob_sup_eq_of_circ hW hW' (ferniqueBox_subset_closure_interior y hb)
    (Φ := fun z r w => Real.sqrt Real.pi * w (measKerL2 openSquare (Ioi 0) (circleUnif z r)) -
      Real.sqrt Real.pi * w (trMeasKerL2 (circleUnif z r)))
    (fun z r => ((measurable_pi_apply _).const_mul _).sub ((measurable_pi_apply _).const_mul _))
    hc hc' hcirc hcirc' A]
  exact ht A hA

/-- **Node 3** (DG:1226 with DG:1243): `P[max_K |ĥ_{W'} − ĥ^tr_{W'}| > A] ≤ c₀ e^{−c₁ A²}` (in the
form `max_K |hatMod'| ≤ A/2 ∧ max_K |trMod'| ≤ A/2` fails), uniformly in the white noise `W'`. -/
theorem hatTr_tail_uniform (hW : IsWhiteNoise P W) {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) :
    ∃ c₀ c₁ : ℝ, 0 < c₁ ∧ ∀ (W' : WNSpace → Ω → ℝ) (hW' : IsWhiteNoise P W') (A : ℝ), 0 ≤ A →
      P {ω | ¬ ∀ z ∈ ferniqueBox y b,
          |hatMod hW' hb hK z ω| ≤ A / 2 ∧ |trMod hW' hb hK z ω| ≤ A / 2} ≤
        ENNReal.ofReal (c₀ * Real.exp (-c₁ * A ^ 2)) := by
  obtain ⟨a₀, a₁, ha, hh⟩ := hatMod_tail_uniform hW hb hK
  obtain ⟨b₀, b₁, hb', ht⟩ := trMod_tail_uniform hW hb hK
  refine ⟨max a₀ 0 + max b₀ 0, min a₁ b₁ / 4, by positivity, fun W' hW' A hA => ?_⟩
  have hsub : {ω | ¬ ∀ z ∈ ferniqueBox y b,
      |hatMod hW' hb hK z ω| ≤ A / 2 ∧ |trMod hW' hb hK z ω| ≤ A / 2} ⊆
      {ω | ¬ ∀ z ∈ ferniqueBox y b, |hatMod hW' hb hK z ω| ≤ A / 2} ∪
      {ω | ¬ ∀ z ∈ ferniqueBox y b, |trMod hW' hb hK z ω| ≤ A / 2} := by
    intro ω hω
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hc hω
    exact hω fun z hz => ⟨hc.1 z hz, hc.2 z hz⟩
  have hA2 : 0 ≤ A / 2 := by linarith
  have h1 : a₀ * Real.exp (-a₁ * (A / 2) ^ 2) ≤
      max a₀ 0 * Real.exp (-(min a₁ b₁ / 4) * A ^ 2) := by
    refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      (le_max_right _ _)
    have := min_le_left a₁ b₁
    nlinarith [sq_nonneg A]
  have h2 : b₀ * Real.exp (-b₁ * (A / 2) ^ 2) ≤
      max b₀ 0 * Real.exp (-(min a₁ b₁ / 4) * A ^ 2) := by
    refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      (le_max_right _ _)
    have := min_le_right a₁ b₁
    nlinarith [sq_nonneg A]
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (a₀ * Real.exp (-a₁ * (A / 2) ^ 2)) +
          ENNReal.ofReal (b₀ * Real.exp (-b₁ * (A / 2) ^ 2)) :=
        add_le_add (hh W' hW' _ hA2) (ht W' hW' _ hA2)
    _ ≤ ENNReal.ofReal (max a₀ 0 * Real.exp (-(min a₁ b₁ / 4) * A ^ 2)) +
          ENNReal.ofReal (max b₀ 0 * Real.exp (-(min a₁ b₁ / 4) * A ^ 2)) :=
        add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]

end DG
end LQGMetric
