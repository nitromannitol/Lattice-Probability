/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3TrInv2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3TrInv1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11In1
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# The joint law of the white noise and a continuous modification (P2-DGTRINV, part 2)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, DG:1243 ("the re-centered field
… agrees in law with `ĥ^tr`") and DG:984–986 (`μ_ĥ`, `μ_{ĥ^tr}` built from the coupling of
Lemma 3.1). In the formalization `μ_{ĥ^tr} = e^{−γ Y} μ_{h^𝕍}|_K` (`muOfMod`, S3MuHat), with `Y`
a *chosen* continuous modification of `h^𝕍 − ĥ^tr` whose circle averages are a fixed linear
functional `Φ` of the white noise. Here:

* `triSel`, `triExt`: a measurable selector of a point of a countable dense sequence `e` near
  `z`, and the extension `triExt e y z = lim_n y(triSel e n z)` of a sequence `y : ℕ → ℝ`;
  `triExt_eq`: for continuous `g`, `triExt e (g ∘ e) = g` on `closure (range e)`;
  `measurable_triExt`: joint measurability (deterministic);
* `triPsi`: the values of the modification at the points `e i`, as the limits of the circle
  averages `Φ (e i) (ρ_i/(m+2))` (a measurable functional of the white noise);
* `ae_triPsi_eq`: a.s. `Y (e i) = triPsi (W)` for all `i`
  (`QuantumZipper.K3.tendsto_integral_circleUnif_zero`);
* **`map_wn_mod_eq`**: the joint law of `(W, (Y (e i))_i)` is the same for every white noise
  (`map_wn_eq`, S3L11In1).

Own elementary glue (DG use the equality in law implicitly).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Classical

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3 SupTail QuantumZipper

/-! ### Deterministic: a measurable dense selector -/

/-- the selection predicate: `e i` is within `1/(n+1)` of `z`, or no point of `e` is -/
def triSelP (e : ℕ → ℂ) (n : ℕ) (z : ℂ) (i : ℕ) : Prop :=
  dist (e i) z < 1 / ((n : ℝ) + 1) ∨ ∀ j, 1 / ((n : ℝ) + 1) ≤ dist (e j) z

lemma triSelP_ex (e : ℕ → ℂ) (n : ℕ) (z : ℂ) : ∃ i, triSelP e n z i := by
  by_cases h : ∃ j, dist (e j) z < 1 / ((n : ℝ) + 1)
  · obtain ⟨j, hj⟩ := h; exact ⟨j, Or.inl hj⟩
  · push Not at h; exact ⟨0, Or.inr h⟩

/-- the index of the first point of `e` within `1/(n+1)` of `z` (`0` if there is none) -/
def triSel (e : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℕ := Nat.find (triSelP_ex e n z)

lemma measurable_triSel (e : ℕ → ℂ) (n : ℕ) : Measurable (triSel e n) := by
  refine measurable_find (triSelP_ex e n) fun k => ?_
  have e1 : {z | triSelP e n z k} = {z | dist (e k) z < 1 / ((n : ℝ) + 1)} ∪
      ⋂ j, {z | 1 / ((n : ℝ) + 1) ≤ dist (e j) z} := by
    ext z; simp [triSelP]
  rw [e1]
  exact (measurableSet_lt (continuous_const.dist continuous_id).measurable measurable_const).union
    (MeasurableSet.iInter fun j =>
      measurableSet_le measurable_const (continuous_const.dist continuous_id).measurable)

lemma dist_triSel_lt {e : ℕ → ℂ} {z : ℂ} (hz : z ∈ closure (range e)) (n : ℕ) :
    dist (e (triSel e n z)) z < 1 / ((n : ℝ) + 1) := by
  rcases Nat.find_spec (triSelP_ex e n z) with h | h
  · exact h
  · obtain ⟨_, ⟨j, rfl⟩, hj⟩ := Metric.mem_closure_iff.1 hz (1 / ((n : ℝ) + 1)) (by positivity)
    rw [dist_comm] at hj
    exact absurd (h j) (not_le.2 hj)

/-- the extension of a sequence `y` (values at the points `e i`) to the plane -/
def triExt (e : ℕ → ℂ) (y : ℕ → ℝ) (z : ℂ) : ℝ := limUnder atTop fun n => y (triSel e n z)

lemma tendsto_triSel {e : ℕ → ℂ} {z : ℂ} (hz : z ∈ closure (range e)) :
    Tendsto (fun n => e (triSel e n z)) atTop (𝓝 z) := by
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
    (fun n => (dist_triSel_lt hz n).le) ?_)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- **`triExt` recovers a continuous function from its values on a dense sequence** -/
theorem triExt_eq {e : ℕ → ℂ} {g : ℂ → ℝ} (hg : Continuous g) {z : ℂ}
    (hz : z ∈ closure (range e)) : triExt e (fun i => g (e i)) z = g z :=
  ((hg.tendsto z).comp (tendsto_triSel hz)).limUnder_eq

theorem measurable_triExt (e : ℕ → ℂ) :
    Measurable fun p : (ℕ → ℝ) × ℂ => triExt e p.1 p.2 := by
  have h : ∀ n, Measurable fun p : (ℕ → ℝ) × ℂ => p.1 (triSel e n p.2) := by
    intro n
    have hev : Measurable fun q : (ℕ → ℝ) × ℕ => q.1 q.2 :=
      measurable_from_prod_countable_left fun i => measurable_pi_apply i
    exact hev.comp (measurable_fst.prodMk ((measurable_triSel e n).comp measurable_snd))
  exact (StronglyMeasurable.limUnder fun n => (h n).stronglyMeasurable).measurable

/-- a dense sequence of `interior K` with radii of closed balls inside `K` -/
theorem exists_triDense {K : Set ℂ} (hne : (interior K).Nonempty) :
    ∃ (e : ℕ → ℂ) (ρ : ℕ → ℝ), range e ⊆ interior K ∧ interior K ⊆ closure (range e) ∧
      ∀ i, 0 < ρ i ∧ Metric.closedBall (e i) (ρ i) ⊆ K := by
  obtain ⟨D, hDK, hDc, hKD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (interior K)).exists_countable_dense_subset
  have hDne : D.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨y, hy, -⟩ := Metric.mem_closure_iff.1 (hKD hz) 1 one_pos
    exact ⟨y, hy⟩
  obtain ⟨e, rfl⟩ := hDc.exists_eq_range hDne
  have hρ : ∀ i, ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall (e i) ρ ⊆ K := by
    intro i
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 isOpen_interior (e i) (hDK ⟨i, rfl⟩)
    exact ⟨ε / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans
      (hb.trans interior_subset)⟩
  choose ρ hρ using hρ
  exact ⟨e, ρ, hDK, hKD, hρ⟩

/-! ### The values of a modification as a functional of the white noise -/

/-- the limit of the circle averages `Φ (e i) (ρ_i/(m+2))` -/
def triPsi (e : ℕ → ℂ) (ρ : ℕ → ℝ) (Φ : ℂ → ℝ → (WNSpace → ℝ) → ℝ) (w : WNSpace → ℝ) :
    ℕ → ℝ := fun i => limUnder atTop fun m : ℕ => Φ (e i) (ρ i / ((m : ℝ) + 2)) w

theorem measurable_triPsi (e : ℕ → ℂ) (ρ : ℕ → ℝ) {Φ : ℂ → ℝ → (WNSpace → ℝ) → ℝ}
    (hΦ : ∀ z r, Measurable (Φ z r)) : Measurable (triPsi e ρ Φ) :=
  measurable_pi_iff.2 fun _ =>
    (StronglyMeasurable.limUnder fun _ => (hΦ _ _).stronglyMeasurable).measurable

/-- the white-noise vector `ω ↦ (f ↦ W f ω)` -/
def wnVec {Ω : Type*} (W : WNSpace → Ω → ℝ) (ω : Ω) : WNSpace → ℝ := fun f => W f ω

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma measurable_wnVec (hW : IsWhiteNoise P W) : Measurable (wnVec W) :=
  measurable_pi_iff.mpr hW.measurable

/-- a.s. the values of the modification at the points `e i` are `triPsi` of the white noise -/
theorem ae_triPsi_eq {K : Set ℂ} {e : ℕ → ℂ} {ρ : ℕ → ℝ}
    (hρ : ∀ i, 0 < ρ i ∧ Metric.closedBall (e i) (ρ i) ⊆ K) {Φ : ℂ → ℝ → (WNSpace → ℝ) → ℝ}
    {Y : ℂ → Ω → ℝ} (hY : IsDGMod P K (fun z r ω => Φ z r (wnVec W ω)) Y) :
    ∀ᵐ ω ∂P, (fun i => Y (e i) ω) = triPsi e ρ Φ (wnVec W ω) := by
  have hr : ∀ i (m : ℕ), 0 < ρ i / ((m : ℝ) + 2) ∧
      Metric.closedBall (e i) (ρ i / ((m : ℝ) + 2)) ⊆ K := fun i m =>
    ⟨div_pos (hρ i).1 (by positivity), (Metric.closedBall_subset_closedBall
      (div_le_self (hρ i).1.le (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]))).trans (hρ i).2⟩
  have hall : ∀ᵐ ω ∂P, ∀ i m : ℕ, ∫ x, Y x ω ∂(circleUnif (e i) (ρ i / ((m : ℝ) + 2))) =
      Φ (e i) (ρ i / ((m : ℝ) + 2)) (wnVec W ω) :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun m => hY.2.2.2 _ _ (hr i m).1 (hr i m).2
  filter_upwards [hall] with ω hω
  funext i
  have hrad : Tendsto (fun m : ℕ => ρ i / ((m : ℝ) + 2)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => (hr i m).1⟩
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have := (QuantumZipper.K3.tendsto_integral_circleUnif_zero (hY.1 ω) (e i)).comp hrad
  exact (this.congr fun m => hω i m).limUnder_eq.symm

/-- **the joint law of the white noise and the modification's values on `e`** is the same for
every white noise (on any probability space) -/
theorem map_wn_mod_eq {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {W' : WNSpace → Ω' → ℝ} (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {K : Set ℂ}
    {e : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i ∧ Metric.closedBall (e i) (ρ i) ⊆ K)
    {Φ : ℂ → ℝ → (WNSpace → ℝ) → ℝ} (hΦ : ∀ z r, Measurable (Φ z r))
    {Y : ℂ → Ω → ℝ} (hY : IsDGMod P K (fun z r ω => Φ z r (wnVec W ω)) Y)
    {Y' : ℂ → Ω' → ℝ} (hY' : IsDGMod P' K (fun z r ω => Φ z r (wnVec W' ω)) Y') :
    P.map (fun ω => (wnVec W ω, fun i => Y (e i) ω)) =
      P'.map (fun ω => (wnVec W' ω, fun i => Y' (e i) ω)) := by
  have hG : Measurable fun w : WNSpace → ℝ => (w, triPsi e ρ Φ w) :=
    measurable_id.prodMk (measurable_triPsi e ρ hΦ)
  have h1 : P.map (fun ω => (wnVec W ω, fun i => Y (e i) ω)) =
      (P.map (wnVec W)).map fun w => (w, triPsi e ρ Φ w) := by
    rw [Measure.map_map hG (measurable_wnVec hW)]
    refine Measure.map_congr ?_
    filter_upwards [ae_triPsi_eq hρ hY] with ω hω
    simp only [Function.comp_apply, hω]
  have h2 : P'.map (fun ω => (wnVec W' ω, fun i => Y' (e i) ω)) =
      (P'.map (wnVec W')).map fun w => (w, triPsi e ρ Φ w) := by
    rw [Measure.map_map hG (measurable_wnVec hW')]
    refine Measure.map_congr ?_
    filter_upwards [ae_triPsi_eq hρ hY'] with ω hω
    simp only [Function.comp_apply, hω]
  rw [h1, h2]
  congr 1
  exact map_wn_eq hW hW'

end DG
end LQGMetric
