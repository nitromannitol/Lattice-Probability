import Mathlib
import LatticeProb.Analysis.VagueLimitSequence
import LatticeProb.LQG.LocalMeasureKernel

/-!
# Measurable choice of a vague limit

Random measures are often defined as almost sure vague limits of explicit approximations (for instance the Liouville
measure, as the limit of `ε^{γ²/2} e^{γ h_ε(z)} dz`). To use such a limit as a random variable with values in the
space of measures, one fixes a choice of the limit off the event where it exists. This file shows that the natural
choice is measurable.

* `IsVagueLimit μs μ`: `μ` is finite on compact sets and `∫ f d(μs k) → ∫ f dμ` for every continuous compactly
  supported `f`.
* `vagueLimitOrZero μs`: a vague limit of `μs` when one exists, and the zero measure otherwise.
* `measurableSet_exists_isVagueLimit`: if `m k ω` are measures finite on compacts on a proper metric space and every
  `ω ↦ ∫ f d(m k ω)` (`f` continuous, compactly supported) is measurable, then the event that `k ↦ m k ω` has a
  vague limit is measurable. It is the event that the integrals converge on the countable family of
  `exists_countable_determining_vague_limit`.
* `measurable_integral_vagueLimitOrZero`: under the same hypotheses, `ω ↦ ∫ f d(vagueLimitOrZero (m · ω))` is
  measurable for every continuous compactly supported `f`: it is the limit of the integrals on that event and `0`
  off it.
* `measurable_vagueLimitOrZero`: under the same hypotheses, `ω ↦ vagueLimitOrZero (m · ω)` is measurable for the Giry
  σ-algebra on `Measure X`. The mass of an open set is the supremum of the integrals of an increasing sequence of
  continuous compactly supported functions, and a family of locally finite measures is measurable once its values on
  open sets are.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb.VagueLimit

section Defs

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- **Vague convergence.** `μ` is finite on compact sets and `∫ f d(μs k) → ∫ f dμ` for every continuous
compactly supported `f`. -/
def IsVagueLimit (μs : ℕ → Measure X) (μ : Measure X) : Prop :=
  (∀ K : Set X, IsCompact K → μ K < ⊤) ∧
    ∀ f : X → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k => ∫ x, f x ∂(μs k)) atTop (𝓝 (∫ x, f x ∂μ))

open Classical in
/-- A vague limit of `μs` when one exists (a chosen one), and the zero measure otherwise. -/
noncomputable def vagueLimitOrZero (μs : ℕ → Measure X) : Measure X :=
  if h : ∃ μ, IsVagueLimit μs μ then h.choose else 0

theorem isVagueLimit_vagueLimitOrZero {μs : ℕ → Measure X} (h : ∃ μ, IsVagueLimit μs μ) :
    IsVagueLimit μs (vagueLimitOrZero μs) := by
  unfold vagueLimitOrZero
  split_ifs
  exact h.choose_spec

theorem vagueLimitOrZero_of_not {μs : ℕ → Measure X} (h : ¬∃ μ, IsVagueLimit μs μ) :
    vagueLimitOrZero μs = 0 := by
  unfold vagueLimitOrZero
  split_ifs
  rfl

theorem vagueLimitOrZero_lt_top (μs : ℕ → Measure X) {K : Set X} (hK : IsCompact K) :
    vagueLimitOrZero μs K < ⊤ := by
  by_cases h : ∃ μ, IsVagueLimit μs μ
  · exact (isVagueLimit_vagueLimitOrZero h).1 K hK
  · rw [vagueLimitOrZero_of_not h]
    simp

instance isFiniteMeasureOnCompacts_vagueLimitOrZero (μs : ℕ → Measure X) :
    IsFiniteMeasureOnCompacts (vagueLimitOrZero μs) :=
  ⟨fun _ hK => vagueLimitOrZero_lt_top μs hK⟩

end Defs

section Measurable

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {Ω : Type*} [MeasurableSpace Ω]

/-- The event that a measurably indexed sequence of measures, finite on compacts, has a vague limit is
measurable: it is the event that the integrals converge on a countable convergence-determining family. -/
theorem measurableSet_exists_isVagueLimit {m : ℕ → Ω → Measure X}
    (hfin : ∀ k ω, IsFiniteMeasureOnCompacts (m k ω))
    (hmeas : ∀ k (f : X → ℝ), Continuous f → HasCompactSupport f →
      Measurable fun ω => ∫ x, f x ∂(m k ω)) :
    MeasurableSet {ω | ∃ μ, IsVagueLimit (fun k => m k ω) μ} := by
  obtain ⟨D, hDc, hDcc, hD⟩ := exists_countable_determining_vague_limit (X := X)
  have hset : {ω | ∃ μ, IsVagueLimit (fun k => m k ω) μ} =
      ⋂ g ∈ D, {ω | ∃ ℓ : ℝ, Tendsto (fun k => ∫ x, g x ∂(m k ω)) atTop (𝓝 ℓ)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · rintro ⟨μ, -, hμ⟩ g hg
      exact ⟨_, hμ g (hDcc g hg).1 (hDcc g hg).2⟩
    · intro hconv
      obtain ⟨μ, hμ, hlim⟩ := hD (fun k => m k ω) (fun k => hfin k ω) hconv
      have := hμ
      exact ⟨μ, fun K hK => hK.measure_lt_top, hlim⟩
  rw [hset]
  refine MeasurableSet.biInter hDc fun g hg => ?_
  exact StronglyMeasurable.measurableSet_exists_tendsto
    (fun k => (hmeas k g (hDcc g hg).1 (hDcc g hg).2).stronglyMeasurable)

/-- The integral of a continuous compactly supported function against the chosen vague limit is measurable: it is
the limit of the integrals against `m k ω` where the vague limit exists, and `0` elsewhere. -/
theorem measurable_integral_vagueLimitOrZero {m : ℕ → Ω → Measure X}
    (hfin : ∀ k ω, IsFiniteMeasureOnCompacts (m k ω))
    (hmeas : ∀ k (f : X → ℝ), Continuous f → HasCompactSupport f →
      Measurable fun ω => ∫ x, f x ∂(m k ω))
    {f : X → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Measurable fun ω => ∫ x, f x ∂(vagueLimitOrZero fun k => m k ω) := by
  classical
  have hE : MeasurableSet {ω | ∃ μ, IsVagueLimit (fun k => m k ω) μ} :=
    measurableSet_exists_isVagueLimit hfin hmeas
  have hlim : Measurable fun ω => limUnder atTop (fun k => ∫ x, f x ∂(m k ω)) :=
    (StronglyMeasurable.limUnder fun k => (hmeas k f hf hfc).stronglyMeasurable).measurable
  have heq : (fun ω => ∫ x, f x ∂(vagueLimitOrZero fun k => m k ω)) =
      {ω | ∃ μ, IsVagueLimit (fun k => m k ω) μ}.piecewise
        (fun ω => limUnder atTop (fun k => ∫ x, f x ∂(m k ω))) fun _ => 0 := by
    funext ω
    by_cases hω : ∃ μ, IsVagueLimit (fun k => m k ω) μ
    · rw [piecewise_eq_of_mem _ _ _ (show ω ∈ {ω | ∃ μ, IsVagueLimit (fun k => m k ω) μ} from hω)]
      exact (((isVagueLimit_vagueLimitOrZero hω).2 f hf hfc).limUnder_eq).symm
    · rw [piecewise_eq_of_notMem _ _ _ (show ω ∉ {ω | ∃ μ, IsVagueLimit (fun k => m k ω) μ} from hω),
        vagueLimitOrZero_of_not hω, integral_zero_measure]
  rw [heq]
  exact hlim.piecewise hE measurable_const

/-- **The chosen vague limit is a random measure.** If the measures `m k ω` are finite on compacts and the integrals
`ω ↦ ∫ f d(m k ω)` against continuous compactly supported `f` are measurable, then `ω ↦ vagueLimitOrZero (m · ω)` is
measurable for the Giry σ-algebra on `Measure X`. -/
theorem measurable_vagueLimitOrZero {m : ℕ → Ω → Measure X}
    (hfin : ∀ k ω, IsFiniteMeasureOnCompacts (m k ω))
    (hmeas : ∀ k (f : X → ℝ), Continuous f → HasCompactSupport f →
      Measurable fun ω => ∫ x, f x ∂(m k ω)) :
    Measurable fun ω => vagueLimitOrZero fun k => m k ω := by
  refine LatticeProb.LocalMeasureKernel.measurable_measure_of_isOpenX (fun _ => inferInstance)
    fun U hU => ?_
  obtain ⟨f, hfc, hfs, hmass⟩ := LatticeProb.LocalMeasureKernel.exists_open_mass_test_functionsX hU
  have heq : (fun ω => (vagueLimitOrZero fun k => m k ω) U) =
      fun ω => ⨆ n, ENNReal.ofReal (∫ x, f n x ∂(vagueLimitOrZero fun k => m k ω)) :=
    funext fun _ => hmass _ inferInstance
  rw [heq]
  exact Measurable.iSup fun n =>
    ENNReal.measurable_ofReal.comp (measurable_integral_vagueLimitOrZero hfin hmeas (hfc n) (hfs n))

end Measurable

end LatticeProb.VagueLimit
