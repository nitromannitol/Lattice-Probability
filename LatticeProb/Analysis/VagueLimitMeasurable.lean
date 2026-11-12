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
* `measurable_vagueLimitOrZero_subtype` and `aemeasurable_vagueLimitOrZero`: no finiteness of the `m k ω` is needed on
  the set where a vague limit exists. On that set (with the subspace σ-algebra) the chosen limit is measurable, and if
  a vague limit exists almost surely, then the chosen limit is almost everywhere measurable.
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

omit [Nonempty X] in
/-- On the set where a vague limit exists, the chosen limit is measurable (for the subspace σ-algebra) as soon as the
integrals `ω ↦ ∫ f d(m k ω)` against continuous compactly supported `f` are measurable; no finiteness of the
measures `m k ω` on compacts is assumed. -/
theorem measurable_vagueLimitOrZero_subtype {m : ℕ → Ω → Measure X}
    (hmeas : ∀ k (f : X → ℝ), Continuous f → HasCompactSupport f →
      Measurable fun ω => ∫ x, f x ∂(m k ω)) :
    Measurable fun ω : {ω | ∃ μ, IsVagueLimit (fun k => m k ω) μ} =>
      vagueLimitOrZero fun k => m k ω.1 := by
  refine LatticeProb.LocalMeasureKernel.measurable_measure_of_isOpenX (fun _ => inferInstance)
    fun U hU => ?_
  obtain ⟨f, hfc, hfs, hmass⟩ := LatticeProb.LocalMeasureKernel.exists_open_mass_test_functionsX hU
  have heq : (fun ω : {ω | ∃ μ, IsVagueLimit (fun k => m k ω) μ} =>
      (vagueLimitOrZero fun k => m k ω.1) U) =
      fun ω => ⨆ n, ENNReal.ofReal (∫ x, f n x ∂(vagueLimitOrZero fun k => m k ω.1)) :=
    funext fun _ => hmass _ inferInstance
  rw [heq]
  refine Measurable.iSup fun n => ENNReal.measurable_ofReal.comp ?_
  have hlim : Measurable fun ω : {ω | ∃ μ, IsVagueLimit (fun k => m k ω) μ} =>
      limUnder atTop (fun k => ∫ x, f n x ∂(m k ω.1)) :=
    (StronglyMeasurable.limUnder fun k =>
      ((hmeas k (f n) (hfc n) (hfs n)).comp measurable_subtype_coe).stronglyMeasurable).measurable
  convert hlim using 1
  funext ω
  exact (((isVagueLimit_vagueLimitOrZero ω.2).2 (f n) (hfc n) (hfs n)).limUnder_eq).symm

omit [Nonempty X] in
/-- **Almost sure vague limits are random measures.** If the integrals `ω ↦ ∫ f d(m k ω)` against continuous
compactly supported `f` are measurable and `k ↦ m k ω` has a vague limit for `P`-almost every `ω`, then the chosen
limit `ω ↦ vagueLimitOrZero (m · ω)` is `P`-almost everywhere measurable. -/
theorem aemeasurable_vagueLimitOrZero {P : Measure Ω} {m : ℕ → Ω → Measure X}
    (hmeas : ∀ k (f : X → ℝ), Continuous f → HasCompactSupport f →
      Measurable fun ω => ∫ x, f x ∂(m k ω))
    (hae : ∀ᵐ ω ∂P, ∃ μ, IsVagueLimit (fun k => m k ω) μ) :
    AEMeasurable (fun ω => vagueLimitOrZero fun k => m k ω) P := by
  classical
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  have hT : ∀ ω ∈ Nᶜ, ∃ μ, IsVagueLimit (fun k => m k ω) μ := fun ω hω => by
    by_contra h
    exact hω (hNsub h)
  refine ⟨Nᶜ.piecewise (fun ω => vagueLimitOrZero fun k => m k ω) fun _ => 0, ?_, ?_⟩
  · refine measurable_of_restrict_of_restrict_compl hNm.compl ?_ ?_
    · have hinc : Measurable fun ω : (Nᶜ : Set Ω) =>
          (⟨ω.1, hT ω.1 ω.2⟩ : {ω | ∃ μ, IsVagueLimit (fun k => m k ω) μ}) :=
        measurable_subtype_coe.subtype_mk
      convert (measurable_vagueLimitOrZero_subtype hmeas).comp hinc using 1
      funext ω
      show Nᶜ.piecewise (fun ω => vagueLimitOrZero fun k => m k ω) (fun _ => 0) ω.1 =
        vagueLimitOrZero fun k => m k ω.1
      exact piecewise_eq_of_mem _ _ _ ω.2
    · convert (measurable_const : Measurable fun _ : ((Nᶜ)ᶜ : Set Ω) => (0 : Measure X)) using 1
      funext ω
      show Nᶜ.piecewise (fun ω => vagueLimitOrZero fun k => m k ω) (fun _ => 0) ω.1 = 0
      exact piecewise_eq_of_notMem _ _ _ ω.2
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    exact (Set.piecewise_eq_of_mem Nᶜ (fun ω => vagueLimitOrZero fun k => m k ω)
      (fun _ => (0 : Measure X)) (show ω ∈ Nᶜ from hω)).symm

end Measurable

end LatticeProb.VagueLimit
