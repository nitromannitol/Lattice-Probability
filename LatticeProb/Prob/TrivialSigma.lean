/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: QuantumZipper/Proofs/Probability/GermZeroOne.lean.
-/
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Trivial σ-algebras and conditional expectations onto decreasing σ-algebras

A σ-algebra `m` is trivial for a measure `P` when every `m`-measurable set has `P`-measure `0`
or `1`; this is `IsTrivialSigma m P`.

The file proves three general facts about trivial σ-algebras:

* `IsTrivialSigma.mono`: a σ-algebra contained in a trivial one is trivial.
* `IsTrivialSigma.indep` and `isTrivialSigma_of_indep_self`: a trivial σ-algebra is independent
  of every σ-algebra under a probability measure, and a σ-algebra independent of itself is trivial.
* `tendsto_integral_abs_condExp_sub`: if `𝒜 n` decreases with trivial intersection, then the
  conditional expectations `P[f | 𝒜 n]` converge to `∫ f dP` in `L¹` for integrable `f`.

The last result uses that orthogonal projections onto a decreasing sequence of complete subspaces
converge strongly (`exists_tendsto_starProjection_antitone`), rather than backward martingale
convergence.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- A σ-algebra is trivial for `P` if each of its sets has measure `0` or `1`. -/
def IsTrivialSigma (m : MeasurableSpace Ω) (P : @Measure Ω mΩ) : Prop :=
  ∀ s, MeasurableSet[m] s → P s = 0 ∨ P s = 1

/-- A σ-algebra contained in a trivial σ-algebra is trivial. -/
lemma IsTrivialSigma.mono {P : Measure Ω} (h : IsTrivialSigma m' P)
    (hle : m ≤ m') : IsTrivialSigma m P :=
  fun s hs => h s (hle s hs)

/-- A trivial σ-algebra `m` (with `m ≤ mΩ`) is independent of every σ-algebra `m'` under a
probability measure `P`. -/
lemma IsTrivialSigma.indep {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsTrivialSigma m P) (hm : m ≤ mΩ) : Indep m m' P := by
  rw [Indep_iff]
  intro t1 t2 ht1 _
  rcases h t1 ht1 with h0 | h1
  · rw [h0, zero_mul]; exact measure_mono_null Set.inter_subset_left h0
  · rw [h1, one_mul]
    have hc : P t1ᶜ = 0 := by
      rw [measure_compl (hm _ ht1) (measure_ne_top _ _), h1, measure_univ, tsub_self]
    have := measure_inter_add_sdiff (μ := P) t2 (hm _ ht1)
    have hd : P (t2 \ t1) = 0 := measure_mono_null (fun x hx => hx.2) hc
    rw [hd, add_zero] at this
    rw [Set.inter_comm, this]

/-- A σ-algebra independent of itself is trivial for a probability measure. -/
lemma isTrivialSigma_of_indep_self {P : Measure Ω} [IsProbabilityMeasure P]
    (h : Indep m m P) : IsTrivialSigma m P :=
  fun _ hs => measure_eq_zero_or_one_of_indep_self h hs

/-! ### Decreasing orthogonal projections converge -/

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Orthogonal projections onto an antitone sequence of complete subspaces converge strongly, and
the limit lies in every subspace. -/
theorem exists_tendsto_starProjection_antitone (K : ℕ → Submodule ℝ E)
    [∀ n, CompleteSpace (K n)] (hK : Antitone K) (x : E) :
    ∃ y, Tendsto (fun n => (K n).starProjection x) atTop (𝓝 y) ∧ ∀ m, y ∈ K m := by
  let U : ℕ → Submodule ℝ E := fun n => (K n)ᗮ
  have hU : Monotone U := fun a b hab => Submodule.orthogonal_le (hK hab)
  haveI : CompleteSpace (⨆ i, U i).topologicalClosure :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hlim := Submodule.starProjection_tendsto_closure_iSup U hU x
  have ht : Tendsto (fun n => (K n).starProjection x) atTop
      (𝓝 (x - (⨆ i, U i).topologicalClosure.starProjection x)) := by
    have : (fun n => (K n).starProjection x) = fun n => x - (U n).starProjection x := by
      funext n; simp only [U, Submodule.starProjection_orthogonal_val, sub_sub_cancel]
    rw [this]; exact tendsto_const_nhds.sub hlim
  refine ⟨_, ht, fun m => ?_⟩
  have hcl : IsClosed (K m : Set E) :=
    (completeSpace_coe_iff_isComplete.mp inferInstance).isClosed
  refine hcl.mem_of_tendsto ht (eventually_atTop.2 ⟨m, fun n hn => hK hn ?_⟩)
  rw [Submodule.starProjection_apply]; exact Submodule.coe_mem _

end Hilbert

/-! ### Conditional expectations onto decreasing σ-algebras with trivial intersection -/

section Mixing

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- For `u ∈ L²(P)`, the `L¹` norm of `u` is at most its `L²` norm. -/
lemma integral_abs_le_norm_Lp_two (u : Lp ℝ 2 P) : ∫ ω, |u ω| ∂P ≤ ‖u‖ := by
  have h1 : ∫ ω, |u ω| ∂P = (eLpNorm u 1 P).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable u)]
    simp only [Real.norm_eq_abs]
  rw [h1, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.aestronglyMeasurable u))

omit [IsProbabilityMeasure P] in
/-- A function a.e. measurable w.r.t. every member of an antitone sequence of σ-algebras is a.e.
equal to a function measurable w.r.t. their infimum. -/
lemma exists_iInf_version {𝒜 : ℕ → MeasurableSpace Ω} (hanti : Antitone 𝒜) {g : Ω → ℝ}
    (hg : ∀ m, ∃ g' : Ω → ℝ, StronglyMeasurable[𝒜 m] g' ∧ g =ᵐ[P] g') :
    ∃ h : Ω → ℝ, Measurable[⨅ n, 𝒜 n] h ∧ g =ᵐ[P] h := by
  choose gm hgm hge using hg
  refine ⟨fun ω => limsup (fun n => gm n ω) atTop, ?_, ?_⟩
  · rw [measurable_iff_comap_le]
    refine le_iInf fun N => ?_
    rw [← measurable_iff_comap_le]
    have : (fun ω => limsup (fun n => gm n ω) atTop)
        = fun ω => limsup (fun n => gm (n + N) ω) atTop := by
      funext ω
      rw [show (fun n => gm (n + N) ω) = (fun n => gm n ω) ∘ (· + N) from rfl,
        Filter.limsup_comp, Filter.map_add_atTop_eq_nat]
    rw [this]
    exact Measurable.limsup fun n =>
      ((hgm (n + N)).measurable).mono (hanti (Nat.le_add_left N n)) le_rfl
  · filter_upwards [ae_all_iff.2 hge] with ω hω
    simp only [← hω, limsup_const]

/-- **Mixing lemma, `L²` input.** If `𝒜 n` decreases with trivial intersection, then
`E[f | 𝒜 n] → E f` in `L¹` for `f ∈ L²`. -/
theorem tendsto_integral_abs_condExp_sub_of_memLp {𝒜 : ℕ → MeasurableSpace Ω}
    (hle : ∀ n, 𝒜 n ≤ mΩ) (hanti : Antitone 𝒜) (htriv : IsTrivialSigma (⨅ n, 𝒜 n) P)
    {f : Ω → ℝ} (hf : MemLp f 2 P) :
    Tendsto (fun n => ∫ ω, |(P[f | 𝒜 n]) ω - ∫ ω, f ω ∂P| ∂P) atTop (𝓝 0) := by
  haveI : ∀ n, CompleteSpace (lpMeas ℝ ℝ (𝒜 n) 2 P) := fun n => by
    haveI : Fact (𝒜 n ≤ mΩ) := ⟨hle n⟩; infer_instance
  set F : Lp ℝ 2 P := hf.toLp f
  have hKanti : Antitone (fun n => lpMeas ℝ ℝ (𝒜 n) 2 P) := by
    intro a b hab u hu
    rw [mem_lpMeas_iff_aestronglyMeasurable] at hu ⊢
    obtain ⟨g, hg, he⟩ := hu
    exact ⟨g, hg.mono (hanti hab), he⟩
  obtain ⟨y, hy, hymem⟩ := exists_tendsto_starProjection_antitone _ hKanti F
  have hyn : ∀ n, (lpMeas ℝ ℝ (𝒜 n) 2 P).starProjection F
      = (condExpL2 ℝ ℝ (hle n) F : Lp ℝ 2 P) := fun n => by
    rw [Submodule.starProjection_apply]; rfl
  have hae : ∀ n, ((condExpL2 ℝ ℝ (hle n) F : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] P[f | 𝒜 n] :=
    fun n => hf.condExpL2_ae_eq_condExp (hle n)
  -- the limit is a.e. constant
  obtain ⟨h, hhm, hyh⟩ := exists_iInf_version (P := P) hanti
    (fun m => (mem_lpMeas_iff_aestronglyMeasurable).1 (hymem m))
  have hTle : (⨅ n, 𝒜 n) ≤ mΩ := (iInf_le _ 0).trans (hle 0)
  have hint_h : Integrable h P := ((Lp.memLp y).integrable one_le_two).congr hyh
  have hind : Indep mΩ (⨅ n, 𝒜 n) P := (htriv.indep hTle).symm
  have h1 := condExp_indep_eq le_rfl hTle (hhm.mono hTle le_rfl).stronglyMeasurable hind
  have h2 : P[h | ⨅ n, 𝒜 n] = h :=
    condExp_of_stronglyMeasurable hTle hhm.stronglyMeasurable hint_h
  rw [h2] at h1
  -- the constant is the mean
  set one : Lp ℝ 2 P := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P _) (1 : ℝ)
  have hinner : ∀ u : Lp ℝ 2 P, inner ℝ one u = ∫ ω, u ω ∂P := fun u => by
    rw [L2.inner_indicatorConstLp_one, setIntegral_univ]
  have hyn_int : ∀ n, ∫ ω, ((condExpL2 ℝ ℝ (hle n) F : Lp ℝ 2 P)) ω ∂P = ∫ ω, f ω ∂P :=
    fun n => by rw [integral_congr_ae (hae n), integral_condExp (hle n)]
  have hlimint : Tendsto (fun n => inner ℝ one ((lpMeas ℝ ℝ (𝒜 n) 2 P).starProjection F))
      atTop (𝓝 (inner ℝ one y)) := tendsto_const_nhds.inner hy
  simp only [hinner, hyn, hyn_int] at hlimint
  have hyf : ∫ ω, y ω ∂P = ∫ ω, f ω ∂P := (tendsto_nhds_unique tendsto_const_nhds hlimint).symm
  have hyc : (y : Ω → ℝ) =ᵐ[P] fun _ => ∫ ω, f ω ∂P := by
    have : ∫ ω, h ω ∂P = ∫ ω, f ω ∂P := by rw [← integral_congr_ae hyh, hyf]
    filter_upwards [hyh, h1] with ω e1 e2
    rw [e1, e2, this]
  have hnorm : Tendsto (fun n => ‖(lpMeas ℝ ℝ (𝒜 n) 2 P).starProjection F - y‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).1 hy
  refine squeeze_zero (fun n => integral_nonneg fun _ => abs_nonneg _) (fun n => ?_) hnorm
  refine le_trans (le_of_eq ?_) (integral_abs_le_norm_Lp_two _)
  refine integral_congr_ae ?_
  filter_upwards [hae n, hyc,
    Lp.coeFn_sub ((lpMeas ℝ ℝ (𝒜 n) 2 P).starProjection F) y] with ω e1 e2 e3
  rw [e3, Pi.sub_apply, hyn n, e1, e2]

/-- **Mixing lemma, `L¹` input.** If `𝒜 n` decreases with trivial intersection, then
`E[f | 𝒜 n] → E f` in `L¹` for integrable `f`. -/
theorem tendsto_integral_abs_condExp_sub {𝒜 : ℕ → MeasurableSpace Ω}
    (hle : ∀ n, 𝒜 n ≤ mΩ) (hanti : Antitone 𝒜) (htriv : IsTrivialSigma (⨅ n, 𝒜 n) P)
    {f : Ω → ℝ} (hf : Integrable f P) :
    Tendsto (fun n => ∫ ω, |(P[f | 𝒜 n]) ω - ∫ ω, f ω ∂P| ∂P) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by positivity
  obtain ⟨g, hfg, -⟩ := (memLp_one_iff_integrable.2 hf).exists_simpleFunc_eLpNorm_sub_lt
    ENNReal.one_ne_top (ε := ENNReal.ofReal (ε / 3)) (ENNReal.ofReal_pos.2 hε3).ne'
  have hg2 : MemLp (g : Ω → ℝ) 2 P := (SimpleFunc.memLp_top g P).mono_exponent le_top
  have hgi : Integrable (g : Ω → ℝ) P := hg2.integrable one_le_two
  have hδ : ∫ ω, |f ω - g ω| ∂P < ε / 3 := by
    have : ∫ ω, |f ω - g ω| ∂P = (eLpNorm (f - ⇑g) 1 P).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm,
        ← integral_norm_eq_lintegral_enorm ((hf.sub hgi).aestronglyMeasurable)]
      simp only [Pi.sub_apply, Real.norm_eq_abs]
    rw [this]; exact ENNReal.toReal_lt_of_lt_ofReal hfg
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (tendsto_integral_abs_condExp_sub_of_memLp hle hanti htriv hg2) (ε / 3) hε3
  refine ⟨N, fun n hn => ?_⟩
  have hNn := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at hNn ⊢
  have hsub : P[f - ⇑g | 𝒜 n] =ᵐ[P] P[f | 𝒜 n] - P[g | 𝒜 n] := condExp_sub hf hgi _
  have hA : ∫ ω, |(P[f | 𝒜 n]) ω - (P[g | 𝒜 n]) ω| ∂P ≤ ∫ ω, |f ω - g ω| ∂P := by
    calc ∫ ω, |(P[f | 𝒜 n]) ω - (P[g | 𝒜 n]) ω| ∂P = ∫ ω, |(P[f - ⇑g | 𝒜 n]) ω| ∂P :=
          integral_congr_ae (by filter_upwards [hsub] with ω h; rw [h]; rfl)
      _ ≤ ∫ ω, |(f - ⇑g) ω| ∂P := integral_abs_condExp_le _
      _ = _ := rfl
  have hC : |∫ ω, g ω ∂P - ∫ ω, f ω ∂P| ≤ ∫ ω, |f ω - g ω| ∂P := by
    rw [← integral_sub hgi hf]
    exact abs_integral_le_integral_abs.trans
      (le_of_eq (integral_congr_ae (Eventually.of_forall fun ω => abs_sub_comm _ _)))
  have hpt : ∀ ω, |(P[f | 𝒜 n]) ω - ∫ ω, f ω ∂P| ≤ |(P[f | 𝒜 n]) ω - (P[g | 𝒜 n]) ω|
      + |(P[g | 𝒜 n]) ω - ∫ ω, g ω ∂P| + |∫ ω, g ω ∂P - ∫ ω, f ω ∂P| := fun ω => by
    calc |(P[f | 𝒜 n]) ω - ∫ ω, f ω ∂P|
        = |((P[f | 𝒜 n]) ω - (P[g | 𝒜 n]) ω) + ((P[g | 𝒜 n]) ω - ∫ ω, g ω ∂P)
            + (∫ ω, g ω ∂P - ∫ ω, f ω ∂P)| := by congr 1; ring
      _ ≤ _ := by
        linarith [abs_add_le ((P[f | 𝒜 n]) ω - (P[g | 𝒜 n]) ω) ((P[g | 𝒜 n]) ω - ∫ ω, g ω ∂P),
          abs_add_le (((P[f | 𝒜 n]) ω - (P[g | 𝒜 n]) ω) + ((P[g | 𝒜 n]) ω - ∫ ω, g ω ∂P))
            (∫ ω, g ω ∂P - ∫ ω, f ω ∂P)]
  have hi1 : Integrable (fun ω => |(P[f | 𝒜 n]) ω - (P[g | 𝒜 n]) ω|) P :=
    (integrable_condExp.sub integrable_condExp).abs
  have hi2 : Integrable (fun ω => |(P[g | 𝒜 n]) ω - ∫ ω, g ω ∂P|) P :=
    (integrable_condExp.sub (integrable_const _)).abs
  have hi0 : Integrable (fun ω => |(P[f | 𝒜 n]) ω - ∫ ω, f ω ∂P|) P :=
    (integrable_condExp.sub (integrable_const _)).abs
  have hi12 : Integrable (fun ω => |(P[f | 𝒜 n]) ω - (P[g | 𝒜 n]) ω|
      + |(P[g | 𝒜 n]) ω - ∫ ω, g ω ∂P|) P := hi1.add hi2
  have hi123 : Integrable (fun ω => |(P[f | 𝒜 n]) ω - (P[g | 𝒜 n]) ω|
      + |(P[g | 𝒜 n]) ω - ∫ ω, g ω ∂P| + |∫ ω, g ω ∂P - ∫ ω, f ω ∂P|) P :=
    hi12.add (integrable_const _)
  calc ∫ ω, |(P[f | 𝒜 n]) ω - ∫ ω, f ω ∂P| ∂P
      ≤ ∫ ω, (|(P[f | 𝒜 n]) ω - (P[g | 𝒜 n]) ω| + |(P[g | 𝒜 n]) ω - ∫ ω, g ω ∂P|
          + |∫ ω, g ω ∂P - ∫ ω, f ω ∂P|) ∂P :=
        integral_mono hi0 hi123 hpt
    _ = ∫ ω, |(P[f | 𝒜 n]) ω - (P[g | 𝒜 n]) ω| ∂P
          + ∫ ω, |(P[g | 𝒜 n]) ω - ∫ ω, g ω ∂P| ∂P + |∫ ω, g ω ∂P - ∫ ω, f ω ∂P| := by
        rw [integral_add hi12 (integrable_const _), integral_add hi1 hi2]
        simp
    _ < ε := by linarith

end Mixing

/-! ### Nonvacuity -/

namespace TrivialSigmaExample

-- The trivial σ-algebra `⊥` is trivial for every probability measure.
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    IsTrivialSigma ⊥ P := by
  intro s hs
  rcases MeasurableSpace.measurableSet_bot_iff.1 hs with rfl | rfl
  · exact Or.inl measure_empty
  · exact Or.inr measure_univ

end TrivialSigmaExample

end LatticeProb
