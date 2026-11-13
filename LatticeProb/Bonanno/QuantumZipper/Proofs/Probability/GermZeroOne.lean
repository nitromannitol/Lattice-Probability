/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.GermZeroOne at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: eLpNorm_one_eq_lintegral_enorm takes the measurability argument and eLpNorm_le_eLpNorm_of_exponent_le no longer does (three proof lines). -/
/-
Blueprint node A8: germ 0-1 toolkit.

(a) Blumenthal 0-1 law for Brownian motion.
(b) Independent-join lemma for decreasing σ-algebras with trivial intersections.
(c) Brownian scaling mixing.

The key analytic tool is the `L²` (hence `L¹`) convergence of conditional expectations onto a
decreasing sequence of σ-algebras with trivial intersection, proved through monotone orthogonal
projections (on the orthogonal complements), avoiding backward martingale convergence.
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

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace GermZeroOne

variable {Ω : Type*} {m m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- A σ-algebra is trivial for `P` if each of its sets has measure `0` or `1`. -/
def IsTrivialSigma (m : MeasurableSpace Ω) (P : @Measure Ω mΩ) : Prop :=
  ∀ s, MeasurableSet[m] s → P s = 0 ∨ P s = 1

lemma IsTrivialSigma.mono {P : Measure Ω} (h : IsTrivialSigma m' P)
    (hle : m ≤ m') : IsTrivialSigma m P :=
  fun s hs => h s (hle s hs)

lemma IsTrivialSigma.indep {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsTrivialSigma m P) (hm : m ≤ mΩ) : Indep m m' P := by
  rw [Indep_iff]
  intro t1 t2 ht1 _
  rcases h t1 ht1 with h0 | h1
  · rw [h0, zero_mul]; exact measure_mono_null Set.inter_subset_left h0
  · rw [h1, one_mul]
    have hc : P t1ᶜ = 0 := by
      rw [measure_compl (hm _ ht1) (measure_ne_top _ _), h1, measure_univ, tsub_self]
    have := measure_inter_add_diff (μ := P) t2 (hm _ ht1)
    have hd : P (t2 \ t1) = 0 := measure_mono_null (fun x hx => hx.2) hc
    rw [hd, add_zero] at this
    rw [Set.inter_comm, this]

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

lemma integral_abs_le_norm_Lp_two (u : Lp ℝ 2 P) : ∫ ω, |u ω| ∂P ≤ ‖u‖ := by
  have h1 : ∫ ω, |u ω| ∂P = (eLpNorm u 1 P).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable u), ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable u)]
    simp only [Real.norm_eq_abs]
  rw [h1, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))

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
      rw [eLpNorm_one_eq_lintegral_enorm ((hf.sub hgi).aestronglyMeasurable),
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

/-! ### (b) The independent-join lemma -/

section Join

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Rectangles `a ∩ b` with `a ∈ m₁`, `b ∈ m₂`. -/
def rectSets (m₁ m₂ : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ a b, MeasurableSet[m₁] a ∧ MeasurableSet[m₂] b ∧ s = a ∩ b}

lemma isPiSystem_rectSets (m₁ m₂ : MeasurableSpace Ω) : IsPiSystem (rectSets m₁ m₂) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩ _ ⟨a', b', ha', hb', rfl⟩ _
  refine ⟨a ∩ a', b ∩ b', ha.inter ha', hb.inter hb', ?_⟩
  ext x; simp only [Set.mem_inter_iff]; tauto

lemma sup_eq_generateFrom_rectSets (m₁ m₂ : MeasurableSpace Ω) :
    m₁ ⊔ m₂ = MeasurableSpace.generateFrom (rectSets m₁ m₂) := by
  apply le_antisymm
  · refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact MeasurableSpace.measurableSet_generateFrom
        ⟨a, Set.univ, ha, MeasurableSet.univ, (Set.inter_univ a).symm⟩
    · exact MeasurableSpace.measurableSet_generateFrom
        ⟨Set.univ, b, MeasurableSet.univ, hb, (Set.univ_inter b).symm⟩
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨a, b, ha, hb, rfl⟩
    exact @MeasurableSet.inter Ω (m₁ ⊔ m₂) a b ((le_sup_left : m₁ ≤ m₁ ⊔ m₂) a ha)
      ((le_sup_right : m₂ ≤ m₁ ⊔ m₂) b hb)

lemma integral_mul_of_indep {m₁ m₂ : MeasurableSpace Ω} (hind : Indep m₁ m₂ P) {f g : Ω → ℝ}
    (hf : StronglyMeasurable[m₁] f) (hg : StronglyMeasurable[m₂] g) (h₁ : m₁ ≤ mΩ)
    (h₂ : m₂ ≤ mΩ) :
    ∫ ω, f ω * g ω ∂P = (∫ ω, f ω ∂P) * ∫ ω, g ω ∂P := by
  have hfg : IndepFun f g P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hf.measurable.comap_le)
      hg.measurable.comap_le
  exact hfg.integral_mul_eq_mul_integral (hf.mono h₁).aestronglyMeasurable
    (hg.mono h₂).aestronglyMeasurable

lemma abs_indicator_one_le (A : Set Ω) (ω : Ω) : |A.indicator (fun _ => (1 : ℝ)) ω| ≤ 1 := by
  by_cases h : ω ∈ A <;> simp [h]

/-- Core computation of the join lemma. -/
lemma measure_inter_rect_eq_of_join {𝒜 ℬ : ℕ → MeasurableSpace Ω} (h𝒜 : ∀ n, 𝒜 n ≤ mΩ)
    (hℬ : ∀ n, ℬ n ≤ mΩ) (ha : Antitone 𝒜) (hb : Antitone ℬ) (hind : Indep (𝒜 0) (ℬ 0) P)
    (hta : IsTrivialSigma (⨅ n, 𝒜 n) P) (htb : IsTrivialSigma (⨅ n, ℬ n) P) {G A B : Set Ω}
    (hG : MeasurableSet[⨅ n, 𝒜 n ⊔ ℬ n] G) (hA : MeasurableSet[𝒜 0] A)
    (hB : MeasurableSet[ℬ 0] B) :
    P (G ∩ (A ∩ B)) = P G * P (A ∩ B) := by
  have hsup : ∀ n, 𝒜 n ⊔ ℬ n ≤ mΩ := fun n => sup_le (h𝒜 n) (hℬ n)
  have hG' : ∀ n, MeasurableSet[𝒜 n ⊔ ℬ n] G := fun n => (iInf_le (fun n => 𝒜 n ⊔ ℬ n) n) G hG
  have hG0 : MeasurableSet G := hsup 0 _ (hG' 0)
  have hA0 : MeasurableSet A := h𝒜 0 _ hA
  have hB0 : MeasurableSet B := hℬ 0 _ hB
  set ia : Ω → ℝ := A.indicator (fun _ => (1 : ℝ)) with hia_def
  set ib : Ω → ℝ := B.indicator (fun _ => (1 : ℝ)) with hib_def
  have hia : Integrable ia P := (integrable_const (1 : ℝ)).indicator hA0
  have hib : Integrable ib P := (integrable_const (1 : ℝ)).indicator hB0
  have hia_sm : StronglyMeasurable[𝒜 0] ia := stronglyMeasurable_const.indicator hA
  have hib_sm : StronglyMeasurable[ℬ 0] ib := stronglyMeasurable_const.indicator hB
  set a : ℕ → Ω → ℝ := fun n => P[ia | 𝒜 n]
  set b : ℕ → Ω → ℝ := fun n => P[ib | ℬ n]
  have ha1 : ∀ n, ∀ᵐ ω ∂P, |a n ω| ≤ 1 := fun n => by
    have := ae_bdd_condExp_of_ae_bdd (m := 𝒜 n) (μ := P) (R := 1)
      (Eventually.of_forall fun ω => by simpa using abs_indicator_one_le A ω)
    simpa using this
  have hb1 : ∀ n, ∀ᵐ ω ∂P, |b n ω| ≤ 1 := fun n => by
    have := ae_bdd_condExp_of_ae_bdd (m := ℬ n) (μ := P) (R := 1)
      (Eventually.of_forall fun ω => by simpa using abs_indicator_one_le B ω)
    simpa using this
  have hu : Integrable (fun ω => ia ω * ib ω) P :=
    hib.bdd_mul hia.aestronglyMeasurable (c := 1)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact abs_indicator_one_le A ω)
  have hv : ∀ n, Integrable (fun ω => a n ω * b n ω) P := fun n =>
    integrable_condExp.bdd_mul integrable_condExp.aestronglyMeasurable (c := 1)
      (by filter_upwards [ha1 n] with ω hω; rwa [Real.norm_eq_abs])
  -- Step 1: conditional factorization
  have C1 : ∀ n G', MeasurableSet[𝒜 n ⊔ ℬ n] G' →
      ∫ ω in G', ia ω * ib ω ∂P = ∫ ω in G', a n ω * b n ω ∂P := by
    intro n
    have hn𝒜 : 𝒜 n ≤ 𝒜 0 := ha (Nat.zero_le n)
    have hnℬ : ℬ n ≤ ℬ 0 := hb (Nat.zero_le n)
    have basic : ∀ A' B', MeasurableSet[𝒜 n] A' → MeasurableSet[ℬ n] B' →
        ∫ ω in A' ∩ B', ia ω * ib ω ∂P = ∫ ω in A' ∩ B', a n ω * b n ω ∂P := by
      intro A' B' hA' hB'
      have e1 : ∀ φ ψ : Ω → ℝ, ∫ ω in A' ∩ B', φ ω * ψ ω ∂P
          = ∫ ω, A'.indicator φ ω * B'.indicator ψ ω ∂P := by
        intro φ ψ
        rw [← integral_indicator (MeasurableSet.inter (h𝒜 n _ hA') (hℬ n _ hB'))]
        congr 1; funext ω
        by_cases h1 : ω ∈ A' <;> by_cases h2 : ω ∈ B' <;> simp [Set.indicator, h1, h2]
      rw [e1, e1]
      rw [integral_mul_of_indep hind (hia_sm.indicator (hn𝒜 _ hA'))
          (hib_sm.indicator (hnℬ _ hB')) (h𝒜 0) (hℬ 0),
        integral_mul_of_indep hind
          ((stronglyMeasurable_condExp.mono hn𝒜).indicator (hn𝒜 _ hA'))
          ((stronglyMeasurable_condExp.mono hnℬ).indicator (hnℬ _ hB')) (h𝒜 0) (hℬ 0)]
      rw [integral_indicator (h𝒜 n _ hA'), integral_indicator (hℬ n _ hB'),
        integral_indicator (h𝒜 n _ hA'), integral_indicator (hℬ n _ hB'),
        setIntegral_condExp (h𝒜 n) hia hA', setIntegral_condExp (hℬ n) hib hB']
    have total : ∫ ω, ia ω * ib ω ∂P = ∫ ω, a n ω * b n ω ∂P := by
      have := basic Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
      simpa using this
    intro G' hG'
    refine @MeasurableSpace.induction_on_inter Ω (𝒜 n ⊔ ℬ n)
      (fun t _ => ∫ ω in t, ia ω * ib ω ∂P = ∫ ω in t, a n ω * b n ω ∂P) _
      (sup_eq_generateFrom_rectSets (𝒜 n) (ℬ n)) (isPiSystem_rectSets _ _) ?_ ?_ ?_ ?_ G' hG'
    · simp
    · rintro _ ⟨A', B', hA', hB', rfl⟩
      exact basic A' B' hA' hB'
    · intro t htm ih
      rw [setIntegral_compl (hsup n t htm) hu, setIntegral_compl (hsup n t htm) (hv n), ih, total]
    · intro f hd hfm ih
      rw [integral_iUnion (fun i => hsup n _ (hfm i)) hd hu.integrableOn,
        integral_iUnion (fun i => hsup n _ (hfm i)) hd (hv n).integrableOn]
      exact tsum_congr ih
  -- Step 2: the mixing limits
  set α := ∫ ω, ia ω ∂P
  set β := ∫ ω, ib ω ∂P
  have hαA : α = P.real A := by
    show ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂P = _
    rw [integral_indicator_const _ hA0, smul_eq_mul, mul_one]
  have hβB : β = P.real B := by
    show ∫ ω, B.indicator (fun _ => (1 : ℝ)) ω ∂P = _
    rw [integral_indicator_const _ hB0, smul_eq_mul, mul_one]
  have hα1 : |α| ≤ 1 := by
    rw [hαA, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  have C2a : Tendsto (fun n => ∫ ω, |a n ω - α| ∂P) atTop (𝓝 0) :=
    tendsto_integral_abs_condExp_sub_of_memLp h𝒜 ha hta
      (memLp_indicator_const 2 hA0 (1 : ℝ) (Or.inr (measure_ne_top _ _)))
  have C2b : Tendsto (fun n => ∫ ω, |b n ω - β| ∂P) atTop (𝓝 0) :=
    tendsto_integral_abs_condExp_sub_of_memLp hℬ hb htb
      (memLp_indicator_const 2 hB0 (1 : ℝ) (Or.inr (measure_ne_top _ _)))
  have e1 : ∫ ω in G, ia ω * ib ω ∂P = P.real (G ∩ (A ∩ B)) := by
    have : (fun ω => ia ω * ib ω) = (A ∩ B).indicator (fun _ => (1 : ℝ)) := by
      funext ω; by_cases h1 : ω ∈ A <;> by_cases h2 : ω ∈ B <;> simp [ia, ib, h1, h2]
    rw [this, integral_indicator_const _ (hA0.inter hB0),
      measureReal_restrict_apply (hA0.inter hB0), Set.inter_comm, smul_eq_mul, mul_one]
  have bound : ∀ n, |P.real (G ∩ (A ∩ B)) - P.real G * (α * β)|
      ≤ ∫ ω, |a n ω - α| ∂P + ∫ ω, |b n ω - β| ∂P := by
    intro n
    have hbd : ∀ᵐ ω ∂P, |a n ω * b n ω - α * β| ≤ |a n ω - α| + |b n ω - β| := by
      filter_upwards [hb1 n] with ω hω
      calc |a n ω * b n ω - α * β| = |(a n ω - α) * b n ω + α * (b n ω - β)| := by
            congr 1; ring
        _ ≤ |(a n ω - α) * b n ω| + |α * (b n ω - β)| := abs_add_le _ _
        _ = |a n ω - α| * |b n ω| + |α| * |b n ω - β| := by rw [abs_mul, abs_mul]
        _ ≤ |a n ω - α| * 1 + 1 * |b n ω - β| := by
            gcongr
        _ = _ := by ring
    have hi1 : Integrable (fun ω => |a n ω - α|) P := (integrable_condExp.sub (integrable_const _)).abs
    have hi2 : Integrable (fun ω => |b n ω - β|) P := (integrable_condExp.sub (integrable_const _)).abs
    have hi3 : Integrable (fun ω => |a n ω * b n ω - α * β|) P :=
      ((hv n).sub (integrable_const _)).abs
    calc |P.real (G ∩ (A ∩ B)) - P.real G * (α * β)|
        = |∫ ω in G, (a n ω * b n ω - α * β) ∂P| := by
          rw [integral_sub (hv n).integrableOn (integrable_const _).integrableOn,
            ← C1 n G (hG' n), e1, setIntegral_const, smul_eq_mul]
      _ ≤ ∫ ω in G, |a n ω * b n ω - α * β| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, |a n ω * b n ω - α * β| ∂P :=
          setIntegral_le_integral hi3 (Eventually.of_forall fun _ => abs_nonneg _)
      _ ≤ ∫ ω, (|a n ω - α| + |b n ω - β|) ∂P := integral_mono_ae hi3 (hi1.add hi2) hbd
      _ = _ := integral_add hi1 hi2
  have hlim : Tendsto (fun n => ∫ ω, |a n ω - α| ∂P + ∫ ω, |b n ω - β| ∂P) atTop (𝓝 0) := by
    simpa using C2a.add C2b
  have h0 := ge_of_tendsto' hlim bound
  have key : P.real (G ∩ (A ∩ B)) = P.real G * (P.real A * P.real B) := by
    rw [← hαA, ← hβB]; exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)
  have hAB : P (A ∩ B) = P A * P B := (Indep_iff _ _ _).1 hind A B hA hB
  rw [hAB]
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _)
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)))).1 ?_
  simpa [measureReal_def, ENNReal.toReal_mul] using key

/-- **Independent join, two families.** If `𝒜 n ↓`, `ℬ n ↓`, `𝒜 0 ⊥ ℬ 0`, and both intersections
are trivial, then `⋂ₙ (𝒜 n ⊔ ℬ n)` is trivial. -/
theorem isTrivialSigma_iInf_sup {𝒜 ℬ : ℕ → MeasurableSpace Ω} (h𝒜 : ∀ n, 𝒜 n ≤ mΩ)
    (hℬ : ∀ n, ℬ n ≤ mΩ) (ha : Antitone 𝒜) (hb : Antitone ℬ) (hind : Indep (𝒜 0) (ℬ 0) P)
    (hta : IsTrivialSigma (⨅ n, 𝒜 n) P) (htb : IsTrivialSigma (⨅ n, ℬ n) P) :
    IsTrivialSigma (⨅ n, 𝒜 n ⊔ ℬ n) P := by
  have hT0 : (⨅ n, 𝒜 n ⊔ ℬ n) ≤ 𝒜 0 ⊔ ℬ 0 := iInf_le (fun n => 𝒜 n ⊔ ℬ n) 0
  have hsup0 : 𝒜 0 ⊔ ℬ 0 ≤ mΩ := sup_le (h𝒜 0) (hℬ 0)
  suffices hTI : Indep (⨅ n, 𝒜 n ⊔ ℬ n) (𝒜 0 ⊔ ℬ 0) P from
    isTrivialSigma_of_indep_self (indep_of_indep_of_le_right hTI hT0)
  refine IndepSets.indep (hT0.trans hsup0) hsup0
    (@MeasurableSpace.isPiSystem_measurableSet Ω (⨅ n, 𝒜 n ⊔ ℬ n)) (isPiSystem_rectSets _ _)
    (@MeasurableSpace.generateFrom_measurableSet Ω (⨅ n, 𝒜 n ⊔ ℬ n)).symm
    (sup_eq_generateFrom_rectSets _ _) ?_
  rw [IndepSets_iff]
  rintro G _ hG ⟨A, B, hA, hB, rfl⟩
  exact measure_inter_rect_eq_of_join h𝒜 hℬ ha hb hind hta htb hG hA hB

/-- **Independent join, finitely many families.** -/
theorem isTrivialSigma_iInf_biSup {ι : Type*} (𝒜 : ι → ℕ → MeasurableSpace Ω)
    (hle : ∀ i n, 𝒜 i n ≤ mΩ) (hanti : ∀ i, Antitone (𝒜 i)) (hind : iIndep (fun i => 𝒜 i 0) P)
    (htriv : ∀ i, IsTrivialSigma (⨅ n, 𝒜 i n) P) (S : Finset ι) :
    IsTrivialSigma (⨅ n, ⨆ i ∈ S, 𝒜 i n) P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro s hs
    have h0 : (⨅ n, ⨆ i ∈ (∅ : Finset ι), 𝒜 i n) = ⊥ := by simp
    rw [h0] at hs
    rcases MeasurableSpace.measurableSet_bot_iff.1 hs with rfl | rfl <;> simp
  | insert j S hj ih =>
    have heq : (⨅ n, ⨆ i ∈ insert j S, 𝒜 i n) = ⨅ n, 𝒜 j n ⊔ ⨆ i ∈ S, 𝒜 i n := by
      simp only [Finset.iSup_insert]
    rw [heq]
    refine isTrivialSigma_iInf_sup (hle j) (fun n => iSup₂_le fun i _ => hle i n) (hanti j)
      (fun a b hab => iSup₂_mono fun i _ => hanti i hab) ?_ (htriv j) ih
    have := indep_iSup_of_disjoint (fun i => hle i 0) hind
      (S := ({j} : Set ι)) (T := (S : Set ι)) (by simpa using hj)
    simpa using this

end Join

/-! ### (a) Blumenthal 0-1 law -/

section Brownian

variable {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit mΩ in
lemma measurable_pi_of {α δ : Type*} {mα : MeasurableSpace α} {g : α → δ → ℝ}
    (hg : ∀ a, Measurable[mα] fun x => g x a) : Measurable[mα] g :=
  measurable_pi_iff.2 hg

omit mΩ in
lemma measurable_comap_coord {α δ : Type*} (g : α → δ → ℝ) (d : δ) :
    Measurable[MeasurableSpace.comap g inferInstance] (fun x => g x d) :=
  (measurable_pi_apply d).comp (comap_measurable g)

/-- `σ(B|[0,u])`. -/
def bmPast (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (t : Set.Iic u) => B t ω) inferInstance

/-- The times `1/(n+1)`. -/
noncomputable def epsSeq (n : ℕ) : ℝ≥0 := ((n : ℝ≥0) + 1)⁻¹

lemma epsSeq_pos (n : ℕ) : 0 < epsSeq n := by
  exact inv_pos.2 (add_pos_of_nonneg_of_pos (by positivity) one_pos)

lemma epsSeq_antitone : Antitone epsSeq := fun a b h => by
  unfold epsSeq
  exact inv_anti₀ (add_pos_of_nonneg_of_pos (by positivity) one_pos)
    ((add_le_add_iff_right 1).2 (Nat.cast_le.2 h))

lemma tendsto_epsSeq : Tendsto epsSeq atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have e : (fun n : ℕ => ((epsSeq n : ℝ≥0) : ℝ)) = fun n : ℕ => 1 / ((n : ℝ) + 1) := by
    funext n; simp [epsSeq]
  exact NNReal.tendsto_coe.1 (by rw [e, NNReal.coe_zero]; exact h)

lemma measurable_bmPast_coord {u s : ℝ≥0} (hs : s ≤ u) : Measurable[bmPast B u] (B s) :=
  measurable_comap_coord (fun ω (t : Set.Iic u) => B t ω) ⟨s, hs⟩

lemma bmPast_le (hBm : ∀ t, Measurable (B t)) (u : ℝ≥0) : bmPast B u ≤ mΩ :=
  (measurable_pi_of (g := fun ω (t : Set.Iic u) => B t ω) fun t => hBm _).comap_le

lemma bmPast_mono {u v : ℝ≥0} (huv : u ≤ v) : bmPast B u ≤ bmPast B v :=
  (measurable_pi_of (g := fun ω (t : Set.Iic u) => B t ω)
    fun t => measurable_bmPast_coord (t.2.trans huv)).comap_le

/-- `σ(B(t₀ + ·) - B t₀)`. -/
def bmFuture (B : ℝ≥0 → Ω → ℝ) (t₀ : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (s : ℝ≥0) => B (t₀ + s) ω - B t₀ ω) inferInstance

lemma measurable_bmFuture {t₀ t : ℝ≥0} (ht : t₀ ≤ t) :
    Measurable[bmFuture B t₀] (fun ω => B t ω - B t₀ ω) := by
  have := measurable_comap_coord (fun ω (s : ℝ≥0) => B (t₀ + s) ω - B t₀ ω) (t - t₀)
  simp only [add_tsub_cancel_of_le ht] at this
  exact this

/-- **Blumenthal 0-1 law** (dyadic form): `⋂ₙ σ(B|[0,1/(n+1)])` is trivial. -/
theorem isTrivialSigma_iInf_bmPast (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) :
    IsTrivialSigma (⨅ n, bmPast B (epsSeq n)) P := by
  haveI : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hℱle : ∀ n, bmFuture B (epsSeq n) ≤ mΩ := fun n =>
    (measurable_pi_of (g := fun ω (s : ℝ≥0) => B (epsSeq n + s) ω - B (epsSeq n) ω)
      fun s => (hBm _).sub (hBm _)).comap_le
  have h𝒢le : (⨅ n, bmPast B (epsSeq n)) ≤ mΩ := (iInf_le _ 0).trans (bmPast_le hBm _)
  have hmono : Monotone fun n => bmFuture B (epsSeq n) := by
    intro n k hnk
    refine Measurable.comap_le (measurable_pi_of
      (g := fun ω (s : ℝ≥0) => B (epsSeq n + s) ω - B (epsSeq n) ω) fun s => ?_)
    have h1 := measurable_bmFuture (B := B) (t := epsSeq n + s)
      ((epsSeq_antitone hnk).trans le_self_add)
    have h2 := measurable_bmFuture (B := B) (t := epsSeq n) (epsSeq_antitone hnk)
    convert h1.sub h2 using 1
    funext ω; simp only [Pi.sub_apply]; ring
  have hind_n : ∀ n, Indep (bmFuture B (epsSeq n)) (⨅ n, bmPast B (epsSeq n)) P := by
    intro n
    have h := hB.toIsPreBrownianReal.indepFun_shift (epsSeq n)
    rw [IndepFun_iff_Indep] at h
    exact indep_of_indep_of_le_right h (iInf_le (fun n => bmPast B (epsSeq n)) n)
  have hsup : Indep (⨆ n, bmFuture B (epsSeq n)) (⨅ n, bmPast B (epsSeq n)) P :=
    indep_iSup_of_directed_le hind_n hℱle h𝒢le hmono.directed_le
  have hWm : Measurable[⨆ n, bmFuture B (epsSeq n)] (fun ω (t : ℝ≥0) =>
      limsup (fun n => B (max t (epsSeq n)) ω - B (epsSeq n) ω) atTop) := by
    refine measurable_pi_of fun t => Measurable.limsup fun n => ?_
    exact (measurable_bmFuture (le_max_right t _)).mono
      (le_iSup (fun n => bmFuture B (epsSeq n)) n) le_rfl
  have hWeq : ∀ᵐ ω ∂P, (fun t => B t ω) = (fun t =>
      limsup (fun n => B (max t (epsSeq n)) ω - B (epsSeq n) ω) atTop) := by
    filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hc h0
    funext t
    symm
    refine Tendsto.limsup_eq ?_
    have h1 : Tendsto (fun n => max t (epsSeq n)) atTop (𝓝 t) := by
      have := (tendsto_const_nhds (x := t)).max tendsto_epsSeq
      rwa [max_eq_left (by positivity : (0 : ℝ≥0) ≤ t)] at this
    have h2 : Tendsto (fun n => B (epsSeq n) ω) atTop (𝓝 0) := by
      have := (hc.tendsto 0).comp tendsto_epsSeq
      simpa [Function.comp_def, h0] using this
    simpa using ((hc.tendsto t).comp h1).sub h2
  have hpath : Indep (MeasurableSpace.comap (fun ω t => B t ω) inferInstance)
      (⨅ n, bmPast B (epsSeq n)) P := by
    rw [Indep_iff]
    rintro _ t2 ⟨S, hS, rfl⟩ ht2
    have hS' := hWm hS
    have heq : (fun ω t => B t ω) ⁻¹' S =ᵐ[P] (fun ω (t : ℝ≥0) =>
        limsup (fun n => B (max t (epsSeq n)) ω - B (epsSeq n) ω) atTop) ⁻¹' S := by
      filter_upwards [hWeq] with ω hω
      change ((fun t => B t ω) ∈ S) = (_ ∈ S)
      rw [hω]
    rw [measure_congr heq, measure_congr (heq.inter (ae_eq_refl t2))]
    exact (Indep_iff _ _ _).1 hsup _ _ hS' ht2
  have hG_le_path : (⨅ n, bmPast B (epsSeq n))
      ≤ MeasurableSpace.comap (fun ω t => B t ω) inferInstance :=
    (iInf_le _ 0).trans (Measurable.comap_le (measurable_pi_of
      (g := fun ω (t : Set.Iic (epsSeq 0)) => B t ω) fun t =>
        measurable_comap_coord (fun ω (t : ℝ≥0) => B t ω) (t : ℝ≥0)))
  exact isTrivialSigma_of_indep_self (indep_of_indep_of_le_right hpath.symm hG_le_path)

/-! ### (c) Brownian scaling mixing -/

/-- Two pre-Brownian motions with measurable coordinates have the same path law. -/
lemma map_path_eq_of_isPreBrownianReal {B B' : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hB' : IsPreBrownianReal B' P) (hBm : ∀ t, Measurable (B t))
    (hBm' : ∀ t, Measurable (B' t)) :
    P.map (fun ω t => B t ω) = P.map (fun ω t => B' t ω) := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hproj : ∀ {C : ℝ≥0 → Ω → ℝ}, IsPreBrownianReal C P → (∀ t, Measurable (C t)) →
      IsProjectiveLimit (P.map (fun ω t => C t ω)) BrownianReal.projectiveFamily := by
    intro C hC hCm I
    rw [Measure.map_map (Finset.measurable_restrict I) (measurable_pi_of hCm)]
    exact (hC.hasLaw I).map_eq
  haveI : ∀ I, IsFiniteMeasure (BrownianReal.projectiveFamily I) := fun I => by
    rw [← (hB.hasLaw I).map_eq]; infer_instance
  exact (hproj hB hBm).unique (hproj hB' hBm')

end Brownian

end GermZeroOne
end QuantumZipper
