/-
Jointly measurable representatives of strongly measurable L2-valued families.

Simple L2-valued functions have jointly measurable scalar representatives. For a
strongly measurable family, measurable selection from simple approximants gives
geometric L2 errors at every parameter; summability then gives almost-sure
convergence at each parameter. The measurable limsup is the required version.

An isonormal covariance identity makes white-noise evaluation an isometry into
random-variable L2. Composing that isometry with a measurable spatial L2 family
therefore gives joint versions without any choice of pointwise linear samples.
-/
import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace
namespace LatticeProb
/-- The scalar evaluation of a simple L2-valued family is jointly measurable. -/
theorem stronglyMeasurable_simpleFunc_L2_eval {U Ω : Type*} [MeasurableSpace U] [MeasurableSpace Ω]
    (P : Measure Ω) (s : SimpleFunc U (Lp ℝ 2 P)) :
    StronglyMeasurable (fun p : U × Ω => s p.1 p.2) := by
  exact ((s.comp Prod.fst measurable_fst).measurable_bind
    (fun v p => v p.2) (fun v => (Lp.stronglyMeasurable v).measurable.comp
      measurable_snd)).stronglyMeasurable


/-- Geometric L2 approximation implies almost-sure pointwise convergence. -/
theorem ae_tendsto_of_L2_geometric_approx {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Lp ℝ 2 P) (f : Lp ℝ 2 P)
    (hF : ∀ n, ‖F n - f‖ ≤ (1 / 2 : ℝ) ^ n) :
    ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (f ω)) := by
  have hs : Summable (fun n => ‖F n - f‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hF summable_geometric_two
  have ht : ∑' n, eLpNorm (fun ω => (F n - f) ω) 2 P ≠ ∞ := by
    simpa only [← Lp.enorm_def] using tsum_enorm_ne_top_iff_summable_norm.mpr hs
  have ha := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (fun n => Lp.aestronglyMeasurable (F n - f)) ht
  filter_upwards [ha, ae_all_iff.mpr (fun n => Lp.coeFn_sub (F n) f)] with ω hω heq
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [dist_eq_norm, heq, Pi.sub_apply] using hω.tendsto_atTop_zero


/-- A strongly measurable L2-valued family has a joint scalar version at every parameter. -/
theorem exists_stronglyMeasurable_L2_version {U Ω : Type*} [MeasurableSpace U] [MeasurableSpace Ω]
    (P : Measure Ω) (F : U → Lp ℝ 2 P) (hF : StronglyMeasurable F) :
    ∃ g : U → Ω → ℝ, StronglyMeasurable (Function.uncurry g) ∧
      ∀ u, g u =ᵐ[P] (F u) := by
  classical
  let s := hF.approx
  have hex : ∀ (n : ℕ) (u : U), ∃ k, ‖s k u - F u‖ < (1 / 2 : ℝ) ^ n := by
    intro n u
    have ht := (tendsto_iff_norm_sub_tendsto_zero.mp (hF.tendsto_approx u))
    exact (ht.eventually (gt_mem_nhds (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n))).exists
  let k (n : ℕ) (u : U) := Nat.find (hex n u)
  let a (n : ℕ) (u : U) : Lp ℝ 2 P := s (k n u) u
  have ha : ∀ n, Measurable (fun p : U × Ω => a n p.1 p.2) := by
    intro n
    exact Measurable.find
      (fun j => (stronglyMeasurable_simpleFunc_L2_eval P (s j)).measurable)
      (fun j => measurableSet_lt
        (((s j).stronglyMeasurable.sub hF).norm.measurable.comp measurable_fst)
        measurable_const)
      (fun p : U × Ω => hex n p.1)
  refine ⟨fun u ω => limsup (fun n => a n u ω) atTop,
    (Measurable.limsup ha).stronglyMeasurable, ?_⟩
  intro u
  have hb : ∀ n, ‖a n u - F u‖ ≤ (1 / 2 : ℝ) ^ n :=
    fun n => (Nat.find_spec (hex n u)).le
  filter_upwards [ae_tendsto_of_L2_geometric_approx P (fun n => a n u) (F u) hb] with ω hω
  exact hω.limsup_eq


/-- The covariance identity passes to the inner product of the L2 classes. -/
theorem inner_toLp_eq_of_covariance {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (P : Measure Ω)
    (W : H → Ω → ℝ) (hm : ∀ f, MemLp (W f) 2 P)
    (hc : ∀ f g, (∫ ω, W f ω * W g ω ∂P) = inner ℝ f g) (f g : H) :
    inner ℝ ((hm f).toLp (W f)) ((hm g).toLp (W g)) = inner ℝ f g := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  calc (∫ ω, (hm g).toLp (W g) ω * (hm f).toLp (W f) ω ∂P)
      = ∫ ω, W g ω * W f ω ∂P := by
        apply integral_congr_ae
        filter_upwards [(hm f).coeFn_toLp, (hm g).coeFn_toLp] with ω hf hg
        rw [hf, hg]
    _ = inner ℝ f g := (hc g f).trans (real_inner_comm f g)


/-- Preserving real inner products preserves distances. -/
theorem isometry_of_inner_eq {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (J : H → E) (hJ : ∀ f g, inner ℝ (J f) (J g) = inner ℝ f g) :
    Isometry J := by
  apply isometry_iff_dist_eq.mpr
  intro f g
  have hsq : ‖J f - J g‖ ^ 2 = ‖f - g‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, hJ]
  simp only [dist_eq_norm]
  nlinarith [norm_nonneg (J f - J g), norm_nonneg (f - g)]


/-- Covariance identifies noise evaluations of almost-everywhere equal test functions. -/
theorem toLp_eq_of_covariance_of_ae_eq {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure X) (P : Measure Ω) (W : (X → ℝ) → Ω → ℝ)
    (hm : ∀ f, MemLp (W f) 2 P)
    (hc : ∀ f g, MemLp f 2 μ → MemLp g 2 μ →
      (∫ ω, W f ω * W g ω ∂P) = ∫ x, f x * g x ∂μ)
    (f g : X → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (heq : f =ᵐ[μ] g) :
    (hm f).toLp (W f) = (hm g).toLp (W g) := by
  let J (a : X → ℝ) : Lp ℝ 2 P := (hm a).toLp (W a)
  have hi (a b : X → ℝ) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
      inner ℝ (J a) (J b) = ∫ x, a x * b x ∂μ := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial]
    calc (∫ ω, J b ω * J a ω ∂P) = ∫ ω, W a ω * W b ω ∂P := by
          apply integral_congr_ae
          filter_upwards [(hm a).coeFn_toLp, (hm b).coeFn_toLp] with ω ha hb
          dsimp only [J]
          rw [ha, hb, mul_comm]
      _ = ∫ x, a x * b x ∂μ := hc a b ha hb
  have hfg : (∫ x, f x * g x ∂μ) = ∫ x, f x * f x ∂μ := by
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  have hgf : (∫ x, g x * f x ∂μ) = ∫ x, f x * f x ∂μ := by
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  have hgg : (∫ x, g x * g x ∂μ) = ∫ x, f x * f x ∂μ := by
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  change J f = J g
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    hi f f hf hf, hi f g hf hg, hi g f hg hf, hi g g hg hg, hfg, hgf, hgg]
  ring


/-- Isonormal covariance supplies joint versions along strongly measurable test families. -/
theorem exists_joint_version_of_covariance {X Ω U : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace U]
    (μ : Measure X) (P : Measure Ω) (W : (X → ℝ) → Ω → ℝ)
    (hm : ∀ f, MemLp (W f) 2 P)
    (hc : ∀ f g, MemLp f 2 μ → MemLp g 2 μ →
      (∫ ω, W f ω * W g ω ∂P) = ∫ x, f x * g x ∂μ)
    (f : U → X → ℝ) (hf : ∀ u, MemLp (f u) 2 μ)
    (hF : StronglyMeasurable (fun u => (hf u).toLp (f u))) :
    ∃ g : U → Ω → ℝ, StronglyMeasurable (Function.uncurry g) ∧
      ∀ u, g u =ᵐ[P] W (f u) := by
  let J (a : Lp ℝ 2 μ) : Lp ℝ 2 P := (hm (fun x => a x)).toLp (W (fun x => a x))
  have hcov (a b : Lp ℝ 2 μ) :
      (∫ ω, W (fun x => a x) ω * W (fun x => b x) ω ∂P) = inner ℝ a b := by
    rw [hc _ _ (Lp.memLp a) (Lp.memLp b), L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial]
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => mul_comm _ _
  have hJ (a b : Lp ℝ 2 μ) : inner ℝ (J a) (J b) = inner ℝ a b :=
    inner_toLp_eq_of_covariance P (fun a : Lp ℝ 2 μ => W (fun x => a x))
      (fun a => hm (fun x => a x)) hcov a b
  have hJs : StronglyMeasurable (fun u => J ((hf u).toLp (f u))) :=
    (isometry_of_inner_eq J hJ).continuous.comp_stronglyMeasurable hF
  obtain ⟨g, hg, heq⟩ := exists_stronglyMeasurable_L2_version P _ hJs
  refine ⟨g, hg, ?_⟩
  intro u
  have he : J ((hf u).toLp (f u)) = (hm (f u)).toLp (W (f u)) :=
    toLp_eq_of_covariance_of_ae_eq μ P W hm hc _ _ (Lp.memLp _) (hf u) (hf u).coeFn_toLp
  have hu := heq u
  rw [he] at hu
  exact hu.trans (hm (f u)).coeFn_toLp

end LatticeProb
