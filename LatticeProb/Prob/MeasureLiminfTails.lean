import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Sequences

/-!
# Liminf and tail bounds for measures and convergence in measure

General forms of elementary facts on liminf, lower and upper tail events,
and measurability of tail probabilities of jointly measurable functions.

The results are stated for an arbitrary measurable space, or for a pseudometric
or normed space, so that they apply to any probability or finite measure.
-/

namespace LatticeProb.MeasureLiminfTails

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

/-- The liminf of a sequence in a complete lattice is bounded by its supremum. -/
theorem liminf_le_iSup_nat {α : Type*} [CompleteLattice α] (f : ℕ → α) :
    liminf f atTop ≤ ⨆ n, f n := by
  rw [liminf_eq_iSup_iInf_of_nat]
  exact iSup_mono fun n => iInf₂_le n le_rfl

/-- Infimum of ball masses over a compact set, computed through a dense sequence.
With `δₙ = δ₀ / (n + 1)`, the infimum over `x ∈ K` of `m (ball x ρ)` equals the supremum over `n`
of the infima of `m (ball (w i) (ρ - 2 δₙ))` over the indices `i` with `infDist (w i) K < δₙ`. -/
theorem iInf_measure_ball_eq {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {m : Measure X} {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty) (ρ : ℝ)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {w : ℕ → X} (hw : DenseRange w) :
    ⨅ x ∈ K, m (ball x ρ) =
      ⨆ n : ℕ, ⨅ i, ⨅ (_ : infDist (w i) K < δ₀ / ((n : ℝ) + 1)),
        m (ball (w i) (ρ - 2 * (δ₀ / ((n : ℝ) + 1)))) := by
  set δ : ℕ → ℝ := fun n => δ₀ / ((n : ℝ) + 1) with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδanti : ∀ {n k : ℕ}, n ≤ k → δ k ≤ δ n := fun {n k} hnk => by
    have : (n : ℝ) ≤ k := by exact_mod_cast hnk
    exact div_le_div_of_nonneg_left hδ₀.le (by positivity) (by linarith)
  refine le_antisymm ?_ (iSup_le fun n => le_iInf₂ fun x hx => ?_)
  swap
  · obtain ⟨i, hi⟩ := hw.exists_mem_open isOpen_ball ⟨x, mem_ball_self (hδpos n)⟩
    refine iInf₂_le_of_le i ((infDist_le_dist_of_mem hx).trans_lt (mem_ball.1 hi)) (measure_mono ?_)
    refine ball_subset_ball' ?_
    have := mem_ball.1 hi
    have := hδpos n
    linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs1, hs2⟩ := exists_between hcon
  have hn : ∀ n, ∃ i, infDist (w i) K < δ n ∧ m (ball (w i) (ρ - 2 * δ n)) < s := by
    intro n
    have h := (le_iSup (fun n : ℕ => ⨅ i, ⨅ (_ : infDist (w i) K < δ n), m (ball (w i) (ρ - 2 * δ n))) n).trans_lt hs1
    obtain ⟨i, hi⟩ := iInf_lt_iff.1 h
    obtain ⟨hc, hlt⟩ := iInf_lt_iff.1 hi
    exact ⟨i, hc, hlt⟩
  choose i hic his using hn
  have hy : ∀ n, ∃ y ∈ K, dist (w (i n)) y < δ n := fun n => (infDist_lt_iff hKne).1 (hic n)
  choose y hyK hyd using hy
  obtain ⟨y₀, hy₀K, φ, hφ, hφlim⟩ := hK.tendsto_subseq hyK
  -- every ball `B_{ρ - 3δ_N}(y₀)` has mass less than `s`
  have hN : ∀ N : ℕ, m (ball y₀ (ρ - 3 * δ N)) ≤ s := by
    intro N
    have h1 : ∀ᶠ j in atTop, dist (y (φ j)) y₀ < δ N / 2 :=
      (tendsto_iff_dist_tendsto_zero.1 hφlim).eventually (gt_mem_nhds (by linarith [hδpos N]))
    have h2 : ∀ᶠ j in atTop, 2 * N + 1 ≤ φ j := hφ.tendsto_atTop.eventually_ge_atTop _
    obtain ⟨j, hj1, hj2⟩ := (h1.and h2).exists
    have hδj : δ (φ j) ≤ δ N / 2 := by
      have := hδanti hj2
      have e : δ (2 * N + 1) = δ N / 2 := by
        simp only [hδdef]
        push_cast
        field_simp
        ring
      linarith
    have hdj : dist y₀ (w (i (φ j))) < δ N := by
      have h3 := hyd (φ j)
      have h4 := dist_triangle y₀ (y (φ j)) (w (i (φ j)))
      rw [dist_comm (y (φ j)) (w (i (φ j)))] at h4
      rw [dist_comm] at hj1
      linarith
    refine (measure_mono (ball_subset_ball' ?_)).trans (his (φ j)).le
    have := hδpos N
    linarith
  have hU : ball y₀ ρ = ⋃ N : ℕ, ball y₀ (ρ - 3 * δ N) := by
    refine Subset.antisymm (fun x hx => ?_) (iUnion_subset fun N => ball_subset_ball (by linarith [hδpos N]))
    have hx' : 0 < ρ - dist x y₀ := by rw [mem_ball] at hx; linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (3 * δ₀ / (ρ - dist x y₀))
    refine mem_iUnion.2 ⟨N, mem_ball.2 ?_⟩
    have h1 : 3 * δ₀ < N * (ρ - dist x y₀) := by rwa [div_lt_iff₀ hx'] at hN
    have h2 : 3 * δ N < ρ - dist x y₀ := by
      simp only [hδdef]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      have e : (ρ - dist x y₀) * ((N : ℝ) + 1) = N * (ρ - dist x y₀) + (ρ - dist x y₀) := by ring
      linarith
    linarith
  have hmono : Monotone fun N : ℕ => ball y₀ (ρ - 3 * δ N) := fun N N' hNN' =>
    ball_subset_ball (by linarith [hδanti hNN'])
  have hball : m (ball y₀ ρ) ≤ s := by
    rw [hU]
    exact le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) hN
  exact absurd ((iInf₂_le y₀ hy₀K).trans hball) (not_le.2 hs2)

/-- In a nontrivial real normed space, the complement of every open ball is nonempty. -/
theorem ball_compl_nonempty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] (x : E) (s : ℝ) : (ball x s)ᶜ.Nonempty := by
  obtain ⟨v, hv⟩ := NormedSpace.exists_lt_norm ℝ E |s|
  refine ⟨x + v, fun h => ?_⟩
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left] at h
  linarith [le_abs_self s]

/-- If `F n ≤ f` pointwise and `F n u = f u` eventually for each `u`, then the integral of `f`
is the supremum of the integrals of the `F n`. -/
theorem lintegral_eq_iSup_of_eventually_eq {α : Type*} [MeasurableSpace α] {m : Measure α}
    {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞}
    (hF : ∀ n, Measurable (F n)) (hle : ∀ n u, F n u ≤ f u)
    (hev : ∀ u, ∀ᶠ n in atTop, F n u = f u) :
    ∫⁻ u, f u ∂m = ⨆ n, ∫⁻ u, F n u ∂m := by
  refine le_antisymm ?_ (iSup_le fun n => lintegral_mono (hle n))
  have hlim : ∀ u, liminf (fun n => F n u) atTop = f u := fun u => by
    rw [liminf_congr (hev u), liminf_const]
  calc ∫⁻ u, f u ∂m = ∫⁻ u, liminf (fun n => F n u) atTop ∂m := by simp_rw [hlim]
    _ ≤ liminf (fun n => ∫⁻ u, F n u ∂m) atTop := lintegral_liminf_le hF
    _ ≤ ⨆ n, ∫⁻ u, F n u ∂m := liminf_le_iSup_nat _

/-- Convergence in measure sandwiches the limiting probability of a lower-tail event between
probabilities at slightly smaller and slightly larger thresholds. -/
theorem lowerTail_liminf_bounds_of_tendstoInMeasure {α : Type} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (hfg : TendstoInMeasure μ f atTop g) {a δ : ℝ} (hδ : 0 < δ) :
    μ {x | g x ≤ a} ≤ liminf (fun k => μ {x | f k x ≤ a + δ}) atTop ∧
      liminf (fun k => μ {x | f k x ≤ a + δ}) atTop ≤ μ {x | g x ≤ a + 2 * δ} := by
  have herr := (tendstoInMeasure_iff_dist.mp hfg) δ hδ
  have hlo : ∀ k, μ {x | g x ≤ a} ≤
      μ {x | f k x ≤ a + δ} + μ {x | δ ≤ dist (f k x) (g x)} := by
    intro k
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro x hx
    change g x ≤ a at hx
    by_cases h : δ ≤ dist (f k x) (g x)
    · exact Or.inr h
    · left
      change f k x ≤ a + δ
      have hdist : |f k x - g x| < δ := by simpa [Real.dist_eq] using lt_of_not_ge h
      have hh := abs_lt.mp hdist
      linarith
  have hhi : ∀ k, μ {x | f k x ≤ a + δ} ≤
      μ {x | g x ≤ a + 2 * δ} + μ {x | δ ≤ dist (f k x) (g x)} := by
    intro k
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro x hx
    change f k x ≤ a + δ at hx
    by_cases h : δ ≤ dist (f k x) (g x)
    · exact Or.inr h
    · left
      change g x ≤ a + 2 * δ
      have hdist : |f k x - g x| < δ := by simpa [Real.dist_eq] using lt_of_not_ge h
      have hh := abs_lt.mp hdist
      linarith
  constructor
  · have hlo' : ∀ᶠ k : ℕ in atTop, μ {x | g x ≤ a} ≤
        μ {x | f k x ≤ a + δ} + μ {x | δ ≤ dist (f k x) (g x)} := Eventually.of_forall hlo
    have h := liminf_le_liminf hlo'
    change liminf (fun _ : ℕ => μ {x | g x ≤ a}) atTop ≤
      liminf ((fun k => μ {x | f k x ≤ a + δ}) +
        (fun k => μ {x | δ ≤ dist (f k x) (g x)})) atTop at h
    rw [ENNReal.liminf_add_of_right_tendsto_zero herr] at h
    simpa using h
  · have hhi' : ∀ᶠ k : ℕ in atTop, μ {x | f k x ≤ a + δ} ≤
        μ {x | g x ≤ a + 2 * δ} + μ {x | δ ≤ dist (f k x) (g x)} := Eventually.of_forall hhi
    have h := liminf_le_liminf hhi'
    change liminf (fun k => μ {x | f k x ≤ a + δ}) atTop ≤
      liminf ((fun _ : ℕ => μ {x | g x ≤ a + 2 * δ}) +
        (fun k => μ {x | δ ≤ dist (f k x) (g x)})) atTop at h
    rw [ENNReal.liminf_add_of_right_tendsto_zero herr] at h
    simpa using h

/-- The analogous probability sandwich for upper-tail events. -/
theorem upperTail_liminf_bounds_of_tendstoInMeasure {α : Type} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (hfg : TendstoInMeasure μ f atTop g) {a δ : ℝ} (hδ : 0 < δ) :
    μ {x | a ≤ g x} ≤ liminf (fun k => μ {x | a - δ ≤ f k x}) atTop ∧
      liminf (fun k => μ {x | a - δ ≤ f k x}) atTop ≤ μ {x | a - 2 * δ ≤ g x} := by
  have hneg : TendstoInMeasure μ (fun k x => -f k x) atTop (fun x => -g x) := by
    apply tendstoInMeasure_iff_dist.mpr
    intro ε hε
    simpa only [dist_neg_neg] using (tendstoInMeasure_iff_dist.mp hfg) ε hε
  have h := lowerTail_liminf_bounds_of_tendstoInMeasure hneg (a := -a) hδ
  have h₁ : {x | -g x ≤ -a} = {x | a ≤ g x} := by ext x; simp
  have h₂ (k : ℕ) : {x | -f k x ≤ -a + δ} = {x | a - δ ≤ f k x} := by
    ext x
    simp only [mem_ofPred_eq]
    constructor <;> intro hx <;> linarith
  have h₃ : {x | -g x ≤ -a + 2 * δ} = {x | a - 2 * δ ≤ g x} := by
    ext x
    simp only [mem_ofPred_eq]
    constructor <;> intro hx <;> linarith
  simpa only [h₁, h₂, h₃] using h

/-- Lower-tail probabilities of a jointly measurable function are measurable in the
first variable. -/
theorem measurable_measure_joint_lowerTail {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β]
    {ν : Measure β} [SFinite ν] {F : Ω × β → ℝ} (hF : Measurable F) (a : ℝ) :
    Measurable (fun ω => ν {b | F (ω, b) ≤ a}) := by
  have hs : MeasurableSet {p : Ω × β | F p ≤ a} := measurableSet_le hF measurable_const
  exact measurable_measure_prodMk_left hs

/-- Upper-tail probabilities of a jointly measurable function are measurable in the
first variable. -/
theorem measurable_measure_joint_upperTail {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β]
    {ν : Measure β} [SFinite ν] {F : Ω × β → ℝ} (hF : Measurable F) (a : ℝ) :
    Measurable (fun ω => ν {b | a ≤ F (ω, b)}) := by
  have hs : MeasurableSet {p : Ω × β | a ≤ F p} := measurableSet_le measurable_const hF
  exact measurable_measure_prodMk_left hs

/-- A positive almost everywhere measurable function has vanishing lower tail at zero under a
finite measure: the masses of the sets `{f ≤ 1 / (n + 1)}` tend to zero. -/
theorem measure_le_inv_nat_tendsto_zero {α : Type} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (hf : AEMeasurable f μ)
    (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    Tendsto (fun n : ℕ => μ {x | f x ≤ 1 / ((n : ℝ) + 1)}) atTop (𝓝 0) := by
  let A : ℕ → Set α := fun n => {x | f x ≤ 1 / ((n : ℝ) + 1)}
  have hmeas : ∀ n, NullMeasurableSet (A n) μ := fun _ =>
    nullMeasurableSet_le hf aemeasurable_const
  have hanti : Antitone A := by
    intro n m hnm x hx
    change f x ≤ 1 / ((m : ℝ) + 1) at hx
    change f x ≤ 1 / ((n : ℝ) + 1)
    have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    exact le_trans hx (one_div_le_one_div_of_le (by positivity) hnm')
  have hinter : (⋂ n, A n) ⊆ {x | ¬ 0 < f x} := by
    intro x hx
    have hall : ∀ n : ℕ, f x ≤ 1 / ((n : ℝ) + 1) := fun n => mem_iInter.mp hx n
    have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hx0 : f x ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Eventually.of_forall hall)
    exact not_lt_of_ge hx0
  have hzero : μ (⋂ n, A n) = 0 := measure_mono_null hinter (ae_iff.mp hpos)
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top _ _⟩
  rw [hzero] at hlim
  exact hlim

/-- The masses of the sets `{n ≤ f}` tend to zero under a finite measure, for an almost
everywhere measurable real function `f`. -/
theorem measure_nat_le_tendsto_zero {α : Type} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (hf : AEMeasurable f μ) :
    Tendsto (fun n : ℕ => μ {x | (n : ℝ) ≤ f x}) atTop (𝓝 0) := by
  let A : ℕ → Set α := fun n => {x | (n : ℝ) ≤ f x}
  have hmeas : ∀ n, NullMeasurableSet (A n) μ := fun _ =>
    nullMeasurableSet_le aemeasurable_const hf
  have hanti : Antitone A := by
    intro n m hnm x hx
    change (m : ℝ) ≤ f x at hx
    change (n : ℝ) ≤ f x
    exact le_trans (Nat.cast_le.mpr hnm) hx
  have hempty : (⋂ n, A n) = ∅ := by
    apply eq_empty_of_forall_notMem
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt (f x)
    exact (not_le_of_gt hn) (mem_iInter.mp hx n)
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at hlim
  exact hlim

end LatticeProb.MeasureLiminfTails
