/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.TailTrivial at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.GermZeroOne
import Mathlib.Probability.StrongLaw

/-!
# Tail triviality for the increments of a Brownian motion (blueprint BM-tail)

For a process `A`, `incrFuture A s = σ(A (s + u) − A s : u ≥ 0)` and
`tailIncr A = ⋂_s incrFuture A s`.

* `isTrivialSigma_tailIncr`: for a pre-Brownian motion with measurable coordinates, the increment
  tail is trivial. Proof: the tail is contained in every `σ(B(s+·) − B s)`, hence (weak Markov
  property) independent of every `σ(B|[0,n])`, hence of their supremum, which contains the tail.
* `isTrivialSigma_tailIncr_drift`: the same for `c B_t + μ t`, whose increment σ-algebras are
  contained in those of `B`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace QuantumZipper
namespace TailTrivial

open GermZeroOne

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-! ## The large-time tail `⋂_t σ(B_u : u ≥ t)` -/

/-- Blumenthal's 0-1 law assuming only `B(1/(n+1)) → 0` a.s. instead of path continuity. -/
theorem isTrivialSigma_iInf_bmPast_of {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (h0 : ∀ᵐ ω ∂P, B 0 ω = 0)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => B (epsSeq n) ω) atTop (nhds 0)) :
    IsTrivialSigma (⨅ n, bmPast B (epsSeq n)) P := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
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
    have h := hB.indepFun_shift (epsSeq n)
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
    filter_upwards [h0, hlim] with ω h0 hl
    funext t
    symm
    refine Tendsto.limsup_eq ?_
    rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ t by positivity) with ht | ht
    · subst ht
      have : (fun n => B (max 0 (epsSeq n)) ω - B (epsSeq n) ω) = fun _ => 0 := by
        funext n; simp
      rw [this, h0]
      exact tendsto_const_nhds
    · have hev : ∀ᶠ n in atTop, epsSeq n ≤ t :=
        (tendsto_epsSeq.eventually (ge_mem_nhds ht)).mono fun n hn => hn
      have h2 := (tendsto_const_nhds (x := B t ω)).sub hl
      rw [sub_zero] at h2
      refine h2.congr' (hev.mono fun n hn => ?_)
      simp [max_eq_left hn]
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

/-- Strong law of large numbers for a pre-Brownian motion along the integers:
`B n / n → 0` a.s. -/
theorem ae_tendsto_div_nat {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * B n ω) atTop (nhds 0) := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set X : ℕ → Ω → ℝ := fun i ω => B ((i : ℝ≥0) + 1) ω - B i ω with hX
  have hXm : ∀ i, Measurable (X i) := fun i => (hBm _).sub (hBm _)
  have hlaw : ∀ i, P.map (X i) = gaussianReal 0 1 := by
    intro i
    have h := (hB.hasLaw_sub ((i : ℝ≥0) + 1) (i : ℝ≥0)).map_eq
    convert h using 2
    all_goals first
      | rfl
      | (apply NNReal.eq; simp [coe_nndist, Real.dist_eq])
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P :=
    fun i => ⟨(hXm i).aemeasurable, (hXm 0).aemeasurable, by rw [hlaw, hlaw]⟩
  have hindep : Pairwise fun i j => IndepFun (X i) (X j) P := by
    have key : ∀ i j : ℕ, i < j → IndepFun (X j) (X i) P := by
      intro i j hij
      set t₀ : ℝ≥0 := (i : ℝ≥0) + 1
      have hle : t₀ ≤ (j : ℝ≥0) := by
        simp only [t₀]; exact_mod_cast Nat.succ_le_of_lt hij
      have h := hB.indepFun_shift t₀
      have hφ : Measurable fun f : ℝ≥0 → ℝ =>
          f ((j : ℝ≥0) + 1 - t₀) - f ((j : ℝ≥0) - t₀) :=
        (measurable_pi_apply ((j : ℝ≥0) + 1 - t₀)).sub (measurable_pi_apply ((j : ℝ≥0) - t₀))
      have hψ : Measurable fun g : Set.Iic t₀ → ℝ =>
          g ⟨t₀, Set.mem_Iic.2 le_rfl⟩ - g ⟨(i : ℝ≥0), by simp [t₀]⟩ :=
        (measurable_pi_apply (⟨t₀, Set.mem_Iic.2 le_rfl⟩ : Set.Iic t₀)).sub
          (measurable_pi_apply (⟨(i : ℝ≥0), by simp [t₀]⟩ : Set.Iic t₀))
      have h2 := h.comp hφ hψ
      convert h2 using 1
      · funext ω
        simp only [Function.comp_apply, X]
        rw [add_tsub_cancel_of_le (hle.trans le_self_add), add_tsub_cancel_of_le hle]
        ring
      · funext ω
        simp [X, t₀]
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact (key i j h).symm
    · exact key j i h
  have hint : Integrable (X 0) P :=
    (hB.integrable_eval _).sub (hB.integrable_eval _)
  have hmean : P[X 0] = 0 := by
    rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _), hB.integral_eval,
      hB.integral_eval, sub_zero]
  have hslln := strong_law_ae X hint hindep hident
  filter_upwards [hslln, hB.eval_zero_ae_eq_zero] with ω hω h0
  rw [hmean] at hω
  refine hω.congr fun n => ?_
  have hs : ∑ i ∈ Finset.range n, X i ω = ∑ i ∈ Finset.range n,
      ((fun i : ℕ => B (i : ℝ≥0) ω) (i + 1) - (fun i : ℕ => B (i : ℝ≥0) ω) i) :=
    Finset.sum_congr rfl fun i _ => by simp [X]
  rw [smul_eq_mul, hs, Finset.sum_range_sub (fun i : ℕ => B (i : ℝ≥0) ω) n]
  simp [h0]

/-- The large-time tail σ-algebra `⋂_t σ(A_u : u ≥ t)` of a process. -/
def tailFar (A : ℝ≥0 → Ω → ℝ) : MeasurableSpace Ω :=
  ⨅ t : ℝ≥0, MeasurableSpace.comap (fun ω (u : Set.Ici t) => A u ω) inferInstance

/-- **Tail triviality of Brownian motion at large times.** -/
theorem isTrivialSigma_tailFar {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) : IsTrivialSigma (tailFar B) P := by
  set W : ℝ≥0 → Ω → ℝ := fun t ω => t * B (1 / t) ω with hW
  have hWB : IsPreBrownianReal W P := hB.inv
  have hWm : ∀ t, Measurable (W t) := fun t => (hBm _).const_mul _
  have hW0 : ∀ᵐ ω ∂P, W 0 ω = 0 := ae_of_all _ fun ω => by simp [W]
  have hWlim : ∀ᵐ ω ∂P, Tendsto (fun n => W (epsSeq n) ω) atTop (nhds 0) := by
    filter_upwards [ae_tendsto_div_nat hB hBm] with ω hω
    have h1 := (tendsto_add_atTop_iff_nat 1).2 hω
    refine h1.congr fun n => ?_
    simp only [W, epsSeq, one_div, inv_inv]
    push_cast
    ring
  refine (isTrivialSigma_iInf_bmPast_of hWB hWm hW0 hWlim).mono (le_iInf fun n => ?_)
  refine (iInf_le _ ((n : ℝ≥0) + 1)).trans (Measurable.comap_le (measurable_pi_of fun u => ?_))
  have hu0 : (u : ℝ≥0) ≠ 0 := by
    intro h; have := u.2; rw [Set.mem_Ici, h] at this
    exact absurd this (not_le.2 (by positivity))
  have hle : 1 / (u : ℝ≥0) ≤ epsSeq n := by
    rw [epsSeq, one_div]; exact inv_anti₀ (by positivity) u.2
  have e : (fun ω => B u ω) = fun ω => (u : ℝ) * W (1 / (u : ℝ≥0)) ω := by
    funext ω
    simp only [W, one_div, inv_inv]
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hu0), one_mul]
  show Measurable[bmPast W (epsSeq n)] fun ω => B u ω
  rw [e]
  exact (measurable_bmPast_coord (B := W) hle).const_mul _

/-- **Tail triviality at large times for Brownian motion with drift** `A_t = c B_t + μ t`. -/
theorem isTrivialSigma_tailFar_drift {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (c μ : ℝ) :
    IsTrivialSigma (tailFar fun t ω => c * B t ω + μ * (t : ℝ)) P := by
  refine (isTrivialSigma_tailFar hB hBm).mono (le_iInf fun t => (iInf_le _ t).trans ?_)
  exact Measurable.comap_le (measurable_pi_of fun u =>
    ((measurable_comap_coord (fun ω (u : Set.Ici t) => B u ω) u).const_mul c).add
      measurable_const)

end TailTrivial
end QuantumZipper
