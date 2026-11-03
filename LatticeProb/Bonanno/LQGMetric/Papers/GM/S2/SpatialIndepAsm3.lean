/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepAsm3 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepAsm2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepOsc
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCentre

/-!
# GM Lemma 2.7, assembly: the good event `{𝔐_z ≤ A}` and the bound on its complement

Source: GM arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`, l. 979–994: on
the event `{𝔐_z ≤ A}` (`𝔐_z = sup_{B_{1+s/2}(z)} |𝔥 − h_{1+s}(z)|`, the centring of GM's event)
MQ Lemma 4.1 applies, and `P[𝔐_z > A] ≤ ε` uniformly in `z` and the configuration.

The good event is read off the `𝓕`-measurable variable `W_z = 𝔥 − h_R(z)` through countably many
radial-bump pairings: `Good = {|W_z(ψ_u)| ≤ A ∫ψ for u ∈ S ∩ B(z, ρ₂R)}` (`goodD`), with `S` a
countable dense set. Off a null set, `W_z(ψ_u) = (𝔥(u) − h_R(z)) ∫ψ` (mean value property), so
`Good` gives `|𝔥 − h_R(z)| ≤ A` on `B(z, ρ₂R)` by continuity (`pointwise_good`), and its complement
is covered by the oscillation event, a large offset `|h(ψ_z)/∫ψ − h_R(z)|` and a large
zero-boundary pairing `|h̊(ψ_z)|` (`pointwise_bad`, `prob_not_goodD_le`). Own elementary
bookkeeping around GM's argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric InnerProductSpace

namespace LQGMetric.GM

open Blueprint

/-- the good set: `|T(ψ_u)| ≤ A ∫ψ` for `u ∈ S ∩ B(x, ρ)` -/
def goodD (δ : ℝ) (hδ : 0 ≤ δ) (S : Set ℂ) (x : ℂ) (ρ A : ℝ) (T : DistC) : Prop :=
  ∀ u ∈ S, u ∈ ball x ρ → |T (radBump δ hδ u)| ≤ A * ∫ y, radProf δ y

lemma measurableSet_goodD {δ : ℝ} (hδ : 0 ≤ δ) {S : Set ℂ} (hS : S.Countable) (x : ℂ)
    (ρ A : ℝ) : MeasurableSet {T : DistC | goodD δ hδ S x ρ A T} := by
  have : {T : DistC | goodD δ hδ S x ρ A T} = ⋂ u ∈ S ∩ ball x ρ,
      {T : DistC | |T (radBump δ hδ u)| ≤ A * ∫ y, radProf δ y} := by
    ext T; simp [goodD, and_imp]
  rw [this]
  exact MeasurableSet.biInter (hS.mono inter_subset_left) fun u _ =>
    measurableSet_le (continuous_abs.measurable.comp (measurable_distOn_apply _)) measurable_const

lemma closedBall_sub_of_mem {x u : ℂ} {R ρ δ : ℝ} (hρδ : ρ + δ < R) (hu : u ∈ ball x ρ) :
    closedBall u δ ⊆ ball x R := by
  intro y hy
  rw [mem_closedBall] at hy
  rw [mem_ball] at hu ⊢
  linarith [dist_triangle y u x]

/-- the pairing of `𝔥 − c` with `ψ_u` -/
lemma pair_addConst_radBump {U : Opens ℂ} {g : ℂ → ℝ} (hg : HarmonicOnNhd g U) {Gω : DistC}
    (hrep : ∀ φ : TestOn U, restrictTo U Gω φ = ∫ y, g y * φ y) {δ : ℝ} (hδ : 0 < δ) {u : ℂ}
    (hB : closedBall u δ ⊆ U) (c : ℝ) :
    addConst Gω (-c) (radBump δ hδ.le u) = (g u - c) * ∫ y, radProf δ y := by
  rw [GFFInv.addConst_apply, integral_radBump, pair_radBump_of_harmonic hg hrep hδ hB]
  ring

/-- on the good set, `𝔥 − c` is represented on `B(x,R)` and bounded by `A` on `B(x, ρ₂R)` -/
theorem pointwise_good {U : Opens ℂ} {g : ℂ → ℝ} (hg : HarmonicOnNhd g U) {Gω : DistC}
    (hrep : ∀ φ : TestOn U, restrictTo U Gω φ = ∫ y, g y * φ y) {x : ℂ} {R ρ δ A c : ℝ}
    (hδ : 0 < δ) (hBU : ball x R ⊆ U) (hρδ : ρ + δ < R) {S : Set ℂ} (hS : Dense S)
    (hgood : goodD δ hδ.le S x ρ A (addConst Gω (-c))) :
    (∀ φ : TestOn (ballO x R), restrictTo (ballO x R) (addConst Gω (-c)) φ =
      ∫ y, (g y - c) * φ y) ∧ ∀ u ∈ ball x ρ, |g u - c| ≤ A := by
  have hcont : ∀ y ∈ ball x R, ContinuousAt g y := fun y hy => (hg y (hBU hy)).1.continuousAt
  have hI := integral_radProf_pos hδ
  refine ⟨rep_addConst hcont (rep_mono hBU hrep) c, ?_⟩
  refine abs_sub_le_of_dense hS (fun u hu => hcont u (ball_subset_ball (by linarith) hu))
    fun u huS hu => ?_
  have h1 := hgood u huS hu
  rw [pair_addConst_radBump hg hrep hδ ((closedBall_sub_of_mem hρδ hu).trans hBU), abs_mul,
    abs_of_pos hI] at h1
  exact le_of_mul_le_mul_right h1 hI

/-- off the good set: oscillation, a large offset, or a large zero-boundary pairing -/
theorem pointwise_bad {U : Opens ℂ} {g : ℂ → ℝ} (hg : HarmonicOnNhd g U) {Gω hzω h'ω : DistC}
    (hrep : ∀ φ : TestOn U, restrictTo U Gω φ = ∫ y, g y * φ y) (hdec : h'ω = Gω + hzω)
    {x : ℂ} {R ρ δ A : ℝ} (hδ : 0 < δ) (hBU : ball x R ⊆ U) (hρδ : ρ + δ < R) (hρ : 0 ≤ ρ)
    {S : Set ℂ} (hbad : ¬ goodD δ hδ.le S x ρ A (addConst Gω (-circleAvg h'ω R x))) :
    (∃ u ∈ ball x ρ, A / 2 < |g u - g x|) ∨ A / 4 < |offsetFun hδ.le R x h'ω| ∨
      A * (∫ y, radProf δ y) / 4 ≤ |hzω (radBump δ hδ.le x)| := by
  set c := circleAvg h'ω R x
  set I := ∫ y, radProf δ y
  have hI : 0 < I := integral_radProf_pos hδ
  simp only [goodD, not_forall, not_le, exists_prop] at hbad
  obtain ⟨u, -, hu, hlt⟩ := hbad
  rw [pair_addConst_radBump hg hrep hδ ((closedBall_sub_of_mem hρδ hu).trans hBU), abs_mul,
    abs_of_pos hI] at hlt
  have hA : A < |g u - c| := lt_of_mul_lt_mul_right hlt hI.le
  by_cases h1 : A / 2 < |g u - g x|
  · exact Or.inl ⟨u, hu, h1⟩
  right
  push Not at h1
  have hBx : closedBall x δ ⊆ U := by
    refine (fun y hy => hBU ?_)
    rw [mem_closedBall] at hy; rw [mem_ball]; linarith
  have hoff : offsetFun hδ.le R x h'ω = g x - c + hzω (radBump δ hδ.le x) / I := by
    simp only [offsetFun]
    rw [hdec]
    show (Gω (radBump δ hδ.le x) + hzω (radBump δ hδ.le x)) / I - circleAvg (Gω + hzω) R x = _
    rw [pair_radBump_of_harmonic hg hrep hδ hBx, ← hdec]
    field_simp
    ring
  have htri : |g u - c| ≤ |g u - g x| + |g x - c| := abs_sub_le _ _ _
  by_cases h2 : A / 4 < |offsetFun hδ.le R x h'ω|
  · exact Or.inl h2
  right
  push Not at h2
  have h3 : |g x - c| ≤ |offsetFun hδ.le R x h'ω| + |hzω (radBump δ hδ.le x)| / I := by
    have := abs_sub (g x - c + hzω (radBump δ hδ.le x) / I) (hzω (radBump δ hδ.le x) / I)
    rw [add_sub_cancel_right, abs_div, abs_of_pos hI] at this
    rwa [hoff]
  have h4 : A / 4 ≤ |hzω (radBump δ hδ.le x)| / I := by linarith
  rw [le_div_iff₀ hI] at h4
  linarith

end LQGMetric.GM
