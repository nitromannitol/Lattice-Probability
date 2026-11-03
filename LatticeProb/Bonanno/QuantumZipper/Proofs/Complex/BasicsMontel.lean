/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.BasicsMontel at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Sequences

/-!
# Montel's theorem (EXT-CA node A4)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3.A, node **A4**.

`montel`: a sequence of holomorphic functions on an open set `U ⊆ ℂ` that is uniformly bounded
on every compact subset of `U` has a subsequence converging locally uniformly on `U`; the limit
is holomorphic. Statement: R. B. Burckel, *Classical Analysis in the Complex Plane*
(Birkhäuser 2021), Corollary 7.6 (Montel 1907), p. 461 (PDF p. 486), for sequences on open
sets (Burckel states it for regions; connectedness is not used). Proof route: the classical
Arzelà–Ascoli argument (Ahlfors, *Complex Analysis*, 3rd ed. 1979, Ch. 5 §5 "Normal
families"; Burckel 7.6 goes through Vitali–Porter instead).

Proof: Cauchy estimates (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) and the mean value
inequality give a uniform local Lipschitz bound, hence equicontinuity; Arzelà–Ascoli
(`ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`) in the space `ℂ →ᵤ[𝔖] ℂ` of uniform
convergence on the compact subsets of `U` gives relative compactness; that space has a
countably generated uniformity (explicit compact exhaustion of `U`), hence compactness is
sequential; finally `TendstoLocallyUniformlyOn.differentiableOn`.
-/

noncomputable section

open Set Metric Filter Topology Uniformity UniformOnFun
open scoped UniformConvergence

namespace QuantumZipper.CA

/-- A family of holomorphic functions, uniformly bounded on compact subsets of `U`, is
uniformly Lipschitz near each point of `U` (Cauchy estimates). -/
theorem exists_uniform_lipschitz_near {U : Set ℂ} (hU : IsOpen U) {ι : Type*}
    {F : ι → ℂ → ℂ} (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖F n z‖ ≤ M) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ r > 0, ∃ C > 0, ∀ n, ∀ z ∈ ball z₀ r, ∀ w ∈ ball z₀ r, ‖F n z - F n w‖ ≤ C * ‖z - w‖ := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  set r := ε / 3 with hr
  have hr0 : 0 < r := by positivity
  have hsub : closedBall z₀ (2 * r) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hεU
  obtain ⟨M, hM⟩ := hb _ hsub (isCompact_closedBall _ _)
  set C := max M 0 / r + 1 with hC
  have hC0 : 0 < C := by positivity
  refine ⟨r, hr0, C, hC0, fun n z hz w hw => ?_⟩
  have hball_sub : ∀ x ∈ ball z₀ r, closedBall x r ⊆ closedBall z₀ (2 * r) := fun x hx y hy => by
    rw [mem_closedBall] at hy ⊢
    rw [mem_ball] at hx
    linarith [dist_triangle y x z₀]
  have hderiv : ∀ x ∈ ball z₀ r, ‖deriv (F n) x‖ ≤ C := by
    intro x hx
    have hd : DiffContOnCl ℂ (F n) (ball x r) :=
      ⟨(hF n).mono (ball_subset_closedBall.trans ((hball_sub x hx).trans hsub)),
        (hF n).continuousOn.mono (by
          rw [closure_ball x hr0.ne']; exact (hball_sub x hx).trans hsub)⟩
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 hd (C := max M 0) fun y hy =>
      (hM n y (hball_sub x hx (sphere_subset_closedBall hy))).trans (le_max_left _ _)
    exact h.trans (by rw [hC]; linarith)
  have hdiff : ∀ x ∈ ball z₀ r, DifferentiableAt ℂ (F n) x := fun x hx =>
    (hF n).differentiableAt (hU.mem_nhds (hsub (ball_subset_closedBall
      (ball_subset_ball (by linarith) hx))))
  exact (convex_ball z₀ r).norm_image_sub_le_of_norm_deriv_le hdiff hderiv hw hz

theorem equicontinuousAt_of_locally_bounded {U : Set ℂ} (hU : IsOpen U) {ι : Type*}
    {F : ι → ℂ → ℂ} (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖F n z‖ ≤ M) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    EquicontinuousAt F z₀ := by
  obtain ⟨r, hr, C, hC, hL⟩ := exists_uniform_lipschitz_near hU hF hb hz₀
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  refine ⟨min r (ε / C), lt_min hr (div_pos hε hC), fun x hx n => ?_⟩
  have hx1 : x ∈ ball z₀ r := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : dist x z₀ < ε / C := lt_of_lt_of_le hx (min_le_right _ _)
  rw [dist_eq_norm]
  calc ‖F n z₀ - F n x‖ ≤ C * ‖z₀ - x‖ := hL n z₀ (mem_ball_self hr) x hx1
    _ = C * dist x z₀ := by rw [← dist_eq_norm, dist_comm]
    _ < C * (ε / C) := by gcongr
    _ = ε := by field_simp

/-- An explicit compact exhaustion of an open set `U ⊆ ℂ`. -/
def exhaust (U : Set ℂ) (n : ℕ) : Set ℂ :=
  {z | ‖z‖ ≤ n ∧ ∀ w ∈ Uᶜ, 1 / ((n : ℝ) + 1) ≤ dist z w}

theorem exhaust_subset (U : Set ℂ) (n : ℕ) : exhaust U n ⊆ U := by
  intro z ⟨_, hz⟩
  by_contra h
  have := hz z h
  rw [dist_self] at this
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem isCompact_exhaust (U : Set ℂ) (n : ℕ) : IsCompact (exhaust U n) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h1 : IsClosed {z : ℂ | ‖z‖ ≤ n} := isClosed_le continuous_norm continuous_const
    have h2 : IsClosed {z : ℂ | ∀ w ∈ Uᶜ, 1 / ((n : ℝ) + 1) ≤ dist z w} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun w => isClosed_iInter fun _ =>
        isClosed_le continuous_const (continuous_id.dist continuous_const)
    exact h1.inter h2
  · exact (isBounded_closedBall (x := (0 : ℂ)) (r := n)).subset fun z hz => by
      simpa using hz.1

theorem exhaust_mono (U : Set ℂ) : Monotone (exhaust U) := by
  intro n m hnm z ⟨hz1, hz2⟩
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  refine ⟨hz1.trans hnm', fun w hw => le_trans ?_ (hz2 w hw)⟩
  gcongr

theorem exists_subset_exhaust {U : Set ℂ} (hU : IsOpen U) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) : ∃ n, K ⊆ exhaust U n := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hKU
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge R
  obtain ⟨n₂, hn₂⟩ := exists_nat_one_div_lt hδ
  refine ⟨max n₁ n₂, fun z hz => ⟨?_, fun w hw => ?_⟩⟩
  · have := hR hz
    rw [mem_closedBall, dist_zero_right] at this
    have : (n₁ : ℝ) ≤ (max n₁ n₂ : ℕ) := by exact_mod_cast le_max_left _ _
    linarith
  · by_contra hlt
    push Not at hlt
    have h2 : 1 / ((max n₁ n₂ : ℕ) + 1 : ℝ) ≤ 1 / ((n₂ : ℝ) + 1) := by
      gcongr; exact_mod_cast le_max_right _ _
    have hw' : w ∈ thickening δ K := by
      rw [mem_thickening_iff]
      exact ⟨z, hz, by rw [dist_comm]; linarith⟩
    exact hw (hδU hw')

/-- **Montel's theorem.** A sequence of holomorphic functions on an open set `U`, uniformly
bounded on each compact subset of `U`, has a subsequence converging locally uniformly on `U`
to a holomorphic function. -/
theorem montel {U : Set ℂ} (hU : IsOpen U) {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖F n z‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (f : ℂ → ℂ), StrictMono φ ∧ DifferentiableOn ℂ f U ∧
      TendstoLocallyUniformlyOn (fun k => F (φ k)) f atTop U := by
  set 𝔖 : Set (Set ℂ) := {K | IsCompact K ∧ K ⊆ U} with h𝔖
  have : IsCountablyGenerated (𝓤 (ℂ →ᵤ[𝔖] ℂ)) :=
    UniformOnFun.isCountablyGenerated_uniformity (α := ℂ) (β := ℂ) (𝔖 := 𝔖)
      (t := exhaust U) (fun n => ⟨isCompact_exhaust U n, exhaust_subset U n⟩)
      (exhaust_mono U) (fun K hK => exists_subset_exhaust hU hK.1 hK.2)
  set s : Set (ℂ →ᵤ[𝔖] ℂ) := range (fun n => UniformOnFun.ofFun 𝔖 (F n)) with hs
  have hcl : IsClosedEmbedding
      (UniformOnFun.ofFun 𝔖 ∘ (UniformOnFun.toFun 𝔖 : (ℂ →ᵤ[𝔖] ℂ) → ℂ → ℂ)) :=
    IsClosedEmbedding.id
  have hcpt : IsCompact (closure s) := by
    refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun K hK => hK.1) hcl ?_ ?_
    · intro K hK
      have hfam : (UniformOnFun.toFun 𝔖 ∘ ((↑) : s → (ℂ →ᵤ[𝔖] ℂ))) =
          F ∘ (fun i : s => i.2.choose) := by
        funext i
        exact (congrArg (UniformOnFun.toFun 𝔖) i.2.choose_spec).symm
      rw [hfam]
      intro x hx
      exact ((equicontinuousAt_of_locally_bounded hU hF hb (hK.2 hx)).comp
        (fun i : s => i.2.choose)).equicontinuousWithinAt K
    · intro K hK x hx
      obtain ⟨M, hM⟩ := hb {x} (singleton_subset_iff.2 (hK.2 hx)) isCompact_singleton
      refine ⟨closedBall 0 M, isCompact_closedBall _ _, ?_⟩
      rintro _ ⟨n, rfl⟩
      rw [mem_closedBall_zero_iff]
      exact hM n x rfl
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    hcpt.isSeqCompact (x := fun n => UniformOnFun.ofFun 𝔖 (F n))
      (fun n => subset_closure ⟨n, rfl⟩)
  have hunif := (UniformOnFun.tendsto_iff_tendstoUniformlyOn).1 hlim
  have hloc : TendstoLocallyUniformlyOn (fun k => F (φ k)) (UniformOnFun.toFun 𝔖 a) atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    exact hunif K ⟨hK, hKU⟩
  exact ⟨φ, UniformOnFun.toFun 𝔖 a, hφ,
    hloc.differentiableOn (Eventually.of_forall fun k => hF (φ k)) hU, hloc⟩

end QuantumZipper.CA
