/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.AnchoredTraceMinimizer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Analysis.AnchoredEnergy
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullNetworkForm
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Closed anchored gradient image and the full-energy trace minimizer

The edge Hilbert space is the existing `lp (fun _ : V × V => ℝ) 2` of `WeightedGradient`
and `FullNetworkForm`; the variation space is the existing `zeroTraceSubmodule` of
`AnchoredEnergy`, which contains **every** finite-energy function vanishing on the
prescribed boundary `A`. The graph may be disconnected, `A` may be infinite, and no
finite patch, finite support, or speed-`L²` restriction is imposed.

The gradient image of the variation space is closed: `ℓ²` convergence of the gradients
forces pointwise convergence of the potentials through the per-vertex anchor-walk bound
`exists_vertex_energy_bound`, and the limiting potential is recovered from the limiting
gradient coordinates. Projecting the gradient of an arbitrary supplied finite-energy
reference function onto this closed subspace gives existence and uniqueness of the energy
minimizer with that boundary trace, orthogonal to all zero-boundary finite-energy
variations.
-/

set_option autoImplicit false

namespace ReflectedGMS

open Filter Topology
open FullNetworkForm

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-! ### Coordinate algebra of the normalized gradient -/

theorem weightedGradientCoord_zero (p : V × V) :
    weightedGradientCoord G (0 : V → ℝ) p = 0 := by
  simp only [weightedGradientCoord, Pi.zero_apply, sub_zero, mul_zero]

theorem weightedGradientCoord_add (f g : V → ℝ) (p : V × V) :
    weightedGradientCoord G (f + g) p =
      weightedGradientCoord G f p + weightedGradientCoord G g p := by
  simp only [weightedGradientCoord, Pi.add_apply]
  ring

theorem weightedGradientCoord_sub (f g : V → ℝ) (p : V × V) :
    weightedGradientCoord G (f - g) p =
      weightedGradientCoord G f p - weightedGradientCoord G g p := by
  simp only [weightedGradientCoord, Pi.sub_apply]
  ring

theorem weightedGradientCoord_smul (a : ℝ) (f : V → ℝ) (p : V × V) :
    weightedGradientCoord G (a • f) p = a * weightedGradientCoord G f p := by
  simp only [weightedGradientCoord, Pi.smul_apply, smul_eq_mul]
  ring

/-- A vector of the edge space whose coordinates are gradient coordinates of `f` certifies
that `f` has full finite energy. -/
theorem hasFiniteEnergy_of_coord {f : V → ℝ} (θ : GradientSpace V)
    (h : ∀ p, θ p = weightedGradientCoord G f p) : G.HasFiniteEnergy f := by
  apply (weightedGradientCoord_mem_iff G f).1
  rw [← funext h]
  exact lp.memℓp θ

theorem weightedGradient_eq_of_coord {f : V → ℝ} (hf : G.HasFiniteEnergy f)
    (θ : GradientSpace V) (h : ∀ p, θ p = weightedGradientCoord G f p) :
    θ = weightedGradient G f hf :=
  lp.ext (funext h)

/-- The squared edge norm of such a vector is exactly the full energy. -/
theorem norm_sq_of_coord {f : V → ℝ} (θ : GradientSpace V)
    (h : ∀ p, θ p = weightedGradientCoord G f p) : ‖θ‖ ^ 2 = G.Energy f := by
  have hf : G.HasFiniteEnergy f := hasFiniteEnergy_of_coord G θ h
  rw [weightedGradient_eq_of_coord G hf θ h, weightedGradient_norm_sq]

/-- Gradients are additive as vectors of the edge space. -/
theorem weightedGradient_add {f g : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hg : G.HasFiniteEnergy g) :
    weightedGradient G (f + g) (hf.add hg) =
      weightedGradient G f hf + weightedGradient G g hg := by
  refine lp.ext (funext fun p => ?_)
  rw [lp.coeFn_add]
  simp only [Pi.add_apply, weightedGradient_apply]
  ring

/-- The edge inner product is the existing Dirichlet form. -/
theorem inner_weightedGradient (f g : V → ℝ) (hf : G.HasFiniteEnergy f)
    (hg : G.HasFiniteEnergy g) :
    inner ℝ (weightedGradient G f hf) (weightedGradient G g hg) = G.dirichletForm f g := by
  rw [lp.inner_eq_tsum]
  have hterm : ∀ p : V × V,
      inner ℝ (weightedGradient G f hf p) (weightedGradient G g hg p) =
        G.gradProd f g p / 2 := by
    intro p
    simp only [RCLike.inner_apply, conj_trivial, weightedGradient_apply,
      ReflectedWalk.ConductanceGraph.gradProd]
    rw [mul_mul_mul_comm,
      Real.mul_self_sqrt (div_nonneg (G.c_nonneg p.1 p.2) (by norm_num))]
    ring
  rw [tsum_congr hterm, tsum_div_const]
  rfl

/-- Energies add along an orthogonal decomposition of the full energy space. -/
theorem energy_add_of_dirichletForm_zero {f φ : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hφ : G.HasFiniteEnergy φ) (h0 : G.dirichletForm f φ = 0) :
    G.Energy (f + φ) = G.Energy f + G.Energy φ := by
  have hn := norm_add_sq_real (weightedGradient G f hf) (weightedGradient G φ hφ)
  rw [← weightedGradient_add G hf hφ, inner_weightedGradient, h0, mul_zero, add_zero] at hn
  rw [← weightedGradient_norm_sq G (f + φ) (hf.add hφ),
    ← weightedGradient_norm_sq G f hf, ← weightedGradient_norm_sq G φ hφ]
  exact hn

/-! ### The closed gradient image of the full zero-trace space -/

/-- The weighted-gradient image of every finite-energy function vanishing on `A`. -/
def zeroTraceGradient (A : Set V) : Submodule ℝ (GradientSpace V) where
  carrier := {θ | ∃ f ∈ zeroTraceSubmodule G A, ∀ p, θ p = weightedGradientCoord G f p}
  zero_mem' := by
    refine ⟨0, Submodule.zero_mem _, fun p => ?_⟩
    rw [weightedGradientCoord_zero]
    rfl
  add_mem' := by
    rintro θ η ⟨f, hf, hθ⟩ ⟨g, hg, hη⟩
    refine ⟨f + g, Submodule.add_mem _ hf hg, fun p => ?_⟩
    rw [weightedGradientCoord_add, ← hθ p, ← hη p, lp.coeFn_add]
    rfl
  smul_mem' := by
    rintro a θ ⟨f, hf, hθ⟩
    refine ⟨a • f, Submodule.smul_mem _ a hf, fun p => ?_⟩
    rw [weightedGradientCoord_smul, ← hθ p, lp.coeFn_smul]
    rfl

/-- Each zero-trace finite-energy variation contributes its gradient. -/
theorem weightedGradient_mem_zeroTraceGradient {A : Set V} {f : V → ℝ}
    (hf : f ∈ zeroTraceSubmodule G A) :
    weightedGradient G f hf.1 ∈ zeroTraceGradient G A :=
  ⟨f, hf, fun _ => rfl⟩

/-- **The gradient image of the full zero-trace space is closed.** The anchor-walk bound
turns `ℓ²` convergence of gradients into pointwise convergence of the potentials, and the
limiting potential has the limiting gradient as its own gradient. No connectedness, single
anchor, finite boundary, finite patch, or finite-support closure is used. -/
theorem isClosed_zeroTraceGradient {A : Set V} (hA : BoundaryAnchored G A) :
    IsClosed (zeroTraceGradient G A : Set (GradientSpace V)) := by
  refine IsSeqClosed.isClosed ?_
  intro u θ hu hconv
  choose f hfmem hfcoord using hu
  have hsub : ∀ n m : ℕ, ∀ p : V × V,
      (u n - u m) p = weightedGradientCoord G (f n - f m) p := by
    intro n m p
    rw [weightedGradientCoord_sub, ← hfcoord n p, ← hfcoord m p, lp.coeFn_sub]
    rfl
  have henergy : ∀ n m : ℕ, ‖u n - u m‖ ^ 2 = G.Energy (f n - f m) := fun n m =>
    norm_sq_of_coord G _ (hsub n m)
  have hcauchy : CauchySeq u := hconv.cauchySeq
  have hptCauchy : ∀ x : V, CauchySeq (fun n => f n x) := by
    intro x
    obtain ⟨C, hC0, hC⟩ := exists_vertex_energy_bound G hA x
    have hK0 : 0 ≤ C * Real.sqrt 2 := mul_nonneg hC0 (Real.sqrt_nonneg 2)
    have hbound : ∀ n m : ℕ, |f n x - f m x| ≤ (C * Real.sqrt 2) * ‖u n - u m‖ := by
      intro n m
      have hmem : f n - f m ∈ zeroTraceSubmodule G A :=
        Submodule.sub_mem _ (hfmem n) (hfmem m)
      have h1 := hC _ hmem
      have h2 : Real.sqrt (2 * G.Energy (f n - f m)) = Real.sqrt 2 * ‖u n - u m‖ := by
        rw [← henergy n m, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),
          Real.sqrt_sq (norm_nonneg _)]
      rw [h2] at h1
      calc |f n x - f m x| = |(f n - f m) x| := by simp only [Pi.sub_apply]
        _ ≤ C * (Real.sqrt 2 * ‖u n - u m‖) := h1
        _ = (C * Real.sqrt 2) * ‖u n - u m‖ := by ring
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hK1 : (0:ℝ) < C * Real.sqrt 2 + 1 := by linarith
    obtain ⟨N, hN⟩ :=
      Metric.cauchySeq_iff.1 hcauchy (ε / (C * Real.sqrt 2 + 1)) (by positivity)
    refine ⟨N, fun n hn m hm => ?_⟩
    have hd : ‖u n - u m‖ < ε / (C * Real.sqrt 2 + 1) := by
      have h := hN n hn m hm
      rwa [dist_eq_norm] at h
    have hstep : (C * Real.sqrt 2) * ‖u n - u m‖
        ≤ (C * Real.sqrt 2) * (ε / (C * Real.sqrt 2 + 1)) :=
      mul_le_mul_of_nonneg_left hd.le hK0
    have hlast : (C * Real.sqrt 2) * (ε / (C * Real.sqrt 2 + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ hK1]
      nlinarith
    calc dist (f n x) (f m x) = |f n x - f m x| := Real.dist_eq _ _
      _ ≤ (C * Real.sqrt 2) * ‖u n - u m‖ := hbound n m
      _ ≤ (C * Real.sqrt 2) * (ε / (C * Real.sqrt 2 + 1)) := hstep
      _ < ε := hlast
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hptCauchy x)
  have hcoord : ∀ p : V × V, θ p = weightedGradientCoord G g p := by
    intro p
    have h1 : Tendsto (fun n => u n p) atTop (𝓝 (θ p)) :=
      ((lp.evalCLM ℝ (fun _ : V × V => ℝ) 2 p).continuous.tendsto θ).comp hconv
    have h3 : Tendsto (fun n => weightedGradientCoord G (f n) p) atTop
        (𝓝 (weightedGradientCoord G g p)) := by
      simp only [weightedGradientCoord]
      exact Tendsto.const_mul _ ((hg p.2).sub (hg p.1))
    exact tendsto_nhds_unique h1 (h3.congr fun n => (hfcoord n p).symm)
  have hzero : ∀ a ∈ A, g a = 0 := by
    intro a ha
    refine tendsto_nhds_unique (hg a) ?_
    have hfa : (fun n => f n a) = fun _ : ℕ => (0:ℝ) :=
      funext fun n => (hfmem n).2 a ha
    rw [hfa]
    exact tendsto_const_nhds
  exact ⟨g, ⟨hasFiniteEnergy_of_coord G θ hcoord, hzero⟩, hcoord⟩

theorem isComplete_zeroTraceGradient {A : Set V} (hA : BoundaryAnchored G A) :
    IsComplete (zeroTraceGradient G A : Set (GradientSpace V)) :=
  (isClosed_zeroTraceGradient G hA).isComplete

/-! ### The full finite-energy minimizer with a supplied boundary trace -/

/-- **Existence of the anchored trace minimizer.** For an arbitrary supplied finite-energy
reference function `u`, there is a finite-energy function with the same trace on the whole
boundary `A` which is orthogonal to every zero-boundary finite-energy variation and
minimizes the full energy among all finite-energy functions with that trace. -/
theorem exists_anchored_trace_minimizer {A : Set V} (hA : BoundaryAnchored G A)
    {u : V → ℝ} (hu : G.HasFiniteEnergy u) :
    ∃ f : V → ℝ, G.HasFiniteEnergy f ∧ (∀ a ∈ A, f a = u a) ∧
      (∀ φ ∈ zeroTraceSubmodule G A, G.dirichletForm f φ = 0) ∧
      (∀ h : V → ℝ, G.HasFiniteEnergy h → (∀ a ∈ A, h a = u a) →
        G.Energy f ≤ G.Energy h) := by
  obtain ⟨w, hwK, hwmin⟩ :=
    (zeroTraceGradient G A).exists_norm_eq_iInf_of_complete_subspace
      (isComplete_zeroTraceGradient G hA) (weightedGradient G u hu)
  have horth : ∀ k ∈ zeroTraceGradient G A,
      inner ℝ (weightedGradient G u hu - w) k = 0 :=
    (Submodule.norm_eq_iInf_iff_real_inner_eq_zero _ hwK).1 hwmin
  obtain ⟨φ₀, hφ₀mem, hφ₀coord⟩ := hwK
  have hfE : G.HasFiniteEnergy (u - φ₀) := hu.sub hφ₀mem.1
  have hgrad : weightedGradient G (u - φ₀) hfE = weightedGradient G u hu - w := by
    refine (weightedGradient_eq_of_coord G hfE _ ?_).symm
    intro p
    rw [weightedGradientCoord_sub, ← hφ₀coord p, lp.coeFn_sub]
    rfl
  have hperp : ∀ φ ∈ zeroTraceSubmodule G A, G.dirichletForm (u - φ₀) φ = 0 := by
    intro φ hφ
    have h := horth _ (weightedGradient_mem_zeroTraceGradient G hφ)
    rwa [← hgrad, inner_weightedGradient] at h
  refine ⟨u - φ₀, hfE, ?_, hperp, ?_⟩
  · intro a ha
    simp only [Pi.sub_apply, hφ₀mem.2 a ha, sub_zero]
  · intro h hh htrace
    have hdiff : h - (u - φ₀) ∈ zeroTraceSubmodule G A := by
      refine ⟨hh.sub hfE, fun a ha => ?_⟩
      simp only [Pi.sub_apply, htrace a ha, hφ₀mem.2 a ha, sub_zero, sub_self]
    have hkey := energy_add_of_dirichletForm_zero G hfE hdiff.1 (hperp _ hdiff)
    have heq : (u - φ₀) + (h - (u - φ₀)) = h := by abel
    rw [heq] at hkey
    have hnn : 0 ≤ G.Energy (h - (u - φ₀)) := G.Energy_nonneg _
    linarith

/-- **Uniqueness and existence of the full-energy minimizer for a supplied trace.** The
competition class is every finite-energy function agreeing with the reference on the whole
boundary; no finite patch or finite-support restriction is present. -/
theorem existsUnique_anchored_trace_minimizer {A : Set V} (hA : BoundaryAnchored G A)
    {u : V → ℝ} (hu : G.HasFiniteEnergy u) :
    ∃! f : V → ℝ, G.HasFiniteEnergy f ∧ (∀ a ∈ A, f a = u a) ∧
      ∀ h : V → ℝ, G.HasFiniteEnergy h → (∀ a ∈ A, h a = u a) →
        G.Energy f ≤ G.Energy h := by
  obtain ⟨f, hfE, hftrace, hforth, hfmin⟩ := exists_anchored_trace_minimizer G hA hu
  refine ⟨f, ⟨hfE, hftrace, hfmin⟩, ?_⟩
  rintro f' ⟨hf'E, hf'trace, hf'min⟩
  have hEeq : G.Energy f' = G.Energy f :=
    le_antisymm (hf'min f hfE hftrace) (hfmin f' hf'E hf'trace)
  have hdiff : f' - f ∈ zeroTraceSubmodule G A := by
    refine ⟨hf'E.sub hfE, fun a ha => ?_⟩
    simp only [Pi.sub_apply, hf'trace a ha, hftrace a ha, sub_self]
  have hkey := energy_add_of_dirichletForm_zero G hfE hdiff.1 (hforth _ hdiff)
  have heq : f + (f' - f) = f' := by abel
  rw [heq] at hkey
  have hE0 : G.Energy (f' - f) = 0 := by linarith
  exact eq_of_eqOn_energy_sub_zero G hA hf'E hfE
    (fun a ha => by rw [hf'trace a ha, hftrace a ha]) hE0

end ReflectedGMS
