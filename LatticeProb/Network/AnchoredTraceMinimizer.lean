/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: ReflectedGMS/Forms/AnchoredTraceMinimizer.lean.
-/
import LatticeProb.Network.WeightedGradient
import LatticeProb.Network.AnchoredEnergy
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Closed anchored gradient image

Let `G` be a conductance graph on a vertex type `V`, and let `A : Set V`. The edge space is the
Hilbert space `GradientSpace V = ℓ²(V × V)` of `Network/WeightedGradient.lean`, and the variation
space is `G.zeroTraceSubmodule A`, which contains every finite-energy function vanishing on `A`.
The graph may be disconnected, `A` may be infinite, and the functions need not have finite
support.

The file proves:

* the coordinate algebra of the normalized gradient `weightedGradientCoord G f`: it is additive,
  subtractive and homogeneous in `f`, and the gradient of `f` is determined by its coordinates;
  the squared `ℓ²` norm of the gradient is `G.Energy f`, the edge inner product of two gradients
  is `G.dirichletForm`, and energies add along a pair with zero Dirichlet form
  (`energy_add_of_dirichletForm_zero`);
* `zeroTraceGradient G A`, the submodule of `GradientSpace V` consisting of the gradients of the
  finite-energy functions vanishing on `A`;
* `isClosed_zeroTraceGradient` and `isComplete_zeroTraceGradient`: under `G.BoundaryAnchored A`,
  this submodule is closed, hence complete. The `ℓ²` convergence of gradients forces pointwise
  convergence of the potentials through the per-vertex bound `exists_vertex_energy_bound`, and the
  limiting potential has the limiting gradient as its own gradient.

`G.BoundaryAnchored A` fails when `A = ∅` and `V` is nonempty, so the closedness results say
nothing in that case. The example section checks the path `0 – 1 – 2` with `A = {0}`, which is
boundary-anchored, and applies `isClosed_zeroTraceGradient` and `isComplete_zeroTraceGradient`
to it.
-/

namespace LatticeProb.Network

open Filter Topology

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-! ### Coordinate algebra of the normalized gradient -/

/-- The normalized gradient of the zero function has every coordinate zero. -/
theorem weightedGradientCoord_zero (p : V × V) :
    weightedGradientCoord G (0 : V → ℝ) p = 0 := by
  simp only [weightedGradientCoord, Pi.zero_apply, sub_zero, mul_zero]

/-- The normalized gradient coordinates are additive in the function. -/
theorem weightedGradientCoord_add (f g : V → ℝ) (p : V × V) :
    weightedGradientCoord G (f + g) p =
      weightedGradientCoord G f p + weightedGradientCoord G g p := by
  simp only [weightedGradientCoord, Pi.add_apply]
  ring

/-- The normalized gradient coordinates are subtractive in the function. -/
theorem weightedGradientCoord_sub (f g : V → ℝ) (p : V × V) :
    weightedGradientCoord G (f - g) p =
      weightedGradientCoord G f p - weightedGradientCoord G g p := by
  simp only [weightedGradientCoord, Pi.sub_apply]
  ring

/-- The normalized gradient coordinates are homogeneous in the function. -/
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

/-- A vector of the edge space whose coordinates are gradient coordinates of a finite-energy
function `f` is the normalized gradient of `f`. -/
theorem weightedGradient_eq_of_coord {f : V → ℝ} (hf : G.HasFiniteEnergy f)
    (θ : GradientSpace V) (h : ∀ p, θ p = weightedGradientCoord G f p) :
    θ = weightedGradient G f hf :=
  lp.ext (funext h)

/-- The squared edge norm of such a vector is exactly the full energy. -/
theorem norm_sq_of_coord {f : V → ℝ} (θ : GradientSpace V)
    (h : ∀ p, θ p = weightedGradientCoord G f p) : ‖θ‖ ^ 2 = G.Energy f := by
  have hf : G.HasFiniteEnergy f := hasFiniteEnergy_of_coord G θ h
  rw [weightedGradient_eq_of_coord G hf θ h, weightedGradient_norm_sq]

/-- Normalized gradients are additive as vectors of the edge space. -/
theorem weightedGradient_add {f g : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hg : G.HasFiniteEnergy g) :
    weightedGradient G (f + g) (hf.add hg) =
      weightedGradient G f hf + weightedGradient G g hg := by
  refine lp.ext (funext fun p => ?_)
  rw [lp.coeFn_add]
  simp only [Pi.add_apply, weightedGradient_apply]
  ring

/-- The edge inner product of two normalized gradients is the Dirichlet form `G.dirichletForm`. -/
theorem inner_weightedGradient (f g : V → ℝ) (hf : G.HasFiniteEnergy f)
    (hg : G.HasFiniteEnergy g) :
    inner ℝ (weightedGradient G f hf) (weightedGradient G g hg) = G.dirichletForm f g := by
  rw [lp.inner_eq_tsum]
  have hterm : ∀ p : V × V,
      inner ℝ (weightedGradient G f hf p) (weightedGradient G g hg p) =
        G.gradProd f g p / 2 := by
    intro p
    simp only [RCLike.inner_apply, conj_trivial, weightedGradient_apply,
      ConductanceGraph.gradProd]
    rw [mul_mul_mul_comm,
      Real.mul_self_sqrt (div_nonneg (G.c_nonneg p.1 p.2) (by norm_num))]
    ring
  rw [tsum_congr hterm, tsum_div_const]
  rfl

/-- Energies add along an orthogonal decomposition of the full energy space: if the Dirichlet
form of `f` and `φ` vanishes, then `G.Energy (f + φ) = G.Energy f + G.Energy φ`. -/
theorem energy_add_of_dirichletForm_zero {f φ : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hφ : G.HasFiniteEnergy φ) (h0 : G.dirichletForm f φ = 0) :
    G.Energy (f + φ) = G.Energy f + G.Energy φ := by
  have hn := norm_add_sq_real (weightedGradient G f hf) (weightedGradient G φ hφ)
  rw [← weightedGradient_add G hf hφ, inner_weightedGradient, h0, mul_zero, add_zero] at hn
  rw [← weightedGradient_norm_sq G (f + φ) (hf.add hφ),
    ← weightedGradient_norm_sq G f hf, ← weightedGradient_norm_sq G φ hφ]
  exact hn

/-! ### The closed gradient image of the full zero-trace space -/

/-- The normalized gradient image of every finite-energy function vanishing on `A`, as a
submodule of `GradientSpace V`. -/
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

/-- The normalized gradient of each zero-trace finite-energy function lies in
`zeroTraceGradient`. -/
theorem weightedGradient_mem_zeroTraceGradient {A : Set V} {f : V → ℝ}
    (hf : f ∈ zeroTraceSubmodule G A) :
    weightedGradient G f hf.1 ∈ zeroTraceGradient G A :=
  ⟨f, hf, fun _ => rfl⟩

/-- **The gradient image of the full zero-trace space is closed.** The anchor-walk bound
turns `ℓ²` convergence of gradients into pointwise convergence of the potentials, and the
limiting potential has the limiting gradient as its own gradient. No connectedness, single
anchor, finite boundary, finite patch, or finite-support closure is used. -/
theorem isClosed_zeroTraceGradient {A : Set V} (hA : G.BoundaryAnchored A) :
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

/-- **The gradient image of the full zero-trace space is complete.** Under `G.BoundaryAnchored A`,
it is closed in the complete space `GradientSpace V`, hence complete. -/
theorem isComplete_zeroTraceGradient {A : Set V} (hA : G.BoundaryAnchored A) :
    IsComplete (zeroTraceGradient G A : Set (GradientSpace V)) :=
  (isClosed_zeroTraceGradient G hA).isComplete

/-! ## Example

The path `0 – 1 – 2` with unit conductances, from `Network/Conductance.lean`, with anchor set
`{0}`. Every vertex is joined to `0`, so `{0}` anchors the graph. -/

namespace ZeroTraceGradient.Example

/-- On the path `0 – 1 – 2` with anchor set `{0}`, the gradient image of the zero-trace space is
closed in `GradientSpace (Fin 3)`. -/
example : IsClosed (ConductanceGraph.zeroTraceGradient ConductanceGraph.Example.path3 {0} :
    Set (GradientSpace (Fin 3))) :=
  ConductanceGraph.isClosed_zeroTraceGradient ConductanceGraph.Example.path3
    ConductanceGraph.Example.boundaryAnchored_path3

/-- On the path `0 – 1 – 2` with anchor set `{0}`, the gradient image of the zero-trace space is
complete in `GradientSpace (Fin 3)`. -/
example : IsComplete (ConductanceGraph.zeroTraceGradient ConductanceGraph.Example.path3 {0} :
    Set (GradientSpace (Fin 3))) :=
  ConductanceGraph.isComplete_zeroTraceGradient ConductanceGraph.Example.path3
    ConductanceGraph.Example.boundaryAnchored_path3

end ZeroTraceGradient.Example

end ConductanceGraph

end LatticeProb.Network
