import Mathlib

/-!
# Markov property of a path in a random environment, as a conditional expectation

Let `κ : Kernel Ω W` be the quenched law of a random path `x ∈ W` in the environment `ω ∈ Ω`, `μ` the
law of the environment and `μ ⊗ₘ κ` the annealed law of `(ω, x)`.  Suppose that for almost every `ω`,
the path satisfies the Markov property at a deterministic time `n`, in set form: for events `π ⁻¹' E`
of the past (`π : W → T` the past, `τ : T → R` the present state) and measurable `B ⊆ W`,
`κ ω (π ⁻¹' E ∩ θ ⁻¹' B) = ∫⁻_{π ⁻¹' E} Q (ω, τ (π x)) B ∂κ ω`
(`θ : W → W` the shift of the path by `n` and `Q (ω, r)` the law of the path started from `r`).
Then for every bounded measurable `F : Ω × W → ℝ`
`E[F (ω, θ x) | σ(ω, π x)] = ∫ F (ω, y) ∂Q (ω, τ (π x))(y)` almost surely under the annealed law.

* `LatticeProb.setIntegral_comp_eq_of_markov`: the integral form of the set identity, for bounded
  measurable `g`.
* `LatticeProb.condExp_comp_eq_integral_kernel`: the conditional expectation statement.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LatticeProb

section Layer1

variable {W T R : Type*} [MeasurableSpace W] [MeasurableSpace T] [MeasurableSpace R]

/-- If a finite measure `P` is mapped by `θ` to its mixture of the laws `Q x`, integrals of bounded
measurable functions agree. -/
theorem integral_comp_eq_integral_kernel {P : Measure W} [IsFiniteMeasure P] {θ : W → W}
    (hθ : Measurable θ) (Q : Kernel W W) [IsMarkovKernel Q]
    (h : ∀ B, MeasurableSet B → P (θ ⁻¹' B) = ∫⁻ x, Q x B ∂P) {g : W → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : ∀ y, |g y| ≤ C) :
    ∫ x, g (θ x) ∂P = ∫ x, ∫ y, g y ∂Q x ∂P := by
  have hmap : P.map θ = Q ∘ₘ P := by
    refine Measure.ext fun B hB => ?_
    rw [Measure.map_apply hθ hB, h B hB, Measure.bind_apply hB Q.aemeasurable]
  have hint : Integrable (fun p : W × W => g p.2) (P ⊗ₘ Q) := by
    refine Integrable.of_bound (hg.comp measurable_snd).aestronglyMeasurable C
      (ae_of_all _ fun p => ?_)
    simpa [Real.norm_eq_abs] using hC p.2
  have hsnd : Q ∘ₘ P = (P ⊗ₘ Q).map Prod.snd := (Measure.snd_compProd P Q).symm
  calc ∫ x, g (θ x) ∂P = ∫ y, g y ∂(P.map θ) :=
        (integral_map hθ.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ y, g y ∂((P ⊗ₘ Q).map Prod.snd) := by rw [hmap, hsnd]
    _ = ∫ p, g p.2 ∂(P ⊗ₘ Q) := integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable
    _ = ∫ x, ∫ y, g y ∂Q x ∂P := Measure.integral_compProd hint

/-- Markov property in integral form on an event of the past. -/
theorem setIntegral_comp_eq_of_markov {P : Measure W} [IsFiniteMeasure P] {π : W → T}
    (hπ : Measurable π) {τ : T → R} (hτ : Measurable τ) {θ : W → W} (hθ : Measurable θ)
    (Q : Kernel R W) [IsMarkovKernel Q] {E : Set T}
    (h : ∀ B, MeasurableSet B →
      P (π ⁻¹' E ∩ θ ⁻¹' B) = ∫⁻ x in π ⁻¹' E, Q (τ (π x)) B ∂P)
    {g : W → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ y, |g y| ≤ C) :
    ∫ x in π ⁻¹' E, g (θ x) ∂P = ∫ x in π ⁻¹' E, ∫ y, g y ∂Q (τ (π x)) ∂P := by
  have hQ : Measurable fun x : W => τ (π x) := hτ.comp hπ
  have key := integral_comp_eq_integral_kernel (P := P.restrict (π ⁻¹' E)) hθ (Q.comap _ hQ)
    (fun B hB => by
      rw [Measure.restrict_apply (hθ hB), inter_comm, h B hB]
      simp only [Kernel.comap_apply]) hg hC
  simpa only [Kernel.comap_apply] using key

end Layer1

section Layer2

variable {Ω W T R : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace T]
  [MeasurableSpace R]

/-- **The Markov property of a path in a random environment as a conditional expectation.** -/
theorem condExp_comp_eq_integral_kernel {μ : Measure Ω} [IsProbabilityMeasure μ]
    (κ : Kernel Ω W) [IsMarkovKernel κ] {π : W → T} (hπ : Measurable π) {τ : T → R}
    (hτ : Measurable τ) {θ : W → W} (hθ : Measurable θ) (Q : Kernel (Ω × R) W)
    [IsMarkovKernel Q] {F : Ω × W → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ p, |F p| ≤ C)
    (hMk : ∀ᵐ ω ∂μ, ∀ E : Set T, MeasurableSet E → ∀ B : Set W, MeasurableSet B →
      κ ω (π ⁻¹' E ∩ θ ⁻¹' B) = ∫⁻ x in π ⁻¹' E, Q (ω, τ (π x)) B ∂κ ω) :
    (μ ⊗ₘ κ)[fun p : Ω × W => F (p.1, θ p.2) |
        MeasurableSpace.comap (fun p : Ω × W => (p.1, π p.2)) inferInstance]
      =ᵐ[μ ⊗ₘ κ] fun p : Ω × W => ∫ y, F (p.1, y) ∂Q (p.1, τ (π p.2)) := by
  have hproj : Measurable fun p : Ω × W => (p.1, π p.2) :=
    measurable_fst.prodMk (hπ.comp measurable_snd)
  have hGle : MeasurableSpace.comap (fun p : Ω × W => (p.1, π p.2))
      (inferInstance : MeasurableSpace (Ω × T)) ≤ (inferInstance : MeasurableSpace (Ω × W)) :=
    hproj.comap_le
  have hFθ : Measurable fun p : Ω × W => F (p.1, θ p.2) :=
    hF.comp (measurable_fst.prodMk (hθ.comp measurable_snd))
  have hint : Integrable (fun p : Ω × W => F (p.1, θ p.2)) (μ ⊗ₘ κ) :=
    Integrable.of_bound hFθ.aestronglyMeasurable C (ae_of_all _ fun p => by
      simpa [Real.norm_eq_abs] using hC _)
  have hg' : Measurable fun q : Ω × R => ∫ y, F (q.1, y) ∂Q q := by
    have hF' : StronglyMeasurable (Function.uncurry fun (q : Ω × R) (y : W) => F (q.1, y)) :=
      (hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
    exact (StronglyMeasurable.integral_kernel_prod_right (κ := Q) hF').measurable
  have hgm : Measurable[MeasurableSpace.comap (fun p : Ω × W => (p.1, π p.2)) inferInstance]
      fun p : Ω × W => ∫ y, F (p.1, y) ∂Q (p.1, τ (π p.2)) := by
    have : Measurable fun p : Ω × T => ∫ y, F (p.1, y) ∂Q (p.1, τ p.2) :=
      hg'.comp (measurable_fst.prodMk (hτ.comp measurable_snd))
    exact this.comp (comap_measurable _)
  have hgb : ∀ p : Ω × W, |∫ y, F (p.1, y) ∂Q (p.1, τ (π p.2))| ≤ C := fun p => by
    have := norm_integral_le_of_norm_le_const (μ := Q (p.1, τ (π p.2)))
      (f := fun y => F (p.1, y)) (C := C) (ae_of_all _ fun y => by
        simpa [Real.norm_eq_abs] using hC (p.1, y))
    simpa [Real.norm_eq_abs] using this
  have hgint : Integrable (fun p : Ω × W => ∫ y, F (p.1, y) ∂Q (p.1, τ (π p.2))) (μ ⊗ₘ κ) :=
    Integrable.of_bound (hgm.mono hGle le_rfl).aestronglyMeasurable C
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hgb p)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hGle hint
    (fun s _ _ => hgint.integrableOn) ?_ hgm.stronglyMeasurable.aestronglyMeasurable).symm
  intro A hA _
  obtain ⟨Cs, hCs, rfl⟩ := hA
  have hAm : MeasurableSet ((fun p : Ω × W => (p.1, π p.2)) ⁻¹' Cs) := hproj hCs
  have hsec : ∀ (ω : Ω) (φ : Ω × W → ℝ),
      ∫ x, ((fun p : Ω × W => (p.1, π p.2)) ⁻¹' Cs).indicator φ (ω, x) ∂κ ω =
        ∫ x in π ⁻¹' (Prod.mk ω ⁻¹' Cs), φ (ω, x) ∂κ ω := fun ω φ => by
    rw [← integral_indicator (hπ (measurable_prodMk_left hCs))]
    rfl
  rw [← integral_indicator hAm, ← integral_indicator hAm,
    Measure.integral_compProd (hgint.indicator hAm), Measure.integral_compProd (hint.indicator hAm)]
  refine integral_congr_ae ?_
  filter_upwards [hMk] with ω hω
  rw [hsec ω, hsec ω]
  have hEm : MeasurableSet (Prod.mk ω ⁻¹' Cs) := measurable_prodMk_left hCs
  have := setIntegral_comp_eq_of_markov (P := κ ω) hπ hτ hθ (Q.comap (fun r : R => (ω, r))
    measurable_prodMk_left) (E := Prod.mk ω ⁻¹' Cs) (fun B hB => by
      simpa only [Kernel.comap_apply] using hω _ hEm B hB)
    (g := fun y => F (ω, y)) (hF.comp (measurable_prodMk_left (x := ω))) (C := C)
    (fun y => hC _)
  simpa only [Kernel.comap_apply] using this.symm

end Layer2

end LatticeProb
