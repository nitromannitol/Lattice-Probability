/-
The Cramér-Wold device: an `E`-valued family of random vectors converges in
distribution as soon as every one-dimensional projection of it does.

The proof is Lévy's convergence theorem,
`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`, applied twice:
the characteristic function of the law of a vector at `t` is the characteristic
function at `1` of the law of its projection on `t`, so pointwise convergence of
the characteristic functions of the vectors is exactly pointwise convergence of
the characteristic functions of the projections.

The finite-dimensional laws of the scaling limits are indexed by `Fin m` and
carry the product measurable structure, not the Euclidean inner product, so the
device is also recorded on `Fin m → ℝ`, transported along the continuous linear
equivalence with `EuclideanSpace ℝ (Fin m)` by the continuous mapping theorem.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Complex

noncomputable section

namespace LatticeProb.CramerWold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The characteristic function of the law of a random vector at `t` is the
characteristic function at `1` of the law of its projection on `t`. -/
theorem charFun_map_inner {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → E) (hX : AEMeasurable X P) (t : E) :
    charFun (P.map X) t = charFun (P.map fun ω => (inner ℝ (X ω) t : ℝ)) 1 := by
  have hcont : Continuous fun x : E => (inner ℝ x t : ℝ) := by fun_prop
  have hXt : AEMeasurable (fun ω => (inner ℝ (X ω) t : ℝ)) P :=
    hcont.measurable.comp_aemeasurable hX
  rw [charFun_apply, charFun_apply_real, MeasureTheory.integral_map hX (by fun_prop),
    MeasureTheory.integral_map hXt (by fun_prop)]
  simp

/-- **The Cramér-Wold device.**  A sequence of random vectors in a finite
dimensional inner product space converges in distribution as soon as every
one-dimensional projection of it converges in distribution. -/
theorem tendstoInDistribution_of_forall_inner {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (X : ℕ → Ω → E) (Z : Ω' → E) (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hX : ∀ n, AEMeasurable (X n) P) (hZ : AEMeasurable Z Q)
    (h : ∀ t : E, TendstoInDistribution
        (fun (n : ℕ) (ω : Ω) => (inner ℝ (X n ω) t : ℝ)) atTop
        (fun ω => (inner ℝ (Z ω) t : ℝ)) (fun _ => P) Q) :
    TendstoInDistribution X atTop Z (fun _ => P) Q := by
  refine ⟨hX, hZ, ?_⟩
  rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t
  have h1 := (h t).tendsto
  rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun] at h1
  have h2 := h1 1
  have hgoal : (fun n : ℕ => charFun (P.map (X n)) t)
      = fun n : ℕ => charFun (P.map fun ω => (inner ℝ (X n ω) t : ℝ)) 1 := by
    funext n; exact charFun_map_inner P (X n) (hX n) t
  show Tendsto (fun n : ℕ => charFun (P.map (X n)) t) atTop (𝓝 (charFun (Q.map Z) t))
  rw [hgoal, charFun_map_inner Q Z hZ t]
  exact h2

/-- The Cramér-Wold device on `Fin m → ℝ` with the product measurable structure,
with the projections written as dot products. -/
theorem tendstoInDistribution_pi_of_forall_dot {m : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (X : ℕ → Ω → (Fin m → ℝ)) (Z : Ω' → (Fin m → ℝ))
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hX : ∀ n, AEMeasurable (X n) P) (hZ : AEMeasurable Z Q)
    (h : ∀ t : Fin m → ℝ, TendstoInDistribution
        (fun (n : ℕ) (ω : Ω) => ∑ i, X n ω i * t i) atTop
        (fun ω => ∑ i, Z ω i * t i) (fun _ => P) Q) :
    TendstoInDistribution X atTop Z (fun _ => P) Q := by
  set e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) := EuclideanSpace.equiv (Fin m) ℝ with he
  have key : TendstoInDistribution (fun (n : ℕ) (ω : Ω) => e.symm (X n ω)) atTop
      (fun ω => e.symm (Z ω)) (fun _ => P) Q := by
    refine tendstoInDistribution_of_forall_inner _ _ P Q
      (fun n => e.symm.continuous.measurable.comp_aemeasurable (hX n))
      (e.symm.continuous.measurable.comp_aemeasurable hZ) ?_
    intro t
    have ht := h (e t)
    have h1 : (fun (n : ℕ) (ω : Ω) => (inner ℝ (e.symm (X n ω)) t : ℝ))
        = fun (n : ℕ) (ω : Ω) => ∑ i, X n ω i * (e t) i := by
      funext n ω
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h2 : (fun ω : Ω' => (inner ℝ (e.symm (Z ω)) t : ℝ))
        = fun ω : Ω' => ∑ i, Z ω i * (e t) i := by
      funext ω
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [h1, h2]
    exact ht
  have hfin := key.continuous_comp (g := fun x : EuclideanSpace ℝ (Fin m) => e x) e.continuous
  simpa [Function.comp_def] using hfin

/-- The Cramér-Wold device on `Fin m → ℝ` along `atTop` on `ℝ`, the index the
scaling limits use. -/
theorem tendstoInDistribution_pi_atTop_of_forall_dot {m : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (X : ℝ → Ω → (Fin m → ℝ))
    (Z : Ω' → (Fin m → ℝ)) (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hX : ∀ R : ℝ, AEMeasurable (X R) P) (hZ : AEMeasurable Z Q)
    (h : ∀ t : Fin m → ℝ, TendstoInDistribution
        (fun (R : ℝ) (ω : Ω) => ∑ i, X R ω i * t i) atTop
        (fun ω => ∑ i, Z ω i * t i) (fun _ => P) Q) :
    TendstoInDistribution X atTop Z (fun _ => P) Q := by
  refine ⟨hX, hZ, ?_⟩
  rw [Filter.tendsto_iff_seq_tendsto]
  intro u hu
  exact (tendstoInDistribution_pi_of_forall_dot (fun n => X (u n)) Z P Q
    (fun n => hX (u n)) hZ (fun t => ⟨fun n => (h t).forall_aemeasurable (u n),
      (h t).aemeasurable_limit, (h t).tendsto.comp hu⟩)).tendsto

/-- Convergence in distribution to a law is convergence in distribution to any
random variable carrying that law. -/
theorem tendstoInDistribution_of_map_eq {ι F : Type*} {l : Filter ι} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace F] [TopologicalSpace F]
    [OpensMeasurableSpace F] {X : ι → Ω → F} {P : Measure Ω} [IsProbabilityMeasure P]
    {μ' : Measure F} [IsProbabilityMeasure μ'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    (h : TendstoInDistribution X l (id : F → F) (fun _ => P) μ')
    (Y : Ω' → F) (hY : AEMeasurable Y Q) (hmap : Q.map Y = μ') :
    TendstoInDistribution X l Y (fun _ => P) Q := by
  refine ⟨h.forall_aemeasurable, hY, ?_⟩
  have h2 : Q.map Y = μ'.map id := by rw [MeasureTheory.Measure.map_id]; exact hmap
  convert h.tendsto using 2
  exact Subtype.ext h2

end LatticeProb.CramerWold
