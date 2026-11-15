import LatticeProb.Topology.FirstHitExitRadius

/-! # First-hit traces and nonnegative-time paths -/

set_option autoImplicit false

open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A first-hit trace and its centered nonnegative-time representation have the
same failure measure, provided the original curves are almost surely proper. -/
theorem measure_firstHit_failure_eq_nonnegativeTrace
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (η : Ω → ℝ → ℂ) (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin 2)))
    (Φ : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) (z : ℂ) (r R : ℝ)
    (hpath : ∀ᵐ ω ∂μ, Continuous (η ω) ∧
      Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧
      (∀ s, f ω s = Complex.orthonormalBasisOneI.repr
        (η ω (MatedCRTHarmonic.GMS4b.hitTime (η ω) z + s) - z)) ∧
      ∀ t : ℝ≥0, Φ ω t = f ω t) :
    μ {ω | ¬ ∃ w, ball w R ⊆ η ω '' Icc
      (MatedCRTHarmonic.GMS4b.hitTime (η ω) z)
      (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (η ω) z ≤ t ∧
        η ω t ∉ ball z r})} =
    μ {ω | ¬ ∃ w, ball w R ⊆ (fun t : ℝ => Φ ω t.toNNReal) '' Icc 0
      (sInf {t : ℝ | 0 ≤ t ∧ Φ ω t.toNNReal ∉ ball 0 r})} := by
  apply measure_congr
  filter_upwards [hpath] with ω hω
  have heq (t : ℝ) (ht : 0 ≤ t) : Φ ω t.toNNReal = f ω t := by
    rw [hω.2.2.2, Real.coe_toNNReal _ ht]
  have hset : {t : ℝ | 0 ≤ t ∧ Φ ω t.toNNReal ∉ ball 0 r} =
      {t : ℝ | 0 ≤ t ∧ f ω t ∉ ball 0 r} := by
    ext t
    simp only [mem_ofPred_eq]
    constructor <;> rintro ⟨ht, h⟩ <;> exact ⟨ht, by simpa only [heq t ht] using h⟩
  have himage : (fun t : ℝ => Φ ω t.toNNReal) ''
      Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ f ω t ∉ ball 0 r}) =
      f ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ f ω t ∉ ball 0 r}) := by
    apply image_congr
    intro t ht
    exact heq t ht.1
  have hb := firstHit_forwardExit_ball_iff (f ω) (η ω) z r R hω.1 hω.2.1 hω.2.2.1
  have hfin : openExitTime (fun s (_ : Unit) => f ω (0 + (s : ℝ))) (ball 0 r) () ≠ ⊤ := by
    have hproper := hω.2.1
    let t₀ := MatedCRTHarmonic.GMS4b.hitTime (η ω) z
    have hfproper : Tendsto (f ω) (cocompact ℝ) (cocompact _) := by
      have hshift := hω.2.2.1
      have hfun : (f ω : ℝ → EuclideanSpace ℝ (Fin 2)) =
          fun s => Complex.orthonormalBasisOneI.repr (η ω (t₀ + s) - z) := funext hshift
      rw [hfun]
      have htrans : Tendsto (fun w : ℂ => w - z) (cocompact ℂ) (cocompact ℂ) := by
        simpa [sub_eq_add_neg] using (Homeomorph.addRight (-z)).isClosedEmbedding.tendsto_cocompact
      exact Complex.orthonormalBasisOneI.repr.toHomeomorph.isClosedEmbedding.tendsto_cocompact.comp
        (htrans.comp (hproper.comp (Homeomorph.addLeft t₀).isClosedEmbedding.tendsto_cocompact))
    exact (openExitTime_ball_ne_top_of_tendsto_cocompact (f ω) hfproper 0 0 r).1
  rw [hset, himage]
  exact propext (not_congr (hb.symm.trans (and_iff_right hfin)))

end LatticeProb
