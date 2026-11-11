import Mathlib

/-!
# Almost sure limits preserve laws and independence

Let `X n → Xlim` almost surely. If all `X n` have the same law `μ`, then the law of `Xlim` is `μ`
(`LatticeProb.map_eq_of_tendsto_ae`). If `X n ⟂ Y n` for every `n` and `X n → Xlim`, `Y n → Ylim`
almost surely, then `Xlim ⟂ Ylim` (`LatticeProb.indepFun_of_tendsto_ae`).

Both statements are the almost sure form of facts that hold for convergence in distribution:
almost sure convergence implies convergence in distribution, convergence in distribution to a
constant-law limit is unique in law, and independence is characterised by the joint characteristic
functional. The proofs use Mathlib's `TendstoInDistribution` API for the first statement and the
characteristic-functional criterion `ProbabilityTheory.indepFun_iff_charFunDual_prod` for the second.

Literature: Billingsley, *Convergence of Probability Measures* (2nd ed.), §2 (weak convergence,
almost sure convergence implies convergence in distribution); Kallenberg, *Foundations of Modern
Probability* (2nd ed.), Ch. 3 (independence) and Ch. 4 (convergence of random sequences).
-/

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology Complex

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **An almost sure limit of identically distributed random variables has their common law.**
If `X n → Xlim` almost surely and every `X n` has law `μ`, then `Xlim` has law `μ`. The target is a
pseudometric space with its Borel σ-algebra; no tightness is assumed. -/
theorem map_eq_of_tendsto_ae {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [IsProbabilityMeasure P] {X : ℕ → Ω → E} {Xlim : Ω → E} {μ : Measure E}
    (hXm : ∀ n, AEMeasurable (X n) P) (hX : ∀ n, P.map (X n) = μ)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Xlim ω))) :
    P.map Xlim = μ := by
  have hXlimm : AEMeasurable Xlim P := aemeasurable_of_tendsto_metrizable_ae atTop hXm hlim
  -- almost sure convergence gives convergence in distribution to `Xlim`
  have h1 : TendstoInDistribution X atTop Xlim (fun _ => P) P :=
    tendstoInDistribution_of_ae_tendsto hXm hXlimm hlim
  -- the constant-in-law sequence converges in distribution to `X 0`
  have h2 : TendstoInDistribution X atTop (X 0) (fun _ => P) P :=
    tendstoInDistribution_of_identDistrib (μ := fun _ => P) 0
      (fun j => ⟨hXm 0, hXm j, (hX 0).trans (hX j).symm⟩) (IdentDistrib.refl (hXm 0))
  exact (tendstoInDistribution_unique X h1 h2).trans (hX 0)

/-- Convergence of characteristic functionals along an almost sure limit: for a continuous linear
functional `L` on a normed space `G`, the characteristic functionals `charFunDual (P.map (Z n)) L`
converge to `charFunDual (P.map Zlim) L`. The bound `|exp (i t)| = 1` and dominated convergence
pass the almost sure limit inside the integral. -/
theorem tendsto_charFunDual_of_tendsto_ae {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [IsProbabilityMeasure P] {Z : ℕ → Ω → G} {Zlim : Ω → G}
    (hZm : ∀ n, AEMeasurable (Z n) P) (hZlimm : AEMeasurable Zlim P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Z n ω) atTop (𝓝 (Zlim ω))) (L : G →L[ℝ] ℝ) :
    Tendsto (fun n => charFunDual (P.map (Z n)) L) atTop (𝓝 (charFunDual (P.map Zlim) L)) := by
  have hcont : Continuous (fun x : G => Complex.exp ((L x : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp L.continuous).mul continuous_const)
  have hmap : ∀ Y : Ω → G, AEMeasurable Y P →
      charFunDual (P.map Y) L = ∫ ω, Complex.exp ((L (Y ω) : ℂ) * Complex.I) ∂P := by
    intro Y hY
    rw [charFunDual_apply, integral_map hY hcont.aestronglyMeasurable]
  have hdct : Tendsto (fun n => ∫ ω, Complex.exp ((L (Z n ω) : ℂ) * Complex.I) ∂P) atTop
      (𝓝 (∫ ω, Complex.exp ((L (Zlim ω) : ℂ) * Complex.I) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => (hcont.measurable.comp_aemeasurable (hZm n)).aestronglyMeasurable) (integrable_const 1)
      (fun n => Eventually.of_forall fun ω => le_of_eq (Complex.norm_exp_ofReal_mul_I _)) ?_
    filter_upwards [hlim] with ω hω
    exact (hcont.tendsto (Zlim ω)).comp hω
  rw [hmap Zlim hZlimm]
  exact Tendsto.congr (fun n => (hmap (Z n) (hZm n)).symm) hdct

/-- **Independence passes to almost sure limits.** If `X n ⟂ Y n` for every `n`, and `X n → Xlim`
and `Y n → Ylim` almost surely, then `Xlim ⟂ Ylim`. The targets are separable Banach spaces, which is the
setting of Mathlib's characteristic-functional criterion `indepFun_iff_charFunDual_prod`. -/
theorem indepFun_of_tendsto_ae {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [SecondCountableTopology F]
    [MeasurableSpace F] [BorelSpace F]
    [IsProbabilityMeasure P] {X : ℕ → Ω → E} {Y : ℕ → Ω → F} {Xlim : Ω → E} {Ylim : Ω → F}
    (hXm : ∀ n, AEMeasurable (X n) P) (hYm : ∀ n, AEMeasurable (Y n) P)
    (hXlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Xlim ω)))
    (hYlim : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)))
    (hind : ∀ n, IndepFun (X n) (Y n) P) :
    IndepFun Xlim Ylim P := by
  have hXlimm : AEMeasurable Xlim P := aemeasurable_of_tendsto_metrizable_ae atTop hXm hXlim
  have hYlimm : AEMeasurable Ylim P := aemeasurable_of_tendsto_metrizable_ae atTop hYm hYlim
  have hpairm : ∀ n, AEMeasurable (fun ω => (X n ω, Y n ω)) P := fun n => (hXm n).prodMk (hYm n)
  have hpairlimm : AEMeasurable (fun ω => (Xlim ω, Ylim ω)) P := hXlimm.prodMk hYlimm
  have hpairlim : ∀ᵐ ω ∂P, Tendsto (fun n => (X n ω, Y n ω)) atTop (𝓝 (Xlim ω, Ylim ω)) := by
    filter_upwards [hXlim, hYlim] with ω h1 h2
    exact h1.prodMk_nhds h2
  rw [indepFun_iff_charFunDual_prod hXlimm hYlimm]
  intro L
  have hprod : ∀ n, charFunDual (P.map (fun ω => (X n ω, Y n ω))) L =
      charFunDual (P.map (X n)) (L.comp (ContinuousLinearMap.inl ℝ E F)) *
      charFunDual (P.map (Y n)) (L.comp (ContinuousLinearMap.inr ℝ E F)) :=
    fun n => (indepFun_iff_charFunDual_prod (hXm n) (hYm n)).1 (hind n) L
  have hA := tendsto_charFunDual_of_tendsto_ae hXm hXlimm hXlim (L.comp (ContinuousLinearMap.inl ℝ E F))
  have hB := tendsto_charFunDual_of_tendsto_ae hYm hYlimm hYlim (L.comp (ContinuousLinearMap.inr ℝ E F))
  have hJ := tendsto_charFunDual_of_tendsto_ae hpairm hpairlimm hpairlim L
  exact tendsto_nhds_unique (Tendsto.congr hprod hJ) (hA.mul hB)

end LatticeProb

end
