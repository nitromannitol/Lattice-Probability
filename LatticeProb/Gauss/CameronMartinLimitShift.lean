import Mathlib
import LatticeProb.Gauss.GaussianClosure
import LatticeProb.Gauss.CameronMartinDerived2

/-!
# Cameron-Martin shifts along limits in the Gaussian Hilbert space of a process

Let `Y = (Y t)_{t ∈ T}` be a centred Gaussian process. The Cameron-Martin theorem says that the law of `Y + m` is
absolutely continuous with respect to the law of `Y` whenever `m t = Cov(Y t, ξ)` for an element `ξ` of the Gaussian
Hilbert space of `Y`, the `L²` closure of the linear span of the `Y t` (Janson, *Gaussian Hilbert spaces*, Theorem 14.1;
Berestycki-Powell, *Gaussian free field and Liouville quantum gravity*, Theorem 1.29 for the Gaussian free field).
This file proves the direction used to transfer almost sure properties: null sets of the law of `Y` are null sets of
the law of `Y + m`.

* `isCentredGaussianSpace_span_range`: the linear span of a centred Gaussian process is a centred Gaussian space.
* `exists_ae_tendsto_subseq_of_cauchy_L2`: a sequence which is Cauchy in `L²` has a subsequence converging almost
  surely to a measurable limit.
* `map_shift_withDensity_eq_map`: for `q ∈ T`, under the tilt `dP'/dP = exp(-Y q - Var(Y q)/2)` the law of the whole
  family `(Y t + Cov(Y t, Y q))_t` on the product σ-algebra equals the law of `Y` under `P`.
* `measure_shift_eq_zero_of_tendsto_covariance`: if `(Y (q n))_n` is Cauchy in `L²` and `Cov(Y t, Y (q n)) → m t`
  for every `t`, then every measurable set of paths which `Y` avoids almost surely is avoided almost surely by `Y + m`.
-/

noncomputable section

namespace LatticeProb.Gauss

open MeasureTheory ProbabilityTheory Filter Topology
open LatticeProb.GaussianClosure
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The linear span of a centred Gaussian process is a centred Gaussian space. -/
theorem isCentredGaussianSpace_span_range [IsProbabilityMeasure P] {T : Type*} {Y : T → Ω → ℝ}
    (hY : IsGaussianProcess Y P) (hYm : ∀ t, Measurable (Y t)) (hcen : ∀ t, P[Y t] = 0) :
    IsCentredGaussianSpace P (Submodule.span ℝ (Set.range Y) : Submodule ℝ (Ω → ℝ)) := by
  classical
  intro W hW
  obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hW
  have hfun : (c.sum fun t a => a • Y t) = fun ω => ∑ t ∈ c.support, c t • Y t ω := by
    funext ω
    simp [Finsupp.sum, Finset.sum_apply]
  rw [hfun]
  have hmeas : Measurable fun ω => ∑ t ∈ c.support, c t • Y t ω :=
    Finset.measurable_sum _ fun t _ => (hYm t).const_smul (c t)
  have hG : HasGaussianLaw (fun ω => ∑ t ∈ c.support, c t • Y t ω) P :=
    (hY.smul c).hasGaussianLaw_fun_sum (I := c.support)
  have hmean : P[fun ω => ∑ t ∈ c.support, c t • Y t ω] = 0 := by
    have hint : ∀ t ∈ c.support, Integrable (fun ω => c t • Y t ω) P := fun t _ =>
      ((hY.hasGaussianLaw_eval t).memLp_two.integrable (by norm_num)).smul (c t)
    show ∫ ω, ∑ t ∈ c.support, c t • Y t ω ∂P = 0
    rw [integral_finsetSum _ hint]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [integral_smul, hcen t, smul_zero]
  have h := hG.map_eq_gaussianReal
  rw [hmean] at h
  exact ⟨hmeas, _, h⟩

/-- The squared `L²` norm of the class of a square integrable real function. -/
lemma norm_toLp_two_sq {g : Ω → ℝ} (hg : MemLp g 2 P) : ‖hg.toLp g‖ ^ 2 = ∫ ω, g ω ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with ω hω
  rw [hω]
  simp [pow_two]

/-- **Riesz-Fischer with an almost surely convergent subsequence.** A sequence of square integrable functions which is
Cauchy in `L²` has a subsequence converging almost everywhere to a measurable function. -/
theorem exists_ae_tendsto_subseq_of_cauchy_L2 {X : ℕ → Ω → ℝ} (hX : ∀ n, MemLp (X n) 2 P)
    (hcauchy : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k ≥ N, ∫ ω, (X n ω - X k ω) ^ 2 ∂P < ε) :
    ∃ (ξ : Ω → ℝ) (ns : ℕ → ℕ), Measurable ξ ∧ StrictMono ns ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => X (ns i) ω) atTop (𝓝 (ξ ω)) := by
  set F : ℕ → Lp ℝ 2 P := fun n => (hX n).toLp (X n) with hF
  have hcs : CauchySeq F := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hcauchy (ε ^ 2) (by positivity)
    refine ⟨N, fun n hn k hk => ?_⟩
    have hsq : ‖F n - F k‖ ^ 2 = ∫ ω, (X n ω - X k ω) ^ 2 ∂P := by
      rw [hF]
      simp only
      rw [← MemLp.toLp_sub (hX n) (hX k), norm_toLp_two_sq]
      rfl
    rw [dist_eq_norm]
    refine lt_of_pow_lt_pow_left₀ 2 hε.le ?_
    rw [hsq]
    exact hN n hn k hk
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcs
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hG).exists_seq_tendsto_ae
  refine ⟨G, ns, (Lp.stronglyMeasurable G).measurable, hns, ?_⟩
  have hrep : ∀ᵐ ω ∂P, ∀ n, F n ω = X n ω := ae_all_iff.2 fun n => (hX n).coeFn_toLp
  filter_upwards [hae, hrep] with ω hω hr
  exact hω.congr fun i => hr (ns i)

variable [IsProbabilityMeasure P]

/-- **Cameron-Martin tilt for the law of the whole process.** Under the tilt `dP'/dP = exp(-Y q - Var(Y q)/2)`, the
family `(Y t + Cov(Y t, Y q))_t` has the same law on the product σ-algebra of `T → ℝ` as `Y` under `P`. -/
theorem map_shift_withDensity_eq_map {T : Type*} {Y : T → Ω → ℝ} (hY : IsGaussianProcess Y P)
    (hYm : ∀ t, Measurable (Y t)) (hcen : ∀ t, P[Y t] = 0) (q : T) :
    (P.withDensity (fun x => ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2)))).map
        (fun x t => Y t x + cov[Y t, Y q; P])
      = P.map (fun x t => Y t x) := by
  classical
  have hF : Measurable (fun x t => Y t x) := measurable_pi_iff.2 hYm
  have hF' : Measurable (fun x t => Y t x + cov[Y t, Y q; P]) :=
    measurable_pi_iff.2 fun t => (hYm t).add_const _
  have hg : ∀ I : Finset T, Measurable (I.restrict : (T → ℝ) → ∀ i : I, ℝ) := fun I =>
    Measurable.of_eval fun i => measurable_pi_apply (i : T)
  have hP : IsProjectiveLimit (P.map fun x t => Y t x)
      (fun I : Finset T => P.map fun x (t : I) => Y t x) := by
    intro I
    rw [Measure.map_map (hg I) hF]
    rfl
  have hQ : IsProjectiveLimit
      ((P.withDensity (fun x => ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2)))).map
        (fun x t => Y t x + cov[Y t, Y q; P]))
      (fun I : Finset T => P.map fun x (t : I) => Y t x) := by
    intro I
    rw [Measure.map_map (hg I) hF']
    exact law_shift hY hYm hcen q (fun t => cov[Y t, Y q; P]) (fun _ => rfl) I
  exact IsProjectiveLimit.unique hQ hP

/-- **Cameron-Martin, null sets of the shifted law.** Let `Y` be a centred Gaussian process, `(Y (q n))_n` a sequence
of its coordinates which is Cauchy in `L²`, and `m t = lim_n Cov(Y t, Y (q n))`. Then every measurable set of paths
of probability zero for `Y` has probability zero for the shifted process `Y + m`. -/
theorem measure_shift_eq_zero_of_tendsto_covariance {T : Type*} {Y : T → Ω → ℝ} (hY : IsGaussianProcess Y P)
    (hYm : ∀ t, Measurable (Y t)) (hcen : ∀ t, P[Y t] = 0) (q : ℕ → T) (m : T → ℝ)
    (hcauchy : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k ≥ N, ∫ ω, (Y (q n) ω - Y (q k) ω) ^ 2 ∂P < ε)
    (hcov : ∀ t, Tendsto (fun n => cov[Y t, Y (q n); P]) atTop (𝓝 (m t)))
    {S : Set (T → ℝ)} (hS : MeasurableSet S) (h0 : P {ω | (fun t => Y t ω) ∈ S} = 0) :
    P {ω | (fun t => Y t ω + m t) ∈ S} = 0 := by
  classical
  obtain ⟨ξ, ns, hξm, hns, hae⟩ := exists_ae_tendsto_subseq_of_cauchy_L2
    (fun n => (hY.hasGaussianLaw_eval (q n)).memLp_two) hcauchy
  -- the Gaussian space spanned by the process and the limit `ξ`
  have hM0g : IsCentredGaussianSpace P (Submodule.span ℝ (Set.range Y) : Submodule ℝ (Ω → ℝ)) :=
    isCentredGaussianSpace_span_range hY hYm hcen
  have hYmem : ∀ t, Y t ∈ Submodule.span ℝ (Set.range Y) := fun t => Submodule.subset_span ⟨t, rfl⟩
  have hξlim : IsAeLimitOf P (Submodule.span ℝ (Set.range Y) : Submodule ℝ (Ω → ℝ)) ξ :=
    ⟨fun i => Y (q (ns i)), fun i => hYmem _, hae⟩
  have hM1g := isCentredGaussianSpace_sup_span hM0g hξm hξlim
  have hYmem1 : ∀ t, Y t ∈ Submodule.span ℝ (Set.range Y) ⊔ Submodule.span ℝ {ξ} := fun t =>
    Submodule.mem_sup_left (hYmem t)
  have hξmem1 : ξ ∈ Submodule.span ℝ (Set.range Y) ⊔ Submodule.span ℝ {ξ} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self ξ)
  -- the process with the limit adjoined
  obtain ⟨W, hWnone, hWsome⟩ : ∃ W : Option T → Ω → ℝ, W none = ξ ∧ ∀ t, W (some t) = Y t :=
    ⟨fun o => o.elim ξ Y, rfl, fun _ => rfl⟩
  have hWmem : ∀ o, W o ∈ Submodule.span ℝ (Set.range Y) ⊔ Submodule.span ℝ {ξ} := by
    intro o
    cases o with
    | none => rw [hWnone]; exact hξmem1
    | some t => rw [hWsome]; exact hYmem1 t
  have hWg : IsGaussianProcess W P := isGaussianProcess_of_isCentredGaussianSpace hM1g hWmem
  have hWm : ∀ o, Measurable (W o) := fun o => (hM1g _ (hWmem o)).1
  have hWcen : ∀ o, P[W o] = 0 := by
    intro o
    obtain ⟨hm, v, hv⟩ := hM1g _ (hWmem o)
    have h := integral_map (μ := P) hm.aemeasurable (aestronglyMeasurable_id (μ := P.map (W o)))
    simp only [id_eq] at h
    rw [← h, hv, integral_id_gaussianReal]
  have ha : ∀ t, cov[Y t, W none; P] = m t := by
    intro t
    rw [hWnone]
    have h1 : Tendsto (fun i => cov[Y t, Y (q (ns i)); P]) atTop (𝓝 cov[Y t, ξ; P]) :=
      tendsto_covariance_of_tendsto_ae hM1g (hYmem1 t) (fun i => hYmem1 _) hξmem1 hae
    have h2 : Tendsto (fun i => cov[Y t, Y (q (ns i)); P]) atTop (𝓝 (m t)) :=
      (hcov t).comp hns.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  have hlaw := map_shift_withDensity_eq_map hWg hWm hWcen none
  -- restriction to the original index set
  have hF : Measurable (fun x o => W o x) := measurable_pi_iff.2 hWm
  have hF' : Measurable (fun x o => W o x + cov[W o, W none; P]) :=
    measurable_pi_iff.2 fun o => (hWm o).add_const _
  have hr : Measurable (fun (f : Option T → ℝ) (t : T) => f (some t)) :=
    measurable_pi_iff.2 fun t => measurable_pi_apply (some t)
  have hS' : MeasurableSet ((fun (f : Option T → ℝ) (t : T) => f (some t)) ⁻¹' S) := hr hS
  have e1 : P.map (fun x o => W o x) ((fun (f : Option T → ℝ) (t : T) => f (some t)) ⁻¹' S) = 0 := by
    rw [Measure.map_apply hF hS']
    have hset : (fun x o => W o x) ⁻¹' ((fun (f : Option T → ℝ) (t : T) => f (some t)) ⁻¹' S)
        = {ω | (fun t => Y t ω) ∈ S} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hWsome]
    rw [hset]
    exact h0
  rw [← hlaw, Measure.map_apply hF' hS'] at e1
  have hset : (fun x o => W o x + cov[W o, W none; P]) ⁻¹'
      ((fun (f : Option T → ℝ) (t : T) => f (some t)) ⁻¹' S) = {ω | (fun t => Y t ω + m t) ∈ S} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hWsome, ha]
  rw [hset] at e1
  have hDm : Measurable fun x => ENNReal.ofReal (Real.exp (-W none x - Var[W none; P] / 2)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (((hWm none).neg).sub_const _))
  have hac : P ≪ P.withDensity (fun x => ENNReal.ofReal (Real.exp (-W none x - Var[W none; P] / 2))) :=
    withDensity_absolutelyContinuous' hDm.aemeasurable
      (ae_of_all _ fun x => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
  exact hac e1

end LatticeProb.Gauss

end
