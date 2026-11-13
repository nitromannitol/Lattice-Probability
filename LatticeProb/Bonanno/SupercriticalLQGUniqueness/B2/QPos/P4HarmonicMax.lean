/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4HarmonicMax at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4OscExpect
import LatticeProb.Bonanno.LQGMetric.Gaussian.ConcentrationVector

 





















set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos.P4

 


theorem borellTIS_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    {X : Ω → Fin N → ℝ} (hn : (Finset.univ : Finset (Fin N)).Nonempty)
    (hX : HasGaussianLaw X P) (h0 : ∀ i, ∫ ω, X ω i ∂P = 0) {σ : ℝ} (hσ : 0 ≤ σ)
    (hvar : ∀ i, Var[fun ω => X ω i; P] ≤ σ ^ 2) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ Finset.univ.sup' hn (X ω) - ∫ ω', Finset.univ.sup' hn (X ω') ∂P} ≤
      Real.exp (-u ^ 2 / (2 * σ ^ 2)) := by
  have := hX.isProbabilityMeasure
  obtain ⟨v, hv, hmap⟩ := LQGMetric.GaussConc.exists_gramVec_of_centered hX h0
  have hvσ : ∀ i, ‖v i‖ ≤ ((⟨σ, hσ⟩ : ℝ≥0) : ℝ) := by
    intro i
    have h : ‖v i‖ ^ 2 ≤ σ ^ 2 := (hv i).trans_le (hvar i)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hσ two_ne_zero).1 h
  have hsc : Continuous fun x : Fin N → ℝ => Finset.univ.sup' hn x :=
    (LQGMetric.GaussConc.lipschitzWith_sup' hn).continuous
  have hm : ∫ ω', Finset.univ.sup' hn (X ω') ∂P =
      ∫ z, Finset.univ.sup' hn (LQGMetric.GaussConc.gramVec v z)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin N))) := by
    have hg : Measurable (LQGMetric.GaussConc.gramVec v) :=
      (LQGMetric.GaussConc.lipschitzWith_gramVec hvσ).continuous.measurable
    rw [← integral_map hX.aemeasurable hsc.aestronglyMeasurable, hmap,
      integral_map hg.aemeasurable hsc.aestronglyMeasurable]
  rw [hm]
  set m := ∫ z, Finset.univ.sup' hn (LQGMetric.GaussConc.gramVec v z)
    ∂(stdGaussian (EuclideanSpace ℝ (Fin N)))
  have hmeas : MeasurableSet {x : Fin N → ℝ | u ≤ Finset.univ.sup' hn x - m} :=
    measurableSet_le measurable_const (hsc.measurable.sub measurable_const)
  have e := LQGMetric.GaussConc.measureReal_preimage_eq hX hmap hmeas
  simp only [Set.preimage_setOf_eq] at e
  rw [e]
  exact LQGMetric.GaussConc.borellTIS_finiteMax hn v hvσ hu

 
def hfunCLM (n : ℕ) (S : Finset (DGFFSite n)) (c : DGFFSite n) :
    EuclideanSpace ℝ (DGFFSite n) →L[ℝ] ℝ :=
  if hc : c ∈ S then
    (EuclideanSpace.proj ⟨c, hc⟩ : EuclideanSpace ℝ {x // x ∈ S} →L[ℝ] ℝ).comp
      (boxHarmonicFieldCLM n (boxInnerOuterEquiv n S))
  else EuclideanSpace.proj c

theorem hfunCLM_apply (n : ℕ) (S : Finset (DGFFSite n)) (c : DGFFSite n)
    (h : EuclideanSpace ℝ (DGFFSite n)) : hfunCLM n S c h = hfun n S h c := by
  unfold hfunCLM
  by_cases hc : c ∈ S
  · rw [dif_pos hc, hfun_of_mem hc]; rfl
  · rw [dif_neg hc, hfun_of_not_mem hc]; rfl

theorem osc_nonneg (n : ℕ) (z : ℤ × ℤ) (k : ℕ) {A : Finset (DGFFSite n)} (hA : A.Nonempty)
    (h : EuclideanSpace ℝ (DGFFSite n)) : 0 ≤ osc n z k A h := by
  unfold osc
  have : Nonempty {c // c ∈ A} := ⟨⟨hA.choose, hA.choose_spec⟩⟩
  obtain ⟨c⟩ := this
  have h1 : hfun n (scaleSites n z k) h c.1 ≤ ⨆ c : {c // c ∈ A}, hfun n (scaleSites n z k) h c.1 :=
    le_ciSup (f := fun c : {c // c ∈ A} => hfun n (scaleSites n z k) h c.1)
      (Set.finite_range _).bddAbove c
  have h2 : -hfun n (scaleSites n z k) h c.1 ≤
      ⨆ c : {c // c ∈ A}, -hfun n (scaleSites n z k) h c.1 :=
    le_ciSup (f := fun c : {c // c ∈ A} => -hfun n (scaleSites n z k) h c.1)
      (Set.finite_range _).bddAbove c
  linarith

theorem osc_integrable (n : ℕ) (z : ℤ × ℤ) (k : ℕ) {A : Finset (DGFFSite n)}
    (hA : A.Nonempty) : Integrable (osc n z k A) (boxDGFF n) := by
  haveI : Nonempty {c // c ∈ A} := ⟨⟨hA.choose, hA.choose_spec⟩⟩
  unfold osc
  apply Integrable.add
  · apply integrable_iSup_fin
    · intro c; exact (hfun_memLp n _ c.1).integrable one_le_two
    · intro c; exact (hfun_continuous n _ c.1).measurable
  · apply integrable_iSup_fin
    · intro c; exact ((hfun_memLp n _ c.1).integrable one_le_two).neg
    · intro c; exact (hfun_continuous n _ c.1).measurable.neg

 
def oscMeanConst : ℝ := 120 * Real.sqrt 5 * Real.sqrt coarseVarConst

theorem oscMeanConst_nonneg : 0 ≤ oscMeanConst := by unfold oscMeanConst; positivity

 

theorem harmonic_osc_sum_tail (n : ℕ) (z : ℤ × ℤ) (W : Finset ℕ) (hWne : W.Nonempty)
    (hW : ∀ k ∈ W, GoodScale n z k) (A : ℕ → Finset (DGFFSite n))
    (hA : ∀ k ∈ W, (A k).Nonempty) (hreg : ∀ k ∈ W, ∀ c ∈ A k, inReg n z k c)
    {u : ℝ} (hu : 0 ≤ u) :
    (boxDGFF n).real {h | (W.card : ℝ) * oscMeanConst + u ≤ ∑ k ∈ W, osc n z k (A k) h} ≤
      Real.exp (-u ^ 2 / (2 * (14 * coarseVarConst * W.card))) := by
  classical
  
  set Ch := {f : W → DGFFSite n × DGFFSite n // ∀ k, (f k).1 ∈ A k.1 ∧ (f k).2 ∈ A k.1}
  have hk0 : ∃ k₀, k₀ ∈ W := hWne
  obtain ⟨k₀, hk₀⟩ := hk0
  have hChne : Nonempty Ch := by
    refine ⟨⟨fun k => ((hA k.1 k.2).choose, (hA k.1 k.2).choose), fun k =>
      ⟨(hA k.1 k.2).choose_spec, (hA k.1 k.2).choose_spec⟩⟩⟩
  set M := Fintype.card Ch
  have hM : 0 < M := Fintype.card_pos
  set eC : Ch ≃ Fin M := Fintype.equivFin Ch
  have hn : (Finset.univ : Finset (Fin M)).Nonempty := ⟨⟨0, hM⟩, Finset.mem_univ _⟩
  
  set Y : Ch → EuclideanSpace ℝ (DGFFSite n) → ℝ := fun f h =>
    ∑ k : W, incrK n z k.1 (f.1 k).1 (f.1 k).2 h
  set T : EuclideanSpace ℝ (DGFFSite n) →L[ℝ] (Fin M → ℝ) :=
    ContinuousLinearMap.pi fun m => ∑ k : W,
      (hfunCLM n (scaleSites n z k.1) ((eC.symm m).1 k).1 -
        hfunCLM n (scaleSites n z k.1) ((eC.symm m).1 k).2)
  set X : EuclideanSpace ℝ (DGFFSite n) → Fin M → ℝ := fun h => T h
  have hXY : ∀ h m, X h m = Y (eC.symm m) h := by
    intro h m
    simp only [X, T, Y, ContinuousLinearMap.pi_apply, ContinuousLinearMap.coe_sum',
      Finset.sum_apply, ContinuousLinearMap.sub_apply, hfunCLM_apply, incrK]
  have hG : IsGaussian (boxDGFF n) := by
    unfold boxDGFF WiredConductances.gaussianOfPrecision
    infer_instance
  have hXG : HasGaussianLaw X (boxDGFF n) :=
    (IsGaussian.hasGaussianLaw_id (μ := boxDGFF n)).map_fun T
  have h0 : ∀ m, ∫ h, X h m ∂(boxDGFF n) = 0 := by
    intro m
    have hi : Integrable (fun h : EuclideanSpace ℝ (DGFFSite n) => h) (boxDGFF n) :=
      IsGaussian.integrable_id
    have := ((ContinuousLinearMap.proj m).comp T).integral_comp_comm hi
    rw [boxDGFF_mean, map_zero] at this
    exact this
  
  have hsup : ∀ h, Finset.univ.sup' hn (X h) =
      ∑ k ∈ W, osc n z k (A k) h := by
    intro h
    rw [Finset.sup'_univ_eq_ciSup]
    simp_rw [hXY]
    rw [eC.symm.iSup_comp (g := fun f => Y f h)]
    apply le_antisymm
    · apply ciSup_le
      intro f
      simp only [Y]
      rw [← Finset.sum_coe_sort W (fun k => osc n z k (A k) h)]
      apply Finset.sum_le_sum
      intro k _
      unfold incrK osc
      have hbdd1 := (Set.finite_range fun c : {c // c ∈ A k.1} =>
        hfun n (scaleSites n z k.1) h c.1).bddAbove
      have hbdd2 := (Set.finite_range fun c : {c // c ∈ A k.1} =>
        -hfun n (scaleSites n z k.1) h c.1).bddAbove
      have e1 := le_ciSup hbdd1 ⟨(f.1 k).1, (f.2 k).1⟩
      have e2 := le_ciSup hbdd2 ⟨(f.1 k).2, (f.2 k).2⟩
      simp only at e1 e2
      linarith
    · 
      have hopt : ∀ k : W, ∃ c₁ ∈ A k.1, ∃ c₂ ∈ A k.1,
          hfun n (scaleSites n z k.1) h c₁ - hfun n (scaleSites n z k.1) h c₂ =
            osc n z k.1 (A k.1) h := by
        intro k
        haveI : Nonempty {c // c ∈ A k.1} := ⟨⟨(hA k.1 k.2).choose, (hA k.1 k.2).choose_spec⟩⟩
        obtain ⟨c₁, hc₁⟩ := exists_eq_ciSup_of_finite (f := fun c : {c // c ∈ A k.1} =>
          hfun n (scaleSites n z k.1) h c.1)
        obtain ⟨c₂, hc₂⟩ := exists_eq_ciSup_of_finite (f := fun c : {c // c ∈ A k.1} =>
          -hfun n (scaleSites n z k.1) h c.1)
        refine ⟨c₁.1, c₁.2, c₂.1, c₂.2, ?_⟩
        unfold osc
        rw [← hc₁, ← hc₂]
        ring
      choose c₁ hc₁ c₂ hc₂ hceq using hopt
      set fstar : Ch := ⟨fun k => (c₁ k, c₂ k), fun k => ⟨hc₁ k, hc₂ k⟩⟩
      have hY : Y fstar h = ∑ k ∈ W, osc n z k (A k) h := by
        simp only [Y, fstar, incrK]
        rw [← Finset.sum_coe_sort W (fun k => osc n z k (A k) h)]
        exact Finset.sum_congr rfl fun k _ => hceq k
      rw [← hY]
      exact le_ciSup (f := fun f => Y f h) (Set.finite_range _).bddAbove fstar
  
  have hint : ∫ h, ∑ k ∈ W, osc n z k (A k) h ∂(boxDGFF n) ≤ (W.card : ℝ) * oscMeanConst := by
    rw [integral_finset_sum _ fun k hk => osc_integrable n z k (hA k hk)]
    calc ∑ k ∈ W, ∫ h, osc n z k (A k) h ∂(boxDGFF n) ≤ ∑ _k ∈ W, oscMeanConst :=
          Finset.sum_le_sum fun k hk => integral_osc_le (hW k hk) (hA k hk) (hreg k hk)
      _ = (W.card : ℝ) * oscMeanConst := by rw [Finset.sum_const, nsmul_eq_mul]
  
  have hV0 : 0 ≤ 14 * coarseVarConst * W.card := by
    have := coarseVarConst_pos; positivity
  have hvar : ∀ m, Var[fun h => X h m; boxDGFF n] ≤
      (Real.sqrt (14 * coarseVarConst * W.card)) ^ 2 := by
    intro m
    rw [Real.sq_sqrt hV0]
    set f := eC.symm m
    set uf : ℕ → DGFFSite n := fun k => if hk : k ∈ W then (f.1 ⟨k, hk⟩).1 else (f.1 ⟨k₀, hk₀⟩).1
    set vf : ℕ → DGFFSite n := fun k => if hk : k ∈ W then (f.1 ⟨k, hk⟩).2 else (f.1 ⟨k₀, hk₀⟩).2
    have hXf : (fun h => X h m) = fun h => ∑ k ∈ W, incrK n z k (uf k) (vf k) h := by
      funext h
      rw [hXY]
      simp only [Y]
      rw [← Finset.sum_coe_sort W (fun k => incrK n z k (uf k) (vf k) h)]
      apply Finset.sum_congr rfl
      intro k _
      simp only [uf, vf, dif_pos k.2]
      rfl
    rw [hXf]
    apply var_sum_scales_le n z W hW uf vf
    · intro k hk; simp only [uf, dif_pos hk]; exact hreg k hk _ (f.2 ⟨k, hk⟩).1
    · intro k hk; simp only [vf, dif_pos hk]; exact hreg k hk _ (f.2 ⟨k, hk⟩).2
  have hB := borellTIS_le hn hXG h0
    (Real.sqrt_nonneg _) hvar hu
  rw [Real.sq_sqrt hV0] at hB
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hB
  intro h hh
  simp only [Set.mem_setOf_eq] at hh ⊢
  rw [hsup h]
  have : ∫ ω', Finset.univ.sup' hn (X ω') ∂(boxDGFF n) =
      ∫ h, ∑ k ∈ W, osc n z k (A k) h ∂(boxDGFF n) := by
    congr 1; funext h; exact hsup h
  rw [this]
  linarith

 



theorem harmonic_osc_count (δ : ℝ) (hδ : 0 < δ) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (n : ℕ) (z : ℤ × ℤ) (W : Finset ℕ) (K : ℕ),
      W.Nonempty → W.card ≤ K → (∀ k ∈ W, GoodScale n z k) →
      ∀ A : ℕ → Finset (DGFFSite n), (∀ k ∈ W, (A k).Nonempty) →
      (∀ k ∈ W, ∀ c ∈ A k, inReg n z k c) →
      boxDGFF n {h | δ * K / 4 < ((W.filter fun k => C₂ < osc n z k (A k) h).card : ℝ)} ≤
        ENNReal.ofReal ((1 / 8 : ℝ) ^ K) := by
  have hv := coarseVarConst_pos
  set a : ℝ := Real.sqrt (84 * coarseVarConst * Real.log 2)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 84 * coarseVarConst * Real.log 2 :=
    Real.sq_sqrt (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity)
  refine ⟨4 * (oscMeanConst + a) / δ + 1, by have := oscMeanConst_nonneg; positivity, ?_⟩
  intro n z W K hWne hWK hW A hA hreg
  set C₂ := 4 * (oscMeanConst + a) / δ + 1
  have hK : 1 ≤ K := le_trans (Finset.card_pos.mpr hWne) hWK
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hWpos : (0 : ℝ) < W.card := by exact_mod_cast Finset.card_pos.mpr hWne
  have hWK' : (W.card : ℝ) ≤ K := by exact_mod_cast hWK
  
  have hsub : {h | δ * K / 4 < ((W.filter fun k => C₂ < osc n z k (A k) h).card : ℝ)} ⊆
      {h | (W.card : ℝ) * oscMeanConst + a * K ≤ ∑ k ∈ W, osc n z k (A k) h} := by
    intro h hh
    simp only [Set.mem_setOf_eq] at hh ⊢
    set F := W.filter fun k => C₂ < osc n z k (A k) h
    have h1 : (F.card : ℝ) * C₂ ≤ ∑ k ∈ F, osc n z k (A k) h := by
      have := Finset.card_nsmul_le_sum F (fun k => osc n z k (A k) h) C₂
        (fun k hk => (Finset.mem_filter.mp hk).2.le)
      rw [nsmul_eq_mul] at this
      exact this
    have h2 : ∑ k ∈ F, osc n z k (A k) h ≤ ∑ k ∈ W, osc n z k (A k) h :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun k hk _ => osc_nonneg n z k (hA k hk) h)
    have hC₂ : δ * K / 4 * C₂ ≥ (K : ℝ) * (oscMeanConst + a) := by
      have : δ * K / 4 * (4 * (oscMeanConst + a) / δ) = K * (oscMeanConst + a) := by
        field_simp
      have hc0 : 0 ≤ δ * K / 4 := by positivity
      simp only [C₂]
      nlinarith
    have h3 : (F.card : ℝ) * C₂ ≥ δ * K / 4 * C₂ := by
      have : (0 : ℝ) < C₂ := by have := oscMeanConst_nonneg; positivity
      nlinarith
    have hE := oscMeanConst_nonneg
    nlinarith
  have hB := harmonic_osc_sum_tail n z W hWne hW A hA hreg (u := a * K) (by positivity)
  
  have hexp : Real.exp (-(a * K) ^ 2 / (2 * (14 * coarseVarConst * W.card))) ≤
      (1 / 8 : ℝ) ^ K := by
    have h8 : (1 / 8 : ℝ) ^ K = Real.exp (-(3 * Real.log 2) * K) := by
      rw [show (1 / 8 : ℝ) = Real.exp (-(3 * Real.log 2)) by
        rw [Real.exp_neg, show 3 * Real.log 2 = Real.log 8 by
          rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num,
          Real.exp_log (by norm_num)]; norm_num]
      rw [← Real.exp_nat_mul]; ring_nf
    rw [h8]
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_mul, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    rw [mul_pow, ha2]
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : 3 * Real.log 2 * K * (2 * (14 * coarseVarConst * W.card)) ≤
        3 * Real.log 2 * K * (2 * (14 * coarseVarConst * K)) := by gcongr
    nlinarith
  calc boxDGFF n {h | δ * K / 4 < ((W.filter fun k => C₂ < osc n z k (A k) h).card : ℝ)}
      ≤ boxDGFF n {h | (W.card : ℝ) * oscMeanConst + a * K ≤ ∑ k ∈ W, osc n z k (A k) h} :=
        measure_mono hsub
    _ = ENNReal.ofReal ((boxDGFF n).real
          {h | (W.card : ℝ) * oscMeanConst + a * K ≤ ∑ k ∈ W, osc n z k (A k) h}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ((1 / 8 : ℝ) ^ K) := ENNReal.ofReal_le_ofReal (hB.trans hexp)

end SupercriticalLQGUniqueness.B2.QPos.P4
