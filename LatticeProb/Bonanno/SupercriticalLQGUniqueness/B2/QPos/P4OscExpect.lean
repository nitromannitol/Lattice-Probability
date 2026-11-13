/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4OscExpect at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4ScaleVariance
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4GaussianChaining
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4HarmonicGaussian

 













set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.QPos.P4

theorem hfun_continuous (n : ℕ) (S : Finset (DGFFSite n)) (c : DGFFSite n) :
    Continuous fun h : EuclideanSpace ℝ (DGFFSite n) => hfun n S h c := by
  by_cases hc : c ∈ S
  · have : (fun h : EuclideanSpace ℝ (DGFFSite n) => hfun n S h c) =
        fun h => (EuclideanSpace.proj ⟨c, hc⟩ : EuclideanSpace ℝ {x // x ∈ S} →L[ℝ] ℝ)
          (boxHarmonicFieldCLM n (boxInnerOuterEquiv n S) h) := by
      funext h; rw [hfun_of_mem hc]; rfl
    rw [this]
    fun_prop
  · have : (fun h : EuclideanSpace ℝ (DGFFSite n) => hfun n S h c) = fun h => h c := by
      funext h; rw [hfun_of_not_mem hc]
    rw [this]
    fun_prop

 
def osc (n : ℕ) (z : ℤ × ℤ) (k : ℕ) (A : Finset (DGFFSite n))
    (h : EuclideanSpace ℝ (DGFFSite n)) : ℝ :=
  (⨆ c : {c // c ∈ A}, hfun n (scaleSites n z k) h c.1) +
    (⨆ c : {c // c ∈ A}, -hfun n (scaleSites n z k) h c.1)

 
theorem integrable_iSup_fin {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ι : Type*} [Fintype ι] [Nonempty ι] {f : ι → Ω → ℝ} (hf : ∀ i, Integrable (f i) μ)
    (hm : ∀ i, Measurable (f i)) :
    Integrable (fun ω => ⨆ i, f i ω) μ := by
  classical
  have hmeas : Measurable fun ω => ⨆ i, f i ω := Measurable.iSup hm
  have hsum : Integrable (fun ω => ∑ i, |f i ω|) μ :=
    integrable_finset_sum _ fun i _ => (hf i).abs
  refine hsum.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have hbdd : BddAbove (Set.range fun i => f i ω) := (Set.finite_range _).bddAbove
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have h1 : f i₀ ω ≤ ⨆ i, f i ω := le_ciSup hbdd i₀
    have h2 : |f i₀ ω| ≤ ∑ i, |f i ω| :=
      Finset.single_le_sum (f := fun i => |f i ω|) (fun i _ => abs_nonneg _) (mem_univ i₀)
    have := neg_abs_le (f i₀ ω)
    linarith
  · apply ciSup_le
    intro i
    have h2 : |f i ω| ≤ ∑ i, |f i ω| :=
      Finset.single_le_sum (f := fun i => |f i ω|) (fun i _ => abs_nonneg _) (mem_univ i)
    have := le_abs_self (f i ω)
    linarith

 
theorem integral_iSup_signed_le {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k)
    {A : Finset (DGFFSite n)} (hA : A.Nonempty) (hreg : ∀ c ∈ A, inReg n z k c)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∫ h, (⨆ c : {c // c ∈ A}, σ * hfun n (scaleSites n z k) h c.1) ∂(boxDGFF n) ≤
      60 * Real.sqrt 5 * Real.sqrt coarseVarConst := by
  classical
  set S := scaleSites n z k
  set N := A.card
  have hN : 0 < N := Finset.card_pos.mpr hA
  set e : {c // c ∈ A} ≃ Fin N := A.equivFin
  have hmemS : ∀ i : Fin N, (e.symm i).1 ∈ S := fun i =>
    mem_scaleSites_of_inReg hk (hreg _ (e.symm i).2)
  
  set T : EuclideanSpace ℝ {x // x ∈ S} →L[ℝ] (Fin N → ℝ) :=
    ContinuousLinearMap.pi fun i => σ • (EuclideanSpace.proj ⟨(e.symm i).1, hmemS i⟩ :
      EuclideanSpace ℝ {x // x ∈ S} →L[ℝ] ℝ)
  set X : EuclideanSpace ℝ (DGFFSite n) → Fin N → ℝ :=
    fun h => T (boxHarmonicFieldCLM n (boxInnerOuterEquiv n S) h)
  have hXapp : ∀ h i, X h i = σ * hfun n S h (e.symm i).1 := by
    intro h i
    simp only [X, T, ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rw [hfun_of_mem (hmemS i)]
    rfl
  have hXG : HasGaussianLaw X (boxDGFF n) :=
    (boxHarmonicField_hasGaussianLaw n (boxInnerOuterEquiv n S)).map_fun T
  have h0 : ∀ i, ∫ h, X h i ∂(boxDGFF n) = 0 := by
    intro i
    simp_rw [hXapp, integral_const_mul]
    rw [show (fun h : EuclideanSpace ℝ (DGFFSite n) => hfun n S h (e.symm i).1) =
        fun h => boxHarmonicField n (boxInnerOuterEquiv n S) h ⟨(e.symm i).1, hmemS i⟩ by
      funext h; rw [hfun_of_mem (hmemS i)]]
    rw [boxHarmonicField_mean_zero_coord, mul_zero]
  
  set p : Fin N → Fin 2 → ℝ := fun i => ![((e.symm i).1.1.1 : ℝ), ((e.symm i).1.1.2 : ℝ)]
  have hp0 : ∀ i j, (p i - p j) 0 = (((e.symm i).1.1.1 - (e.symm j).1.1.1 : ℤ) : ℝ) := by
    intro i j; simp [p]
  have hp1 : ∀ i j, (p i - p j) 1 = (((e.symm i).1.1.2 - (e.symm j).1.1.2 : ℤ) : ℝ) := by
    intro i j; simp [p]
  have hL : (0 : ℝ) < 2 ^ (n - k) := by positivity
  have hdiam : ∀ i j, ‖p i - p j‖ ≤ 3 * (2 ^ (n - k) : ℝ) := by
    intro i j
    obtain ⟨d1, d2⟩ := inReg_dist (hreg _ (e.symm i).2) (hreg _ (e.symm j).2)
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro c
    fin_cases c
    · show ‖(p i - p j) 0‖ ≤ _
      rw [hp0, Real.norm_eq_abs, ← Int.cast_abs]
      have : (|(e.symm i).1.1.1 - (e.symm j).1.1.1| : ℝ) ≤ ((2 * 2 ^ (n - k) : ℕ) : ℝ) := by
        exact_mod_cast d1
      push_cast at this ⊢
      linarith
    · show ‖(p i - p j) 1‖ ≤ _
      rw [hp1, Real.norm_eq_abs, ← Int.cast_abs]
      have : (|(e.symm i).1.1.2 - (e.symm j).1.1.2| : ℝ) ≤ ((2 * 2 ^ (n - k) : ℕ) : ℝ) := by
        exact_mod_cast d2
      push_cast at this ⊢
      linarith
  have hinc : ∀ i j, ∫ h, (X h i - X h j) ^ 2 ∂(boxDGFF n) ≤
      coarseVarConst * ‖p i - p j‖ / (2 ^ (n - k) : ℝ) := by
    intro i j
    set d : ℕ := ⌊‖p i - p j‖⌋₊
    have hd : (d : ℝ) ≤ ‖p i - p j‖ := Nat.floor_le (norm_nonneg _)
    have hcoord : ∀ m : ℤ, (|(m : ℝ)|) ≤ ‖p i - p j‖ → |m| ≤ d := by
      intro m hm
      have h1 : ((|m|.toNat : ℕ) : ℝ) ≤ ‖p i - p j‖ := by
        rw [show ((|m|.toNat : ℕ) : ℝ) = |(m : ℝ)| by
          rw [← Int.cast_abs]; exact_mod_cast Int.toNat_of_nonneg (abs_nonneg m)]
        exact hm
      have h2 : |m|.toNat ≤ d := Nat.le_floor h1
      have h3 := Int.toNat_of_nonneg (abs_nonneg m)
      omega
    have hd1 : |(e.symm i).1.1.1 - (e.symm j).1.1.1| ≤ d := by
      apply hcoord
      rw [← hp0, ← Real.norm_eq_abs]
      exact norm_le_pi_norm (p i - p j) 0
    have hd2 : |(e.symm i).1.1.2 - (e.symm j).1.1.2| ≤ d := by
      apply hcoord
      rw [← hp1, ← Real.norm_eq_abs]
      exact norm_le_pi_norm (p i - p j) 1
    have hvar := var_hfun_incr_le hk (hreg _ (e.symm i).2) (hreg _ (e.symm j).2) d hd1 hd2
    have hfX : (fun h => X h i - X h j) =
        fun h => σ * (hfun n S h (e.symm i).1 - hfun n S h (e.symm j).1) := by
      funext h; rw [hXapp, hXapp]; ring
    have hmeas : AEMeasurable (fun h => X h i - X h j) (boxDGFF n) := by
      rw [hfX]
      exact ((hfun_continuous n S _).sub (hfun_continuous n S _)).measurable.aemeasurable.const_mul _
    have hint0 : ∫ h, (X h i - X h j) ∂(boxDGFF n) = 0 := by
      rw [integral_sub, h0, h0, sub_zero]
      · exact (hXG.map_fun (ContinuousLinearMap.proj i)).integrable
      · exact (hXG.map_fun (ContinuousLinearMap.proj j)).integrable
    have hV := variance_of_integral_eq_zero hmeas hint0
    have hsq : ∫ h, (X h i - X h j) ^ 2 ∂(boxDGFF n) =
        Var[fun h => X h i - X h j; boxDGFF n] := by
      rw [hV]
    rw [hsq, hfX, variance_const_mul]
    have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
    rw [hσ2, one_mul]
    refine hvar.trans ?_
    have hv0 := coarseVarConst_pos
    gcongr
  have hchain := gaussian_box_max_expectation_uniform (boxDGFF n) hN X hXG h0 p
    coarseVarConst_pos.le hL hdiam hinc
  have hre : (fun h : EuclideanSpace ℝ (DGFFSite n) =>
        ⨆ c : {c // c ∈ A}, σ * hfun n (scaleSites n z k) h c.1) =
      fun h => ⨆ i, X h i := by
    funext h
    simp_rw [hXapp]
    exact (e.symm.iSup_comp (g := fun c : {c // c ∈ A} => σ * hfun n S h c.1)).symm
  rw [hre]
  exact hchain

 
theorem integral_osc_le {n : ℕ} {z : ℤ × ℤ} {k : ℕ} (hk : GoodScale n z k)
    {A : Finset (DGFFSite n)} (hA : A.Nonempty) (hreg : ∀ c ∈ A, inReg n z k c) :
    ∫ h, osc n z k A h ∂(boxDGFF n) ≤ 120 * Real.sqrt 5 * Real.sqrt coarseVarConst := by
  haveI : Nonempty {c // c ∈ A} := ⟨⟨hA.choose, hA.choose_spec⟩⟩
  have h1 := integral_iSup_signed_le hk hA hreg 1 (Or.inl rfl)
  have h2 := integral_iSup_signed_le hk hA hreg (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at h1 h2
  have hint : ∀ σ : ℝ, Integrable (fun h : EuclideanSpace ℝ (DGFFSite n) =>
      ⨆ c : {c // c ∈ A}, σ * hfun n (scaleSites n z k) h c.1) (boxDGFF n) := by
    intro σ
    apply integrable_iSup_fin
    · intro c
      exact ((hfun_memLp n _ c.1).integrable one_le_two).const_mul σ
    · intro c
      exact ((hfun_continuous n _ c.1).measurable).const_mul σ
  have hi1 := hint 1
  have hi2 := hint (-1)
  simp only [one_mul, neg_one_mul] at hi1 hi2
  unfold osc
  rw [integral_add hi1 hi2]
  linarith

end SupercriticalLQGUniqueness.B2.QPos.P4
