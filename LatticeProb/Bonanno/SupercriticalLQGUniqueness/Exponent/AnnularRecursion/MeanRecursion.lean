/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.AnnularRecursion.MeanRecursion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Selector
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.UpperMoment
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Moments.ScaleLaw




 















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.AnnularRecursion

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

instance : Nonempty Exponent.PolygonalCost.RatPolygonFamily := ⟨⟨0, fun _ => ⟨0, fun _ => (0, 0)⟩⟩⟩

 
theorem polyAnnularCost_lt_top_of_contDiff {ξ : ℝ} (hξ : 0 ≤ ξ) {f : ℂ → ℝ}
    (hf : ContDiff ℝ 1 f) : Exponent.PolygonalCost.polyAnnularCost ξ f < ⊤ := by
  have h := Exponent.InwardMap.polyAnnularCost_le_four_rectLen (inwardParam 8) (inwardParam_pos 8)
    (inwardParam_le 8) ξ hξ f hf.continuous
    (fun z _ => (hf.differentiable (by norm_num)).differentiableAt)
    (hf.continuous_fderiv (by norm_num)).continuousOn
  refine lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  have hfin : ∀ R : MarkedRect, 0 ≤ R.w → 0 ≤ R.h → rectLen ξ f R < ⊤ := fun R hw hh =>
    lt_top_iff_ne_top.2 (rectLen_ne_top R hw hh hf.continuous)
  refine ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩ <;>
    exact hfin _ (by norm_num [sB, sT, sL, sR]) (by norm_num [sB, sT, sL, sR])

theorem tileMap_eq (m : ℕ) (ij : ℤ × ℤ) (x : ℂ) :
    tileMap m ij x = ((((2 : ℝ)⁻¹ ^ m) : ℝ) : ℂ) * x + ratC (cornerQ m ij) := by
  rw [tileMap, aQ_cast, inv_pow]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

 
theorem mean_recursion (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 ≤ ξ) {m k : ℕ}
    (hm : 8 ≤ m) (hk : 1 ≤ k) {δ : ℝ≥0∞} (hδ : 0 < δ) {Y : ℂ → Ω → ℝ}
    (hYae : ∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ m)⁻¹ 1 x)
    (hYm : ∀ x, Measurable (Y x)) (hYc : ∀ ω, ContDiff ℝ 1 fun x => Y x ω) :
    ∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 (m + k) x ω) ∂P ≤
      (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 k x ω) ∂P) *
        (20 * ∫⁻ ω, ENNReal.ofReal (Real.exp (54 * ξ * T20C.Obig m Y ω)) *
          (Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y x ω) + δ) ∂P) := by
  classical
  have := hW.isProbabilityMeasure
  set n := m + k with hn
  have hmn : m ≤ n := Nat.le_add_right m k
  set a : ℝ := ((2 : ℝ) ^ m)⁻¹ with ha_def
  have ha : 0 < a := by positivity
  have hYc' : ∀ ω, Continuous fun x => Y x ω := fun ω => (hYc ω).continuous
  set ψ := phiMN W P m n with hψ_def
  have hψ := isPhiVersion_phiMN hW hmn
  have hΦ := isPhiVersion_phiMN hW (Nat.zero_le n)
  
  have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hle1 : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  have hle2 : (2 : ℝ)⁻¹ ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hY2 : ∀ x, Y x =ᵐ[P] phi W ((2 : ℝ)⁻¹ ^ m) 1 x := fun x => by
    rw [inv_pow]; exact hYae x
  have hΦ2 : ∀ x, phiMN W P 0 n x =ᵐ[P] phi W ((2 : ℝ)⁻¹ ^ n) 1 x := fun x => by
    have h := hΦ.ae_eq x; rwa [pow_zero] at h
  have hadd : ∀ᵐ ω ∂P, ∀ x, phiMN W P 0 n x ω = ψ x ω + Y x ω :=
    phi_version_add_ae hW hpos hle1 hle2 hψ.cont hYc' hΦ.cont hψ.ae_eq hY2 hΦ2
  have hind : IndepFun (fun ω x => ψ x ω) (fun ω x => Y x ω) P :=
    indepFun_phi_version hW hpos hle1 hψ.meas hYm hψ.ae_eq hY2
  
  set ψT : ℤ × ℤ → ℂ → Ω → ℝ := fun ij x ω => ψ (tileMap m ij x) ω with hψT
  have hψTc : ∀ ij ω, Continuous fun x => ψT ij x ω := fun ij ω =>
    (hψ.cont ω).comp (by unfold tileMap; fun_prop)
  have hψTm : ∀ ij x, Measurable (ψT ij x) := fun ij x => hψ.meas _
  have hindT : ∀ ij, IndepFun (fun ω x => Y x ω) (fun ω x => ψT ij x ω) P := by
    intro ij
    have hmap : Measurable fun g : ℂ → ℝ => fun x => g (tileMap m ij x) :=
      measurable_pi_iff.mpr fun x => measurable_pi_apply _
    exact hind.symm.comp measurable_id hmap
  have hlaw : ∀ ij, ∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => ψT ij x ω) ∂P =
      ∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 k x ω) ∂P := by
    intro ij
    have hφk := isPhiVersion_phiMN hW (Nat.zero_le k)
    have hl := Exponent.Moments.tile_fine_field_law hW hmn (ratC (cornerQ m ij))
    have e1 : (fun ω x => ψT ij x ω) = fun ω x => phiMN W P m n
        ((((2 : ℝ)⁻¹ ^ m : ℝ) : ℂ) * x + ratC (cornerQ m ij)) ω := by
      funext ω x; simp only [hψT, tileMap_eq, hψ_def]
    have hk' : n - m = k := by omega
    rw [hk'] at hl
    exact lintegral_polyAnnularCost_eq_of_law ξ (hψTc ij) (hψTm ij) hφk.cont hφk.meas
      (by rw [e1]; exact hl)
  
  obtain ⟨e, he⟩ := exists_surjective_nat Exponent.PolygonalCost.RatPolygonFamily
  set f : Ω → C(ℂ, ℝ) := sampleC Y hYc' with hf_def
  have hsel : ∀ ω, ∃ j, SelProp ξ δ e j (f ω) := by
    intro ω
    have hU : polyCostC ξ (f ω) < ⊤ := polyAnnularCost_lt_top_of_contDiff hξ (hYc ω)
    have hlt : polyCostC ξ (f ω) < polyCostC ξ (f ω) + δ := ENNReal.lt_add_right hU.ne hδ.ne'
    obtain ⟨F, hF⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hadm, hcost⟩ := iInf_lt_iff.1 hF
    obtain ⟨j, rfl⟩ := he F
    exact ⟨j, hadm, hcost⟩
  
  have hcWm : ∀ ij, Measurable fun ω => chargedWeight ξ δ e m ij (f ω) := fun ij =>
    measurable_sampleC_comp (measurable_chargedWeight ξ δ e m ij) hYc' hYm
  have hUTm : ∀ ij, Measurable fun ω => Exponent.PolygonalCost.polyAnnularCost ξ (fun x => ψT ij x ω) :=
    fun ij => Exponent.PolygonalCost.measurable_polyAnnularCost (hψTc ij) (hψTm ij) ξ
  have hindW : ∀ ij, IndepFun (fun ω => chargedWeight ξ δ e m ij (f ω))
      (fun ω => Exponent.PolygonalCost.polyAnnularCost ξ (fun x => ψT ij x ω)) P := fun ij =>
    indepFun_sampleC (measurable_chargedWeight ξ δ e m ij) (measurable_polyCostC ξ) hYc'
      (hψTc ij) (hindT ij)
  set μk := ∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 k x ω) ∂P
  
  have hpath : ∀ᵐ ω ∂P, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ≤
      ∑ ij ∈ tileUniv m, chargedWeight ξ δ e m ij (f ω) * ENNReal.ofReal a *
        Exponent.PolygonalCost.polyAnnularCost ξ (fun x => ψT ij x ω) := by
    filter_upwards [hadd] with ω hω
    have hfun : (fun x => phiMN W P 0 n x ω) = fun z => f ω z + ψ z ω := by
      funext x; rw [hω x, add_comm]; rfl
    rw [hfun]
    exact (charged_bounds ξ δ e m hm hξ (f ω) (hYc ω) (hsel ω) fun z => ψ z ω).1
  have hcoarse : ∀ ω, ∑ ij ∈ tileUniv m, ENNReal.ofReal a * chargedWeight ξ δ e m ij (f ω) ≤
      20 * (ENNReal.ofReal (Real.exp (54 * ξ * T20C.Obig m Y ω)) *
        (Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y x ω) + δ)) := by
    intro ω
    have h2 := (charged_bounds ξ δ e m hm hξ (f ω) (hYc ω) (hsel ω) fun _ => 0).2
    refine h2.trans ?_
    rw [mul_assoc]
    gcongr
    · exact gradientSup_le_obig hYc m ω
    · exact le_rfl
  calc ∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ∂P ≤
      ∫⁻ ω, ∑ ij ∈ tileUniv m, chargedWeight ξ δ e m ij (f ω) * ENNReal.ofReal a *
        Exponent.PolygonalCost.polyAnnularCost ξ (fun x => ψT ij x ω) ∂P := lintegral_mono_ae hpath
    _ = ∑ ij ∈ tileUniv m, ∫⁻ ω, chargedWeight ξ δ e m ij (f ω) * ENNReal.ofReal a *
        Exponent.PolygonalCost.polyAnnularCost ξ (fun x => ψT ij x ω) ∂P :=
        lintegral_finsetSum _ fun ij _ => ((hcWm ij).mul_const _).mul (hUTm ij)
    _ = ∑ ij ∈ tileUniv m, ENNReal.ofReal a *
        ((∫⁻ ω, chargedWeight ξ δ e m ij (f ω) ∂P) * μk) := by
        refine Finset.sum_congr rfl fun ij _ => ?_
        have hprod := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hcWm ij) (hUTm ij)
          (hindW ij)
        rw [← hlaw ij, ← hprod, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun ω => ?_
        simp only [Pi.mul_apply]
        ring
    _ = μk * ∫⁻ ω, ∑ ij ∈ tileUniv m, ENNReal.ofReal a * chargedWeight ξ δ e m ij (f ω) ∂P := by
        rw [lintegral_finsetSum _ fun ij _ => (hcWm ij).const_mul _, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ij _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        ring
    _ ≤ μk * ∫⁻ ω, 20 * (ENNReal.ofReal (Real.exp (54 * ξ * T20C.Obig m Y ω)) *
        (Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y x ω) + δ)) ∂P := by
        gcongr with ω
        exact hcoarse ω
    _ = μk * (20 * ∫⁻ ω, ENNReal.ofReal (Real.exp (54 * ξ * T20C.Obig m Y ω)) *
        (Exponent.PolygonalCost.polyAnnularCost ξ (fun x => Y x ω) + δ) ∂P) := by
        rw [lintegral_const_mul' _ _ (by norm_num)]


end SupercriticalLQGUniqueness.Exponent.AnnularRecursion
