/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.AnnularRecursion.UpperMomentBands at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.LowerMoment
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.PolygonalUpperBound
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28U1Mom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Up0
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S2Site
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldOscExp




 













set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.AnnularRecursion

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

 

private theorem floor_offset {r : ℝ} (h0 : -2 ≤ r) (h1 : r ≤ 3) :
    -2 ≤ min ⌊r⌋ 2 ∧ min ⌊r⌋ 2 ≤ 2 ∧
      0 ≤ r - ((min ⌊r⌋ 2 : ℤ) : ℝ) ∧ r - ((min ⌊r⌋ 2 : ℤ) : ℝ) ≤ 1 := by
  have hf0 : (-2 : ℤ) ≤ ⌊r⌋ := Int.le_floor.2 (by exact_mod_cast h0)
  refine ⟨le_min hf0 (by norm_num), min_le_right _ _, ?_, ?_⟩
  · have : ((min ⌊r⌋ 2 : ℤ) : ℝ) ≤ (⌊r⌋ : ℝ) := by exact_mod_cast min_le_left _ _
    linarith [Int.floor_le r]
  · rcases le_total ⌊r⌋ 2 with h | h
    · rw [min_eq_left h]
      linarith [Int.lt_floor_add_one r]
    · rw [min_eq_right h]
      push_cast
      linarith

 
theorem gradientSup_le_obig {Ω : Type*} {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, ContDiff ℝ 1 fun x => Y x ω) (k : ℕ) (ω : Ω) :
    ((2 : ℝ) ^ k)⁻¹ * Exponent.InwardMap.gradientSup (fun x => Y x ω) ≤ T20C.Obig k Y ω := by
  have hk : (0 : ℝ) < ((2 : ℝ) ^ k)⁻¹ := by positivity
  have hpt : ∀ z ∈ Exponent.InwardMap.gradientBox,
      ‖fderiv ℝ (fun x => Y x ω) z‖ ≤ (2 : ℝ) ^ k * T20C.Obig k Y ω := by
    intro z hz
    obtain ⟨hre, him⟩ := hz
    obtain ⟨a0, a1, a2, a3⟩ := floor_offset hre.1 hre.2
    obtain ⟨b0, b1, b2, b3⟩ := floor_offset him.1 him.2
    set i : ℤ := min ⌊z.re⌋ 2
    set j : ℤ := min ⌊z.im⌋ 2
    set c : ℂ := ⟨(i : ℝ), (j : ℝ)⟩
    have hc : c ∈ T20C.offs := by
      unfold T20C.offs
      refine Finset.mem_image.2 ⟨(i, j), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩
    have hzc : z - c ∈ ferniqueBox 0 1 := by
      refine ⟨?_, ?_⟩
      · simp only [c, Complex.zero_re, zero_add]
        exact ⟨a2, a3⟩
      · simp only [c, Complex.zero_im, zero_add]
        exact ⟨b2, b3⟩
    have hder : fderiv ℝ (fun x => Y (x + c) ω) (z - c) = fderiv ℝ (fun x => Y x ω) z := by
      rw [fderiv_comp_add_right (f := fun x => Y x ω) c, sub_add_cancel]
    have hcont : Continuous fun w => ‖fderiv ℝ (fun x => Y (x + c) ω) w‖ :=
      continuous_norm.comp (((hYc ω).comp (contDiff_id.add contDiff_const)).continuous_fderiv
        (by norm_num))
    have hbdd : BddAbove (range fun w : ferniqueBox (0 : ℂ) 1 =>
        ‖fderiv ℝ (fun x => Y (x + c) ω) w‖) := by
      have := (isCompact_ferniqueBox 0 1).bddAbove_image hcont.continuousOn
      rwa [image_eq_range] at this
    have h1 : ‖fderiv ℝ (fun x => Y x ω) z‖ ≤
        ⨆ w : ferniqueBox (0 : ℂ) 1, ‖fderiv ℝ (fun x => Y (x + c) ω) w‖ := by
      rw [← hder]
      exact le_ciSup hbdd ⟨z - c, hzc⟩
    have h2 : ((2 : ℝ) ^ k)⁻¹ *
        (⨆ w : ferniqueBox (0 : ℂ) 1, ‖fderiv ℝ (fun x => Y (x + c) ω) w‖) ≤
          T20C.Obig k Y ω :=
      Finset.le_sup' (fun c₁ => ((2 : ℝ) ^ k)⁻¹ *
        ⨆ w : ferniqueBox (0 : ℂ) 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) w‖) hc
    have h3 : ‖fderiv ℝ (fun x => Y x ω) z‖ ≤
        (2 : ℝ) ^ k * (((2 : ℝ) ^ k)⁻¹ *
          ⨆ w : ferniqueBox (0 : ℂ) 1, ‖fderiv ℝ (fun x => Y (x + c) ω) w‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      exact h1
    exact h3.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hne : ((fun z : ℂ => ‖fderiv ℝ (fun x => Y x ω) z‖) '' Exponent.InwardMap.gradientBox).Nonempty :=
    ⟨_, mem_image_of_mem _ (show (0 : ℂ) ∈ Exponent.InwardMap.gradientBox by
      refine ⟨?_, ?_⟩ <;> simp)⟩
  have hsup : Exponent.InwardMap.gradientSup (fun x => Y x ω) ≤ (2 : ℝ) ^ k * T20C.Obig k Y ω := by
    unfold Exponent.InwardMap.gradientSup
    refine csSup_le hne ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hpt z hz
  calc ((2 : ℝ) ^ k)⁻¹ * Exponent.InwardMap.gradientSup (fun x => Y x ω) ≤
      ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k * T20C.Obig k Y ω) :=
        mul_le_mul_of_nonneg_left hsup hk.le
    _ = T20C.Obig k Y ω := by rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

 
theorem aemeasurable_obig (hW : IsWhiteNoise P W) (k : ℕ) {Y : ℂ → Ω → ℝ}
    (hY : ∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ k)⁻¹ 1 x)
    (hYc : ∀ ω, ContDiff ℝ 1 fun x => Y x ω) :
    AEMeasurable (fun ω => T20C.Obig k Y ω) P := by
  have hone : ∀ c₁ : ℂ, AEMeasurable (fun ω => ((2 : ℝ) ^ k)⁻¹ *
      ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖) P := by
    intro c₁
    set W' : WNSpace → Ω → ℝ := fun f => W (motionL2 1 c₁ f)
    have hW' : IsWhiteNoise P W' := isWhiteNoise_isometry hW _
    have hY' : ∀ x, (fun ω => Y (x + c₁) ω) =ᵐ[P] phi W' ((2 : ℝ) ^ k)⁻¹ 1 x := by
      intro x
      have e := phi_motion W (a := ((2 : ℝ) ^ k)⁻¹) (by positivity) 1 1 x c₁
      simp only [Circle.coe_one, one_mul] at e
      rw [← e]; exact hY (x + c₁)
    have hYc' : ∀ ω, ContDiff ℝ 1 fun x => Y (x + c₁) ω := fun ω =>
      (hYc ω).comp (contDiff_id.add contDiff_const)
    exact aemeasurable_osc hW' k hY' hYc'
  have e : (fun ω => T20C.Obig k Y ω) = T20C.offs.sup' T20C.offs_nonempty
      (fun c₁ ω => ((2 : ℝ) ^ k)⁻¹ *
        ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖) := by
    funext ω
    rw [Finset.sup'_apply]
    rfl
  rw [e]
  exact Finset.sup'_induction (p := fun f : Ω → ℝ => AEMeasurable f P) T20C.offs_nonempty _
    (fun f hf g hg => hf.sup hg) (fun c₁ _ => hone c₁)

 

 
theorem prob_lenObs_image (hW : IsWhiteNoise P W) (ξ : ℝ) (n : ℕ) (R : MarkedRect)
    (u : Circle) (c : ℂ) (hR : ∀ g : ℂ → ℝ, rectLen ξ g R = s2ImLen ξ g u c)
    {S : Set ℝ} (hS : MeasurableSet S) :
    P {ω | lenObs ξ (phiMN W P 0 n) R ω ∈ S} =
      P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω ∈ S} := by
  have h := measure_crossLenIn_phiMN_motion (ξ := ξ) hW (Nat.zero_le n) u c
    (K := (rectAB 3 1).toSet) (A := (rectAB 3 1).side₁) (B := (rectAB 3 1).side₂)
    (rectAB 3 1).isCompact_toSet (ENNReal.measurable_toReal hS)
  have e1 : {ω | lenObs ξ (phiMN W P 0 n) R ω ∈ S} =
      {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω)
        ((fun x => (u : ℂ) * x + c) '' (rectAB 3 1).toSet)
        ((fun x => (u : ℂ) * x + c) '' (rectAB 3 1).side₁)
        ((fun x => (u : ℂ) * x + c) '' (rectAB 3 1).side₂) ∈ ENNReal.toReal ⁻¹' S} := by
    ext ω
    simp only [lenObs, hR, s2ImLen, mem_ofPred_eq, mem_preimage]
    rfl
  have e2 : {ω | lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω ∈ S} =
      {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) (rectAB 3 1).toSet
        (rectAB 3 1).side₁ (rectAB 3 1).side₂ ∈ ENNReal.toReal ⁻¹' S} := by
    ext ω
    simp only [lenObs, rectLen, mem_ofPred_eq, mem_preimage]
  rw [e1, e2]
  exact h

 
def band : Fin 4 → MarkedRect
  | 0 => sB (0, 0)
  | 1 => sT (0, 0)
  | 2 => sL (0, 0)
  | 3 => sR (0, 0)

theorem band_motion (i : Fin 4) : ∃ (u : Circle) (c : ℂ),
    ∀ (ξ : ℝ) (g : ℂ → ℝ), rectLen ξ g (band i) = s2ImLen ξ g u c := by
  fin_cases i
  · exact ⟨_, _, fun ξ g => rectLen_sB_eq (ξ := ξ) g (0, 0)⟩
  · exact ⟨_, _, fun ξ g => rectLen_sT_eq (ξ := ξ) g (0, 0)⟩
  · exact ⟨_, _, fun ξ g => rectLen_sL_eq (ξ := ξ) g (0, 0)⟩
  · exact ⟨_, _, fun ξ g => rectLen_sR_eq (ξ := ξ) g (0, 0)⟩

theorem band_dims (i : Fin 4) : 0 ≤ (band i).w ∧ 0 ≤ (band i).h := by
  fin_cases i <;> norm_num [band, sB, sT, sL, sR]

theorem sum_band_rectLen (ξ : ℝ) (g : ℂ → ℝ) :
    rectLen ξ g (sB (0, 0)) + rectLen ξ g (sT (0, 0)) + rectLen ξ g (sL (0, 0)) +
      rectLen ξ g (sR (0, 0)) = ∑ i : Fin 4, rectLen ξ g (band i) := by
  simp [Fin.sum_univ_four, band]

 
theorem band_moment (hW : IsWhiteNoise P W) {ξ : ℝ} {p C₈ c₈ : ℝ}
    (hp : 0 < p) (hp4 : p ≤ 1 / 4) (hC₈ : 0 < C₈) (hc₈ : 0 < c₈)
    (h18 : ∀ (n : ℕ) (s : ℝ), 2 < s →
      P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
          lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} ≤
        ENNReal.ofReal (C₈ * Real.exp (-c₈ * s ^ 2 / Real.log s)))
    (q : ℕ) (hq : 1 ≤ q) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (n : ℕ) (i : Fin 4),
      ∫⁻ ω, ENNReal.ofReal (lenObs ξ (phiMN W P 0 n) (band i) ω ^ q) ∂P ≤
        ENNReal.ofReal (K₀ * (LambdaN ξ W P n (ENNReal.ofReal p) *
          ellN ξ W P n (ENNReal.ofReal p)) ^ q) := by
  have := hW.isProbabilityMeasure
  obtain ⟨K₀, hK₀, hmom⟩ := S6P28U.moment_of_tail (Ω := Ω) (P := P) q hq hc₈ hC₈
  refine ⟨K₀, hK₀, fun n i => ?_⟩
  have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.2 hp
  have hpq : ENNReal.ofReal p ≤ 2⁻¹ := by
    rw [← ofReal_half_eq']; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hℓ0 : 0 < ellN ξ W P n (ENNReal.ofReal p) :=
    T20B.ellN_pos hW hpq0 (lt_of_le_of_lt hpq inv_two_lt_one') n
  have hΛ0 : 0 < LambdaN ξ W P n (ENNReal.ofReal p) := T20B.LambdaN_pos hW hpq0 hpq n
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  obtain ⟨u, c, hR⟩ := band_motion i
  refine hmom (lenObs ξ (phiMN W P 0 n) (band i)) _ inferInstance
    (measurable_lenObs hφ.cont hφ.meas _) (fun ω => ENNReal.toReal_nonneg)
    (mul_pos hΛ0 hℓ0) fun s hs => ?_
  have e := prob_lenObs_image hW ξ n (band i) u c (hR ξ)
    (S := Ici (Real.exp s * (LambdaN ξ W P n (ENNReal.ofReal p) *
      ellN ξ W P n (ENNReal.ofReal p)))) measurableSet_Ici
  have e' : {ω | Real.exp s * (LambdaN ξ W P n (ENNReal.ofReal p) *
      ellN ξ W P n (ENNReal.ofReal p)) ≤ lenObs ξ (phiMN W P 0 n) (band i) ω} =
      {ω | lenObs ξ (phiMN W P 0 n) (band i) ω ∈ Ici (Real.exp s *
        (LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p)))} := rfl
  rw [e', e]
  have h := h18 n s hs
  simp only [mul_assoc] at h
  exact h

 

theorem lintegral_ofReal_mul_le {f g : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hf : AEMeasurable f P) (hg : AEMeasurable g P) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfA : ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P ≤ ENNReal.ofReal A)
    (hgB : ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂P ≤ ENNReal.ofReal B) :
    ∫⁻ ω, ENNReal.ofReal (f ω * g ω) ∂P ≤ ENNReal.ofReal (Real.sqrt A * Real.sqrt B) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
    hf.ennreal_ofReal hg.ennreal_ofReal
  have e1 : ∀ ω, (fun ω => ENNReal.ofReal (f ω)) ω ^ (2 : ℝ) = ENNReal.ofReal (f ω ^ 2) := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg (hf0 ω) (by norm_num)]
    norm_cast
  have e2 : ∀ ω, (fun ω => ENNReal.ofReal (g ω)) ω ^ (2 : ℝ) = ENNReal.ofReal (g ω ^ 2) := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg (hg0 ω) (by norm_num)]
    norm_cast
  simp only [e1, e2] at h
  have e3 : (fun ω => ENNReal.ofReal (f ω) * ENNReal.ofReal (g ω)) =
      fun ω => ENNReal.ofReal (f ω * g ω) := by
    funext ω; rw [ENNReal.ofReal_mul (hf0 ω)]
  simp only [Pi.mul_apply, e3] at h
  refine h.trans ?_
  have hsq : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt x) := by
    intro x hx
    rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num), Real.sqrt_eq_rpow]
  calc (∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal A ^ (1 / 2 : ℝ) * ENNReal.ofReal B ^ (1 / 2 : ℝ) := by
        gcongr
    _ = ENNReal.ofReal (Real.sqrt A * Real.sqrt B) := by
        rw [hsq A hA, hsq B hB, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]



end SupercriticalLQGUniqueness.Exponent.AnnularRecursion
