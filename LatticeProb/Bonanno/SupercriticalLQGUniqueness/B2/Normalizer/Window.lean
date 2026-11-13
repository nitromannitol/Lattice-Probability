/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Normalizer.Window at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.HeatVersion
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_6Path

 







set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Normalizer

open LQGMetric

 
theorem lfppCrossingLength_pos (ξ : ℝ) (φ : C(ℂ, ℝ)) : 0 < lfppCrossingLength ξ φ := by
  rw [Exponent.HeatVersion.lfppCrossingLength_eq_rectLen]
  exact DDDF.rectLen_pos _ (by simp [DDDF.MarkedRect.crossWidth, DDDF.rectAB]) φ.continuous

 
theorem lfppCrossingLength_add_const (ξ : ℝ) (φ : C(ℂ, ℝ)) (κ : ℝ) :
    lfppCrossingLength ξ (φ + ContinuousMap.const ℂ κ) =
      ENNReal.ofReal (Real.exp (ξ * κ)) * lfppCrossingLength ξ φ := by
  have h0 : ENNReal.ofReal (Real.exp (ξ * κ)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  rw [Exponent.HeatVersion.lfppCrossingLength_eq_rectLen,
    Exponent.HeatVersion.lfppCrossingLength_eq_rectLen]
  unfold DDDF.rectLen
  rw [DDDF.crossLenIn_eq_biInf, DDDF.crossLenIn_eq_biInf,
    ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine iInf_congr fun P => ?_
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine iInf_congr fun _ => ?_
  exact DFGPS.lfppLen_add_const ξ φ P κ

 
theorem toReal_lfppCrossingLength_le {ξ : ℝ} (hξ : 0 < ξ) (φ₁ φ₂ : C(ℂ, ℝ)) (K : ℝ)
    (h : ∀ z ∈ unitSquare, |φ₁ z - φ₂ z| ≤ K) :
    (lfppCrossingLength ξ φ₁).toReal ≤
      Real.exp (ξ * K) * (lfppCrossingLength ξ φ₂).toReal := by
  have hle := Exponent.HeatVersion.lfppCrossingLength_le_exp_of_abs_sub_le ξ K φ₁ φ₂ h
  rw [abs_of_pos hξ] at hle
  have hfin : ENNReal.ofReal (Real.exp (ξ * K)) * lfppCrossingLength ξ φ₂ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lfppCrossingLength_lt_top ξ φ₂).ne
  have := ENNReal.toReal_mono hfin hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this

 

theorem exists_rat_lfppCrossingLength_mem_Ioo {ξ : ℝ} (hξ : 0 < ξ) (H ψ : C(ℂ, ℝ))
    {m₀ M₀ : ℝ} (hm₀ : 0 < m₀) (hψ : ∀ z ∈ unitSquare, m₀ ≤ ψ z ∧ ψ z ≤ M₀)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ q : ℚ, ENNReal.ofReal a < lfppCrossingLength ξ (H + (q : ℝ) • ψ) ∧
      lfppCrossingLength ξ (H + (q : ℝ) • ψ) < ENNReal.ofReal b := by
  set c : ℝ → ℝ := fun t => (lfppCrossingLength ξ (H + t • ψ)).toReal with hc_def
  have hcpos : ∀ t, 0 < c t := fun t =>
    ENNReal.toReal_pos (lfppCrossingLength_pos ξ _).ne' (lfppCrossingLength_lt_top ξ _).ne
  have happ : ∀ t z, (H + t • ψ) z = H z + t * ψ z := fun t z => by
    simp [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
  have hexp : ∀ {x y X : ℝ}, x ≤ Real.exp X * y → Real.exp (-X) * x ≤ y := by
    intro x y X hxy
    have h2 := mul_le_mul_of_nonneg_left hxy (Real.exp_pos (-X)).le
    rwa [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at h2
  
  have hcmp : ∀ s t, c s ≤ Real.exp (ξ * (|s - t| * M₀)) * c t := by
    intro s t
    refine toReal_lfppCrossingLength_le hξ _ _ _ fun z hz => ?_
    rw [happ, happ, add_sub_add_left_eq_sub, ← sub_mul, abs_mul,
      abs_of_pos (hm₀.trans_le (hψ z hz).1)]
    exact mul_le_mul_of_nonneg_left (hψ z hz).2 (abs_nonneg _)
  have hcont : Continuous c := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    have hup : Tendsto (fun s => Real.exp (ξ * (|s - t| * M₀)) * c t) (𝓝 t) (𝓝 (c t)) := by
      have : Continuous fun s => Real.exp (ξ * (|s - t| * M₀)) * c t := by fun_prop
      simpa using this.tendsto t
    have hlo : Tendsto (fun s => Real.exp (-(ξ * (|s - t| * M₀))) * c t) (𝓝 t)
        (𝓝 (c t)) := by
      have : Continuous fun s => Real.exp (-(ξ * (|s - t| * M₀))) * c t := by fun_prop
      simpa using this.tendsto t
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup (fun s => ?_) (fun s => hcmp s t)
    have h1 := hcmp t s
    rw [abs_sub_comm] at h1
    exact hexp h1
  
  have hconst : ∀ t, ∀ z ∈ unitSquare,
      |(H + t • ψ) z - (H + ContinuousMap.const ℂ (t * ((m₀ + M₀) / 2))) z| ≤
        |t| * ((M₀ - m₀) / 2) := by
    intro t z hz
    rw [happ, ContinuousMap.add_apply, ContinuousMap.const_apply, add_sub_add_left_eq_sub,
      ← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_le]
    constructor <;> linarith [(hψ z hz).1, (hψ z hz).2]
  have hshift : ∀ t, c 0 * Real.exp (ξ * (t * ((m₀ + M₀) / 2))) =
      (lfppCrossingLength ξ (H + ContinuousMap.const ℂ (t * ((m₀ + M₀) / 2)))).toReal := by
    intro t
    rw [lfppCrossingLength_add_const, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, mul_comm]
    simp [hc_def]
  have hlow : ∀ t, 0 ≤ t → c 0 * Real.exp (ξ * m₀ * t) ≤ c t := by
    intro t ht
    have h1 := toReal_lfppCrossingLength_le hξ _ _ _ fun z hz => by
      rw [abs_sub_comm]; exact hconst t z hz
    rw [← hshift, abs_of_nonneg ht] at h1
    refine le_trans (le_of_eq ?_) (hexp h1)
    have he : Real.exp (-(ξ * (t * ((M₀ - m₀) / 2)))) * Real.exp (ξ * (t * ((m₀ + M₀) / 2))) =
        Real.exp (ξ * m₀ * t) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← he]; ring
  have hhigh : ∀ t, t ≤ 0 → c t ≤ c 0 * Real.exp (ξ * m₀ * t) := by
    intro t ht
    have h1 := toReal_lfppCrossingLength_le hξ _ _ _ fun z hz => hconst t z hz
    rw [← hshift, abs_of_nonpos ht] at h1
    refine h1.trans (le_of_eq ?_)
    have he : Real.exp (ξ * (-t * ((M₀ - m₀) / 2))) * Real.exp (ξ * (t * ((m₀ + M₀) / 2))) =
        Real.exp (ξ * m₀ * t) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← he]; ring
  have hk : 0 < ξ * m₀ := mul_pos hξ hm₀
  set mid := (a + b) / 2 with hmid
  have hmid_lo : a < mid := by linarith
  have hmid_hi : mid < b := by linarith
  have hTop : Tendsto (fun t => c 0 * Real.exp (ξ * m₀ * t)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hk)).const_mul_atTop (hcpos 0)
  have hBot : Tendsto (fun t => c 0 * Real.exp (ξ * m₀ * t)) atBot (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hk)).const_mul (c 0)
    simpa using this
  obtain ⟨tp, htp⟩ := ((hTop.eventually_gt_atTop mid).and (eventually_ge_atTop 0)).exists
  obtain ⟨tm, htm⟩ := ((hBot.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < mid))).and
    (eventually_le_atBot 0)).exists
  have hcp : mid ≤ c tp := (htp.1.trans_le (hlow tp htp.2)).le
  have hcm : c tm ≤ mid := ((hhigh tm htm.2).trans_lt htm.1).le
  obtain ⟨t, ht⟩ := intermediate_value_univ tm tp hcont ⟨hcm, hcp⟩
  have hopen : IsOpen (c ⁻¹' Ioo a b) := isOpen_Ioo.preimage hcont
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hopen
    ⟨t, by simp only [mem_preimage, ht, mem_Ioo]; exact ⟨hmid_lo, hmid_hi⟩⟩
  have hL : lfppCrossingLength ξ (H + (q : ℝ) • ψ) = ENNReal.ofReal (c q) :=
    (ENNReal.ofReal_toReal (lfppCrossingLength_lt_top ξ _).ne).symm
  refine ⟨q, ?_⟩
  rw [hL]
  exact ⟨(ENNReal.ofReal_lt_ofReal_iff (hcpos q)).2 hq.1,
    (ENNReal.ofReal_lt_ofReal_iff (ha.trans hab)).2 hq.2⟩

end SupercriticalLQGUniqueness.B2.Normalizer
