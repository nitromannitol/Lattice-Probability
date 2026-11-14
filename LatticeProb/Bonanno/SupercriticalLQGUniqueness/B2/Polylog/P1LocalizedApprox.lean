/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedApprox at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedTail

 


















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP LQGMetric.DFGPS

 

lemma tendsto_log_inv_nhdsGT : Tendsto (fun ε : ℝ => Real.log ε⁻¹) (𝓝[>] 0) atTop :=
  Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero

lemma eventually_mem_Ioo01 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) 1 :=
  Ioo_mem_nhdsGT one_pos

 
lemma tendsto_rpow_mul_exp_neg_rpow (m : ℝ) {k q : ℝ} (hk : 0 < k) (hq : 0 < q) :
    Tendsto (fun t : ℝ => t ^ m * Real.exp (-k * t ^ (2 * q))) atTop (𝓝 0) := by
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m / (2 * q)) k hk).comp
    (tendsto_rpow_atTop (by positivity : 0 < 2 * q))
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Function.comp]
  rw [← Real.rpow_mul ht.le]
  congr 2
  field_simp

lemma epsilon_eq_exp_neg {ε : ℝ} (hε : 0 < ε) : ε = Real.exp (-Real.log ε⁻¹) := by
  rw [Real.log_inv, neg_neg, Real.exp_log hε]

 
lemma plRad_sq_div_sq (q : ℝ) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    plRad q ε ^ 2 / ε ^ 2 = Real.log ε⁻¹ ^ (2 * q) := by
  have ht := log_inv_pos hε
  rw [plRad, mul_pow, mul_div_right_comm, div_self (by have := hε.1; positivity), one_mul,
    ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  push_cast; ring_nf

 
lemma log_one_div_plRad_le (q : ℝ) (hq : 0 < q) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1)
    (ht : 1 ≤ Real.log ε⁻¹) : Real.log (1 / plRad q ε) ≤ Real.log ε⁻¹ := by
  have ht0 := log_inv_pos hε
  rw [plRad, one_div, Real.log_inv, Real.log_mul hε.1.ne' (Real.rpow_pos_of_pos ht0 q).ne',
    Real.log_rpow ht0]
  have : 0 ≤ q * Real.log (Real.log ε⁻¹) := mul_nonneg hq.le (Real.log_nonneg ht)
  have e : Real.log ε⁻¹ = -Real.log ε := Real.log_inv ε
  linarith

 
lemma eventually_plRad_le_sqrt (q : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), plRad q ε ≤ Real.sqrt ε := by
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero q (1 / 2) (by norm_num)).comp
    tendsto_log_inv_nhdsGT
  filter_upwards [h1.eventually (ge_mem_nhds one_pos), eventually_mem_Ioo01] with ε hε hε'
  simp only [Function.comp] at hε
  have he : ε = Real.exp (-Real.log ε⁻¹) := epsilon_eq_exp_neg hε'.1
  show ε * Real.log ε⁻¹ ^ q ≤ Real.sqrt ε
  generalize Real.log ε⁻¹ = t at hε he ⊢
  subst he
  rw [sqrt_exp_eq]
  have e2 : Real.exp (-t) = Real.exp (-t / 2) * Real.exp (-(1 / 2) * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e2, mul_assoc]
  calc Real.exp (-t / 2) * (Real.exp (-(1 / 2) * t) * t ^ q) ≤ Real.exp (-t / 2) * 1 :=
        mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact hε) (Real.exp_pos _).le
    _ = _ := mul_one _

 
lemma eventually_plZ_ge (q : ℝ) (hq : 0 < q) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : ε ∈ Ioo (0 : ℝ) 1, 1 / 2 ≤ plZ q ε hε := by
  have h1 := ((tendsto_rpow_mul_exp_neg_rpow 0 (by norm_num : (0 : ℝ) < 1 / 8) hq).comp
    tendsto_log_inv_nhdsGT).const_mul 2
  rw [mul_zero] at h1
  filter_upwards [h1.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with ε hε hε'
  simp only [Function.comp, Real.rpow_zero, one_mul] at hε
  have := one_sub_plZ_le q ε hε'
  rw [← plRad_sq_div_sq q hε'] at hε
  have e : -(1 / 8) * (plRad q ε ^ 2 / ε ^ 2) = -(plRad q ε ^ 2 / (8 * ε ^ 2)) := by ring
  rw [e] at hε
  linarith

 

lemma abs_plProf_le (q ε r : ℝ) : |plProf q ε r| ≤ 1 := by
  have h := plProf_mem_Icc q ε r
  rw [abs_le]; constructor <;> linarith [h.1, h.2]
lemma plProf_eq_zero (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) {r : ℝ} (hr : 0 ≤ r)
    (hρ : plRad q ε ≤ r) : plProf q ε r = 0 := by
  rw [plProf_eq q ε hε]
  exact plBump_eq_zero q ε hε (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]; exact hρ)

 
def diffProf (q ε r : ℝ) : ℝ := locProf (Real.log ε) (r : ℂ) - plProf q ε r

lemma abs_diffProf_le (q ε r : ℝ) : |diffProf q ε r| ≤ 1 := by
  have h1 := locProf_mem_Icc (Real.log ε) (r : ℂ)
  have h2 := plProf_mem_Icc q ε r
  rw [diffProf, abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma diffProf_eq_zero (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (hρ : plRad q ε ≤ Real.sqrt ε)
    {r : ℝ} (hr : 0 < r) (hra : r < plRad q ε / 2) : diffProf q ε r = 0 := by
  have hn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [diffProf, plProf_eq q ε hε, ← locBump_eq_locProf hε.1,
    locBump_eq_one ε hε.1 (by rw [hn]; linarith),
    plBump_eq_one q ε hε (by rw [hn]; linarith), sub_self]

lemma continuousOn_diffProf (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => diffProf q p.1 p.2) (Ioo (0 : ℝ) 1 ×ˢ univ) :=
  continuousOn_dfgpsProf.sub (continuousOn_plProf q)

lemma plTestT_apply' (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (z x : ℂ) :
    plTestT q (ε, z) x = plProf q ε ‖x - z‖ * heatKernel (ε ^ 2 / 2) z x := by
  rw [plTestT_of_mem q hε, plTest_apply, plBump_radial, plProf_eq q ε hε, norm_sub_rev]

 
def diffTestT (q : ℝ) (p : ℝ × ℂ) : TestC := locTestT p - plTestT q p

lemma continuousOn_diffTestT (q : ℝ) : ContinuousOn (diffTestT q) (Ioo (0 : ℝ) 1 ×ˢ univ) :=
  (continuousOn_locTestT.mono (prod_mono (fun _ hε => hε.1) subset_rfl)).sub
    (continuousOn_plTestT q)

lemma diffTestT_apply (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (z x : ℂ) :
    diffTestT q (ε, z) x = diffProf q ε ‖x - z‖ * heatKernel (ε ^ 2 / 2) z x := by
  have h1 : diffTestT q (ε, z) x = locTestT (ε, z) x - plTestT q (ε, z) x := rfl
  rw [h1, plTestT_apply' q ε hε, locTestT_of_pos hε.1, locTest_apply', locBump_radial,
    locBump_eq_locProf hε.1, norm_sub_rev, diffProf]
  ring

 

 


theorem lem_localized_approx_sup.{u} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → DistC} (hg : IsWholePlaneGFF g P) {q : ℝ} (hq : 0 < q) {U : Set ℂ}
    (hU : Bornology.IsBounded U) :
    ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : ε ∈ Ioo (0 : ℝ) 1,
      ∀ z ∈ closure U,
        (∃ L : ℝ, Tendsto (fun n : ℕ => g ω (heatTrunc (ε ^ 2 / 2) z n)) atTop (𝓝 L)) ∧
        |heatMollify ε (g ω) z - plMollify q ε hε (g ω) z| ≤ δ := by
  obtain ⟨H, hH⟩ := exists_isCircleAvgVersion hg
  obtain ⟨R, hR⟩ := hU.closure.subset_ball (0 : ℂ)
  obtain ⟨A, hA, hAb⟩ := lem2_2 hg hH R
  have hI : IsOpen (Ioo (0 : ℝ) 1) := isOpen_Ioo
  have hI0 : Ioo (0 : ℝ) 1 ⊆ Ioi 0 := fun ε hε => hε.1
  have hP1 := ae_pairing_eq_polarInt hg hH hI hI0 (plTestT q) (continuousOn_plTestT q)
    (plProf q) (continuousOn_plProf q) (fun ε _ r => abs_plProf_le q ε r)
    (fun ε hε z x => plTestT_apply' q ε hε z x)
  have hP2 := ae_pairing_eq_polarInt hg hH hI hI0 (diffTestT q) (continuousOn_diffTestT q)
    (diffProf q) (continuousOn_diffProf q) (fun ε _ r => abs_diffProf_le q ε r)
    (fun ε hε z x => diffTestT_apply q ε hε z x)
  filter_upwards [lem2_1GffApprox P g hg U hU, hP1, hP2, hAb (1 / 2) (by norm_num)] with
    ω hD hω1 hω2 hC δ hδ
  obtain ⟨C, hC⟩ := hC
  set C' := |C|
  have hC' : 0 ≤ C' := abs_nonneg C
  have hF : ∀ z ∈ closure U, ∀ r, 0 < r → |H r z ω| ≤ C' * ((A + 1) * |Real.log r| + 1) :=
    fun z hz r hr => abs_le_logBound hA.le (hC r hr z (hR hz))
  
  set Φ : ℝ → ℝ := fun t =>
    C' * (((A + 1) * (Real.log 2 + t) + 1) * Real.exp (-(1 / 4) * t ^ (2 * q)))
  set Ψ : ℝ → ℝ := fun t =>
    C' * (4 * Real.exp (-(1 / 8) * t ^ (2 * q)) * (t ^ (2 * q) * ((A + 1) * (t + 2) + 1)))
  have hΦ : Tendsto Φ atTop (𝓝 0) := by
    have k0 := tendsto_rpow_mul_exp_neg_rpow 0 (by norm_num : (0 : ℝ) < 1 / 4) hq
    have k1 := tendsto_rpow_mul_exp_neg_rpow 1 (by norm_num : (0 : ℝ) < 1 / 4) hq
    have := ((k0.const_mul ((A + 1) * Real.log 2 + 1)).add (k1.const_mul (A + 1))).const_mul C'
    simp only [mul_zero, add_zero] at this
    refine this.congr fun t => ?_
    simp only [Φ, Real.rpow_zero, Real.rpow_one]
    ring
  have hΨ : Tendsto Ψ atTop (𝓝 0) := by
    have k0 := tendsto_rpow_mul_exp_neg_rpow (2 * q) (by norm_num : (0 : ℝ) < 1 / 8) hq
    have k1 := tendsto_rpow_mul_exp_neg_rpow (2 * q + 1) (by norm_num : (0 : ℝ) < 1 / 8) hq
    have := ((k0.const_mul (2 * (A + 1) + 1)).add (k1.const_mul (A + 1))).const_mul (4 * C')
    simp only [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Ψ, Real.rpow_add ht, Real.rpow_one]
    ring
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have hΦε : Tendsto (fun ε => Φ (Real.log ε⁻¹) + 2 * C' * (A + 1) * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hΦ.comp tendsto_log_inv_nhdsGT).add (hid.const_mul (2 * C' * (A + 1)))
  have hΨε : Tendsto (fun ε => Ψ (Real.log ε⁻¹)) (𝓝[>] 0) (𝓝 0) := hΨ.comp tendsto_log_inv_nhdsGT
  have hδ3 : 0 < δ / 3 := by positivity
  filter_upwards [hD (δ / 3) hδ3, eventually_mem_Ioo01, eventually_plRad_le_sqrt q,
    eventually_plZ_ge q hq, tendsto_log_inv_nhdsGT.eventually (eventually_ge_atTop 1),
    hΦε.eventually (ge_mem_nhds hδ3), hΨε.eventually (ge_mem_nhds hδ3)] with
    ε h1 _ h3 h4 h5 h6 h7 hε z hz
  obtain ⟨hex, hDb⟩ := h1 hε.1 z hz
  refine ⟨hex, ?_⟩
  
  have e1 := hω1 ε hε z
  rw [plTestT_of_mem q hε] at e1
  have e2' : locMollify ε hε.1 (g ω) z - g ω (plTest q ε hε z) =
      polarInt (diffProf q) (fun r z => H r z ω) (ε, z) := by
    rw [← hω2 ε hε z, diffTestT, map_sub, locTestT_of_pos hε.1, plTestT_of_mem q hε]; rfl
  set Zε := plZ q ε hε
  have hZ0 : 0 < Zε := plZ_pos q ε hε
  have hZ1 : Zε ≤ 1 := plZ_le_one q ε hε
  have hZ2 : 1 / 2 ≤ Zε := h4 hε
  have hdec : heatMollify ε (g ω) z - plMollify q ε hε (g ω) z =
      (heatMollify ε (g ω) z - locMollify ε hε.1 (g ω) z) +
        polarInt (diffProf q) (fun r z => H r z ω) (ε, z) +
        (1 - Zε⁻¹) * polarInt (plProf q) (fun r z => H r z ω) (ε, z) := by
    rw [← e2', ← e1, plMollify]; ring
  
  set t := Real.log ε⁻¹
  set ρ := plRad q ε
  have hρ0 : 0 < ρ := plRad_pos q hε
  have hρ1 : ρ ≤ 1 := h3.trans (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hε.2.le)
  have hρε : ρ ^ 2 / ε ^ 2 = t ^ (2 * q) := plRad_sq_div_sq q hε
  have hT : |polarInt (diffProf q) (fun r z => H r z ω) (ε, z)| ≤ Φ t + 2 * C' * (A + 1) * ε := by
    have hT0 := abs_polarInt_tail_le hε.1 (by positivity : 0 < ρ / 2) (by linarith) hA.le hC'
      (fun r hr => hF z hz r hr) (fun r => abs_diffProf_le q ε r)
      (fun r hr hra => diffProf_eq_zero q ε hε h3 hr hra)
    refine hT0.trans ?_
    have hl : Real.log (1 / (ρ / 2)) ≤ Real.log 2 + t := by
      rw [show 1 / (ρ / 2) = 2 * (1 / ρ) by field_simp, Real.log_mul two_ne_zero (by positivity)]
      linarith [log_one_div_plRad_le q hq hε h5]
    have he : Real.exp (-(ρ / 2) ^ 2 / ε ^ 2) = Real.exp (-(1 / 4) * t ^ (2 * q)) := by
      rw [← hρε]; congr 1; ring
    rw [he]
    simp only [Φ]
    have hE := (Real.exp_pos (-(1 / 4) * t ^ (2 * q))).le
    have hA1 : 0 ≤ A + 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hl hA1, mul_nonneg hC' hE]
  have hHd : |(1 - Zε⁻¹) * polarInt (plProf q) (fun r z => H r z ω) (ε, z)| ≤ Ψ t := by
    have hH0 := abs_polarInt_head_le hε.1 hρ0 hρ1 hA.le hC' (fun r hr => hF z hz r hr)
      (fun r => abs_plProf_le q ε r) (fun r hr => plProf_eq_zero q ε hε (hρ0.le.trans hr) hr)
    have hL := log_one_div_plRad_le q hq hε h5
    have hz1 : |1 - Zε⁻¹| ≤ 4 * Real.exp (-(1 / 8) * t ^ (2 * q)) := by
      have hZb := one_sub_plZ_le q ε hε
      change 1 - Zε ≤ 2 * Real.exp (-(ρ ^ 2 / (8 * ε ^ 2))) at hZb
      have e : -(ρ ^ 2 / (8 * ε ^ 2)) = -(1 / 8) * t ^ (2 * q) := by
        rw [← hρε]; ring
      rw [e] at hZb
      have h1' : 1 - Zε⁻¹ = -((1 - Zε) / Zε) := by field_simp; ring
      rw [h1', abs_neg, abs_of_nonneg (div_nonneg (by linarith) hZ0.le), div_le_iff₀ hZ0]
      nlinarith [Real.exp_pos (-(1 / 8) * t ^ (2 * q))]
    have hh : 2 / ε ^ 2 * (C' * ((A + 1) * (ρ ^ 2 / 2 * Real.log (1 / ρ) + ρ ^ 2) + ρ ^ 2 / 2)) ≤
        C' * (t ^ (2 * q) * ((A + 1) * (t + 2) + 1)) := by
      have e : 2 / ε ^ 2 * (C' * ((A + 1) * (ρ ^ 2 / 2 * Real.log (1 / ρ) + ρ ^ 2) + ρ ^ 2 / 2)) =
          C' * (ρ ^ 2 / ε ^ 2 * ((A + 1) * (Real.log (1 / ρ) + 2) + 1)) := by
        have := hε.1; field_simp
      rw [e, hρε]
      have ht0 : 0 ≤ t ^ (2 * q) := Real.rpow_nonneg (log_inv_pos hε).le _
      gcongr
    rw [abs_mul]
    calc |1 - Zε⁻¹| * |polarInt (plProf q) (fun r z => H r z ω) (ε, z)|
        ≤ (4 * Real.exp (-(1 / 8) * t ^ (2 * q))) *
            (C' * (t ^ (2 * q) * ((A + 1) * (t + 2) + 1))) := by
          refine mul_le_mul hz1 (hH0.trans hh) (abs_nonneg _) (by positivity)
      _ = Ψ t := by simp only [Ψ]; ring
  rw [hdec]
  calc |heatMollify ε (g ω) z - locMollify ε hε.1 (g ω) z +
        polarInt (diffProf q) (fun r z => H r z ω) (ε, z) +
        (1 - Zε⁻¹) * polarInt (plProf q) (fun r z => H r z ω) (ε, z)|
      ≤ |heatMollify ε (g ω) z - locMollify ε hε.1 (g ω) z| +
        |polarInt (diffProf q) (fun r z => H r z ω) (ε, z)| +
        |(1 - Zε⁻¹) * polarInt (plProf q) (fun r z => H r z ω) (ε, z)| := abs_add_three _ _ _
    _ ≤ δ / 3 + δ / 3 + δ / 3 := by
        gcongr
        · exact hT.trans h6
        · exact hHd.trans h7
    _ = δ := by ring

end SupercriticalLQGUniqueness.B2.Polylog
