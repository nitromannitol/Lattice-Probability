/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedPolar at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedCont
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1RadialMain

 



















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP LQGMetric.DFGPS

 
def polarInt (w : ℝ → ℝ → ℝ) (F : ℝ → ℂ → ℝ) (p : ℝ × ℂ) : ℝ :=
  2 / p.1 ^ 2 * ∫ r in Ioi 0, r * F r p.2 * w p.1 r * Real.exp (-r ^ 2 / p.1 ^ 2)

 
lemma abs_le_of_lem2_2 {A C r : ℝ} (hA : 0 ≤ A) (hr : 0 < r) {x : ℝ}
    (hx : |x| ≤ C * max (max (A * Real.log (1 / r)) (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1) :
    |x| ≤ |C| * (A / r + r + 1) := by
  have hm := max_log_le hA hr
  have hm1 : (1 : ℝ) ≤ max (max (A * Real.log (1 / r))
      (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 := le_max_right _ _
  calc |x| ≤ C * max (max (A * Real.log (1 / r)) (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 := hx
    _ ≤ |C| * max (max (A * Real.log (1 / r)) (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
    _ ≤ |C| * (A / r + r + 1) := mul_le_mul_of_nonneg_left hm (abs_nonneg C)

 

theorem continuousOn_polarInt {I : Set ℝ} (hI : IsOpen I) (hI0 : I ⊆ Ioi 0) {w : ℝ → ℝ → ℝ}
    (hw : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (I ×ˢ univ))
    (hw1 : ∀ ε ∈ I, ∀ r, |w ε r| ≤ 1) {F : ℝ → ℂ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℂ => F p.1 p.2) (Ioi 0 ×ˢ univ))
    (hb : ∀ R : ℝ, ∃ A C : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 0 < r → ∀ z ∈ ball (0 : ℂ) R,
      |F r z| ≤ C * max (max (A * Real.log (1 / r)) (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1) :
    ContinuousOn (polarInt w F) (I ×ˢ univ) := by
  refine continuousOn_of_forall_continuousAt fun p0 hp0 => ?_
  obtain ⟨ε0, z0⟩ := p0
  have hεI : ε0 ∈ I := (mem_prod.1 hp0).1
  have hε0 : 0 < ε0 := hI0 hεI
  obtain ⟨A, C, hA, hC⟩ := hb (‖z0‖ + 1)
  set b := 2 * ε0
  have hb0 : 0 < b := by positivity
  have hN : ∀ᶠ p : ℝ × ℂ in 𝓝 (ε0, z0), p.1 ∈ I ∧ p.1 < b ∧
      p.2 ∈ ball (0 : ℂ) (‖z0‖ + 1) := by
    have h1 : ∀ᶠ p : ℝ × ℂ in 𝓝 (ε0, z0), p.1 ∈ I :=
      continuous_fst.continuousAt.eventually (hI.mem_nhds hεI)
    have h2 : ∀ᶠ p : ℝ × ℂ in 𝓝 (ε0, z0), p.1 < b :=
      continuous_fst.continuousAt.eventually (gt_mem_nhds (by simp only [b]; linarith))
    have h3 : ∀ᶠ p : ℝ × ℂ in 𝓝 (ε0, z0), p.2 ∈ ball (0 : ℂ) (‖z0‖ + 1) :=
      continuous_snd.continuousAt.eventually (isOpen_ball.mem_nhds (by simp))
    filter_upwards [h1, h2, h3] with p a1 a2 a3 using ⟨a1, a2, a3⟩
  set G : ℝ × ℂ → ℝ → ℝ := fun p r => r * F r p.2 * w p.1 r * Real.exp (-r ^ 2 / p.1 ^ 2)
  have hFr : ∀ z : ℂ, ContinuousOn (fun r => F r z) (Ioi 0) := fun z =>
    hF.comp (continuous_id.prodMk continuous_const).continuousOn fun r hr => ⟨hr, mem_univ _⟩
  have hwr : ∀ ε ∈ I, Continuous fun r => w ε r := fun ε hε =>
    continuousOn_univ.1 (hw.comp (continuous_const.prodMk continuous_id).continuousOn
      fun r _ => ⟨hε, mem_univ _⟩)
  have hInt : ContinuousAt (fun p : ℝ × ℂ => ∫ r in Ioi 0, G p r) (ε0, z0) := by
    refine continuousAt_of_dominated (bound := fun r => |C| * ((A + r ^ 2 + r) *
      Real.exp (-(1 / b ^ 2) * r ^ 2))) ?_ ?_ ?_ ?_
    · filter_upwards [hN] with p hp
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ((continuousOn_id.mul (hFr p.2)).mul (hwr p.1 hp.1).continuousOn).mul ?_
      exact (Real.continuous_exp.comp ((continuous_pow 2).neg.div_const _)).continuousOn
    · filter_upwards [hN] with p hp
      have hp1 : 0 < p.1 := hI0 hp.1
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
      have hr : 0 < r := hr
      have hFb : |F r p.2| ≤ |C| * (A / r + r + 1) := abs_le_of_lem2_2 hA hr (hC r hr p.2 hp.2.2)
      have hw1' := hw1 p.1 hp.1 r
      have he : Real.exp (-r ^ 2 / p.1 ^ 2) ≤ Real.exp (-(1 / b ^ 2) * r ^ 2) := by
        refine Real.exp_le_exp.2 ?_
        have hpb : p.1 ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hp1.le hp.2.1.le 2
        rw [neg_div, neg_mul, neg_le_neg_iff, one_div, inv_mul_eq_div]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpb
      simp only [G, Real.norm_eq_abs, abs_mul, abs_of_pos hr, abs_of_pos (Real.exp_pos _)]
      calc r * |F r p.2| * |w p.1 r| * Real.exp (-r ^ 2 / p.1 ^ 2)
          ≤ r * (|C| * (A / r + r + 1)) * 1 * Real.exp (-(1 / b ^ 2) * r ^ 2) := by
            gcongr
        _ = |C| * ((A + r ^ 2 + r) * Real.exp (-(1 / b ^ 2) * r ^ 2)) := by
            field_simp
    · exact ((integrableOn_gaussW A (by positivity)).const_mul _)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
      have hr : 0 < r := hr
      have hm : ((r, z0) : ℝ × ℂ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ) := ⟨hr, mem_univ _⟩
      have hS : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) := isOpen_Ioi.prod isOpen_univ
      have hH : ContinuousAt (fun p : ℝ × ℂ => F r p.2) (ε0, z0) := by
        have h2 : ContinuousAt (fun p : ℝ × ℂ => ((r, p.2) : ℝ × ℂ)) (ε0, z0) :=
          continuousAt_const.prodMk continuous_snd.continuousAt
        exact ContinuousAt.comp (g := fun q : ℝ × ℂ => F q.1 q.2)
          (f := fun p : ℝ × ℂ => ((r, p.2) : ℝ × ℂ)) (hF.continuousAt (hS.mem_nhds hm)) h2
      have hW : ContinuousAt (fun p : ℝ × ℂ => w p.1 r) (ε0, z0) := by
        have hm' : ((ε0, r) : ℝ × ℝ) ∈ I ×ˢ (univ : Set ℝ) := ⟨hεI, mem_univ _⟩
        have hS' : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
        have h2 : ContinuousAt (fun p : ℝ × ℂ => ((p.1, r) : ℝ × ℝ)) (ε0, z0) :=
          continuous_fst.continuousAt.prodMk continuousAt_const
        exact ContinuousAt.comp (g := fun q : ℝ × ℝ => w q.1 q.2)
          (f := fun p : ℝ × ℂ => ((p.1, r) : ℝ × ℝ)) (hw.continuousAt (hS'.mem_nhds hm')) h2
      have hE : ContinuousAt (fun p : ℝ × ℂ => Real.exp (-r ^ 2 / p.1 ^ 2)) (ε0, z0) :=
        Real.continuous_exp.continuousAt.comp (continuousAt_const.div
          (continuous_fst.continuousAt.pow 2) (by simpa using hε0.ne'))
      exact ((continuousAt_const.mul hH).mul hW).mul hE
  exact (continuousAt_const.div (continuous_fst.continuousAt.pow 2)
    (by simpa using hε0.ne')).mul hInt

lemma heatKernel_add_real' (ε : ℝ) (hε : 0 < ε) (z : ℂ) (r : ℝ) :
    2 * Real.pi * r * heatKernel (ε ^ 2 / 2) z (z + r) =
      2 / ε ^ 2 * (r * Real.exp (-r ^ 2 / ε ^ 2)) := by
  rw [heatKernel_add_real]
  have hpi := Real.pi_pos.ne'
  rw [show 2 * (ε ^ 2 / 2) = ε ^ 2 by ring]
  field_simp

 


theorem ae_pairing_eq_polarInt_pt.{u} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ} (hg : IsWholePlaneGFF g P)
    (hH : IsCircleAvgVersion g P H) (w : ℝ → ℝ → ℝ) (ε : ℝ) (hε : 0 < ε) (z : ℂ) (φ : TestC)
    (hφ : ∀ x, φ x = w ε ‖x - z‖ * heatKernel (ε ^ 2 / 2) z x) :
    ∀ᵐ ω ∂P, g ω φ = polarInt w (fun r z => H r z ω) (ε, z) := by
  have hrad : ∀ x : ℂ, φ x = φ (z + ((‖x - z‖ : ℝ) : ℂ)) := by
    intro x
    rw [hφ x, hφ, add_sub_cancel_left, Complex.norm_real, norm_norm, ← heatKernel_radial]
  filter_upwards [lem2_1RadialPairing P g H hg hH z φ hrad] with ω hω
  rw [hω, polarInt, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr : 0 < r := hr
  simp only
  rw [hφ, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have := heatKernel_add_real' ε hε z r
  calc 2 * Real.pi * r * (w ε r * heatKernel (ε ^ 2 / 2) z (z + ↑r)) * H r z ω
      = (2 * Real.pi * r * heatKernel (ε ^ 2 / 2) z (z + ↑r)) * (w ε r * H r z ω) := by ring
    _ = 2 / ε ^ 2 * (r * Real.exp (-r ^ 2 / ε ^ 2)) * (w ε r * H r z ω) := by rw [this]
    _ = _ := by ring

 


theorem ae_pairing_eq_polarInt.{u} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ} (hg : IsWholePlaneGFF g P)
    (hH : IsCircleAvgVersion g P H) {I : Set ℝ} (hI : IsOpen I) (hI0 : I ⊆ Ioi 0)
    (K : ℝ × ℂ → TestC) (hK : ContinuousOn K (I ×ˢ univ)) (w : ℝ → ℝ → ℝ)
    (hw : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (I ×ˢ univ))
    (hw1 : ∀ ε ∈ I, ∀ r, |w ε r| ≤ 1)
    (hKw : ∀ ε ∈ I, ∀ z x : ℂ, K (ε, z) x = w ε ‖x - z‖ * heatKernel (ε ^ 2 / 2) z x) :
    ∀ᵐ ω ∂P, ∀ ε ∈ I, ∀ z : ℂ, g ω (K (ε, z)) = polarInt w (fun r z => H r z ω) (ε, z) := by
  set S : Set (ℝ × ℂ) := I ×ˢ univ
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense S
  have hD : ∀ᵐ ω ∂P, ∀ q ∈ D, g ω (K q.1) = polarInt w (fun r z => H r z ω) q.1 := by
    refine (ae_ball_iff hDc).2 fun q _ => ?_
    obtain ⟨⟨ε, z⟩, hq⟩ := q
    have hεI : ε ∈ I := (mem_prod.1 hq).1
    exact ae_pairing_eq_polarInt_pt hg hH w ε (hI0 hεI) z _ (hKw ε hεI z)
  have hA : ∀ n : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ ζ : ℝ, 0 < ζ → ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ r : ℝ, 0 < r →
      ∀ z ∈ ball (0 : ℂ) n,
        |H r z ω| ≤ C * max (max (A * Real.log (1 / r)) (Real.log r ^ (1 / 2 + ζ))) 1 :=
    fun n => lem2_2 hg hH n
  choose A hA0 hAb using hA
  have hB : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ z ∈ ball (0 : ℂ) n,
      |H r z ω| ≤ C * max (max (A n * Real.log (1 / r))
        (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 :=
    ae_all_iff.2 fun n => hAb n (1 / 2) (by norm_num)
  filter_upwards [hD, hB] with ω hωD hωB ε hε z
  have hb : ∀ R : ℝ, ∃ A C : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 0 < r → ∀ z ∈ ball (0 : ℂ) R,
      |H r z ω| ≤ C * max (max (A * Real.log (1 / r))
        (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 := by
    intro R
    obtain ⟨C, hC⟩ := hωB ⌈R⌉₊
    exact ⟨A ⌈R⌉₊, C, (hA0 _).le, fun r hr z hz =>
      hC r hr z (ball_subset_ball (Nat.le_ceil R) hz)⟩
  have hR : ContinuousOn (polarInt w fun r z => H r z ω) S :=
    continuousOn_polarInt hI hI0 hw hw1 (hH.cont ω) hb
  have hL : ContinuousOn (fun p => g ω (K p)) S := (map_continuous (g ω)).comp_continuousOn hK
  have heq : S.domRestrict (fun p => g ω (K p)) = S.domRestrict (polarInt w fun r z => H r z ω) :=
    Continuous.ext_on hDd (continuousOn_iff_continuous_domRestrict.1 hL)
      (continuousOn_iff_continuous_domRestrict.1 hR) fun q hq => hωD q hq
  exact congrFun heq ⟨(ε, z), ⟨hε, mem_univ _⟩⟩

end SupercriticalLQGUniqueness.B2.Polylog
