/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCoord.WPModulus at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.WPLimit
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaOffsetsModulus

/-!
At a point
`z` and a scale `ε`, for offsets `a ∈ [1, 2]`,

  `wDens (a ε) z = wDens (2ε) z · H(a)`, `H(a) = (a/2)^{γ²/2} e^{γ Φ(a)}`,
  `Φ(a) = X_{aε}(z) − X_{2ε}(z)`,

with the band process `Φ` independent of `X_{2ε}(z) − X_δ(0)` and with independent Gaussian
increments `Var(Φ(b') − Φ(b)) = log(b/b')`. Hence (QuantumZipper's dyadic chaining
`AllOffsets.chain_bound`, `chainT`, `θm = 7/8`):

* `bandH_moment`: `E (H(b) − H(b'))⁴ ≤ C (b − b')²`;
* `chainT_band_moment`: `E chainT m n H ≤ (8 + 4C) θ^m`;
* `lintegral_wDens_chainT_le`: `E[wDens (2ε) z · chainT m n H] ≤ δ^{γ²/2} (8 + 4C) θ^m`.

The proofs copy QuantumZipper's, with the free-boundary folded-circle increments `fcPairVal`
replaced by LQGMetric's whole-plane increments `cInc` (laws `hasLaw_cInc_same`, independence from
`incCov_nested_band`, `incCov_nested_inner`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric LQGMetric.CircleAvg QuantumZipper QuantumZipper.TwoRadius QuantumZipper.AllOffsets
open MatedCRTHarmonic.MoTPort.ConeArea6 (indepFun_incProc)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}

/-- the band increment `Φ(a) = X_{aε}(z) − X_{2ε}(z)` -/
def bandΦ (X : Ω → DistC) (z : ℂ) (ε a : ℝ) (ω : Ω) : ℝ := cInc X (a * ε) z (2 * ε) z ω

/-- `H(a) = (a/2)^{γ²/2} e^{γ Φ(a)}` -/
def bandH (γ : ℝ) (X : Ω → DistC) (z : ℂ) (ε a : ℝ) (ω : Ω) : ℝ :=
  (a / 2) ^ (γ ^ 2 / 2) * exp (γ * bandΦ X z ε a ω)

omit [MeasurableSpace Ω] in
/-- the density at an offset radius factors through the band process -/
lemma wDens_offset_eq (γ δ : ℝ) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) (z : ℂ) (ω : Ω) :
    wDens γ X δ (a * ε) z ω = wDens γ X δ (2 * ε) z ω * bandH γ X z ε a ω := by
  have h1 : (a * ε) ^ (γ ^ 2 / 2) = (2 * ε) ^ (γ ^ 2 / 2) * (a / 2) ^ (γ ^ 2 / 2) := by
    rw [← mul_rpow (by positivity) (by positivity)]; congr 1; ring
  have h2 : exp (γ * cInc X (a * ε) z δ 0 ω) = exp (γ * cInc X (2 * ε) z δ 0 ω) *
      exp (γ * bandΦ X z ε a ω) := by
    rw [← exp_add]; congr 1; simp only [bandΦ, cInc]; ring
  rw [wDens, wDens, bandH, h1, h2]; ring

theorem bandH_moment [IsProbabilityMeasure P] (hX : IsWholePlaneGFF X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {z : ℂ} {ε : ℝ} (hε : 0 < ε) {b b' : ℝ}
    (hb'1 : 1 ≤ b') (hbb' : b' ≤ b) (hb2 : b ≤ 2) (hd : b - b' ≤ 1 / 2) :
    Integrable (fun ω => (bandH γ X z ε b ω - bandH γ X z ε b' ω) ^ 4) P ∧
    ∫ ω, (bandH γ X z ε b ω - bandH γ X z ε b' ω) ^ 4 ∂P ≤
      5436416 * exp 32 * (b - b') ^ 2 := by
  have hb0 : 0 < b' := by linarith
  have hb : 0 < b := by linarith
  have hbε : 0 < b * ε := mul_pos hb hε
  have hb'ε : 0 < b' * ε := mul_pos hb0 hε
  have h2ε : 0 < 2 * ε := by positivity
  have hbε2 : b * ε ≤ 2 * ε := by nlinarith
  have hb'εb : b' * ε ≤ b * ε := by nlinarith
  set Δ : Ω → ℝ := cInc X (b' * ε) z (b * ε) z with hΔ
  set s : ℝ := log (b / b') with hs
  have hs0 : 0 ≤ s := log_nonneg ((one_le_div hb0).2 hbb')
  have hsle : s ≤ b - b' := by
    have h1 := log_le_sub_one_of_pos (div_pos hb hb0)
    have h2 : b / b' - 1 ≤ b - b' := by
      rw [div_sub_one hb0.ne', div_le_iff₀ hb0]; nlinarith
    rw [hs]; linarith
  have hsplit : ∀ ω, bandΦ X z ε b' ω = bandΦ X z ε b ω + Δ ω := by
    intro ω; simp only [bandΦ, hΔ, cInc]; ring
  have hrp : (b' / 2) ^ (γ ^ 2 / 2) = (b / 2) ^ (γ ^ 2 / 2) * exp (-((2 * γ) ^ 2 / 8 * s)) := by
    rw [show b' / 2 = (b / 2) * (b' / b) by field_simp, mul_rpow (by positivity) (by positivity),
      rpow_def_of_pos (div_pos hb0 hb), hs, log_div hb0.ne' hb.ne', log_div hb.ne' hb0.ne']
    congr 2; ring
  set A : Ω → ℝ := fun ω => ((b / 2) ^ (γ ^ 2 / 2)) ^ 4 * exp (4 * γ * bandΦ X z ε b ω)
    with hA
  set B : Ω → ℝ := fun ω => tiltY (2 * γ) s (Δ ω) ^ 4 with hB
  have hH : (fun ω => (bandH γ X z ε b ω - bandH γ X z ε b' ω) ^ 4) = A * B := by
    funext ω
    simp only [Pi.mul_apply, hA, hB, bandH, hsplit ω, hrp, tiltY]
    have e4 : exp (4 * γ * bandΦ X z ε b ω) = exp (γ * bandΦ X z ε b ω) ^ 4 := by
      rw [← exp_nat_mul]; congr 1; push_cast; ring
    rw [e4, mul_add, exp_add]
    have e5 : exp (-((2 * γ) ^ 2 / 8 * s) + 2 * γ / 2 * Δ ω) =
        exp (-((2 * γ) ^ 2 / 8 * s)) * exp (γ * Δ ω) := by
      rw [← exp_add]; congr 1; ring
    rw [e5]
    ring
  have hLΦ : HasLaw (bandΦ X z ε b) (gaussianReal 0 (log (2 * ε / (b * ε))).toNNReal) P :=
    hasLaw_cInc_same hX hbε hbε2
  have hLΔ : HasLaw Δ (gaussianReal 0 s.toNNReal) P := by
    have := hasLaw_cInc_same hX (z := z) hb'ε hb'εb
    rwa [show b * ε / (b' * ε) = b / b' by field_simp] at this
  have hI : IndepFun Δ (bandΦ X z ε b) P := by
    have h := indepFun_incProc hX
      (fun _ : Unit => (((⟨b' * ε, hb'ε⟩, z), (⟨b * ε, hbε⟩, z)) : IncIdx))
      (fun _ : Unit => (((⟨b * ε, hbε⟩, z), (⟨2 * ε, h2ε⟩, z)) : IncIdx))
      (fun _ _ => incCov_nested_band hb'ε hb'εb hbε2)
    exact h.comp (measurable_pi_apply ()) (measurable_pi_apply ())
  have hIAB : IndepFun A B P := by
    have hmA : Measurable (fun x : ℝ => ((b / 2) ^ (γ ^ 2 / 2)) ^ 4 * exp (4 * γ * x)) := by
      fun_prop
    have hmB : Measurable (fun d : ℝ => tiltY (2 * γ) s d ^ 4) :=
      (measurable_tiltY (2 * γ) s).pow_const 4
    exact (hI.symm.comp hmA hmB)
  have hiA : Integrable A P := by
    have := hLΦ.integrable_fun_comp (integrable_exp_mul_add_gaussianReal _ (4 * γ) 0)
    simp only [zero_add] at this
    exact this.const_mul _
  have hmomB := tiltY_pow4_moment (2 * γ) s.toNNReal
  rw [Real.coe_toNNReal _ hs0] at hmomB
  have hiB : Integrable B P := hLΔ.integrable_fun_comp hmomB.1
  have hEA : ∫ ω, A ω ∂P ≤ exp 32 := by
    have h1 : ∫ ω, exp (0 + 4 * γ * bandΦ X z ε b ω) ∂P =
        exp (0 + (log (2 * ε / (b * ε))).toNNReal * (4 * γ) ^ 2 / 2) := by
      rw [← integral_exp_mul_add_gaussianReal]
      exact hLΦ.integral_comp (f := fun x => exp (0 + 4 * γ * x)) (by fun_prop)
    simp only [zero_add] at h1
    rw [hA, integral_const_mul, h1]
    have hq1 : ((b / 2) ^ (γ ^ 2 / 2)) ^ 4 ≤ 1 :=
      pow_le_one₀ (by positivity) (rpow_le_one (by positivity) (by linarith) (by positivity))
    have hv : ((log (2 * ε / (b * ε))).toNNReal : ℝ) ≤ 1 := by
      rw [show 2 * ε / (b * ε) = 2 / b by field_simp, log_div two_ne_zero hb.ne']
      have hl : log 2 ≤ 1 := by
        have := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      have hlb : 0 ≤ log b := log_nonneg (by linarith)
      have hl0 : 0 ≤ log 2 - log b := by
        have := log_le_log hb hb2; linarith
      rw [Real.coe_toNNReal _ hl0]; linarith
    have hexp : exp ((log (2 * ε / (b * ε))).toNNReal * (4 * γ) ^ 2 / 2) ≤ exp 32 := by
      apply exp_le_exp.2
      have : (4 * γ) ^ 2 ≤ 64 := by nlinarith
      have h0 : (0 : ℝ) ≤ ((log (2 * ε / (b * ε))).toNNReal : ℝ) := NNReal.coe_nonneg _
      nlinarith
    calc ((b / 2) ^ (γ ^ 2 / 2)) ^ 4 *
          exp ((log (2 * ε / (b * ε))).toNNReal * (4 * γ) ^ 2 / 2)
        ≤ 1 * exp 32 := mul_le_mul hq1 hexp (exp_pos _).le zero_le_one
      _ = exp 32 := one_mul _
  have hEB : ∫ ω, B ω ∂P ≤ 5436416 * (b - b') ^ 2 := by
    simp only [hB]
    rw [show (∫ ω, tiltY (2 * γ) s (Δ ω) ^ 4 ∂P) =
        ∫ d, tiltY (2 * γ) s d ^ 4 ∂(gaussianReal 0 s.toNNReal)
      from hLΔ.integral_comp (f := fun d => tiltY (2 * γ) s d ^ 4)
        ((measurable_tiltY (2 * γ) s).pow_const 4).aestronglyMeasurable]
    rw [hmomB.2]
    set x := γ ^ 2 * s with hx
    have hx0 : 0 ≤ x := by positivity
    have hxs : x ≤ 4 * s := by
      rw [hx]; have : γ ^ 2 ≤ 4 := by nlinarith
      nlinarith
    have hx2 : x ≤ 2 := by linarith
    have e2 : 2 * ((2 * γ) ^ 2 / 8 * s) = x := by rw [hx]; ring
    have e6 : 6 * ((2 * γ) ^ 2 / 8 * s) = 3 * x := by rw [hx]; ring
    have e12 : 12 * ((2 * γ) ^ 2 / 8 * s) = 6 * x := by rw [hx]; ring
    rw [e2, e6, e12]
    have := AreaOffsets.tilt_moment_bound2 hx0 hx2
    have hxb : x ^ 2 ≤ 16 * (b - b') ^ 2 := by nlinarith
    nlinarith
  have hB0 : 0 ≤ ∫ ω, B ω ∂P := integral_nonneg fun ω => by simp only [hB]; positivity
  rw [hH]
  refine ⟨hIAB.integrable_mul hiA hiB, ?_⟩
  rw [hIAB.integral_mul_eq_mul_integral hiA.aestronglyMeasurable hiB.aestronglyMeasurable]
  calc (∫ ω, A ω ∂P) * ∫ ω, B ω ∂P ≤ exp 32 * (5436416 * (b - b') ^ 2) :=
        mul_le_mul hEA hEB hB0 (exp_pos _).le
    _ = 5436416 * exp 32 * (b - b') ^ 2 := by ring

/-- the modulus constant `8 + 4 · 5436416 e^{32}` -/
def modConst : ℝ := 8 + 4 * (5436416 * exp 32)

lemma modConst_nonneg : 0 ≤ modConst := by unfold modConst; positivity

/-- `E chainT m n H ≤ (8 + 4C) θ^m` -/
theorem chainT_band_moment [IsProbabilityMeasure P] (hX : IsWholePlaneGFF X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {z : ℂ} {ε : ℝ} (hε : 0 < ε) (m n : ℕ) :
    Integrable (fun ω => chainT m n (fun a => bandH γ X z ε a ω)) P ∧
    ∫ ω, chainT m n (fun a => bandH γ X z ε a ω) ∂P ≤ modConst * θm ^ m := by
  set Cm := 5436416 * exp 32 with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  have hpair : ∀ j l : ℕ, l ∈ Finset.range (2 ^ (j + 1) + 1) →
      Integrable (fun ω => (bandH γ X z ε (dpt (j + 1) l) ω -
        bandH γ X z ε (dpt j (l / 2)) ω) ^ 4) P ∧
      ∫ ω, (bandH γ X z ε (dpt (j + 1) l) ω - bandH γ X z ε (dpt j (l / 2)) ω) ^ 4 ∂P ≤
        Cm * (1 / 2 ^ (j + 1)) ^ 2 := by
    intro j l hl
    have hl' := Finset.mem_range.1 hl
    have hd0 := dpt_diff_nonneg j l
    have hd1 := dpt_diff_le j l
    have h12 : (1 : ℝ) / 2 ^ (j + 1) ≤ 1 / 2 := by
      have : (2 : ℝ) ≤ 2 ^ (j + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      exact one_div_le_one_div_of_le (by norm_num) this
    obtain ⟨hi, hb⟩ := bandH_moment hX hγ hγ2 hε (z := z) (b := dpt (j + 1) l)
      (b' := dpt j (l / 2)) (dpt_ge_one j (l / 2)) (by linarith) (dpt_le_two (by omega))
      (by linarith)
    exact ⟨hi, hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd0 hd1 2) hCm0)⟩
  have hincr : ∀ j, Integrable (fun ω => incr j (fun a => bandH γ X z ε a ω)) P ∧
      ∫ ω, incr j (fun a => bandH γ X z ε a ω) ∂P ≤ Cm / 2 ^ j := by
    intro j
    have hint : Integrable (fun ω => incr j (fun a => bandH γ X z ε a ω)) P := by
      unfold incr
      exact integrable_finsetSum _ fun l hl => (hpair j l hl).1
    refine ⟨hint, ?_⟩
    unfold incr
    rw [integral_finsetSum _ fun l hl => (hpair j l hl).1]
    refine (Finset.sum_le_sum fun l hl => (hpair j l hl).2).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hy : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    push_cast
    rw [pow_succ, div_pow, one_pow, mul_pow,
      show ((2 : ℝ) ^ j * 2 + 1) * (Cm * (1 / ((2 ^ j) ^ 2 * 2 ^ 2))) =
        Cm * (2 ^ j * 2 + 1) / ((2 ^ j) ^ 2 * 4) by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hCm0 (by linarith : (0 : ℝ) ≤ 2 ^ j - 1),
      mul_nonneg (mul_nonneg hCm0 (by linarith : (0 : ℝ) ≤ 2 ^ j - 1))
        (by linarith : (0:ℝ) ≤ 2 ^ j)]
  have hjint : ∀ j, Integrable (fun ω => θm ^ j +
      incr j (fun a => bandH γ X z ε a ω) / θm ^ (3 * j)) P :=
    fun j => (integrable_const _).add ((hincr j).1.div_const _)
  have hint : Integrable (fun ω => chainT m n (fun a => bandH γ X z ε a ω)) P := by
    unfold chainT
    exact integrable_finsetSum _ fun j _ => hjint j
  refine ⟨hint, ?_⟩
  unfold chainT
  rw [integral_finsetSum _ fun j _ => hjint j]
  have hterm : ∀ j ∈ Finset.Ico m n, ∫ ω, (θm ^ j +
      incr j (fun a => bandH γ X z ε a ω) / θm ^ (3 * j)) ∂P ≤
      θm ^ j + Cm * (256 / 343 : ℝ) ^ j := by
    intro j _
    rw [integral_add (integrable_const _) ((hincr j).1.div_const _), integral_const,
      integral_div]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have h := div_le_div_of_nonneg_right (hincr j).2 (pow_pos θm_pos (3 * j)).le
    rw [div_eq_mul_one_div Cm, mul_div_assoc, ratio_eq] at h
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := sum_Ico_geom_le θm_pos.le θm_lt_one m n
  have h2 := sum_Ico_geom_le (q := 256 / 343) (by norm_num) (by norm_num) m n
  have hq : (256 / 343 : ℝ) ^ m ≤ θm ^ m :=
    pow_le_pow_left₀ (by norm_num) (by norm_num [θm]) m
  have hθ0 := pow_nonneg θm_pos.le m
  have h2' : ∑ j ∈ Finset.Ico m n, (256 / 343 : ℝ) ^ j ≤ 4 * θm ^ m := by
    refine h2.trans ?_
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have h1' : ∑ j ∈ Finset.Ico m n, θm ^ j ≤ 8 * θm ^ m := by
    refine h1.trans (le_of_eq ?_)
    rw [show (1 : ℝ) - θm = 1 / 8 by norm_num [θm]]
    ring
  unfold modConst
  nlinarith [mul_le_mul_of_nonneg_left h2' hCm0]

/-- the band family is independent of the normalized coarse value `X_{2ε}(z) − X_δ(0)` -/
theorem indepFun_band (hX : IsWholePlaneGFF X P) {z : ℂ} {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (h : ‖z‖ + 2 * ε ≤ δ) :
    IndepFun (fun ω (a : Set.Icc (1 : ℝ) 2) => bandΦ X z ε a.1 ω)
      (fun ω (_ : Unit) => cInc X (2 * ε) z δ 0 ω) P := by
  have h2ε : (0 : ℝ) < 2 * ε := by positivity
  have hpos : ∀ a : Set.Icc (1 : ℝ) 2, 0 < a.1 * ε := fun a =>
    mul_pos (by linarith [a.2.1]) hε
  let f : Set.Icc (1 : ℝ) 2 → IncIdx := fun a => ((⟨a.1 * ε, hpos a⟩, z), (⟨2 * ε, h2ε⟩, z))
  let g : Unit → IncIdx := fun _ => ((⟨2 * ε, h2ε⟩, z), (⟨δ, hδ⟩, 0))
  have hcov : ∀ a t, incCov (f a).1.2 (f a).1.1 (f a).2.2 (f a).2.1
      (g t).1.2 (g t).1.1 (g t).2.2 (g t).2.1 = 0 := fun a _ =>
    incCov_nested_inner (hpos a) (mul_le_mul_of_nonneg_right a.2.2 hε.le) h
  have hI := indepFun_incProc hX f g hcov
  have e1 : (fun ω (a : Set.Icc (1 : ℝ) 2) => bandΦ X z ε a.1 ω) =
      fun ω a => incProc X (f a) ω := rfl
  have e2 : (fun ω (_ : Unit) => cInc X (2 * ε) z δ 0 ω) = fun ω t => incProc X (g t) ω := rfl
  rw [e1, e2]
  exact hI

/-- **The modulus bound**: `E[wDens (2ε) z · chainT m n H] ≤ δ^{γ²/2} (8 + 4C) θ^m`. -/
theorem lintegral_wDens_chainT_le [IsProbabilityMeasure P] (hX : IsWholePlaneGFF X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ ε : ℝ} {z : ℂ} (hε : 0 < ε)
    (h : ‖z‖ + 2 * ε ≤ δ) (m n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (wDens γ X δ (2 * ε) z ω *
        chainT m n (fun a => bandH γ X z ε a ω)) ∂P ≤
      ENNReal.ofReal (δ ^ (γ ^ 2 / 2) * (modConst * θm ^ m)) := by
  have h2ε : 0 < 2 * ε := by positivity
  have hδ : 0 < δ := by linarith [norm_nonneg z]
  set G : Ω → ℝ := fun ω => chainT m n (fun a => bandH γ X z ε a ω) with hG
  set E0 : Ω → ℝ := fun ω => wDens γ X δ (2 * ε) z ω with hE0
  have hI0 := indepFun_band (P := P) hX hε hδ h
  let hfun : (Icc (1 : ℝ) 2 → ℝ) → ℝ → ℝ := fun φ a =>
    if h : a ∈ Icc (1 : ℝ) 2 then (a / 2) ^ (γ ^ 2 / 2) * exp (γ * φ ⟨a, h⟩) else 0
  have hmeas_pt : ∀ a : ℝ, Measurable (fun φ : Icc (1 : ℝ) 2 → ℝ => hfun φ a) := by
    intro a
    by_cases ha : a ∈ Icc (1 : ℝ) 2
    · simp only [hfun, ha, ↓reduceDIte]
      exact measurable_const.mul (((measurable_pi_apply _).const_mul _).exp)
    · simp only [hfun, ha, ↓reduceDIte]; exact measurable_const
  have hmG : Measurable (fun φ : Icc (1 : ℝ) 2 → ℝ => chainT m n (hfun φ)) := by
    unfold chainT incr
    exact Finset.measurable_sum _ fun j _ => measurable_const.add
      ((Finset.measurable_sum _ fun l _ =>
        ((hmeas_pt _).sub (hmeas_pt _)).pow_const 4).div_const _)
  have hGeq : G = (fun φ => chainT m n (hfun φ)) ∘
      (fun ω (a : Icc (1 : ℝ) 2) => bandΦ X z ε a.1 ω) := by
    funext ω
    simp only [Function.comp, hG]
    refine chainT_congr m n fun j l hl => ?_
    have hmem : dpt j l ∈ Icc (1 : ℝ) 2 := ⟨dpt_ge_one j l, dpt_le_two hl⟩
    simp only [hfun, hmem, ↓reduceDIte, bandH]
  have hE0eq : E0 = (fun v : Unit → ℝ => (2 * ε) ^ (γ ^ 2 / 2) * exp (γ * v ())) ∘
      (fun ω (_ : Unit) => cInc X (2 * ε) z δ 0 ω) := rfl
  have hI : IndepFun E0 G P := by
    rw [hGeq, hE0eq]
    exact (hI0.comp hmG (by fun_prop :
      Measurable (fun v : Unit → ℝ => (2 * ε) ^ (γ ^ 2 / 2) * exp (γ * v ())))).symm
  obtain ⟨hiE, hEE⟩ := integral_wDens hX γ h2ε h (P := P)
  obtain ⟨hiG, hEG⟩ := chainT_band_moment hX hγ hγ2 hε (z := z) m n
  have hint : Integrable (fun ω => E0 ω * G ω) P := hI.integrable_mul hiE hiG
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω =>
    mul_nonneg (wDens_pos γ δ h2ε z ω).le (chainT_nonneg _ _ _))]
  refine ENNReal.ofReal_le_ofReal ?_
  have hmul : ∫ ω, E0 ω * G ω ∂P = (∫ ω, E0 ω ∂P) * ∫ ω, G ω ∂P :=
    hI.integral_mul_eq_mul_integral hiE.aestronglyMeasurable hiG.aestronglyMeasurable
  rw [hmul]
  simp only [hE0] at hEE ⊢
  rw [hEE]
  exact mul_le_mul_of_nonneg_left hEG (Real.rpow_nonneg hδ.le _)

end MatedCRTHarmonic.LQGCoord
