/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCoord.ConeTight at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ConeArea
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea6D
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FractionalMoments

/-!
For a whole-plane GFF `X`, `0 < γ < 2` and `0 ≤ c < Q`, almost surely: for every
`ε > 0` there is `r₀ > 0` with

  `∫_{B(0,r₀)} max(|w|, s)^{−γc} d(areaS γ X s)(w) ≤ ε` for every `0 < s ≤ r₀`

(`ae_tight_wp`; this is `ConeGood.tight`, the input that makes the cone singularity harmless).

Proof. On the dyadic annuli the weight is `≤ 2^{γc} 2^{γcn}` (`weight_le_tsum`), so the integral is
bounded by `2^{γc} Σ_{n ≥ J} 2^{γcn} sup_{0 < s ≤ 2·2^{-n}} μ_s(B̄(0, 2^{-n}))`. With the window
`(B̄(0,2^{-n}), δ = 4·2^{-n})`, `μ_s(B̄(0,2^{-n})) ≤ e^{γ X_δ(0)} wMassSup` (`WPOffsets`), and
`E (e^{γ(X_δ(0) − X_1(0))} wMassSup)^p ≤ C 2^{-n p (γQ − pγ²)}` (Cauchy–Schwarz as in MoTPort's
`ConeArea6D`, Jensen for `x ↦ x^{2p}`, `E wMassSup ≤ C δ^{2+γ²/2}`); QuantumZipper's
`AtomlessUncond.ae_tsum_ne_top_of_moments` (Borel–Cantelli for fractional moments) gives
`Σ_n 2^{γcn} e^{−γ X_1(0)} · (…) < ∞` a.s. when `γc + pγ² < γQ`. (Duplantier–Sheffield,
Invent. Math. 185 (2011), §3.2, the multifractal bound at a fixed point; QuantumZipper M4-P3(b)
and dyadic-radius bounds from `MoTPort`.)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.CellScaling QuantumZipper

/-! ## Dyadic radii -/

lemma radius_rpow_neg (n : ℕ) (a : ℝ) : radius n ^ (-a) = (2 : ℝ) ^ (a * n) := by
  rw [radius, inv_pow, ← Real.rpow_natCast, Real.inv_rpow (by positivity),
    ← Real.rpow_neg_one, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
  congr 1; ring

lemma radius_le_one (n : ℕ) : radius n ≤ 1 := by
  rw [radius]; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma radius_succ' (n : ℕ) : radius (n + 1) = radius n / 2 := by
  rw [radius, radius, pow_succ]; ring

lemma radius_lt_radius_iff {m n : ℕ} : radius m < radius n ↔ n < m := by
  rw [radius, radius]
  exact pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)

/-- the dyadic bracket of `x ∈ (0, 1]` -/
lemma exists_radius_bracket {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ∃ n : ℕ, radius (n + 1) < x ∧ x ≤ radius n := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near (one_le_one_div hx0 hx1)
    (show (1 : ℝ) < 2 by norm_num)
  refine ⟨n, ?_, ?_⟩
  · rw [radius, inv_pow, inv_lt_comm₀ (by positivity) hx0]
    simpa [one_div] using h2
  · rw [radius, inv_pow, le_inv_comm₀ hx0 (by positivity)]
    simpa [one_div] using h1

/-! ## The dyadic weight bound -/

/-- the pointwise dyadic bound of the weight `max(|w|, s)^{−λ}` -/
lemma weight_le_tsum {lam s : ℝ} (hlam : 0 ≤ lam) (hs : 0 < s) {J : ℕ} (hsJ : s ≤ radius J)
    {w : ℂ} (hw : ‖w‖ ≤ radius J) :
    ENNReal.ofReal (max ‖w‖ s ^ (-lam)) ≤ ENNReal.ofReal (2 ^ lam) *
      ∑' n, (if J ≤ n ∧ s ≤ 2 * radius n then
        ENNReal.ofReal (2 ^ (lam * n)) * (closedBall (0 : ℂ) (radius n)).indicator 1 w else 0) := by
  have h2l : (1 : ℝ) ≤ 2 ^ lam := Real.one_le_rpow (by norm_num) hlam
  -- a single term dominates
  suffices h : ∃ n, J ≤ n ∧ s ≤ 2 * radius n ∧ ‖w‖ ≤ radius n ∧
      max ‖w‖ s ^ (-lam) ≤ 2 ^ lam * 2 ^ (lam * n) by
    obtain ⟨n, hJn, hsn, hwn, hle⟩ := h
    have hterm : ENNReal.ofReal (max ‖w‖ s ^ (-lam)) ≤ ENNReal.ofReal (2 ^ lam) *
        (if J ≤ n ∧ s ≤ 2 * radius n then ENNReal.ofReal (2 ^ (lam * n)) *
          (closedBall (0 : ℂ) (radius n)).indicator 1 w else 0) := by
      rw [if_pos ⟨hJn, hsn⟩, indicator_of_mem (by rw [mem_closedBall, dist_zero_right]; exact hwn),
        Pi.one_apply, mul_one, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hle
    exact hterm.trans (mul_le_mul' le_rfl (ENNReal.le_tsum (f := fun n => if J ≤ n ∧
      s ≤ 2 * radius n then ENNReal.ofReal (2 ^ (lam * n)) *
        (closedBall (0 : ℂ) (radius n)).indicator 1 w else 0) n))
  by_cases hcase : ‖w‖ < s / 2
  · -- the dyadic scale of `s`
    obtain ⟨m, hm1, hm2⟩ := exists_radius_bracket (show 0 < s / 2 by positivity)
      (by linarith [radius_le_one J])
    have hJm : J ≤ m := by
      have h1 : radius (m + 1) < radius (J + 1) := by
        rw [radius_succ' J]; linarith
      have := radius_lt_radius_iff.1 h1
      omega
    have hsm' : radius m < s := by rw [radius_succ'] at hm1; linarith
    refine ⟨m, hJm, by linarith, by linarith, ?_⟩
    have hmax : max ‖w‖ s = s := max_eq_right (by linarith)
    rw [hmax]
    calc s ^ (-lam) ≤ radius m ^ (-lam) :=
          Real.rpow_le_rpow_of_nonpos (QuantumZipper.radius_pos m) hsm'.le (by linarith)
      _ = 2 ^ (lam * m) := radius_rpow_neg m lam
      _ ≤ 2 ^ lam * 2 ^ (lam * m) := le_mul_of_one_le_left (by positivity) h2l
  · rw [not_lt] at hcase
    have hw0 : 0 < ‖w‖ := by linarith
    obtain ⟨n, hn1, hn2⟩ := exists_radius_bracket hw0 (hw.trans (radius_le_one J))
    have hJn : J ≤ n := by
      have := radius_lt_radius_iff.1 (hn1.trans_le hw)
      omega
    refine ⟨n, hJn, by linarith, hn2, ?_⟩
    calc max ‖w‖ s ^ (-lam) ≤ radius (n + 1) ^ (-lam) :=
          Real.rpow_le_rpow_of_nonpos (QuantumZipper.radius_pos _) (hn1.le.trans (le_max_left _ _))
            (by linarith)
      _ = 2 ^ (lam * (n + 1 : ℕ)) := radius_rpow_neg _ lam
      _ = 2 ^ lam * 2 ^ (lam * n) := by
          rw [← Real.rpow_add (by norm_num)]; push_cast; ring_nf

/-- the integrated dyadic bound -/
lemma lintegral_weight_le {lam s : ℝ} (hlam : 0 ≤ lam) (hs : 0 < s) {J : ℕ}
    (hsJ : s ≤ radius J) (μ : Measure ℂ) :
    ∫⁻ w in ball 0 (radius J), ENNReal.ofReal (max ‖w‖ s ^ (-lam)) ∂μ ≤
      ENNReal.ofReal (2 ^ lam) * ∑' n, (if J ≤ n ∧ s ≤ 2 * radius n then
        ENNReal.ofReal (2 ^ (lam * n)) * μ (closedBall (0 : ℂ) (radius n)) else 0) := by
  have hpt : ∀ w ∈ ball (0 : ℂ) (radius J), ENNReal.ofReal (max ‖w‖ s ^ (-lam)) ≤
      ENNReal.ofReal (2 ^ lam) * ∑' n, (if J ≤ n ∧ s ≤ 2 * radius n then
        ENNReal.ofReal (2 ^ (lam * n)) * (closedBall (0 : ℂ) (radius n)).indicator 1 w
        else 0) := fun w hw =>
    weight_le_tsum hlam hs hsJ (by
      rw [mem_ball, dist_zero_right] at hw; exact hw.le)
  have hm : ∀ n : ℕ, Measurable fun w : ℂ => (if J ≤ n ∧ s ≤ 2 * radius n then
      ENNReal.ofReal (2 ^ (lam * n)) * (closedBall (0 : ℂ) (radius n)).indicator 1 w else 0) := by
    intro n
    split_ifs
    · exact measurable_const.mul (measurable_one.indicator measurableSet_closedBall)
    · exact measurable_const
  refine (setLIntegral_mono (Measurable.const_mul (Measurable.ennreal_tsum hm) _) hpt).trans ?_
  rw [lintegral_const_mul _ (Measurable.ennreal_tsum hm), lintegral_tsum fun n => (hm n).aemeasurable]
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun n => ?_)
  split_ifs
  · rw [lintegral_const_mul _ (measurable_one.indicator measurableSet_closedBall)]
    refine mul_le_mul' le_rfl ?_
    rw [lintegral_indicator measurableSet_closedBall]
    simp only [Pi.one_apply, lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter]
    exact Measure.restrict_apply_le _ _
  · simp

/-! ## The windows at the cone point -/

/-- the disc `B̄(0, 2^{-n})` -/
def tS (n : ℕ) : Set ℂ := closedBall 0 (radius n)

/-- the window scale `4 · 2^{-n}` -/
def tδ (n : ℕ) : ℝ := 4 * radius n

/-- the indicator of `B̄(0, 2^{-n})` -/
def tF (n : ℕ) : ℂ → ℝ := (tS n).indicator 1

lemma tWin (n : ℕ) : Win (tS n) (tδ n) where
  meas := measurableSet_closedBall
  pos := by unfold tδ; have := QuantumZipper.radius_pos n; positivity
  sub := fun z hz => by
    simp only [tS, mem_closedBall, dist_zero_right] at hz
    unfold tδ; linarith

lemma tWinFun (n : ℕ) : WinFun (tS n) (tF n) 1 where
  meas := measurable_one.indicator measurableSet_closedBall
  bdd := fun z => by
    unfold tF
    by_cases hz : z ∈ tS n
    · rw [indicator_of_mem hz]; simp
    · rw [indicator_of_notMem hz]; simp
  zero := fun z hz => indicator_of_notMem hz _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}

omit [MeasurableSpace Ω] in
/-- **domination on the good event**: `μ_s(B̄(0,2^{-n})) ≤ e^{γ X_δ(0)} wMassSup` for
`0 < s ≤ 2 · 2^{-n}` -/
lemma areaS_tS_le {ω : Ω} (hg : GoodCirc (X ω)) (γ : ℝ) (n : ℕ) (L : Ω → ℝ) {s : ℝ}
    (hs : 0 < s) (hs2 : s ≤ 2 * radius n) :
    areaS γ (X ω) s (tS n) ≤ ENNReal.ofReal (Real.exp (γ * circleAvg (X ω) (tδ n) 0)) *
      wMassSup γ X (tδ n) (tF n) L ω := by
  have hfin : areaS γ (X ω) s (tS n) < ⊤ :=
    areaS_lt_top_of_good hg hs (isCompact_closedBall _ _)
  have h1 : ∫ z, tF n z ∂areaS γ (X ω) s = (areaS γ (X ω) s).real (tS n) :=
    integral_indicator_one measurableSet_closedBall
  have h2 := integral_areaS_eq_wMass (X := X) γ (tδ n) hs.le (tF n) ω
  have hsδ : s ≤ tδ n / 2 := by unfold tδ; linarith
  have h3 := ofReal_wMass_le_wMassSup hg γ (tWin n) (tWinFun n) L hs hsδ
  rw [← ofReal_measureReal hfin.ne, ← h1, h2]
  refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _), ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact mul_le_mul' le_rfl h3

/-! ## The fractional moments -/

/-- the constant of the fractional moment bound -/
def tightC (γ p : ℝ) : ℝ :=
  (π / 16 + sumC γ) ^ p * 4 ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2)

lemma tight_rpow_identity {δ K p γ : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) :
    (δ ^ (2 * p * (γ ^ 2 / 2)) * Real.exp ((Real.log 1 - Real.log δ) * (2 * p * γ) ^ 2 / 2))
        ^ (1 / 2 : ℝ) * (δ ^ 2 * K) ^ p =
      K ^ p * δ ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2) := by
  have he : Real.exp ((Real.log 1 - Real.log δ) * (2 * p * γ) ^ 2 / 2) =
      δ ^ (-(2 * p ^ 2 * γ ^ 2)) := by
    rw [Real.rpow_def_of_pos hδ, Real.log_one]; congr 1; ring
  have hδ2 : (δ ^ 2 : ℝ) ^ p = δ ^ (2 * p) := by
    rw [show (δ ^ 2 : ℝ) = δ ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul hδ.le]
  rw [he, ← Real.rpow_add hδ, ← Real.rpow_mul hδ.le, Real.mul_rpow (by positivity) hK, hδ2]
  rw [show ∀ a b c : ℝ, a * (b * c) = c * (a * b) from fun a b c => by ring,
    ← Real.rpow_add hδ]
  congr 2
  ring

lemma tδ_rpow (n : ℕ) (x : ℝ) : tδ n ^ x = 4 ^ x * (2 : ℝ) ^ ((n : ℝ) * (-x)) := by
  rw [tδ, Real.mul_rpow (by norm_num) (QuantumZipper.radius_pos n).le]
  congr 1
  rw [show x = -(-x) by ring, radius_rpow_neg n (-x)]
  congr 1; ring

theorem lintegral_tight_rpow_le (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {n : ℕ} (hn : 2 ≤ n) {L : Ω → ℝ}
    (hL : WMassLimit γ X P (tδ n) (tF n) 1 L) {p : ℝ} (hp0 : 0 < p) (hp : 2 * p ≤ 1) :
    ∫⁻ ω, (ENNReal.ofReal (Real.exp (γ * cInc X (tδ n) 0 1 0 ω)) *
        wMassSup γ X (tδ n) (tF n) L ω) ^ p ∂P ≤
      ENNReal.ofReal (tightC γ p) *
        ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * (-(p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2)))) := by
  have := hX.gaussian.isProbabilityMeasure
  set δ := tδ n with hδdef
  have hδ : 0 < δ := (tWin n).pos
  have hδ1 : δ ≤ 1 := by
    have : radius n ≤ radius 2 := by
      rw [radius, radius]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    rw [hδdef, tδ]
    have h2 : radius 2 = 1 / 4 := by rw [radius]; norm_num
    linarith
  set K := π / 16 + sumC γ with hKdef
  have hK : 0 ≤ K := add_nonneg (by positivity) (sumC_nonneg hγ hγ2)
  set W : Ω → ℝ≥0∞ := wMassSup γ X δ (tF n) L with hW
  have hWm : AEMeasurable W P := by
    refine (continuous_abs.measurable.comp_aemeasurable hL.aemeas).ennreal_ofReal.add ?_
    refine AEMeasurable.ennreal_tsum fun k => AEMeasurable.iSup fun m => AEMeasurable.iSup
      fun i => (continuous_abs.measurable.comp_aemeasurable
        ((measurable_wMass hX γ (tWinFun n) δ _).aemeasurable.sub hL.aemeas)).ennreal_ofReal
  have hWint : ∫⁻ ω, W ω ∂P ≤ ENNReal.ofReal (1 * δ ^ (2 + γ ^ 2 / 2) * K) :=
    lintegral_wMassSup_le hX hγ hγ2 (tWin n) (tWinFun n) hL
  set A : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (γ * cInc X δ 0 1 0 ω) * δ ^ (γ ^ 2 / 2)) with hA
  set W' : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (δ ^ (-(γ ^ 2 / 2))) * W ω with hW'
  have hfac : ∀ ω, ENNReal.ofReal (Real.exp (γ * cInc X δ 0 1 0 ω)) * W ω = A ω * W' ω := by
    intro ω
    rw [hA, hW', ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_assoc,
      ← Real.rpow_add hδ, add_neg_cancel, Real.rpow_zero, mul_one]
  have hAm : Measurable A := ENNReal.measurable_ofReal.comp
    ((((measurable_cInc hX _ _ _ _).const_mul γ).exp).mul_const _)
  have hW'm : AEMeasurable W' P := hWm.const_mul _
  -- Cauchy–Schwarz
  have hCS : ∫⁻ ω, (A ω * W' ω) ^ p ∂P ≤
      (∫⁻ ω, A ω ^ (2 * p) ∂P) ^ (1 / 2 : ℝ) * (∫⁻ ω, W' ω ^ (2 * p) ∂P) ^ (1 / 2 : ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
      (hAm.pow_const p).aemeasurable (hW'm.pow_const p)
    have e2 : ∀ x : ℝ≥0∞, (x ^ p) ^ (2 : ℝ) = x ^ (2 * p) := fun x => by
      rw [← ENNReal.rpow_mul, mul_comm]
    calc ∫⁻ ω, (A ω * W' ω) ^ p ∂P
        = ∫⁻ ω, ((fun ω => A ω ^ p) * fun ω => W' ω ^ p) ω ∂P :=
          lintegral_congr fun ω => ENNReal.mul_rpow_of_nonneg _ _ hp0.le
      _ ≤ _ := h
      _ = _ := by simp only [e2]
  have hAint := MoTPort.ConeArea6.lintegral_gaussFactor_rpow (P := P) γ hδ hδ1
    (by positivity : (0 : ℝ) ≤ 2 * p) (MoTPort.ConeArea6.hasLaw_cInc_center hX hδ hδ1)
  have hW'int : ∫⁻ ω, W' ω ^ (2 * p) ∂P ≤ ENNReal.ofReal ((δ ^ 2 * K) ^ (2 * p)) := by
    refine (FracMom.lintegral_rpow_le_rpow_lintegral hW'm (by positivity) hp).trans ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    rw [hW', lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (δ ^ (-(γ ^ 2 / 2))) * ∫⁻ ω, W ω ∂P
        ≤ ENNReal.ofReal (δ ^ (-(γ ^ 2 / 2))) * ENNReal.ofReal (1 * δ ^ (2 + γ ^ 2 / 2) * K) :=
          mul_le_mul' le_rfl hWint
      _ = ENNReal.ofReal (δ ^ 2 * K) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [one_mul, ← mul_assoc, ← Real.rpow_add hδ,
            show -(γ ^ 2 / 2) + (2 + γ ^ 2 / 2) = (2 : ℝ) by ring, Real.rpow_two]
  set a1 : ℝ := δ ^ (2 * p * (γ ^ 2 / 2)) *
    Real.exp ((Real.log 1 - Real.log δ) * (2 * p * γ) ^ 2 / 2) with ha1
  have ha10 : 0 ≤ a1 := by positivity
  calc ∫⁻ ω, (ENNReal.ofReal (Real.exp (γ * cInc X (tδ n) 0 1 0 ω)) * W ω) ^ p ∂P
      = ∫⁻ ω, (A ω * W' ω) ^ p ∂P := lintegral_congr fun ω => by rw [hfac ω]
    _ ≤ (∫⁻ ω, A ω ^ (2 * p) ∂P) ^ (1 / 2 : ℝ) * (∫⁻ ω, W' ω ^ (2 * p) ∂P) ^ (1 / 2 : ℝ) :=
        hCS
    _ ≤ (ENNReal.ofReal a1) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal ((δ ^ 2 * K) ^ (2 * p))) ^ (1 / 2 : ℝ) := by
        rw [hAint]
        exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hW'int (by norm_num))
    _ = ENNReal.ofReal (tightC γ p) *
          ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * (-(p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2)))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg ha10 (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by
            unfold tightC; positivity)]
        congr 1
        rw [← Real.rpow_mul (by positivity), show 2 * p * (1 / 2 : ℝ) = p by ring,
          tight_rpow_identity hδ hK, hδdef, tδ_rpow, tightC]
        ring

/-! ## Almost sure tightness -/

lemma tsum_ite_le_eq (f : ℕ → ℝ≥0∞) (J : ℕ) :
    ∑' n, (if J ≤ n then f n else 0) = ∑' k, f (k + J) := by
  let e : ℕ ≃ {n : ℕ | J ≤ n} :=
    { toFun := fun k => ⟨k + J, by simp⟩
      invFun := fun n => n.1 - J
      left_inv := fun k => by simp
      right_inv := fun n => by
        ext
        have := n.2
        simp only [mem_setOf_eq] at this
        simp only
        omega }
  have h1 : ∑' n, (if J ≤ n then f n else 0) = ∑' x : {n : ℕ | J ≤ n}, f x := by
    rw [tsum_subtype {n : ℕ | J ≤ n} f]
    refine tsum_congr fun n => ?_
    simp only [Set.indicator_apply, mem_setOf_eq]
  rw [h1, ← e.tsum_eq (fun x => f x)]
  rfl

/-- **almost sure tightness of the weighted whole-plane masses at `0`** (all radii) -/
theorem ae_tight_wp (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {c : ℝ}
    (hc0 : 0 ≤ c) (hcQ : c < lqgQ γ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ s : ℝ, 0 < s → s ≤ r₀ →
      ∫⁻ w in ball 0 r₀, ENNReal.ofReal (max ‖w‖ s ^ (-(γ * c))) ∂areaS γ (X ω) s ≤
        ENNReal.ofReal ε := by
  have := hX.gaussian.isProbabilityMeasure
  set lam := γ * c with hlam
  have hlam0 : 0 ≤ lam := mul_nonneg hγ.le hc0
  have hγQ : γ * lqgQ γ = 2 + γ ^ 2 / 2 := gamma_mul_lqgQ hγ.ne'
  have hgap0 : 0 < γ * lqgQ γ - lam := by
    rw [hlam, ← mul_sub]; exact mul_pos hγ (by linarith)
  set p := min (1 / 2) ((γ * lqgQ γ - lam) / (2 * γ ^ 2)) with hpdef
  have hp0 : 0 < p := lt_min (by norm_num) (by positivity)
  have hp : 2 * p ≤ 1 := by have := min_le_left (1 / 2 : ℝ) ((γ * lqgQ γ - lam) / (2 * γ ^ 2)); linarith
  have hp1 : p ≤ 1 := by linarith
  have hgap : lam + p * γ ^ 2 < γ * lqgQ γ := by
    have h1 : p ≤ (γ * lqgQ γ - lam) / (2 * γ ^ 2) := min_le_right _ _
    have h2 : p * γ ^ 2 ≤ (γ * lqgQ γ - lam) / 2 := by
      rw [le_div_iff₀ (by positivity)] at h1; nlinarith
    linarith
  set e : ℝ := -(p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2) with he
  have hneg : lam * p + e < 0 := by
    rw [he]; nlinarith
  choose L hL using fun n => exists_wMass_limit hX hγ hγ2 (tWin n) (tWinFun n) (P := P)
  set T : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (Real.exp (γ * cInc X (tδ n) 0 1 0 ω)) *
    wMassSup γ X (tδ n) (tF n) (L n) ω with hT
  have hTm : ∀ n, AEMeasurable (T n) P := by
    intro n
    refine (ENNReal.measurable_ofReal.comp ((measurable_cInc hX _ _ _ _).const_mul γ).exp
      ).aemeasurable.mul ?_
    refine (continuous_abs.measurable.comp_aemeasurable (hL n).aemeas).ennreal_ofReal.add ?_
    refine AEMeasurable.ennreal_tsum fun k => AEMeasurable.iSup fun m => AEMeasurable.iSup
      fun i => (continuous_abs.measurable.comp_aemeasurable
        ((measurable_wMass hX γ (tWinFun n) _ _).aemeasurable.sub (hL n).aemeas)).ennreal_ofReal
  set T' : ℕ → Ω → ℝ≥0∞ := fun n => (hTm n).mk with hT'
  have hT'm : ∀ n, Measurable (T' n) := fun n => (hTm n).measurable_mk
  have hTT' : ∀ n, T n =ᵐ[P] T' n := fun n => (hTm n).ae_eq_mk
  have hbd : ∀ n, 2 ≤ n → ∫⁻ ω, T' n ω ^ p ∂P ≤
      ENNReal.ofReal (tightC γ p) * ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * e)) := by
    intro n hn
    have hc : (fun ω => T n ω ^ p) =ᵐ[P] fun ω => T' n ω ^ p :=
      (hTT' n).mono fun ω h => by simp only at h ⊢; rw [h]
    rw [← lintegral_congr_ae hc]
    exact lintegral_tight_rpow_le hX hγ hγ2 hn (hL n) hp0 hp
  have hBC := AtomlessUncond.ae_tsum_ne_top_of_moments hT'm hp0 hp1 hneg ENNReal.ofReal_ne_top hbd
  filter_upwards [hBC, ae_all_iff.2 hTT', ae_goodCirc hX] with ω hω hTω hg
  intro ε hε
  obtain ⟨N, hN⟩ := hω
  set E1 := ENNReal.ofReal (Real.exp (γ * circleAvg (X ω) 1 0)) with hE1
  set a : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (2 ^ (lam * n)) *
    (ENNReal.ofReal (Real.exp (γ * circleAvg (X ω) (tδ n) 0)) *
      wMassSup γ X (tδ n) (tF n) (L n) ω) with ha
  have haT : ∀ n, a n ≤ E1 * (ENNReal.ofReal (radius (n + 1) ^ (-lam)) * T' n ω) := by
    intro n
    have hsplit : ENNReal.ofReal (Real.exp (γ * circleAvg (X ω) (tδ n) 0)) =
        E1 * ENNReal.ofReal (Real.exp (γ * cInc X (tδ n) 0 1 0 ω)) := by
      rw [hE1, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; simp only [cInc]; ring
    have haeq : a n = ENNReal.ofReal (2 ^ (lam * n)) * (E1 * T n ω) := by
      show ENNReal.ofReal (2 ^ (lam * n)) *
        (ENNReal.ofReal (Real.exp (γ * circleAvg (X ω) (tδ n) 0)) *
          wMassSup γ X (tδ n) (tF n) (L n) ω) = _
      rw [hsplit]
      simp only [hT]
      ring
    have h2 : ENNReal.ofReal (2 ^ (lam * n)) ≤ ENNReal.ofReal (radius (n + 1) ^ (-lam)) := by
      rw [radius_rpow_neg]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by push_cast; nlinarith))
    rw [haeq, ← hTω n]
    calc ENNReal.ofReal (2 ^ (lam * n)) * (E1 * T n ω)
        ≤ ENNReal.ofReal (radius (n + 1) ^ (-lam)) * (E1 * T n ω) := mul_le_mul' h2 le_rfl
      _ = E1 * (ENNReal.ofReal (radius (n + 1) ^ (-lam)) * T n ω) := by ring
  have hsumN : ∑' k, a (k + N) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (a := E1) ENNReal.ofReal_ne_top hN) ?_
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun k => (haT (k + N)).trans (le_of_eq ?_)
    congr 3
  have htail := ENNReal.tendsto_sum_nat_add (fun k => a (k + N)) hsumN
  have htail' : Tendsto (fun i => ENNReal.ofReal (2 ^ lam) * ∑' k, a (k + i + N)) atTop
      (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2 ^ lam)) htail
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 (htail'.eventually (gt_mem_nhds
    (ENNReal.ofReal_pos.2 hε)))
  set J := N + i₀ + 2 with hJ
  refine ⟨radius J, QuantumZipper.radius_pos J, fun s hs hsJ => ?_⟩
  refine (lintegral_weight_le hlam0 hs hsJ (areaS γ (X ω) s)).trans ?_
  have hterm : ∀ n, (if J ≤ n ∧ s ≤ 2 * radius n then ENNReal.ofReal (2 ^ (lam * n)) *
      areaS γ (X ω) s (closedBall (0 : ℂ) (radius n)) else 0) ≤ (if J ≤ n then a n else 0) := by
    intro n
    by_cases h : J ≤ n ∧ s ≤ 2 * radius n
    · rw [if_pos h, if_pos h.1]
      exact mul_le_mul' le_rfl (areaS_tS_le hg γ n (L n) hs h.2)
    · rw [if_neg h]; exact bot_le
  calc ENNReal.ofReal (2 ^ lam) * ∑' n, (if J ≤ n ∧ s ≤ 2 * radius n then
        ENNReal.ofReal (2 ^ (lam * n)) * areaS γ (X ω) s (closedBall (0 : ℂ) (radius n)) else 0)
      ≤ ENNReal.ofReal (2 ^ lam) * ∑' n, (if J ≤ n then a n else 0) :=
        mul_le_mul' le_rfl (ENNReal.tsum_le_tsum hterm)
    _ = ENNReal.ofReal (2 ^ lam) * ∑' k, a (k + (i₀ + 2) + N) := by
        rw [tsum_ite_le_eq]
        congr 2; funext k; congr 1; omega
    _ ≤ ENNReal.ofReal ε := (hi₀ (i₀ + 2) (by omega)).le

end MatedCRTHarmonic.LQGCoord
