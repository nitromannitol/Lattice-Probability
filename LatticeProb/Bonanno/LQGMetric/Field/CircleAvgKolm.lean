/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgKolm at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGP
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.KolmN
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity

/-!
# A jointly continuous version of the circle-average process

`exists_continuous_version_circleAvg`: for a whole-plane GFF `h` there is `H : ℝ → ℂ → Ω → ℝ`,
continuous in `(r, z) ∈ (0,∞) × ℂ` for every `ω`, with `H r z = h_r(z) − h_1(0)` a.s. for each
`r > 0`, `z` (DS arXiv:0808.1560 §3.1 / Hu–Miller–Peres, *Thick points of the Gaussian free
field*, Prop. 2.1: the circle average process has a continuous modification).
Proof: Kolmogorov–Čentsov in the parameters `q = (log r, Re z, Im z) ∈ ℝ³`
(QuantumZipper `KolmN.exists_continuous_modification_N`, Revuz–Yor Ch. I Thm 2.1) with the
8th moment of the Gaussian increment (`CircleCont.lintegral_pow8_of_map_eq`) and the variance
bound `Var(h_r(z) − h_s(w)) ≤ 2(|r − s| + |z − w|)/min(r, s)` (`incCov_self_le`, own
elementary estimate: `log max(r, |z − ·|)` is Lipschitz in `(r, z)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace LQGMetric
namespace CircleAvg

lemma circLog_eq_log_max {r : ℝ} (hr : 0 < r) (z x : ℂ) :
    circLog z r x = Real.log (max r ‖z - x‖) := by
  rw [circLog_eq hr.ne', Real.posLog_eq_log_max_one (by positivity),
    ← Real.log_mul hr.ne' (by positivity), mul_max_of_nonneg _ _ hr.le, mul_one,
    ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

lemma abs_log_sub_log_le {A B m : ℝ} (hm : 0 < m) (hA : m ≤ A) (hB : m ≤ B) :
    |Real.log A - Real.log B| ≤ |A - B| / m := by
  have hA0 : 0 < A := hm.trans_le hA
  have hB0 : 0 < B := hm.trans_le hB
  have key : ∀ {A B : ℝ}, 0 < A → m ≤ B → Real.log A - Real.log B ≤ |A - B| / m := by
    intro A B hA0 hB
    have hB0 : 0 < B := hm.trans_le hB
    rw [← Real.log_div hA0.ne' hB0.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hA0 hB0)).trans ?_
    rw [div_sub_one hB0.ne']
    calc (A - B) / B ≤ |A - B| / B := by gcongr; exact le_abs_self _
      _ ≤ |A - B| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hB
  rw [abs_le]
  constructor
  · have := key hB0 hA
    rw [abs_sub_comm] at this
    linarith
  · exact key hA0 hB

lemma abs_circLog_sub_circLog_le {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w x : ℂ) :
    |circLog w s x - circLog z r x| ≤ (|r - s| + ‖z - w‖) / min r s := by
  rw [circLog_eq_log_max hr, circLog_eq_log_max hs]
  refine (abs_log_sub_log_le (lt_min hr hs) ((min_le_right r s).trans (le_max_left _ _))
    ((min_le_left r s).trans (le_max_left _ _))).trans ?_
  gcongr
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [abs_sub_comm]; linarith [norm_nonneg (z - w)]
  · refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [sub_sub_sub_cancel_right, norm_sub_rev]
    linarith [abs_nonneg (r - s)]

lemma circCov_sub_le {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (c : ℂ) (ρ : ℝ) (z w : ℂ) :
    Real.circleAverage (circLog w s) c ρ - Real.circleAverage (circLog z r) c ρ ≤
      (|r - s| + ‖z - w‖) / min r s := by
  have hci : ∀ (a : ℂ) (t : ℝ), 0 < t → CircleIntegrable (circLog a t) c ρ := fun a t ht =>
    ((continuous_circLog ht.ne' a).continuousOn).circleIntegrable'
  rw [← Real.circleAverage_fun_sub (hci w s hs) (hci z r hr)]
  refine Real.circleAverage_mono_on_of_le_circle ((hci w s hs).sub (hci z r hr)) fun x _ => ?_
  exact (le_abs_self _).trans (abs_circLog_sub_circLog_le hr hs z w x)

/-- `Var(h_r(z) − h_s(w)) ≤ 2(|r − s| + |z − w|)/min(r, s)` -/
lemma incCov_self_le {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    incCov z r w s z r w s ≤ 2 * ((|r - s| + ‖z - w‖) / min r s) := by
  have h1 := circCov_sub_le hr hs z r z w
  have h2 := circCov_sub_le hs hr w s w z
  rw [abs_sub_comm, norm_sub_rev, min_comm] at h2
  simp only [incCov, circCov]
  linarith

lemma exp_sub_exp_le {a b R : ℝ} (hab : a ≤ b) (hb : b ≤ R) :
    Real.exp b - Real.exp a ≤ Real.exp R * (b - a) := by
  have h1 : 1 - Real.exp (a - b) ≤ b - a := by
    have := Real.add_one_le_exp (a - b); linarith
  have h2 : Real.exp b - Real.exp a = Real.exp b * (1 - Real.exp (a - b)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
  rw [h2]
  calc Real.exp b * (1 - Real.exp (a - b)) ≤ Real.exp b * (b - a) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos b).le
    _ ≤ Real.exp R * (b - a) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hb) (by linarith)

lemma abs_exp_sub_exp_le {a b R : ℝ} (ha : a ≤ R) (hb : b ≤ R) :
    |Real.exp a - Real.exp b| ≤ Real.exp R * |a - b| := by
  rcases le_total a b with h | h
  · rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.exp_le_exp.mpr h]),
      abs_sub_comm, abs_of_nonneg (by linarith)]
    exact exp_sub_exp_le h hb
  · rw [abs_of_nonneg (by linarith [Real.exp_le_exp.mpr h]), abs_of_nonneg (by linarith)]
    exact exp_sub_exp_le h ha

/-- the parametrization `q ↦ (e^{q₀}, q₁ + i q₂)` -/
def parR (q : Fin 3 → ℝ) : ℝ := Real.exp (q 0)
def parZ (q : Fin 3 → ℝ) : ℂ := ⟨q 1, q 2⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- the process `q ↦ h_{e^{q₀}}(q₁ + i q₂) − h_1(0)` -/
def kolmProc (h : Ω → DistC) (q : Fin 3 → ℝ) (ω : Ω) : ℝ :=
  cInc h (parR q) (parZ q) 1 0 ω

lemma norm_parZ_sub_le (q q' : Fin 3 → ℝ) : ‖parZ q - parZ q'‖ ≤ 2 * ‖q - q'‖ := by
  have h1 : |q 1 - q' 1| ≤ ‖q - q'‖ := by
    have := norm_le_pi_norm (q - q') 1; simpa [Real.norm_eq_abs] using this
  have h2 : |q 2 - q' 2| ≤ ‖q - q'‖ := by
    have := norm_le_pi_norm (q - q') 2; simpa [Real.norm_eq_abs] using this
  have : ‖parZ q - parZ q'‖ ≤ |q 1 - q' 1| + |q 2 - q' 2| := by
    have := Complex.norm_le_abs_re_add_abs_im (parZ q - parZ q')
    simpa [parZ] using this
  linarith

theorem momentBound_kolmProc (hh : IsWholePlaneGFF h P) (R : ℕ) :
    ∃ K, 0 ≤ K ∧ QuantumZipper.KolmG.MomentBoundG (kolmProc h) P 8 4 K R := by
  set C : ℝ := 2 * (Real.exp R * (Real.exp R + 2))
  refine ⟨C ^ 4 * QuantumZipper.gaussianAbsMoment 8,
    mul_nonneg (pow_nonneg (by positivity) _) (QuantumZipper.gaussianAbsMoment_nonneg 8),
    fun q hq q' hq' => ?_⟩
  have hq0 : |q 0| ≤ R := hq 0
  have hq0' : |q' 0| ≤ R := hq' 0
  have hr : 0 < parR q := Real.exp_pos _
  have hr' : 0 < parR q' := Real.exp_pos _
  have e : ∀ ω, kolmProc h q ω - kolmProc h q' ω = cInc h (parR q) (parZ q) (parR q') (parZ q') ω :=
    fun ω => by simp only [kolmProc, cInc]; ring
  simp only [e]
  rw [QuantumZipper.CircleCont.lintegral_pow8_of_map_eq (measurable_cInc hh _ _ _ _)
    (map_cInc hh hr hr' _ _).1]
  apply ENNReal.ofReal_le_ofReal
  have hnn : 0 ≤ incCov (parZ q) (parR q) (parZ q') (parR q') (parZ q) (parR q) (parZ q')
      (parR q') := by
    rw [← (map_cInc hh hr hr' _ _).2]; exact variance_nonneg _ _
  have hΔ0 : |q 0 - q' 0| ≤ ‖q - q'‖ := by
    have := norm_le_pi_norm (q - q') 0; simpa [Real.norm_eq_abs] using this
  have hmin : Real.exp (-(R : ℝ)) ≤ min (parR q) (parR q') :=
    le_min (Real.exp_le_exp.mpr (by linarith [neg_abs_le (q 0)]))
      (Real.exp_le_exp.mpr (by linarith [neg_abs_le (q' 0)]))
  have hexp : |parR q - parR q'| ≤ Real.exp R * ‖q - q'‖ :=
    (abs_exp_sub_exp_le (le_of_abs_le hq0) (le_of_abs_le hq0')).trans
      (mul_le_mul_of_nonneg_left hΔ0 (Real.exp_pos _).le)
  have hv : incCov (parZ q) (parR q) (parZ q') (parR q') (parZ q) (parR q) (parZ q') (parR q')
      ≤ C * ‖q - q'‖ := by
    refine (incCov_self_le hr hr' _ _).trans ?_
    have hnum : |parR q - parR q'| + ‖parZ q - parZ q'‖ ≤ (Real.exp R + 2) * ‖q - q'‖ := by
      linarith [norm_parZ_sub_le q q']
    have h3 : (|parR q - parR q'| + ‖parZ q - parZ q'‖) / min (parR q) (parR q') ≤
        (Real.exp R + 2) * ‖q - q'‖ / Real.exp (-(R : ℝ)) :=
      div_le_div₀ (by positivity) hnum (Real.exp_pos _) hmin
    rw [Real.exp_neg, div_inv_eq_mul] at h3
    have : C * ‖q - q'‖ = 2 * ((Real.exp R + 2) * ‖q - q'‖ * Real.exp R) := by
      simp only [C]; ring
    rw [this]
    linarith
  rw [Real.coe_toNNReal _ hnn]
  calc _ ≤ (C * ‖q - q'‖) ^ 4 * QuantumZipper.gaussianAbsMoment 8 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn hv 4)
          (QuantumZipper.gaussianAbsMoment_nonneg 8)
    _ = C ^ 4 * QuantumZipper.gaussianAbsMoment 8 * ‖q - q'‖ ^ (4 : ℝ) := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring

/-- **Jointly continuous version of the circle-average process.** -/
theorem exists_continuous_version_circleAvg (hh : IsWholePlaneGFF h P) :
    ∃ H : ℝ → ℂ → Ω → ℝ, (∀ ω, ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω) (Ioi 0 ×ˢ univ)) ∧
      ∀ r, 0 < r → ∀ z, (fun ω => H r z ω) =ᵐ[P]
        fun ω => circleAvg (h ω) r z - circleAvg (h ω) 1 0 := by
  obtain ⟨Y, hYc, hYZ, -⟩ := QuantumZipper.KolmN.exists_continuous_modification_N
    (Z := kolmProc h) (fun q => (measurable_cInc hh _ _ _ _).aemeasurable) (p := 8)
    (by norm_num) (a := 4) (by norm_num) (momentBound_kolmProc hh)
  set qOf : ℝ × ℂ → (Fin 3 → ℝ) := fun p => ![Real.log p.1, p.2.re, p.2.im]
  refine ⟨fun r z ω => Y (qOf (r, z)) ω, fun ω => ?_, fun r hr z => ?_⟩
  · have hq : ContinuousOn qOf (Ioi 0 ×ˢ univ) := by
      refine continuousOn_pi.mpr fun i => ?_
      fin_cases i
      · exact (Real.continuousOn_log.comp continuous_fst.continuousOn fun p hp =>
          (ne_of_gt (show (0 : ℝ) < p.1 from hp.1))).congr fun p _ => rfl
      · exact (Complex.continuous_re.comp continuous_snd).continuousOn
      · exact (Complex.continuous_im.comp continuous_snd).continuousOn
    exact (hYc ω).comp_continuousOn hq
  · refine (hYZ (qOf (r, z))).trans (Eventually.of_forall fun ω => ?_)
    simp only [kolmProc, cInc, parR, parZ, qOf]
    simp [Real.exp_log hr]
