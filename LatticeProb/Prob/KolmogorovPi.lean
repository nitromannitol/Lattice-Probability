/-
Quantitative probability bounds for continuous processes on finite-dimensional boxes.
-/
import LatticeProb.Prob.ChentsovPiProcess
import LatticeProb.Prob.ChentsovPiLimit

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

def LatticeProb.boxClamp {k : ℕ} (a b : Fin k → ℝ) (hab : a ≤ b)
    (x : Fin k → ℝ) : Fin k → ℝ := fun i => Set.projIcc (a i) (b i) (hab i) (x i)

theorem LatticeProb.boxClamp_mem {k : ℕ} (a b : Fin k → ℝ) (hab : a ≤ b)
    (x : Fin k → ℝ) : boxClamp a b hab x ∈ Set.Icc a b := by
  unfold boxClamp
  rw [Set.mem_Icc]
  constructor
  · simp only [Pi.le_def]
    intro i
    exact (Set.projIcc (a i) (b i) (hab i) (x i)).property.1
  · simp only [Pi.le_def]
    intro i
    exact (Set.projIcc (a i) (b i) (hab i) (x i)).property.2

theorem LatticeProb.boxClamp_eq {k : ℕ} {a b x : Fin k → ℝ} (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b) : boxClamp a b hab x = x := by
  funext i
  exact congrArg Subtype.val (Set.projIcc_of_mem (hab i) ⟨hx.1 i, hx.2 i⟩)

theorem LatticeProb.dist_boxClamp_le {k : ℕ} (a b : Fin k → ℝ) (hab : a ≤ b)
    (x y : Fin k → ℝ) : dist (boxClamp a b hab x) (boxClamp a b hab y) ≤ dist x y := by
  refine (dist_pi_le_iff dist_nonneg).mpr ?_
  intro i
  change |(Set.projIcc (a i) (b i) (hab i) (x i) : ℝ) - Set.projIcc (a i) (b i) (hab i) (y i)| ≤ dist x y
  exact (Set.abs_projIcc_sub_projIcc (hab i)).trans (dist_le_pi_dist x y i)

theorem LatticeProb.continuous_boxClamp {k : ℕ} (a b : Fin k → ℝ) (hab : a ≤ b) :
    Continuous (boxClamp a b hab) := by
  apply continuous_pi
  intro i
  change Continuous (fun x : Fin k → ℝ => max (a i) (min (b i) (x i)))
  fun_prop

theorem LatticeProb.exists_incr_exponent_pi (k : ℕ) {p q : ℝ} (hp : 0 < p) (hq : (k : ℝ) < q) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ (2 : ℝ) ^ ((k : ℝ) - q) / c ^ p < 1 := by
  set β : ℝ := (2 : ℝ) ^ (((k : ℝ) - q) / p) with hβdef
  have hβpos : 0 < β := Real.rpow_pos_of_pos (by norm_num) _
  have hβlt : β < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    exact div_neg_of_neg_of_pos (sub_neg.mpr hq) hp
  refine ⟨(β + 1) / 2, by positivity, by linarith, ?_⟩
  have hβb : β < (β + 1) / 2 := by linarith
  have hpow : β ^ p < ((β + 1) / 2) ^ p := Real.rpow_lt_rpow hβpos.le hβb hp
  have hβp : β ^ p = (2 : ℝ) ^ ((k : ℝ) - q) := by
    rw [hβdef, ← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hp.ne']
  rw [div_lt_one (by positivity), ← hβp]
  exact hpow

theorem LatticeProb.measure_abs_ge_le_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {f : Ω → ℝ} {p r C : ℝ}
    (hp : 0 < p) (hr : 0 < r) (hint : Integrable (fun ω => |f ω| ^ p) P)
    (hbound : ∫ ω, |f ω| ^ p ∂P ≤ C) :
    P {ω | r ≤ |f ω|} ≤ ENNReal.ofReal (C / r ^ p) := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (abs_nonneg (f ω)) p)) hint (r ^ p)
  have hsub : {ω | r ≤ |f ω|} ⊆ {ω | r ^ p ≤ |f ω| ^ p} :=
    fun ω hω => Real.rpow_le_rpow hr.le hω hp.le
  calc
    P {ω | r ≤ |f ω|} ≤ P {ω | r ^ p ≤ |f ω| ^ p} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | r ^ p ≤ |f ω| ^ p}) :=
      (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    _ ≤ ENNReal.ofReal (C / r ^ p) := by
      apply ENNReal.ofReal_le_ofReal
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hr p)).mpr
      simpa [mul_comm] using hmarkov.trans hbound
