/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L6FinalTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6FinalBox

/-!
# DDDF Lemma 6, Step 2: continuous version and Gaussian sup tail on a compact set

DDDF (Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `tightness.tex` l. 578–583): Kolmogorov's
criterion and Fernique's theorem give "uniform Gaussian tails" for `‖φ_L^{(δ)}‖_{L^∞(K)}`.

`exists_version_tail`: for a compact `K`, `r > 0` and `A, σ > 0` there are `C, c > 0` such that
every centered Gaussian field `G` with `E(G v − G u)² ≤ A|u − v|` and `Var G ≤ σ²` on the closed
`r`-thickening of `K` has a version `Y` on `K`, continuous on `K` for every `ω`, with
`P(sup_K |Y| ≥ u) ≤ C e^{−c u²}` for all `u ≥ 0`. `K` is covered by finitely many boxes inside
the thickening (compactness); on each box `exists_box_version` gives a continuous version; the
versions agree a.s. on the overlaps (they agree a.s. on a countable dense subset and are
continuous), and are glued; the tail is the union bound over the boxes. DDDF assume `K`
convex and do not detail the covering (own routine step, proposed DEVIATION D-DDDF-L6-1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real Metric Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- the box of side `b` centred at `x` -/
def cBox (b : ℝ) (x : ℂ) : Set ℂ := ferniqueBox (x - (((b / 2 : ℝ) : ℂ) + ((b / 2 : ℝ) : ℂ) * Complex.I)) b

lemma cBox_subset {b : ℝ} (x : ℂ) : cBox b x ⊆ closedBall x b := by
  intro y hy
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hy
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im] at h1 h2 h3 h4
  rw [mem_closedBall, dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]
  have e1 : |y.re - x.re| ≤ b / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have e2 : |y.im - x.im| ≤ b / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

lemma cBox_mem_nhds {b : ℝ} (hb : 0 < b) (x : ℂ) : cBox b x ∈ 𝓝 x := by
  refine mem_of_superset (ball_mem_nhds x (half_pos hb)) fun y hy => ?_
  rw [mem_ball, dist_eq_norm] at hy
  have e1 := (Complex.abs_re_le_norm (y - x)).trans_lt hy
  have e2 := (Complex.abs_im_le_norm (y - x)).trans_lt hy
  rw [Complex.sub_re, abs_lt] at e1
  rw [Complex.sub_im, abs_lt] at e2
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im] <;>
    linarith

/-- **Continuous version with Gaussian sup tail on a compact set** (DDDF Lemma 6, Step 2). -/
theorem exists_version_tail {K : Set ℂ} (hK : IsCompact K) {r : ℝ} (hr : 0 < r) {A σ : ℝ}
    (hA : 0 < A) (hσ : 0 < σ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ G : ℂ → Ω → ℝ, IsGaussianProcess G P →
      (∀ v, ∫ ω, G v ω ∂P = 0) →
      (∀ u ∈ cthickening r K, ∀ v ∈ cthickening r K,
        ∫ ω, (G v ω - G u ω) ^ 2 ∂P ≤ A * ‖u - v‖) →
      (∀ v ∈ cthickening r K, Var[G v; P] ≤ σ ^ 2) →
      ∃ Y : ℂ → Ω → ℝ, (∀ x ∈ K, Y x =ᵐ[P] G x) ∧ (∀ ω, ContinuousOn (fun x => Y x ω) K) ∧
        ∀ u : ℝ, 0 ≤ u → P {ω | ENNReal.ofReal u ≤ ⨆ x ∈ K, ENNReal.ofReal |Y x ω|} ≤
          ENNReal.ofReal (C * exp (-c * u ^ 2)) := by
  classical
  obtain ⟨t, htK0, htK⟩ := hK.elim_nhds_subcover (cBox r) (fun x _ => cBox_mem_nhds hr x)
  set a : ℝ := ferniqueCF * √(A * r)
  have ha : 0 < a := by
    have := ferniqueCF_pos
    have : 0 < √(A * r) := sqrt_pos.2 (by positivity)
    positivity
  set N : ℝ := (t.card : ℝ)
  refine ⟨(2 * N + 1) * exp (a ^ 2 / (2 * σ ^ 2)), 1 / (8 * σ ^ 2), by positivity, by positivity,
    fun G hG h0 hinc hvar => ?_⟩
  have hP := hG.isProbabilityMeasure
  set B : t → Set ℂ := fun i => cBox r i.1
  have hBS : ∀ i : t, B i ⊆ cthickening r K := fun i =>
    (cBox_subset i.1).trans (closedBall_subset_cthickening (htK0 _ i.2) r)
  have hKB : K ⊆ ⋃ i : t, B i := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (htK hx)
    exact mem_iUnion.2 ⟨⟨z, hz⟩, hxz⟩
  have hver := fun i : t => exists_box_version hG h0 hA hσ hinc hvar (x₀ := (i : ℂ) -
    (((r / 2 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I)) hr (hBS i)
  choose Ys hYc hYae hYt using hver
  set Gd : Set Ω := {ω | ∀ i j : t, ∀ x ∈ B i ∩ B j, Ys i x ω = Ys j x ω}
  have hGd : ∀ᵐ ω ∂P, ω ∈ Gd := by
    simp only [Gd, mem_ofPred_eq]
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    obtain ⟨D, hDc, hDs, hDd⟩ := TopologicalSpace.exists_countable_dense_subset (B i ∩ B j)
    have hD : ∀ᵐ ω ∂P, ∀ q ∈ D, Ys i q ω = Ys j q ω := by
      rw [ae_ball_iff hDc]
      intro q hq
      filter_upwards [hYae i q (hDs hq).1, hYae j q (hDs hq).2] with ω h1 h2
      rw [h1, h2]
    filter_upwards [hD] with ω hω
    exact Set.EqOn.of_subset_closure hω (hYc i ω).continuousOn (hYc j ω).continuousOn hDs hDd
  set Y : ℂ → Ω → ℝ := fun x ω =>
    if h : ω ∈ Gd ∧ ∃ i : t, x ∈ B i then Ys h.2.choose x ω else 0
  have hYeq : ∀ ω ∈ Gd, ∀ i : t, ∀ x ∈ B i, Y x ω = Ys i x ω := by
    intro ω hω i x hx
    have h : ω ∈ Gd ∧ ∃ i : t, x ∈ B i := ⟨hω, i, hx⟩
    simp only [Y, dif_pos h]
    exact hω _ _ x ⟨h.2.choose_spec, hx⟩
  refine ⟨Y, fun x hx => ?_, fun ω => ?_, fun u hu => ?_⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (hKB hx)
    filter_upwards [hGd, hYae i x hi] with ω h1 h2
    rw [hYeq ω h1 i x hi, h2]
  · by_cases hω : ω ∈ Gd
    · refine (LocallyFinite.continuousOn_iUnion (locallyFinite_of_finite B)
        (fun i => (isCompact_ferniqueBox _ _).isClosed) fun i => ?_).mono hKB
      exact (hYc i ω).continuousOn.congr fun x hx => hYeq ω hω i x hx
    · have e : (fun x => Y x ω) = fun _ => 0 := by
        funext x; simp only [Y]; exact dif_neg (fun h => hω h.1)
      rw [e]; exact continuousOn_const
  · rcases lt_or_ge u (2 * a) with hua | hua
    · refine (prob_le_one).trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : 1 ≤ 2 * N + 1 := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
      have h2 : 0 ≤ a ^ 2 / (2 * σ ^ 2) + -(1 / (8 * σ ^ 2)) * u ^ 2 := by
        have : u ^ 2 ≤ 4 * a ^ 2 := by nlinarith
        have e : a ^ 2 / (2 * σ ^ 2) + -(1 / (8 * σ ^ 2)) * u ^ 2 =
            (4 * a ^ 2 - u ^ 2) / (8 * σ ^ 2) := by field_simp; ring
        rw [e]; exact div_nonneg (by linarith) (by positivity)
      calc (1 : ℝ) ≤ (2 * N + 1) * exp (a ^ 2 / (2 * σ ^ 2) + -(1 / (8 * σ ^ 2)) * u ^ 2) :=
            one_le_mul_of_one_le_of_one_le h1 (one_le_exp h2)
        _ = _ := by rw [exp_add]; ring
    · have hu0 : 0 < u := by linarith
      set s := u - a
      have hs : 0 ≤ s := by simp only [s]; linarith
      set E : t → Set Ω := fun i => {ω | ENNReal.ofReal (a + s) ≤
        ⨆ v ∈ B i, ENNReal.ofReal |Ys i v ω|}
      have hsub : {ω | ENNReal.ofReal u ≤ ⨆ x ∈ K, ENNReal.ofReal |Y x ω|} ⊆
          Gdᶜ ∪ ⋃ i, E i := by
        intro ω hω
        by_cases hg : ω ∈ Gd
        · right
          simp only [mem_ofPred_eq] at hω
          have hle : ⨆ x ∈ K, ENNReal.ofReal |Y x ω| ≤
              ⨆ i : t, ⨆ v ∈ B i, ENNReal.ofReal |Ys i v ω| := by
            refine iSup₂_le fun x hx => ?_
            obtain ⟨i, hi⟩ := mem_iUnion.1 (hKB hx)
            rw [hYeq ω hg i x hi]
            exact le_iSup_of_le i (le_iSup₂_of_le x hi le_rfl)
          have hus : a + s = u := by simp only [s]; ring
          rcases isEmpty_or_nonempty t with he | hne
          · rw [iSup_of_empty (ι := t)] at hle
            have := (hω.trans hle)
            rw [le_bot_iff, ENNReal.bot_eq_zero, ENNReal.ofReal_eq_zero] at this
            linarith
          · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite
              (f := fun i : t => ⨆ v ∈ B i, ENNReal.ofReal |Ys i v ω|)
            refine mem_iUnion.2 ⟨i, ?_⟩
            simp only [E, mem_ofPred_eq, hus]
            rw [hi]; exact hω.trans hle
        · left; exact hg
      have hGd0 : P Gdᶜ = 0 := ae_iff.1 hGd
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
      rw [hGd0, zero_add]
      refine (measure_iUnion_fintype_le P E).trans ?_
      have hEi : ∀ i, P (E i) ≤ ENNReal.ofReal (2 * exp (-s ^ 2 / (2 * σ ^ 2))) :=
        fun i => hYt i s hs
      refine (Finset.sum_le_sum fun i _ => hEi i).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      have hsq : u ^ 2 / 4 ≤ s ^ 2 := by simp only [s]; nlinarith
      have hx1 : exp (-s ^ 2 / (2 * σ ^ 2)) ≤ exp (-(1 / (8 * σ ^ 2)) * u ^ 2) := by
        refine exp_le_exp.2 ?_
        have e : -(1 / (8 * σ ^ 2)) * u ^ 2 = -(u ^ 2 / 4) / (2 * σ ^ 2) := by
          field_simp; ring
        rw [e]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      have hx2 : 1 ≤ exp (a ^ 2 / (2 * σ ^ 2)) := one_le_exp (by positivity)
      calc (t.card : ℝ) * (2 * exp (-s ^ 2 / (2 * σ ^ 2)))
          ≤ (2 * N + 1) * exp (-(1 / (8 * σ ^ 2)) * u ^ 2) := by
            rw [← mul_assoc, mul_comm (t.card : ℝ) 2]
            exact mul_le_mul (by linarith) hx1 (exp_pos _).le (by positivity)
        _ ≤ (2 * N + 1) * exp (a ^ 2 / (2 * σ ^ 2)) * exp (-(1 / (8 * σ ^ 2)) * u ^ 2) := by
            rw [mul_assoc (2 * N + 1)]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact le_mul_of_one_le_left (exp_pos _).le hx2

end DDDF
end LQGMetric
