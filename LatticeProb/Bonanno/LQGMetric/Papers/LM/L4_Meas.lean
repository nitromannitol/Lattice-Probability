/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L4_Meas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L4_Trans
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1N2
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_6Main
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_2Meas

/-!
# LM Lemma 4.1: the event `E_r(z)` is determined by the rescaled internal metrics (task P2-LM42)

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Lemma 4.1, l. 812–813: "Since scaling each of `D` and `D̃` by
the same constant factor does not affect the occurrence of `E_r(z)`, it follows that `E_r(z)` is
a.s. determined by `e^{−ξh_r(z)} D(·,·;𝔸_{r/2,2r}(z))` and `e^{−ξh_r(z)} D̃(·,·;𝔸_{r/2,2r}(z))`."

`lmGoodE_aeEventIn`: after translating by `w` (`L4_Trans`), `E_ρ(w)` is a.s. equal to an event of
the σ-algebra of LM Lemma 3.1 with `N = 2` at the radius `R = 4ρ`, `s₁ = 1/8`, `s₂ = 1/2`
(annulus `𝔸_{ρ/2, 2ρ}(0)`), for the normalization `e^{−ξ h̃_{4ρ}(0)}` of Lemma 3.1 (LM's text uses
`e^{−ξh_r(z)}`; any common constant works).

Details (own routine arguments):
* the internal diameter is a supremum over a dense sequence (`DFGPS.L32M.internalDiam_eq_iSup`);
* the inner circle `∂B_{ρ/2}(w)` lies on the boundary of the open annulus `𝔸_{ρ/2,2ρ}(w)`, so
  `D(∂B_{ρ/2}(w), ∂B_ρ(w))` is written as the increasing limit of `D(∂B_{ρ_n}(w), ∂B_ρ(w))`,
  `ρ_n ↓ ρ/2` (`setDist_sphere_eq_iSup`: any path crosses the intermediate circles, and `D` is
  uniformly continuous on compacts), each of which is an infimum of internal distances in the
  annulus over dense sequences (`DFGPS.L32M.setDist_eq_iInf_dense`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint GM.Bilip MetricGeometry

/-- a path from `∂B_{ρ₁}(w)` to `∂B_{ρ₂}(w)` crosses `∂B_{ρ'}(w)` -/
lemma setDist_sphere_le_of_cross (D : ContMetric) (hD : D.IsLength) {w : ℂ} {ρ₁ ρ' ρ₂ : ℝ}
    (h1 : ρ₁ ≤ ρ') (h2 : ρ' ≤ ρ₂) :
    setDist D (sphere w ρ') (sphere w ρ₂) ≤ setDist D (sphere w ρ₁) (sphere w ρ₂) := by
  rw [GM.setDist_eq_iInf D (sphere w ρ₁)]
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨P, a, b, hab, hPc, hPa, hPb, hlen⟩ :=
    isLengthSpace_iff_curves.1 hD (D.pt x) (D.pt y) ε (by exact_mod_cast hε)
  set f : ℝ → ℝ := fun t => ‖D.unpt (P t) - w‖ with hf
  have hfc : ContinuousOn f (Icc a b) :=
    (continuous_norm.comp (D.continuous_unpt.sub continuous_const)).comp_continuousOn hPc
  have hfa : f a = ρ₁ := by simp only [hf, hPa]; exact mem_sphere_iff_norm.1 hx
  have hfb : f b = ρ₂ := by simp only [hf, hPb]; exact mem_sphere_iff_norm.1 hy
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hfc
    (show ρ' ∈ Icc (f a) (f b) from ⟨by rw [hfa]; exact h1, by rw [hfb]; exact h2⟩)
  have hp : D.unpt (P t) ∈ sphere w ρ' := mem_sphere_iff_norm.2 hft
  have hy' : D.unpt (P b) ∈ sphere w ρ₂ := by rw [hPb]; exact hy
  calc setDist D (sphere w ρ') (sphere w ρ₂)
        ≤ ENNReal.ofReal (D.1 (D.unpt (P t), D.unpt (P b))) := by
          rw [GM.setDist_eq_iInf]; exact iInf₂_le_of_le _ hp (iInf₂_le _ hy')
    _ = edist (P t) (P b) := (ContMetric.edist_pt D _ _).symm
    _ ≤ curveLength P t b := edist_le_curveLength P ht.2
    _ ≤ curveLength P a b := eVariationOn.mono _ (Icc_subset_Icc ht.1 le_rfl)
    _ ≤ edist (D.pt x) (D.pt y) + ENNReal.ofReal ε := hlen
    _ = ENNReal.ofReal (D.1 (x, y)) + ε := by
        rw [ContMetric.edist_pt, ENNReal.ofReal_coe_nnreal]

/-- the radii `ρ_n = ρ₁ + (ρ₂ − ρ₁)/(n + 2) ↓ ρ₁` -/
def radSeq (ρ₁ ρ₂ : ℝ) (n : ℕ) : ℝ := ρ₁ + (ρ₂ - ρ₁) / (n + 2)

lemma radSeq_mem {ρ₁ ρ₂ : ℝ} (h12 : ρ₁ < ρ₂) (n : ℕ) :
    ρ₁ < radSeq ρ₁ ρ₂ n ∧ radSeq ρ₁ ρ₂ n < ρ₂ := by
  have h : 0 < ρ₂ - ρ₁ := by linarith
  have hn : (1 : ℝ) < n + 2 := by have := n.cast_nonneg (α := ℝ); linarith
  refine ⟨by unfold radSeq; have : 0 < (ρ₂ - ρ₁) / (n + 2) := by positivity
             linarith, ?_⟩
  unfold radSeq
  have : (ρ₂ - ρ₁) / (n + 2) < ρ₂ - ρ₁ := div_lt_self h hn
  linarith

/-- **`D(∂B_{ρ₁}(w), ∂B_{ρ₂}(w)) = sup_n D(∂B_{ρ_n}(w), ∂B_{ρ₂}(w))`** for length metrics -/
theorem setDist_sphere_eq_iSup (D : ContMetric) (hD : D.IsLength) {w : ℂ} {ρ₁ ρ₂ : ℝ}
    (h0 : 0 < ρ₁) (h12 : ρ₁ < ρ₂) :
    setDist D (sphere w ρ₁) (sphere w ρ₂) =
      ⨆ n : ℕ, setDist D (sphere w (radSeq ρ₁ ρ₂ n)) (sphere w ρ₂) := by
  refine le_antisymm ?_ (iSup_le fun n => setDist_sphere_le_of_cross D hD
    (radSeq_mem h12 n).1.le (radSeq_mem h12 n).2.le)
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  -- uniform continuity of `D` on `B̄_{ρ₂}(w)`
  have hK := (isCompact_closedBall w ρ₂).prod (isCompact_closedBall w ρ₂)
  obtain ⟨δ, hδ, hUC⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous D.1.continuous.continuousOn) η (by exact_mod_cast hη)
  obtain ⟨n, hn⟩ := exists_nat_gt ((ρ₂ - ρ₁) / δ)
  have hgap : radSeq ρ₁ ρ₂ n - ρ₁ < δ := by
    unfold radSeq
    rw [add_sub_cancel_left, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hn
    nlinarith
  obtain ⟨hn1, hn2⟩ := radSeq_mem h12 n
  set ρn := radSeq ρ₁ ρ₂ n with hρn
  have hρn0 : 0 < ρn := h0.trans hn1
  refine (le_trans ?_ (add_le_add (le_iSup (fun n : ℕ =>
    setDist D (sphere w (radSeq ρ₁ ρ₂ n)) (sphere w ρ₂)) n) le_rfl))
  rw [GM.setDist_eq_iInf D (sphere w ρn)]
  simp_rw [ENNReal.iInf_add]
  refine le_iInf₂ fun p hp => le_iInf₂ fun y hy => ?_
  have hpn : ‖p - w‖ = ρn := mem_sphere_iff_norm.1 hp
  set x' : ℂ := w + ((ρ₁ / ρn : ℝ) : ℂ) * (p - w) with hx'
  have hx'w : ‖x' - w‖ = ρ₁ := by
    rw [hx', add_sub_cancel_left, norm_mul, Complex.norm_real, hpn, Real.norm_of_nonneg
      (by positivity)]
    field_simp
  have hpx : ‖p - x'‖ = ρn - ρ₁ := by
    have : p - x' = ((1 - ρ₁ / ρn : ℝ) : ℂ) * (p - w) := by
      rw [hx']; push_cast; ring
    rw [this, norm_mul, Complex.norm_real, hpn, Real.norm_of_nonneg]
    · field_simp
    · rw [sub_nonneg, div_le_one hρn0]; exact hn1.le
  have hx'K : x' ∈ closedBall w ρ₂ := by
    rw [mem_closedBall, dist_eq_norm, hx'w]; exact h12.le
  have hpK : p ∈ closedBall w ρ₂ := by
    rw [mem_closedBall, dist_eq_norm, hpn]; exact hn2.le
  have hsmall : D.1 (x', p) < η := by
    have := hUC (x', p) ⟨hx'K, hpK⟩ (p, p) ⟨hpK, hpK⟩ (by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_comm, dist_eq_norm, hpx]
      exact hgap)
    rw [D.2.self_eq_zero p, Real.dist_eq, sub_zero, abs_of_nonneg (ContMetric.nonneg D _ _)] at this
    exact this
  calc setDist D (sphere w ρ₁) (sphere w ρ₂) ≤ ENNReal.ofReal (D.1 (x', y)) := by
        rw [GM.setDist_eq_iInf]
        exact iInf₂_le_of_le x' (mem_sphere_iff_norm.2 hx'w) (iInf₂_le y hy)
    _ ≤ ENNReal.ofReal (D.1 (p, y) + D.1 (x', p)) :=
        ENNReal.ofReal_le_ofReal (by linarith [D.2.triangle x' p y])
    _ ≤ ENNReal.ofReal (D.1 (p, y)) + η := by
        rw [ENNReal.ofReal_add (ContMetric.nonneg D _ _) (ContMetric.nonneg D _ _)]
        refine add_le_add le_rfl ?_
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal hsmall.le

/-! ### The event `E_ρ(w)` in terms of the rescaled internal metrics -/

/-- the countable form of `E_ρ`: `sup_{i,j} J₂(a_i, a_j) ≤ C sup_n inf_{i,j} J₁(b_{n,i}, a_j)` -/
def goodI (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (C : ℝ) (J : (ℂ → ℂ → ℝ≥0∞) × (ℂ → ℂ → ℝ≥0∞)) : Prop :=
  ⨆ p : ℕ × ℕ, J.2 (a p.1) (a p.2) ≤
    ENNReal.ofReal C * ⨆ n : ℕ, ⨅ p : ℕ × ℕ, J.1 (b n p.1) (a p.2)

lemma measurableSet_goodI (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (C : ℝ) :
    MeasurableSet {J | goodI a b C J} := by
  have hc : ∀ x y : ℂ, Measurable fun F : ℂ → ℂ → ℝ≥0∞ => F x y := fun x y =>
    (measurable_pi_apply y).comp (measurable_pi_apply x)
  exact measurableSet_le (Measurable.iSup fun p => (hc _ _).comp measurable_snd)
    ((Measurable.iSup fun n => Measurable.iInf fun p => (hc _ _).comp measurable_fst).const_mul _)

lemma preimage_annulus (w : ℂ) (ρ : ℝ) :
    (fun x => x - w) ⁻¹' (annulus 0 (1 / 8 * (4 * ρ)) (1 / 2 * (4 * ρ)) : Set ℂ) =
      annulus w (ρ / 2) (2 * ρ) := by
  ext x
  show (1 / 8 * (4 * ρ) < ‖x - w - 0‖ ∧ ‖x - w - 0‖ < 1 / 2 * (4 * ρ)) ↔
    (ρ / 2 < ‖x - w‖ ∧ ‖x - w‖ < 2 * ρ)
  rw [sub_zero]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **LM l. 812–815**: `E_ρ(w)` is a.s. an event of
`σ(e^{−ξh̃_{4ρ}(0)} D̃(·,·;𝔸_{ρ/2,2ρ}(0)), e^{−ξh̃_{4ρ}(0)} D̃'(·,·;𝔸_{ρ/2,2ρ}(0)))` for the
translated field `h̃ = h(· + w) − h_1(w)` and metrics `D̃ = e^{−ξh_1(w)} D(· + w, · + w)`. -/
theorem lmGoodE_aeEventIn {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℝ}
    {h : Ω → DistC} {D D' : Ω → ContMetric} (hxi : IsXiAdditive2 ξ P h D D') (C : ℝ) (w : ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ F : Set Ω, MeasurableSet[
        famSigma (normIntFam ξ (transField h w) (transMetric ξ h w D) (4 * ρ))
          (annulus 0 (1 / 8 * (4 * ρ)) (1 / 2 * (4 * ρ))) ⊔
        famSigma (normIntFam ξ (transField h w) (transMetric ξ h w D') (4 * ρ))
          (annulus 0 (1 / 8 * (4 * ρ)) (1 / 2 * (4 * ρ)))] F ∧
      F =ᵐ[P] {ω | lmGoodE (D ω) (D' ω) C w ρ} := by
  set A : Set ℂ := (annulus 0 (1 / 8 * (4 * ρ)) (1 / 2 * (4 * ρ)) : Set ℂ) with hA
  have hAw := preimage_annulus w ρ
  have hSA : sphere w ρ ⊆ (annulus w (ρ / 2) (2 * ρ) : Set ℂ) := fun x hx => by
    have := mem_sphere_iff_norm.1 hx
    show ρ / 2 < ‖x - w‖ ∧ ‖x - w‖ < 2 * ρ
    constructor <;> linarith
  obtain ⟨a', ha'S, ha'd⟩ := DFGPS.L32M.exists_denseSeq (S := sphere w ρ)
    (NormedSpace.sphere_nonempty.2 hρ.le)
  have hrs := fun n => radSeq_mem (half_lt_self hρ) n
  choose b' hb'S hb'd using fun n => DFGPS.L32M.exists_denseSeq
    (S := sphere w (radSeq (ρ / 2) ρ n))
    (NormedSpace.sphere_nonempty.2 ((half_pos hρ).trans (hrs n).1).le)
  set a : ℕ → ℂ := fun i => a' i - w with ha
  set b : ℕ → ℕ → ℂ := fun n i => b' n i - w with hb
  set I₁ := normIntFam ξ (transField h w) (transMetric ξ h w D) (4 * ρ) with hI₁
  set I₂ := normIntFam ξ (transField h w) (transMetric ξ h w D') (4 * ρ) with hI₂
  refine ⟨(fun ω => (I₁ ω A, I₂ ω A)) ⁻¹' {J | goodI a b C J}, ?_, ?_⟩
  · exact (Measurable.prodMk (Measurable.mono (comap_measurable _) le_sup_left le_rfl)
      (Measurable.mono (comap_measurable _) le_sup_right le_rfl)) (measurableSet_goodI a b C)
  filter_upwards [hxi.1.2.2.1] with ω ⟨hl, hl'⟩
  set κ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-ξ * circleAvg (transField h w ω) (4 * ρ) 0)) *
    ENNReal.ofReal (Real.exp (-ξ * circleAvg (h ω) 1 w)) with hκ
  have hκ0 : κ ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hκt : κ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hI : ∀ Dj : Ω → ContMetric, ∀ x y : ℂ,
      normIntFam ξ (transField h w) (transMetric ξ h w Dj) (4 * ρ) ω A (x - w) (y - w) =
        κ * (Dj ω).internal (annulus w (ρ / 2) (2 * ρ)) x y := by
    intro Dj x y
    simp only [normIntFam]
    rw [internal_transMetric, hA, hAw, sub_add_cancel, sub_add_cancel, hκ]
    ring
  have e1 : ⨆ p : ℕ × ℕ, I₂ ω A (a p.1) (a p.2) =
      κ * internalDiam (D' ω) (sphere w ρ) (annulus w (ρ / 2) (2 * ρ)) := by
    simp only [ha, hI₂, hI]
    rw [DFGPS.L32M.internalDiam_eq_iSup (D' ω) hl' (annulus w _ _).isOpen hSA ha'S ha'd,
      ENNReal.mul_iSup]
  have e2 : ⨆ n : ℕ, ⨅ p : ℕ × ℕ, I₁ ω A (b n p.1) (a p.2) =
      κ * setDist (D ω) (sphere w (ρ / 2)) (sphere w ρ) := by
    simp only [ha, hb, hI₁, hI]
    rw [setDist_sphere_eq_iSup (D ω) hl (half_pos hρ) (half_lt_self hρ), ENNReal.mul_iSup]
    refine iSup_congr fun n => ?_
    have hsub : ∀ x : ℂ, radSeq (ρ / 2) ρ n ≤ ‖x - w‖ → ‖x - w‖ ≤ ρ →
        x ∈ (annulus w (ρ / 2) (2 * ρ) : Set ℂ) := fun x h1 h2 => by
      show ρ / 2 < ‖x - w‖ ∧ ‖x - w‖ < 2 * ρ
      exact ⟨(hrs n).1.trans_le h1, by linarith⟩
    rw [DFGPS.L32M.setDist_eq_iInf_dense (D ω) hl (annulus w _ _).isOpen (hrs n).2 hsub
      (hb'S n) ha'S (hb'd n) ha'd, ENNReal.mul_iInf_of_ne hκ0 hκt]
  show goodI a b C (I₁ ω A, I₂ ω A) = lmGoodE (D ω) (D' ω) C w ρ
  apply propext
  simp only [goodI, lmGoodE]
  rw [e1, e2, mul_left_comm, ENNReal.mul_le_mul_iff_right hκ0 hκt]

end LQGMetric.LM
