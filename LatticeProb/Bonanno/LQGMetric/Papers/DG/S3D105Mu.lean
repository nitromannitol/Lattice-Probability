/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3D105Mu at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3MuHat
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent5Ind
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqExist

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D105 N4: `μ_ĥ` is the vague limit of its own circle-average approximations (DG:980–988)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, DG:984: "If `h` is a GFF and `f`
is a (possibly random) continuous function, then … we can define the average
`(h+f)_ε(z) = h_ε(z) + f_ε(z)` of `h+f` over the circle `∂B_ε(z)`. We can then define `μ_{h+f}`
as the a.s. weak limit `lim_{ε→0} ε^{γ²/2} e^{γ(h+f)_ε(z)} dz` … With this definition, one has
`dμ_{h+f} = e^{γ f} dμ_h` a.s."

The project defines `μ_ĥ := e^{−γY} μ_{h^𝕍}|_K` (`muOfMod`, Papers/DG/S3MuHat.lean) with `Y` a
continuous modification of `h^𝕍 − ĥ` on the box `K` (DG Lemma 3.1). Here we prove DG's defining
property (decision D105 item 4, node N4): a.s., on `interior K`,

`μ_ĥ = vague-lim_k (2^{-k})^{γ²/2} e^{γ ĥ_{2^{-k}}(z)} dz`,

where `ĥ_{2^{-k}}(z)` is any jointly measurable version of the circle averages `dgHat W z 2^{-k}`
of `ĥ` (`ae_isVagueLimitOn_muOfMod`, `ae_isVagueLimitOn_muHat` in `S3D105Mu2.lean`). This replaces DG's appeal to Rhodes–Vargas Thm 5.5
(DG:988): the limit only involves the circle averages of `ĥ`, so `μ_ĥ` is intrinsic to `ĥ` and
does not depend on the modification `Y` (deviation DV-D105-2).

Proof (DG:984 made explicit, own glue): `μ_{h^𝕍}` is a.s. the vague limit of
`areaApprox γ h^𝕍` (`GMCIdent3.ae_isVagueLimitOn_wn`, DS Prop 1.1); a.s. for a.e. `z` the
circle averages satisfy `ĥ_ε(z) = h^𝕍_ε(z) − Y_ε(z)` (`IsDGMod`, `avgReg_ae_eq_wn`, Fubini);
`Y_ε → Y` uniformly on compacts (`Y` continuous), so `e^{−γ Y_ε} → e^{−γ Y}` uniformly and the
approximation densities differ from those of `areaApprox` by this uniformly convergent factor
(`tendsto_integral_of_density`). Finiteness of `areaApprox` on compacts is transferred from a
zero-boundary GFF to the white-noise field by the circle law (D85).

This file: the deterministic core, measurability, the a.s. inputs (`ae_areaApprox_wnField_lt_top`,
`ae_ae_hatCirc_eq`) and `exists_hatCircVer`; the theorems are in `S3D105Mu2.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3 SupTail QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-! ### Deterministic lemmas -/

/-- uniform convergence passes through `x ↦ e^{−γ x}` when the limit is continuous on a compact -/
lemma tendstoUniformlyOn_exp_neg {F : ℕ → ℂ → ℝ} {f : ℂ → ℝ} {C : Set ℂ} (γ : ℝ)
    (hC : IsCompact C) (hf : Continuous f) (h : TendstoUniformlyOn F f atTop C) :
    TendstoUniformlyOn (fun k z => Real.exp (γ * -F k z)) (fun z => Real.exp (γ * -f z))
      atTop C := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  set c := 2 * (|γ| + 1) * Real.exp (|γ| * M) with hc
  have hc0 : 0 < c := by positivity
  set η := min (1 / (|γ| + 1)) (ε / c) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  filter_upwards [h η hη0] with k hk z hz
  have hd := hk z hz
  rw [Real.dist_eq] at hd ⊢
  set d := |f z - F k z| with hd'
  have hg1 : (|γ| + 1) * d < (|γ| + 1) * η := mul_lt_mul_of_pos_left hd (by positivity)
  have hη1 : (|γ| + 1) * η ≤ 1 := by
    have := min_le_left (1 / (|γ| + 1)) (ε / c)
    rw [← hη] at this
    calc (|γ| + 1) * η ≤ (|γ| + 1) * (1 / (|γ| + 1)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 := by field_simp
  have hη2 : c * η ≤ ε := by
    have := min_le_right (1 / (|γ| + 1)) (ε / c)
    rw [← hη] at this
    calc c * η ≤ c * (ε / c) := mul_le_mul_of_nonneg_left this hc0.le
      _ = ε := by field_simp
  have hab : |γ * -F k z - γ * -f z| = |γ| * d := by
    rw [hd', ← abs_mul]; congr 1; ring
  have hd0 : 0 ≤ d := abs_nonneg _
  have hab1 : |γ * -F k z - γ * -f z| ≤ 1 := by
    rw [hab]; nlinarith [abs_nonneg γ]
  have hb : γ * -f z ≤ |γ| * M := by
    have h1 := hM z hz
    rw [Real.norm_eq_abs] at h1
    calc γ * -f z ≤ |γ * -f z| := le_abs_self _
      _ = |γ| * |f z| := by rw [abs_mul, abs_neg]
      _ ≤ |γ| * M := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have e1 : Real.exp (γ * -f z) - Real.exp (γ * -F k z) =
      -(Real.exp (γ * -f z) * (Real.exp (γ * -F k z - γ * -f z) - 1)) := by
    rw [mul_sub, ← Real.exp_add]; ring_nf
  rw [e1, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h2 := Real.abs_exp_sub_one_le hab1
  have h3 : Real.exp (γ * -f z) ≤ Real.exp (|γ| * M) := Real.exp_le_exp.2 hb
  calc Real.exp (γ * -f z) * |Real.exp (γ * -F k z - γ * -f z) - 1|
      ≤ Real.exp (|γ| * M) * (2 * (|γ| * d)) := by
        rw [← hab]; exact mul_le_mul h3 h2 (abs_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (|γ| * M) * (2 * ((|γ| + 1) * d)) := by
        gcongr; linarith
    _ < Real.exp (|γ| * M) * (2 * ((|γ| + 1) * η)) := by
        gcongr
    _ = c * η := by rw [hc]; ring
    _ ≤ ε := hη2

/-- the circle averages `y_{2^{-k}}` of a continuous `y` converge to `y` uniformly on compacts -/
lemma tendstoUniformlyOn_circleAvg {y : ℂ → ℝ} (hy : Continuous y) {C : Set ℂ}
    (hC : IsCompact C) :
    TendstoUniformlyOn (fun k z => ∫ x, y x ∂(circleUnif z (radius k))) y atTop C := by
  have hC1 : IsCompact (cthickening 1 C) := hC.cthickening
  have hu := hC1.uniformContinuousOn_of_continuous hy.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδu⟩ := hu (ε / 2) (by positivity)
  have hr : Tendsto radius atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hr.eventually (gt_mem_nhds (lt_min hδ one_pos))] with k hk z hz
  have hk1 : radius k < δ := lt_of_lt_of_le hk (min_le_left _ _)
  have hk2 : radius k < 1 := lt_of_lt_of_le hk (min_le_right _ _)
  have hint := integrable_circleUnif_of_continuous hy (z := z) (radius_pos k)
  have hae : ∀ᵐ x ∂(circleUnif z (radius k)), ‖y x - y z‖ ≤ ε / 2 := by
    filter_upwards [mem_ae_iff.2 (circleUnif_compl_closedBall (radius_pos k) z)] with x hx
    have hxz : dist x z ≤ radius k := mem_closedBall.1 hx
    have h1 : x ∈ cthickening 1 C := mem_cthickening_of_dist_le x z 1 C hz (by linarith)
    have h2 : z ∈ cthickening 1 C := self_subset_cthickening C hz
    exact (hδu x h1 z h2 (by linarith)).le
  have e : ∫ x, (y x - y z) ∂(circleUnif z (radius k)) =
      ∫ x, y x ∂(circleUnif z (radius k)) - y z := by
    rw [integral_sub hint (integrable_const _), integral_const]; simp
  have h3 := norm_integral_le_of_norm_le_const hae
  rw [e, Real.norm_eq_abs] at h3
  simp only [probReal_univ, mul_one] at h3
  rw [dist_comm, Real.dist_eq]
  linarith

/-- a bounded measurable function vanishing off `C` is integrable when `μ C < ∞` -/
lemma integrable_of_bdd_supp {μ : Measure ℂ} {C : Set ℂ} (hCm : MeasurableSet C) (hC : μ C < ⊤)
    {g : ℂ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ z ∈ C, |g z| ≤ M)
    (h0 : ∀ z, z ∉ C → g z = 0) : Integrable g μ :=
  (Measure.integrableOn_of_bounded hC.ne hg.aestronglyMeasurable
    (ae_restrict_of_forall_mem hCm fun z hz => by rw [Real.norm_eq_abs]; exact hM z hz)
    ).integrable_of_forall_notMem_eq_zero h0

/-- **vague convergence with a uniformly convergent density factor** (deterministic core of N4):
if `A_k → μ` vaguely on `𝕍`, `ν_k = e_k · A_k` on compacts of `U ⊆ 𝕍` at fine scales and
`e_k → e` uniformly on compacts of `U`, then `∫ f dν_k → ∫ f e dμ` for `f ∈ C_c(U)` -/
lemma tendsto_integral_of_density {U : Set ℂ} (hUS : U ⊆ openSquare) {μ : Measure ℂ}
    {A ν : ℕ → Measure ℂ} (hA : IsVagueLimitOn openSquare A μ)
    (hfin : ∀ C, IsCompact C → C ⊆ U → ∀ᶠ k in atTop, A k C < ⊤)
    {e : ℂ → ℝ} (he : Continuous e) {ek : ℕ → ℂ → ℝ} (hekm : ∀ k, Measurable (ek k))
    (hunif : ∀ C, IsCompact C → C ⊆ U → TendstoUniformlyOn ek e atTop C)
    (hν : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      ∀ᶠ k in atTop, ∫ z, f z ∂(ν k) = ∫ z, f z * ek k z ∂(A k))
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    Tendsto (fun k => ∫ z, f z ∂(ν k)) atTop (𝓝 (∫ z, f z * e z ∂μ)) := by
  set C := tsupport f with hCdef
  have hC : IsCompact C := hfc
  have hCm : MeasurableSet C := (isClosed_tsupport f).measurableSet
  have hf0 : ∀ z, z ∉ C → f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  obtain ⟨Mf, hMf⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨Me, hMe⟩ := hC.exists_bound_of_continuousOn he.continuousOn
  have hJ : Tendsto (fun k => ∫ z, f z * e z ∂(A k)) atTop (𝓝 (∫ z, f z * e z ∂μ)) :=
    hA.2.2 _ (hf.mul he) (hfc.mul_right) ((tsupport_mul_subset_left).trans (hfU.trans hUS))
  have hB : Tendsto (fun k => ∫ z, |f z| ∂(A k)) atTop (𝓝 (∫ z, |f z| ∂μ)) :=
    hA.2.2 _ hf.abs (hfc.comp_left abs_zero)
      ((tsupport_comp_subset abs_zero f).trans (hfU.trans hUS))
  set L := ∫ z, |f z| ∂μ + 1 with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ ∫ z, |f z| ∂μ := integral_nonneg fun z => abs_nonneg _
    linarith
  have hD : Tendsto (fun k => ∫ z, f z * ek k z ∂(A k) - ∫ z, f z * e z ∂(A k)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set ε' := ε / (2 * L) with hε'
    have hε'0 : 0 < ε' := by positivity
    filter_upwards [hfin C hC hfU, Metric.tendstoUniformlyOn_iff.1 (hunif C hC hfU) ε' hε'0,
      hB.eventually (gt_mem_nhds (show ∫ z, |f z| ∂μ < L by linarith))] with k hk hu hb
    have hfm := hf.measurable
    have i1 : Integrable (fun z => f z * ek k z) (A k) :=
      integrable_of_bdd_supp hCm hk (hfm.mul (hekm k)) (M := Mf * (Me + ε'))
        (fun z hz => by
          have h1 := hMf z hz; have h2 := hMe z hz; have h3 := hu z hz
          rw [Real.norm_eq_abs] at h1 h2; rw [Real.dist_eq] at h3
          rw [abs_mul]
          have : |ek k z| ≤ Me + ε' := by
            have := abs_sub_abs_le_abs_sub (ek k z) (e z)
            rw [abs_sub_comm (ek k z)] at this; linarith
          exact mul_le_mul h1 this (abs_nonneg _) ((abs_nonneg _).trans h1))
        (fun z hz => by simp [hf0 z hz])
    have i2 : Integrable (fun z => f z * e z) (A k) :=
      integrable_of_bdd_supp hCm hk (hfm.mul he.measurable) (M := Mf * Me)
        (fun z hz => by
          have h1 := hMf z hz; have h2 := hMe z hz
          rw [Real.norm_eq_abs] at h1 h2
          rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))
        (fun z hz => by simp [hf0 z hz])
    have i3 : Integrable (fun z => |f z|) (A k) :=
      integrable_of_bdd_supp hCm hk hf.abs.measurable (M := Mf)
        (fun z hz => by have h1 := hMf z hz; rw [Real.norm_eq_abs] at h1; rwa [abs_abs])
        (fun z hz => by simp [hf0 z hz])
    rw [dist_zero_right, ← integral_sub i1 i2]
    calc ‖∫ z, (f z * ek k z - f z * e z) ∂(A k)‖ ≤ ∫ z, ε' * |f z| ∂(A k) := by
          refine norm_integral_le_of_norm_le (i3.const_mul ε') (Eventually.of_forall fun z => ?_)
          rw [Real.norm_eq_abs, ← mul_sub, abs_mul, mul_comm]
          by_cases hz : z ∈ C
          · have h3 := hu z hz
            rw [Real.dist_eq, abs_sub_comm] at h3
            exact mul_le_mul_of_nonneg_right h3.le (abs_nonneg _)
          · simp [hf0 z hz]
      _ = ε' * ∫ z, |f z| ∂(A k) := integral_const_mul _ _
      _ ≤ ε' * L := mul_le_mul_of_nonneg_left hb.le hε'0.le
      _ = ε / 2 := by rw [hε']; field_simp
      _ < ε := by linarith
  have hsum := hD.add hJ
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [hν f hf hfc hfU] with k hk
  rw [hk]; ring

/-! ### Measurability and the a.s. inputs -/

/-- the circle averages of a jointly measurable (continuous in `z`) field are jointly measurable -/
lemma measurable_circAvg {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun z => Y z ω)
    (hYm : ∀ z, Measurable (Y z)) (r : ℝ) :
    Measurable fun p : ℂ × Ω => ∫ x, Y x p.2 ∂(circleUnif p.1 r) := by
  have hYu : Measurable (fun q : ℂ × Ω => Y q.1 q.2) :=
    measurable_uncurry_of_continuous_of_measurable hYc hYm
  have hcm : Continuous fun q : ℂ × ℝ => circleMap q.1 r q.2 := by
    unfold circleMap; fun_prop
  have hG : Measurable fun q : (ℂ × Ω) × ℝ => Y (circleMap q.1.1 r q.2) q.1.2 :=
    hYu.comp ((hcm.measurable.comp ((measurable_fst.comp measurable_fst).prodMk
      measurable_snd)).prodMk (measurable_snd.comp measurable_fst))
  have e : (fun p : ℂ × Ω => ∫ x, Y x p.2 ∂(circleUnif p.1 r)) = fun p =>
      (ENNReal.ofReal (2 * Real.pi))⁻¹.toReal *
        ∫ θ, Y (circleMap p.1 r θ) p.2 ∂(volume.restrict (Ico 0 (2 * Real.pi))) := by
    funext p
    unfold circleUnif
    rw [integral_smul_measure, integral_map (continuous_circleMap p.1 r).measurable.aemeasurable
      (hYc p.2).aestronglyMeasurable, smul_eq_mul]
  rw [e]
  exact (hG.stronglyMeasurable.integral_prod_right').measurable.const_mul _

/-- the dyadic level sets `{z : 2·2^{-k} < d(z, Uᶜ)}`: their points have `B̄(z, 2·2^{-k}) ⊆ U` -/
def dSet (U : Set ℂ) (k : ℕ) : Set ℂ := {z | 2 * radius k < infDist z Uᶜ}

lemma measurableSet_dSet (U : Set ℂ) (k : ℕ) : MeasurableSet (dSet U k) :=
  measurableSet_lt measurable_const (continuous_infDist_pt _).measurable

lemma closedBall_subset_of_mem_dSet {U : Set ℂ} {k : ℕ} {z : ℂ} (hz : z ∈ dSet U k) :
    closedBall z (2 * radius k) ⊆ U := by
  intro w hw
  by_contra hwU
  have h1 := infDist_le_dist_of_mem (x := z) (show w ∈ Uᶜ from hwU)
  have h2 : dist z w ≤ 2 * radius k := by rw [dist_comm]; exact mem_closedBall.1 hw
  have h3 : 2 * radius k < infDist z Uᶜ := hz
  linarith

/-- **a.s. finiteness of `areaApprox` of the white-noise field on the squares `sqIn`**
(transferred from a zero-boundary GFF through the circle law, D85) -/
theorem ae_areaApprox_wnField_lt_top (hW : IsWhiteNoise P W) (γ : ℝ) :
    ∀ᵐ ω ∂P, ∀ n k : ℕ, radius k < 1 / ((n : ℝ) + 2) / 2 →
      areaApprox γ (wnField W ω) k (sqIn (1 / ((n : ℝ) + 2))) < ⊤ := by
  obtain ⟨Ω₀, _, P₀, X, hP₀, hX⟩ := GMCIdent5.exists_zeroGFF_openSquare
  refine ae_all_iff.2 fun n => ae_all_iff.2 fun k => ?_
  by_cases hk : radius k < 1 / ((n : ℝ) + 2) / 2
  swap
  · exact Eventually.of_forall fun _ h => absurd h hk
  set s := 1 / ((n : ℝ) + 2)
  have hs : 0 < s := by positivity
  have hT : MeasurableSet (sqIn s) := (isClosed_sqIn s).measurableSet
  set p : (CircIdx → ℝ) → Prop := fun v => areaApprox γ (circExt v) k (sqIn s) < ⊤
  have hE : MeasurableSet {v | p v} :=
    measurableSet_lt ((Measure.measurable_coe hT).comp
      ((measurable_areaApprox γ k).comp measurable_circExt)) measurable_const
  have hm : Measurable fun ω => circVec (X ω) := measurable_circVec.comp (measurable_field hX)
  have hν : ∀ᵐ v ∂(circLaw P₀ X), p v := by
    refine (ae_map_iff (p := p) hm.aemeasurable hE).2 ?_
    filter_upwards [ae_areaApprox_sqIn_lt_top hX γ n k hk] with ω h
    simp only [p]
    rw [← Measure.restrict_apply_self, areaApprox_restrict_circExt γ (by linarith) (X ω),
      Measure.restrict_apply_self]
    exact h
  have hW' : ∀ᵐ ω ∂P, p (wnCircVec W ω) := by
    refine ae_of_ae_map (p := p) (measurable_wnCircVec hW).aemeasurable ?_
    rw [← map_circVec_eq hX hW]; exact hν
  filter_upwards [hW'] with ω h _
  exact h


end DG
end LQGMetric
