/-
A central limit theorem for finite weighted rows of independent copies, under
only a second moment (no third-moment or Lindeberg-array machinery): the proof
compares characteristic functions with Gaussian factors, using quadratic
Taylor remainders of the characteristic function itself and a telescoping
product estimate.

Moved from Divisible-Sandpile-Percolation, `Sandpile/Support/WeightedCLT.lean`.
The source file's final theorem, `weighted_iid_central_limit_pick`, specializes
the array to distinct sites of an i.i.d. field on the lattice, reading it
through `Sandpile.Support.FiniteCoord.measurePreserving_pick`; that lemma is
itself a rederivation of the already-existing `LatticeProb.measurePreserving_pick`
(`LatticeProb/Prob/FiniteMarginal.lean`), so the specialization is restated here
directly against the library's own `LatticeProb.iidLaw` and
`LatticeProb.measurePreserving_pick`, with no new lattice-specific content.
-/
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Analysis.SpecialFunctions.Exp
import LatticeProb.Prob.FiniteMarginal

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ComplexOrder

namespace LatticeProb

/-- An i.i.d. field is a probability measure.  Instance search does not see
this on its own because `iidLaw` does not unfold reducibly to the
`Measure.infinitePi` it is built from. -/
instance iidLaw_isProbabilityMeasure {d : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
  unfold LatticeProb.iidLaw; infer_instance

/-- A telescoping bound: two products of unit-ball-valued factors differ by at
most the sum of the pairwise differences. -/
theorem norm_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hf' : ∀ j ∈ s, ‖f j‖ ≤ 1 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hg' : ∀ j ∈ s, ‖g j‖ ≤ 1 := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have hprod : ‖∏ j ∈ s, g j‖ ≤ 1 := by
      calc ‖∏ j ∈ s, g j‖ = ∏ j ∈ s, ‖g j‖ := norm_prod _ _
        _ ≤ ∏ _j ∈ s, (1 : ℝ) := Finset.prod_le_prod (fun j _ => norm_nonneg _) hg'
        _ = 1 := by simp
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have he : f i * (∏ j ∈ s, f j) - g i * (∏ j ∈ s, g j) =
        f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j) +
          (f i - g i) * (∏ j ∈ s, g j) := by ring
    rw [he]
    have h := norm_add_le (f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j))
      ((f i - g i) * (∏ j ∈ s, g j))
    simp only [norm_mul] at h
    have h1 := mul_le_mul_of_nonneg_right (hf i (Finset.mem_insert_self _ _))
      (norm_nonneg ((∏ j ∈ s, f j) - ∏ j ∈ s, g j))
    have h2 := mul_le_mul_of_nonneg_left hprod (norm_nonneg (f i - g i))
    have hi' := ih hf' hg'
    linarith

/-- The characteristic function of a centred, `L²` law agrees with `1 - σ² t²/2`
to second order at `0`. -/
theorem charFun_second_order (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hmean : ∫ z, z ∂ν = 0) :
    (fun t : ℝ => charFun ν t - (1 - (∫ z, z ^ 2 ∂ν : ℝ) * (t : ℂ) ^ 2 / 2)) =o[𝓝 0]
      (fun t : ℝ => t ^ 2) := by
  have ht := taylor_isLittleO_univ (MeasureTheory.contDiff_charFun hsq) (x₀ := (0 : ℝ))
  have hpoly (t : ℝ) : taylorWithinEval (charFun ν) 2 Set.univ 0 t =
      1 - (∫ z, z ^ 2 ∂ν : ℝ) * (t : ℂ) ^ 2 / 2 := by
    have h := MeasureTheory.taylorWithinEval_charFun_two_zero (P := ν) (X := id)
      measurable_id.aemeasurable (by simpa using hsq) t
    simpa [hmean] using h
  simpa only [hpoly, sub_zero] using ht

/-- The characteristic function of a centred, `L²` law agrees with the
Gaussian factor `exp(-σ² t²/2)` to second order at `0`. -/
theorem charFun_gaussian_second_order (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hmean : ∫ z, z ∂ν = 0) :
    (fun t : ℝ => charFun ν t -
      Complex.exp (-(∫ z, z ^ 2 ∂ν : ℝ) * (t : ℂ) ^ 2 / 2)) =o[𝓝 0]
      (fun t : ℝ => t ^ 2) := by
  set v : ℝ := ∫ z, z ^ 2 ∂ν
  have hExp : (fun z : ℂ => Complex.exp z - (1 + z)) =o[𝓝 0] (fun z : ℂ => z) := by
    simpa [Finset.sum_range_succ] using Complex.exp_sub_sum_range_succ_isLittleO_pow 1
  have hz : Tendsto (fun t : ℝ => -(v : ℂ) * (t : ℂ) ^ 2 / 2) (𝓝 0) (𝓝 0) := by
    have h := (((Complex.continuous_ofReal.tendsto 0).pow 2).const_mul (-(v : ℂ))).div_const 2
    simpa using h
  have hcomp := hExp.comp_tendsto hz
  have hE : (fun t : ℝ => Complex.exp (-(v : ℂ) * (t : ℂ) ^ 2 / 2) -
      (1 - (v : ℂ) * (t : ℂ) ^ 2 / 2)) =o[𝓝 0] (fun t : ℝ => (t : ℂ) ^ 2) := by
    apply Asymptotics.IsLittleO.of_const_mul_right (c := -(v : ℂ) / 2)
    exact hcomp.congr (fun t => by dsimp; ring) (fun t => by dsimp; ring)
  have hE' : (fun t : ℝ => Complex.exp (-(v : ℂ) * (t : ℂ) ^ 2 / 2) -
      (1 - (v : ℂ) * (t : ℂ) ^ 2 / 2)) =o[𝓝 0] (fun t : ℝ => t ^ 2) := by
    rw [← Asymptotics.isLittleO_norm_right] at hE ⊢
    simpa only [norm_pow, Complex.norm_real] using hE
  have hT := charFun_second_order ν hsq hmean
  exact (hT.sub hE').congr_left (fun t => by dsimp [v]; ring)

/-- Products of contractions with quadratic contact have the same limit along
an array with small coefficients and bounded square sums. -/
theorem tendsto_prod_sub_prod_of_quadratic (N : ℕ → ℕ) (a : (n : ℕ) → Fin (N n) → ℝ)
    (f g : ℝ → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1) (hg : ∀ u, ‖g u‖ ≤ 1)
    (hfg : (fun u => f u - g u) =o[𝓝 0] (fun u : ℝ => u ^ 2))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i, |a n i| ≤ δ)
    (B : ℝ) (hB : 0 < B) (hbound : ∀ᶠ n : ℕ in atTop, ∑ i, a n i ^ 2 ≤ B) :
    Tendsto (fun n : ℕ => (∏ i, f (a n i)) - ∏ i, g (a n i)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he := hfg.def (show 0 < ε / (2 * B) by positivity)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.mem_nhds_iff.mp he
  filter_upwards [hsmall (δ / 2) (half_pos hδ), hbound] with n hn hb
  rw [dist_zero_right]
  have hprod := norm_prod_sub_prod_le_sum Finset.univ (fun i => f (a n i))
    (fun i => g (a n i)) (fun i _ => hf _) (fun i _ => hg _)
  have hsum : ∑ i, ‖f (a n i) - g (a n i)‖ ≤ ε / (2 * B) * B := by
    calc ∑ i, ‖f (a n i) - g (a n i)‖ ≤ ∑ i, ε / (2 * B) * a n i ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hi : a n i ∈ Metric.ball 0 δ := by
            rw [Metric.mem_ball, Real.dist_eq, sub_zero]
            exact (hn i).trans_lt (by linarith)
          have h := hδbound hi
          simpa only [Set.mem_setOf_eq, Real.norm_eq_abs, abs_sq] using h
      _ = ε / (2 * B) * ∑ i, a n i ^ 2 := (Finset.mul_sum ..).symm
      _ ≤ ε / (2 * B) * B := mul_le_mul_of_nonneg_left hb (by positivity)
  have heq : ε / (2 * B) * B = ε / 2 := by field_simp
  rw [heq] at hsum
  linarith

/-- The product of characteristic functions of the rescaled array converges to
the Gaussian characteristic function with variance `σ² Q`. -/
theorem tendsto_prod_charFun_weighted (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hmean : ∫ z, z ∂ν = 0)
    (N : ℕ → ℕ) (a : (n : ℕ) → Fin (N n) → ℝ)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i, |a n i| ≤ δ)
    (Q : ℝ) (hQ : Tendsto (fun n => ∑ i, a n i ^ 2) atTop (𝓝 Q)) (t : ℝ) :
    Tendsto (fun n : ℕ => ∏ i, charFun ν (a n i * t)) atTop
      (𝓝 (Complex.exp (-(∫ z, z ^ 2 ∂ν : ℝ) * (Q : ℂ) * (t : ℂ) ^ 2 / 2))) := by
  set v : ℝ := ∫ z, z ^ 2 ∂ν
  have hv : 0 ≤ v := integral_nonneg fun z => sq_nonneg z
  set B := |Q| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hQB : Q < B := by dsimp [B]; linarith [le_abs_self Q]
  have hbound : ∀ᶠ n : ℕ in atTop, ∑ i, (a n i * t) ^ 2 ≤ B * (t ^ 2 + 1) := by
    filter_upwards [hQ.eventually (gt_mem_nhds hQB)] with n hn
    have hsum : ∑ i, (a n i * t) ^ 2 = (∑ i, a n i ^ 2) * t ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.sum_mul]
    rw [hsum]
    have := mul_le_mul_of_nonneg_right hn.le (sq_nonneg t)
    nlinarith
  have hsmall' : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i, |a n i * t| ≤ δ := by
    intro δ hδ
    filter_upwards [hsmall (δ / (|t| + 1)) (by positivity)] with n hn i
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_right (hn i) (abs_nonneg t)
    have htpos : 0 < |t| + 1 := by positivity
    have h' : δ / (|t| + 1) * |t| ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ htpos]
      nlinarith
    exact h.trans h'
  have hg : ∀ u : ℝ, ‖Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2)‖ ≤ 1 := by
    intro u
    have he : -(v : ℂ) * (u : ℂ) ^ 2 / 2 = ((-v * u ^ 2 / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, Complex.norm_exp_ofReal]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv) (sq_nonneg u)) (by norm_num))
  have hd := tendsto_prod_sub_prod_of_quadratic N (fun n i => a n i * t)
    (charFun ν) (fun u => Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2))
    (fun u => norm_charFun_le_one u) hg (charFun_gaussian_second_order ν hsq hmean)
    hsmall' (B * (t ^ 2 + 1)) (by positivity) hbound
  have hgauss : Tendsto (fun n : ℕ => ∏ i,
      Complex.exp (-(v : ℂ) * ((a n i * t : ℝ) : ℂ) ^ 2 / 2)) atTop
      (𝓝 (Complex.exp (-(v : ℂ) * (Q : ℂ) * (t : ℂ) ^ 2 / 2))) := by
    have he (n : ℕ) : (∏ i, Complex.exp (-(v : ℂ) * ((a n i * t : ℝ) : ℂ) ^ 2 / 2)) =
        Complex.exp (-(v : ℂ) * ((∑ i, a n i ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [he]
    exact (((Complex.continuous_ofReal.tendsto Q).comp hQ).const_mul (-(v : ℂ))).mul_const
      ((t : ℂ) ^ 2) |>.div_const 2 |>.cexp
  have h := hd.add hgauss
  simpa only [sub_add_cancel, zero_add] using h

/-- The characteristic function of the weighted sum of `N` i.i.d. copies of
`ν` is the product of the individually rescaled characteristic functions. -/
theorem charFun_weighted_pi {N : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a : Fin N → ℝ) (t : ℝ) :
    charFun ((Measure.pi fun _ : Fin N => ν).map (fun ξ => ∑ i, a i * ξ i)) t =
      ∏ i, charFun ν (a i * t) := by
  have hi : iIndepFun (fun (i : Fin N) (ξ : Fin N → ℝ) => a i * ξ i)
      (Measure.pi fun _ : Fin N => ν) := iIndepFun_pi (fun i => by fun_prop)
  rw [hi.charFun_map_fun_sum_eq_prod (fun i =>
    ((measurable_pi_apply i).const_mul (a i)).aemeasurable)]
  simp only [Finset.prod_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [charFun_map_mul_comp (measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _ : Fin N => ν) i).map_eq]

/-- **The weighted i.i.d. central limit theorem, by characteristic functions.**
For a triangular array of weights with vanishing sup-norm and second moments
converging to `Q`, the weighted row sum of independent copies of a centred,
`L²` law `ν` converges in distribution to the centred Gaussian of variance
`σ² Q`. -/
theorem weighted_iid_central_limit (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hmean : ∫ z, z ∂ν = 0)
    (N : ℕ → ℕ) (a : (n : ℕ) → Fin (N n) → ℝ)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i, |a n i| ≤ δ)
    (Q : ℝ) (hQ : Tendsto (fun n => ∑ i, a n i ^ 2) atTop (𝓝 Q)) :
    TendstoInDistribution (fun (n : ℕ) (ξ : Fin (N n) → ℝ) => ∑ i, a n i * ξ i)
      atTop (id : ℝ → ℝ) (fun n => Measure.pi fun _ : Fin (N n) => ν)
      (gaussianReal 0 (Real.toNNReal ((∫ z, z ^ 2 ∂ν) * Q))) where
  forall_aemeasurable n := by
    have hm (i : Fin (N n)) : Measurable (fun ξ : Fin (N n) → ℝ => a n i * ξ i) :=
      measurable_const.mul (measurable_pi_apply i)
    exact (Finset.measurable_sum Finset.univ (fun i _ => hm i)).aemeasurable
  tendsto := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
    intro t
    have hv : 0 ≤ ∫ z, z ^ 2 ∂ν := integral_nonneg fun z => sq_nonneg z
    have hQ0 : 0 ≤ Q := ge_of_tendsto hQ (Eventually.of_forall fun n =>
      Finset.sum_nonneg fun i _ => sq_nonneg (a n i))
    have hvQ : 0 ≤ (∫ z, z ^ 2 ∂ν) * Q := mul_nonneg hv hQ0
    have h := tendsto_prod_charFun_weighted ν hsq hmean N a hsmall Q hQ t
    change Tendsto (fun n => charFun ((Measure.pi fun _ : Fin (N n) => ν).map
      (fun ξ => ∑ i, a n i * ξ i)) t) atTop
        (𝓝 (charFun ((gaussianReal 0 (Real.toNNReal ((∫ z, z ^ 2 ∂ν) * Q))).map id) t))
    simp_rw [charFun_weighted_pi]
    rw [Measure.map_id, charFun_gaussianReal]
    have he : Complex.exp (-(∫ z, z ^ 2 ∂ν : ℝ) * (Q : ℂ) * (t : ℂ) ^ 2 / 2) =
        Complex.exp ((t : ℂ) * (0 : ℝ) * Complex.I -
          (Real.toNNReal ((∫ z, z ^ 2 ∂ν) * Q) : ℝ) * (t : ℂ) ^ 2 / 2) := by
      congr 1
      rw [Real.coe_toNNReal _ hvQ]
      push_cast
      ring
    rw [← he]
    exact h

/-- **The weighted i.i.d. central limit theorem, read at distinct sites of an
i.i.d. field on the lattice.**  The same convergence as
`weighted_iid_central_limit`, for the array picked out at `N n` distinct sites
`e n : Fin (N n) → Site d` of the field `LatticeProb.iidLaw d ν`. -/
theorem weighted_iid_central_limit_pick {d : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hmean : ∫ z, z ∂ν = 0)
    (N : ℕ → ℕ) (a : (n : ℕ) → Fin (N n) → ℝ)
    (e : (n : ℕ) → Fin (N n) → Site d) (he : ∀ n, Function.Injective (e n))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i, |a n i| ≤ δ)
    (Q : ℝ) (hQ : Tendsto (fun n => ∑ i, a n i ^ 2) atTop (𝓝 Q)) :
    TendstoInDistribution (fun (n : ℕ) (ζ : Site d → ℝ) => ∑ i, a n i * ζ (e n i))
      atTop (id : ℝ → ℝ) (fun _ => LatticeProb.iidLaw d ν)
      (gaussianReal 0 (Real.toNNReal ((∫ z, z ^ 2 ∂ν) * Q))) := by
  have hm (n : ℕ) : Measurable (fun ζ : Site d → ℝ => ∑ i, a n i * ζ (e n i)) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul (measurable_pi_apply (e n i))
  have hlin (n : ℕ) : Measurable (fun ξ : Fin (N n) → ℝ => ∑ i, a n i * ξ i) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul (measurable_pi_apply i)
  have hmap (n : ℕ) : (LatticeProb.iidLaw d ν).map (fun ζ => ∑ i, a n i * ζ (e n i)) =
      (Measure.pi fun _ : Fin (N n) => ν).map (fun ξ => ∑ i, a n i * ξ i) := by
    rw [← (measurePreserving_pick d ν (e n) (he n)).map_eq,
      Measure.map_map (hlin n) (measurePreserving_pick d ν (e n) (he n)).measurable]
    rfl
  have hclt := weighted_iid_central_limit ν hsq hmean N a hsmall Q hQ
  refine ⟨fun n => (hm n).aemeasurable, measurable_id.aemeasurable, ?_⟩
  convert hclt.tendsto using 2 with n
  exact Subtype.ext (hmap n)

end LatticeProb
