/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.L510C8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.L510C7
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.L510B
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyPoint

/-!
# GM Lemma 5.10, condition (10) (task P2-M2M6)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`,
l. 3189–3192 and 3331–3333: "the number of functions in `𝓖_r` and the Dirichlet energies of these
functions are each bounded above by constants which depend only on [the parameters] …
Consequently, we can find a constant `Λ₀` … such that condition 10 holds with probability at
least `1 − (1 − 𝕡)/100`." Here (`gm_L510Dir`):

* the bumps are `f_r^{x,y} = T_f(U_r^{x,y}/r)(·/r)` and `g_r^x = T_g(W_r^x/r)(·/r)` for fixed
  templates `T_f, T_g` (`l510_exists_bump`); the sets `U/r`, `W/r` range over the finite family
  `𝒯` of square tubes of side `ε₀` (resp. `θ`) near `cl B_2(0)` (resp. `cl B_3(0)`), so `𝓖_r`
  consists of `0` and the rescalings `ψ(·/r)` of the finitely many `ψ ∈ Ψ` (independent of `r`);
* `(φ, φ)_∇` is scale invariant (`gradEnergy_dilT`), and `E|(h, φ)_∇| ≤ ((φ,φ)_∇ + 1)/2` since
  `Var (h, φ)_∇ = (φ, φ)_∇` (`IsWholePlaneGFF.integral_abs_le`, `logCov_cmTest_cmTest`); Markov's
  inequality and a union bound over `Ψ` give `Λ₀` (GM say "Gaussian tails"; the first-moment
  bound suffices).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

namespace LQGMetric.GM
open Blueprint

lemma l510_cmTest_zero : cmTest (0 : TestC) = 0 := by
  have h := cmTest_neg_cm (0 : TestC)
  rw [neg_zero] at h
  have : (2 : ℝ) • cmTest (0 : TestC) = 0 := by rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  exact (smul_eq_zero.1 this).resolve_left two_ne_zero

lemma l510_dirInner_zero (g : DistC) : dirInner g 0 = 0 := by
  show g (cmTest 0) = 0
  rw [l510_cmTest_zero, map_zero]

lemma l510_gradEnergy_zero : gradEnergy ⇑(0 : TestC) = 0 := by
  have e : (⇑(0 : TestC) : ℂ → ℝ) = fun _ => 0 := rfl
  simp [gradEnergy, e]

/-- the tail of `(h, φ)_∇` (Markov's inequality, `Var (h, φ)_∇ = (φ, φ)_∇`) -/
lemma l510_dir_tail {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (φ : TestC) {M : ℝ} (hM : 0 < M) :
    P {ω | M ≤ |dirInner (h ω) φ|} ≤ ENNReal.ofReal ((gradEnergy φ + 1) / 2 / M) := by
  have hL2 := hh.memLp_two (cmTest0 φ)
  have hint : Integrable (fun ω => |h ω (cmTest0 φ).1|) P :=
    (hL2.integrable one_le_two).abs
  have h1 := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _)
    hint M
  have h2 := hh.integral_abs_le (cmTest0 φ) one_pos
  have e : logCov (cmTest0 φ).1 (cmTest0 φ).1 = gradEnergy φ := logCov_cmTest_cmTest φ
  rw [e, div_one] at h2
  have h3 : (P {ω | M ≤ |dirInner (h ω) φ|}).toReal ≤ (gradEnergy φ + 1) / 2 / M := by
    rw [le_div_iff₀ hM, mul_comm]; exact h1.trans h2
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal h3

set_option maxHeartbeats 1000000 in
/-- **GM Lemma 5.10, condition (10)** (l. 3189–3192, 3331–3333) -/
theorem gm_L510Dir : L510Dir := by
  classical
  intro S hS q hq
  obtain ⟨-, -, hb, -, hε, -, hζ, -, hθ, -⟩ := hS
  have hθ1 : S.θ ≤ 1 / 2 := by
    have := hθ.2; have := hζ.2; have := hε.2; have := hb.2; linarith
  have hθ2 : 0 < S.θ ^ 2 := pow_pos hθ.1 2
  -- the finite family of unit-scale tubes
  set 𝒯 : Set (Set ℂ) := sqTubes S.ε₀ (squareSet S.ε₀ (closedBall 0 2)) ∪
    sqTubes S.θ (squareSet S.θ (closedBall 0 3)) with h𝒯def
  have h𝒯 : 𝒯.Finite :=
    (sqTubes_finite_m2m2 _ (squareSet_finite_m2m2 hε.1 (closedBall_subset_ball (lt_add_one _)))).union
      (sqTubes_finite_m2m2 _ (squareSet_finite_m2m2 hθ.1 (closedBall_subset_ball (lt_add_one _))))
  -- the templates
  let Tf : Set ℂ → TestC := fun W =>
    if hW : Bornology.IsBounded W then Classical.choose (l510_exists_bump hW hζ.1) else 0
  let Tg : Set ℂ → TestC := fun W =>
    if hW : Bornology.IsBounded W then Classical.choose (l510_exists_bump hW hθ2) else 0
  have hTf : ∀ W, Bornology.IsBounded W → IsBumpFor (Tf W) W S.ζ := fun W hW => by
    simp only [Tf, hW]; exact Classical.choose_spec (l510_exists_bump hW hζ.1)
  have hTg : ∀ W, Bornology.IsBounded W → IsBumpFor (Tg W) W (S.θ ^ 2) := fun W hW => by
    simp only [Tg, hW]; exact Classical.choose_spec (l510_exists_bump hW hθ2)
  let Φ : Set ℂ × Set ℂ × Set ℂ → TestC := fun p => S.Kf • Tf p.1 + S.Kg • (Tg p.2.1 + Tg p.2.2)
  have hΨ : (Φ '' (𝒯 ×ˢ (𝒯 ×ˢ 𝒯))).Finite := (h𝒯.prod (h𝒯.prod h𝒯)).image Φ
  set F := hΨ.toFinset with hF
  set N : ℝ := (F.card : ℝ) with hN
  set C₀ : ℝ := ∑ ψ ∈ F, gradEnergy ψ with hC₀
  have hC₀0 : 0 ≤ C₀ := Finset.sum_nonneg fun ψ _ => gradEnergy_nonneg_cm _
  have hgC : ∀ ψ ∈ F, gradEnergy ψ ≤ C₀ := fun ψ hψ =>
    Finset.single_le_sum (f := fun ψ : TestC => gradEnergy ψ) (fun ψ _ => gradEnergy_nonneg_cm _)
      hψ
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set M0 : ℝ := (N + 1) * (C₀ + 1) / q + 2 with hM0
  have hM00 : 2 ≤ M0 := by rw [hM0]; have : 0 ≤ (N + 1) * (C₀ + 1) / q := by positivity
                           linarith
  refine ⟨C₀ / 2 + M0, by linarith [hC₀0], ?_⟩
  intro r hr U hU
  -- the tubes rescale into `𝒯`
  have hUT : ∀ x ∈ sphere (0 : ℂ) (2 * r), ∀ y ∈ sphere (0 : ℂ) (2 * r), S.δ * r ≤ ‖x - y‖ →
      (r⁻¹ : ℝ) • U x y ∈ sqTubes S.ε₀ (squareSet S.ε₀ (closedBall 0 2)) := by
    intro x hx y hy hxy
    have h1 := tube_mem_sqTubes_m2m2 (hU x hx y hy hxy).2.2.2.1
    have h2 : U x y ∈ sqTubes (S.ε₀ * r) (squareSet (S.ε₀ * r) (closedBall 0 (2 * r))) :=
      image_mono (powerset_mono.2 (squareSet_mono _ fun w hw => by
        rw [mem_closedBall, dist_zero_right]; exact hw.2)) h1
    exact sqTubes_smul hr h2
  have hWT : ∀ x ∈ sphere (0 : ℂ) (2 * r),
      (r⁻¹ : ℝ) • lineTube S.θ r x ∈ sqTubes S.θ (squareSet S.θ (closedBall 0 3)) := by
    intro x hx
    rw [mem_sphere, dist_zero_right] at hx
    exact sqTubes_smul (R := 3) hr (lineTube_mem_sqTubes_m2m2 hθ.1.le hθ1 hx)
  have hbdd1 : ∀ W ∈ sqTubes S.ε₀ (squareSet S.ε₀ (closedBall 0 2)), Bornology.IsBounded W :=
    fun W hW => isBounded_closedBall.subset (sqTubes_subset_ball hε.1 hW)
  have hbdd2 : ∀ W ∈ sqTubes S.θ (squareSet S.θ (closedBall 0 3)), Bornology.IsBounded W :=
    fun W hW => isBounded_closedBall.subset (sqTubes_subset_ball hθ.1 hW)
  refine ⟨fun V => dilT r (Tf ((r⁻¹ : ℝ) • V)), fun V => dilT r (Tg ((r⁻¹ : ℝ) • V)),
    ⟨fun x hx y hy hxy => ?_, fun x hx => ?_⟩, ?_⟩
  · exact isBumpFor_dilT hr (hTf _ (hbdd1 _ (hUT x hx y hy hxy)))
  · exact isBumpFor_dilT hr (hTg _ (hbdd2 _ (hWT x hx)))
  intro Ω _ P _ h hh
  -- every nonzero element of `𝓖_r` is the rescaling of some `ψ ∈ Ψ`
  have hfam : ∀ φ ∈ bumpFam S U (fun V => dilT r (Tf ((r⁻¹ : ℝ) • V)))
      (fun V => dilT r (Tg ((r⁻¹ : ℝ) • V))) r, φ = 0 ∨ ∃ ψ ∈ F, φ = dilT r ψ := by
    rintro φ (⟨x, hx, y, hy, hxy, rfl⟩ | h0)
    · right
      refine ⟨Φ ((r⁻¹ : ℝ) • U x y, (r⁻¹ : ℝ) • lineTube S.θ r x,
        (r⁻¹ : ℝ) • lineTube S.θ r y), ?_, ?_⟩
      · rw [hF, Set.Finite.mem_toFinset]
        exact mem_image_of_mem Φ (show ((r⁻¹ : ℝ) • U x y, (r⁻¹ : ℝ) • lineTube S.θ r x,
          (r⁻¹ : ℝ) • lineTube S.θ r y) ∈ 𝒯 ×ˢ (𝒯 ×ˢ 𝒯) from
          ⟨Or.inl (hUT x hx y hy hxy), Or.inr (hWT x hx), Or.inr (hWT y hy)⟩)
      · simp only [bumpPhi, Φ, map_add, map_smul]
    · left; exact h0
  -- the union bound
  have hsub : {ω | ¬ ∀ φ ∈ bumpFam S U (fun V => dilT r (Tf ((r⁻¹ : ℝ) • V)))
      (fun V => dilT r (Tg ((r⁻¹ : ℝ) • V))) r,
        |dirInner (h ω) φ| + gradEnergy φ / 2 ≤ C₀ / 2 + M0} ⊆
      ⋃ ψ ∈ F, {ω | M0 ≤ |dirInner (h ω) (dilT r ψ)|} := by
    intro ω hω
    simp only [mem_ofPred_eq, not_forall, not_le, exists_prop] at hω
    obtain ⟨φ, hφ, hlt⟩ := hω
    rcases hfam φ hφ with rfl | ⟨ψ, hψ, rfl⟩
    · rw [l510_dirInner_zero, l510_gradEnergy_zero] at hlt
      simp only [abs_zero, zero_div, add_zero] at hlt
      linarith [hC₀0]
    · refine mem_iUnion₂.2 ⟨ψ, hψ, ?_⟩
      show M0 ≤ |dirInner (h ω) (dilT r ψ)|
      rw [gradEnergy_dilT hr] at hlt
      linarith [hgC ψ hψ]
  have hM0pos : 0 < M0 := by linarith
  calc _ ≤ P (⋃ ψ ∈ F, {ω | M0 ≤ |dirInner (h ω) (dilT r ψ)|}) := measure_mono hsub
    _ ≤ ∑ ψ ∈ F, P {ω | M0 ≤ |dirInner (h ω) (dilT r ψ)|} := measure_biUnion_finset_le F _
    _ ≤ ∑ _ψ ∈ F, ENNReal.ofReal ((C₀ + 1) / 2 / M0) := by
        refine Finset.sum_le_sum fun ψ hψ => (l510_dir_tail hh _ hM0pos).trans
          (ENNReal.ofReal_le_ofReal ?_)
        rw [gradEnergy_dilT hr]
        have := hgC ψ hψ
        gcongr
    _ = ENNReal.ofReal (N * ((C₀ + 1) / 2 / M0)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul hN0, hN, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal q := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hM1 : (N + 1) * (C₀ + 1) / q ≤ M0 := by rw [hM0]; linarith
        rw [div_le_iff₀ hq] at hM1
        rw [div_div, mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith

end LQGMetric.GM
