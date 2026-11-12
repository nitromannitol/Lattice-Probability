/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_2Small
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.2 (`lem-gff-sup`): growth of the circle-average process at all radii

Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380, `lqg-metric-estimates-final.tex`
T:704–709, proof T:788–799. For a whole-plane GFF `h` (any additive constant), its jointly
continuous circle-average process `H`, and `R > 0`, `ζ > 0`, a.s.
`sup_{z ∈ B_R(0)} sup_{r > 0} |h_r(z)| / max{A log(1/r), (log r)^{1/2+ζ}, 1} < ∞`
(`lem2_2`), with a deterministic constant `A` in place of the paper's `2 + ζ`
(DEV-DFGPS-1: the only use, T:733, needs some constant).

Proof as in the paper: small radii by the HMP estimate (`L2_2Small`, here transferred from
rational parameters to all parameters by continuity of `H`), radii in a compact interval by
continuity, large radii by Lemma 2.3 (`lem2_3`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace LQGMetric.DFGPS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}

/-- the HMP growth constant used for `B_R` -/
def hmpConst (R : ℝ) : ℝ := QuantumZipper.R18.RTHmp.hmpA 3 (8 + 4 * R)

lemma hmpConst_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ hmpConst R := by
  have := QuantumZipper.R18.RTHmp.hmp_log4_nonneg 3
  unfold hmpConst QuantumZipper.R18.RTHmp.hmpA; positivity

/-- **Small radii** (T:790–792 via HMP Lemma 3.1): a.s. there is `r₀ ∈ (0, 1]` with
`|H(r, z)| ≤ |H(1, 0)| + a (2 log(1/r) + 1)` for `r ≤ r₀`, `|z| ≤ R`. -/
theorem small_bound (hh : IsWholePlaneGFF h P) (hH : IsCircleAvgVersion h P H) {R : ℝ}
    (hR : 0 ≤ R) :
    ∀ᵐ ω ∂P, ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ ∀ r, 0 < r → r ≤ r₀ → ∀ z ∈ closedBall (0 : ℂ) R,
      |H r z ω| ≤ |H 1 0 ω| + hmpConst R * (2 * Real.log (1 / r) + 1) := by
  set cast3 : (Fin 3 → ℚ) → (Fin 3 → ℝ) := fun q i => (q i : ℝ)
  have h2 := ae_all_iff.2 fun q : Fin 3 → ℚ =>
    hH.sub_ae_eq (hmpRad_pos (cast3 q)) one_pos (hmpPt (cast3 q)) 0
  filter_upwards [hmp_rat_ae hh hR, h2] with ω h1 h2
  obtain ⟨K, hK⟩ := eventually_atTop.1 h1
  have hrK := radius_pos' K
  have hK1 : QuantumZipper.radius K ≤ 1 := by
    unfold QuantumZipper.radius; exact pow_le_one₀ (by norm_num) (by norm_num)
  refine ⟨QuantumZipper.radius K, hrK, hK1, fun r hr hrr z hz => ?_⟩
  have hr1 : 1 ≤ 1 / r := by rw [le_div_iff₀ hr]; linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hr1 (by norm_num : (1 : ℝ) < 2)
  have erad : ∀ m : ℕ, QuantumZipper.radius m = (2 ^ m)⁻¹ := fun m => by
    unfold QuantumZipper.radius; rw [inv_pow]
  have hKn : K ≤ n := by
    by_contra hc
    have h3 : (2 : ℝ) ^ (n + 1) ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : (2 : ℝ) ^ K ≤ 1 / r := by
      rw [erad] at hrr
      rw [le_div_iff₀ hr]; rw [le_inv_comm₀ hr (by positivity)] at hrr
      rw [mul_comm]; calc r * 2 ^ K ≤ r * r⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hr.ne'
    linarith
  -- the parameter point
  set θs : Fin 3 → ℝ := ![z.re, z.im, r]
  have hpt : hmpPt θs = z := by simp [θs, hmpPt, Complex.re_add_im]
  have hθs : θs ∈ hmpU R n := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hpt]; have := mem_closedBall_zero_iff.1 hz; linarith
    · show QuantumZipper.radius (n + 2) < r
      have : (1 / r) < 2 ^ (n + 2) := by
        calc 1 / r < 2 ^ (n + 1) := hn2
          _ < 2 ^ (n + 2) := pow_lt_pow_right₀ (by norm_num) (by omega)
      rw [erad, inv_lt_comm₀ (by positivity) hr]
      simpa [one_div] using this
    · show r < 2 * QuantumZipper.radius n
      rw [erad]
      have : r ≤ (2 ^ n)⁻¹ := by
        rw [le_inv_comm₀ hr (by positivity)]; simpa [one_div] using hn1
      have : (0 : ℝ) < (2 ^ n)⁻¹ := by positivity
      linarith
  have hcl : θs ∈ closure (hmpU R n ∩ ratPts) :=
    dense_ratPts.open_subset_closure_inter (isOpen_hmpU R n) hθs
  set g : (Fin 3 → ℝ) → ℝ := fun θ => |H (θ 2) (hmpPt θ) ω - H 1 0 ω|
  have hgc : ContinuousOn g {θ | 0 < θ 2} :=
    (((hH.cont ω).comp ((continuous_apply 2).prodMk continuous_hmpPt).continuousOn
      fun θ hθ => ⟨hθ, mem_univ _⟩).sub continuousOn_const).abs
  have hclsub : closure (hmpU R n ∩ ratPts) ⊆ {θ | 0 < θ 2} := by
    refine (closure_minimal (fun θ hθ => ?_) (isClosed_le continuous_const (continuous_apply 2)) :
      closure (hmpU R n ∩ ratPts) ⊆ {θ | QuantumZipper.radius (n + 2) ≤ θ 2}).trans
      fun θ hθ => (radius_pos' _).trans_le hθ
    exact hθ.1.2.1.le
  have hle := le_on_closure (f := g) (g := fun _ => hmpConst R * (n + 1)) (s := hmpU R n ∩ ratPts)
    (fun θ hθ => ?_) (hgc.mono hclsub) continuousOn_const hcl
  · have hθr : θs 2 = r := rfl
    simp only [g, hθr, hpt] at hle
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hnl : (n : ℝ) * Real.log 2 ≤ Real.log (1 / r) := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hn1
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have hn : (n : ℝ) ≤ 2 * Real.log (1 / r) := by nlinarith
    have ha := hmpConst_nonneg hR
    have htri : |H r z ω| ≤ |H r z ω - H 1 0 ω| + |H 1 0 ω| := by
      have := abs_add_le (H r z ω - H 1 0 ω) (H 1 0 ω); simpa using this
    have : hmpConst R * (n + 1) ≤ hmpConst R * (2 * Real.log (1 / r) + 1) := by gcongr
    linarith
  · obtain ⟨hθU, q, rfl⟩ := hθ
    have hrad : hmpRad (cast3 q) = cast3 q 2 := by
      unfold hmpRad
      exact ite_eq_left_iff.2 fun h => absurd ((radius_pos' _).trans hθU.2.1) h
    have e := h2 q
    rw [hrad] at e
    show |H (cast3 q 2) (hmpPt (cast3 q)) ω - H 1 0 ω| ≤ hmpConst R * (n + 1)
    rw [e]
    have := hK n hKn _ ⟨hθU, q, rfl⟩
    rw [hrad] at this
    exact this

/-- **DFGPS Lemma 2.2** (`lem-gff-sup`, T:704–709), with a deterministic constant `A` in place
of `2 + ζ` (DEV-DFGPS-1). Let `h` be a whole-plane GFF (any additive constant) and `H` a jointly
continuous version of its circle-average process. For each `R` there is `A > 0` such that for
every `ζ > 0`, a.s. `sup_{z ∈ B_R(0)} sup_{r > 0} |h_r(z)| / max{A log(1/r), (log r)^{1/2+ζ}, 1}`
is finite. -/
theorem lem2_2 (hh : IsWholePlaneGFF h P) (hH : IsCircleAvgVersion h P H) (R : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ ζ : ℝ, 0 < ζ → ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ r : ℝ, 0 < r →
      ∀ z ∈ ball (0 : ℂ) R,
        |H r z ω| ≤ C * max (max (A * Real.log (1 / r)) (Real.log r ^ (1 / 2 + ζ))) 1 := by
  set R' : ℝ := max R 0
  have hR' : 0 ≤ R' := le_max_right _ _
  set a := hmpConst R'
  have ha := hmpConst_nonneg hR'
  refine ⟨2 * a + 1, by positivity, fun ζ hζ => ?_⟩
  filter_upwards [small_bound hh hH hR', lem2_3 hh hH R hζ] with ω hsmall hlarge
  obtain ⟨r₀, hr₀, hr₀1, hsm⟩ := hsmall
  obtain ⟨r₁, hr₁⟩ := eventually_atTop.1 ((hlarge.eventually (ge_mem_nhds one_pos)).and
    (eventually_gt_atTop 1))
  set r₂ := max r₁ 2
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := r₀) (b := r₂)).prod (isCompact_closedBall (0 : ℂ) R')
    |>.exists_bound_of_continuousOn (f := fun p : ℝ × ℂ => H p.1 p.2 ω)
    ((hH.cont ω).mono fun p hp => ⟨hr₀.trans_le hp.1.1, mem_univ _⟩)
  refine ⟨|H 1 0 ω| + a + 1 + |B| + 1, fun r hr z hz => ?_⟩
  set M := max (max ((2 * a + 1) * Real.log (1 / r)) (Real.log r ^ (1 / 2 + ζ))) 1
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMA : (2 * a + 1) * Real.log (1 / r) ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hMr : Real.log r ^ (1 / 2 + ζ) ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hC : 0 ≤ |H 1 0 ω| + a + 1 + |B| := by positivity
  have hzR : z ∈ closedBall (0 : ℂ) R' := by
    rw [mem_closedBall, dist_zero_right]
    have := mem_ball_zero_iff.1 hz; exact this.le.trans (le_max_left _ _)
  rcases le_or_gt r r₀ with h0 | h0
  · have hb := hsm r hr h0 z hzR
    have hl : 0 ≤ Real.log (1 / r) := Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
    have e1 : a * (2 * Real.log (1 / r) + 1) = (2 * a + 1) * Real.log (1 / r) - Real.log (1 / r)
        + a := by ring
    have e2 : (|H 1 0 ω| + a + 1 + |B| + 1) * M = (|H 1 0 ω| + a) * M + M + (|B| + 1) * M := by
      ring
    have e3 : |H 1 0 ω| + a ≤ (|H 1 0 ω| + a) * M := le_mul_of_one_le_right (by positivity) hM1
    have e4 : 0 ≤ (|B| + 1) * M := by positivity
    linarith
  rcases le_or_gt r r₂ with h1 | h1
  · have hb := hB (r, z) ⟨⟨h0.le, h1⟩, hzR⟩
    rw [Real.norm_eq_abs] at hb
    simp only at hb
    have e1 : |B| ≤ |B| * M := le_mul_of_one_le_right (abs_nonneg _) hM1
    have e2 : 0 ≤ (|H 1 0 ω| + a + 1 + 1) * M := by positivity
    have e3 : (|H 1 0 ω| + a + 1 + |B| + 1) * M = |B| * M + (|H 1 0 ω| + a + 1 + 1) * M := by ring
    linarith [le_abs_self B]
  · obtain ⟨hrat, hr1⟩ := hr₁ r ((le_max_left _ _).trans h1.le)
    have hL : 0 < Real.log r := Real.log_pos hr1
    have hp : 0 < Real.log r ^ (1 / 2 + ζ) := Real.rpow_pos_of_pos hL _
    rw [div_le_one hp] at hrat
    have hbdd : BddAbove (range fun w : ball (0 : ℂ) R => |H r w ω|) := by
      obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
        (f := fun w => H r w ω) ((hH.cont ω).comp (continuous_const.prodMk continuous_id).continuousOn
          fun w _ => ⟨hr, mem_univ _⟩)
      refine ⟨D, ?_⟩
      rintro _ ⟨w, rfl⟩
      exact hD w (ball_subset_closedBall w.2)
    have := (le_ciSup hbdd ⟨z, hz⟩).trans hrat
    have : (1 : ℝ) * M ≤ (|H 1 0 ω| + a + 1 + |B| + 1) * M := by gcongr; linarith
    linarith

end LQGMetric.DFGPS
