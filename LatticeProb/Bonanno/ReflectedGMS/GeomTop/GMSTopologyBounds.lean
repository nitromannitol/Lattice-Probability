/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeomTop.GMSTopologyBounds at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.GMSTopologyTriangle
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Util.AssertNoSorry

/-!
# Comparison of `d_sing` and `d^CC` near a locally finite configuration

The two sequential implications in the proof of Proposition 2.5
(`work/geomtop/manuscript-text.txt:433-450`), in `ε`-`δ` form around a configuration `H` whose
restriction to every ball is finite (every GMS configuration):

* `GMSTopology.exists_dSing_lt_imp_dCC_lt`: `d_sing(H,·)` small forces `d^CC(H,·)` small.  With
  the one-point tuple `(0)` the window `U_{(0),r}` is the ball `B_r(0)`, a whole-cell matching of
  the two restrictions to `B_r(0)` is admissible in `d^CC` with the same distortion
  (`dCCIntegrand_le_restrictionDist`), and below a radius `R` the restriction of `H` has at most
  `N` cells, so the capped restriction of `H` is not `†`.  This gives the explicit bound
  `d^CC(H,H'') ≤ e^R 2^{j+N+2} d_sing(H,H'') + e^{-R}` (`dCC_le_of_dSing`).  No almost-every-radius
  argument is needed on this side.
* `GMSTopology.exists_dCC_lt_imp_dSing_lt`: `d^CC(H,·)` small forces `d_sing(H,·)` small.  A
  matching at a large radius `ρ` of small distortion `η` restricts to a whole-cell matching of the
  restrictions to a test window `U_{q,r}` whenever `r` stays at distance `≥ γ > η` from the finitely
  many exceptional radii `dist(q_i, K)` of the cells `K` near the window (the manuscript's
  strict-comparison argument, `restrictionDist_le_of_admissible`); the exceptional radii carry
  Lebesgue measure `≤ 2γ · #`.  Only the configuration `H` needs to be locally finite.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace ReflectedGMS.GeomTop

open GMS

namespace GMSTopology

/-! ### Elementary facts -/

theorem lintegral_exp_neg_Ioi (c : ℝ) :
    ∫⁻ r in Ioi c, ENNReal.ofReal (Real.exp (-r)) = ENNReal.ofReal (Real.exp (-c)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi c)
    (ae_of_all _ fun r => (Real.exp_pos (-r)).le), integral_exp_neg_Ioi]

theorem ofReal_exp_neg_le_one {r : ℝ} (hr : 0 ≤ r) : ENNReal.ofReal (Real.exp (-r)) ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 (by linarith))

theorem restrictionDist_le_one (o o' : Option CellConfig) : restrictionDist o o' ≤ 1 := by
  rcases o with _ | F <;> rcases o' with _ | F' <;>
    simp only [restrictionDist, zero_le, le_refl, min_le_iff, true_or]

theorem integrand_le_exp (H H' : CellConfig) (j N : ℕ) (r : ℝ) :
    CoordsMeasurable.integrand H H' j N r ≤ ENNReal.ofReal (Real.exp (-r)) := by
  unfold CoordsMeasurable.integrand
  exact mul_le_of_le_one_right' (restrictionDist_le_one _ _)

theorem lintegral_integrand_le_one (H H' : CellConfig) (j N : ℕ) :
    ∫⁻ r in Ioi (0 : ℝ), CoordsMeasurable.integrand H H' j N r ≤ 1 := by
  calc _ ≤ ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-r)) :=
        lintegral_mono fun r => integrand_le_exp H H' j N r
    _ = 1 := by rw [lintegral_exp_neg_Ioi, neg_zero, Real.exp_zero, ENNReal.ofReal_one]

theorem lintegral_le_two_pow_mul_dSing (H H' : CellConfig) (j N : ℕ) :
    ∫⁻ r in Ioi (0 : ℝ), CoordsMeasurable.integrand H H' j N r ≤
      (2 : ℝ≥0∞) ^ ((j + 1) + (N + 1)) * dSing H H' := by
  have h2 : (2 : ℝ≥0∞) ^ ((j + 1) + (N + 1)) * (2 : ℝ≥0∞)⁻¹ ^ ((j + 1) + (N + 1)) = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  calc _ = (2 : ℝ≥0∞) ^ ((j + 1) + (N + 1)) * ((2 : ℝ≥0∞)⁻¹ ^ ((j + 1) + (N + 1)) *
        ∫⁻ r in Ioi (0 : ℝ), CoordsMeasurable.integrand H H' j N r) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl (CoordsMeasurable.term_le_dSing H H' j N)

/-- A GMS configuration has finite restrictions to all balls. -/
theorem finite_restrict_ball {H : CellConfig} (hH : H.IsCellConfiguration) (R : ℝ) :
    (H.restrict (ball (0 : Plane) R)).Finite :=
  (CellConfig.finite_restrict_of_isCompact hH (isCompact_closedBall 0 R)).subset
    (restrict_mono H ball_subset_closedBall)

theorem restrictConfig_adj_iff {H : CellConfig} {W : Set Plane} {K K' : Cell}
    (hK : K ∈ H.restrict W) (hK' : K' ∈ H.restrict W) :
    (CellConfigOps.restrictConfig H W).Adj K K' ↔ H.Adj K K' := by
  unfold CellConfig.Adj
  rw [CoordsMeasurable.restrictConfig_c_of_mem hK hK']

/-! ### The one-point window at the origin -/

theorem ratPoint_zero : ratPoint 0 = 0 := by
  ext i
  fin_cases i <;> simp [ratPoint]

theorem window_origin (r : ℝ) :
    window ⟨[(0 : ℚ × ℚ)], List.cons_ne_nil _ _⟩ r = ball (0 : Plane) r := by
  ext x
  simp [window, ratPoint_zero]

/-! ### `d_sing` small forces `d^CC` small -/

theorem admissibleAt_of_matchesWhole {H H'' : CellConfig} {r : ℝ} {f : Plane ≃ₜ Plane}
    (hm : MatchesWhole (CellConfigOps.restrictConfig H (ball 0 r))
      (CellConfigOps.restrictConfig H'' (ball 0 r)) f) :
    CellConfig.AdmissibleAt H H'' r f := by
  refine ⟨fun K hK => hm.1 K hK, fun K hK => hm.2.1 K hK, fun K hK K' hK' hadj => ?_,
    fun K hK K' hK' hadj => ?_⟩
  · exact (restrictConfig_adj_iff (hm.1 K hK) (hm.1 K' hK')).1
      ((hm.2.2 K hK K' hK').1 ((restrictConfig_adj_iff hK hK').2 hadj))
  · have hL : CellConfig.mapCell f.symm K ∈ H.restrict (ball 0 r) := hm.2.1 K hK
    have hL' : CellConfig.mapCell f.symm K' ∈ H.restrict (ball 0 r) := hm.2.1 K' hK'
    refine (restrictConfig_adj_iff hL hL').1 ((hm.2.2 _ hL _ hL').2 ?_)
    rw [CellConfig.mapCell_mapCell_symm, CellConfig.mapCell_mapCell_symm]
    exact (restrictConfig_adj_iff hK hK').2 hadj

theorem distortion_le_wholeDistortion {H H'' : CellConfig} {r : ℝ} {f : Plane ≃ₜ Plane}
    (hm : MatchesWhole (CellConfigOps.restrictConfig H (ball 0 r))
      (CellConfigOps.restrictConfig H'' (ball 0 r)) f) :
    CellConfig.distortion H H'' r f ≤ wholeDistortion (CellConfigOps.restrictConfig H (ball 0 r))
      (CellConfigOps.restrictConfig H'' (ball 0 r)) f := by
  unfold CellConfig.distortion wholeDistortion
  refine add_le_add (iSup_mono fun z => (edist_comm z (f z)).le) ?_
  refine iSup₂_le fun K hK => iSup₂_le fun K' hK' => iSup_le fun hadj => ?_
  refine le_iSup₂_of_le K hK (le_iSup₂_of_le K' hK'
    (le_iSup_of_le ((restrictConfig_adj_iff hK hK').2 hadj) (le_of_eq ?_)))
  rw [CoordsMeasurable.restrictConfig_c_of_mem hK hK',
    CoordsMeasurable.restrictConfig_c_of_mem (hm.1 K hK) (hm.1 K' hK')]

/-- On a ball on which `H` has at most `n` cells, the integrand of `d^CC` is dominated by the
distance (2.1) of the capped restrictions: a whole-cell matching of the restrictions to `B_r(0)` is
admissible for `d^CC` at radius `r`, with no larger distortion. -/
theorem dCCIntegrand_le_restrictionDist {H H'' : CellConfig} {r : ℝ} (hr : 0 ≤ r) {n : ℕ}
    (hn : (H.restrict (ball (0 : Plane) r)).encard ≤ n) :
    dCCIntegrand H H'' r ≤ restrictionDist (CellConfigOps.capped H n (ball 0 r))
      (CellConfigOps.capped H'' n (ball 0 r)) := by
  have hexp := ofReal_exp_neg_le_one hr
  have hcapH : CellConfigOps.capped H n (ball 0 r) =
      some (CellConfigOps.restrictConfig H (ball 0 r)) := by
    unfold CellConfigOps.capped
    rw [if_pos hn]
  rw [hcapH]
  cases hcap : CellConfigOps.capped H'' n (ball (0 : Plane) r) with
  | none =>
    show dCCIntegrand H H'' r ≤ 1
    exact (min_le_left _ _).trans hexp
  | some F'' =>
    have hF'' : F'' = CellConfigOps.restrictConfig H'' (ball 0 r) := by
      unfold CellConfigOps.capped at hcap
      split_ifs at hcap
      exact (Option.some.inj hcap).symm
    subst hF''
    refine le_min ((min_le_left _ _).trans hexp) ((min_le_right _ _).trans ?_)
    exact le_iInf₂ fun f hf => (iInf₂_le f (admissibleAt_of_matchesWhole hf)).trans
      (distortion_le_wholeDistortion hf)

/-- **Quantitative comparison `d^CC ≲ d_sing`** near a configuration with finite restrictions to
all balls. -/
theorem dCC_le_of_dSing {H : CellConfig}
    (hfin : ∀ R : ℝ, (H.restrict (ball (0 : Plane) R)).Finite) {R : ℝ} (hR : 0 < R) :
    ∃ k : ℕ, ∀ H'' : CellConfig,
      CellConfig.dCC H H'' ≤ ENNReal.ofReal (Real.exp R) * ((2 : ℝ≥0∞) ^ k * dSing H H'') +
        ENNReal.ofReal (Real.exp (-R)) := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, ratTuple j = ⟨[(0 : ℚ × ℚ)], List.cons_ne_nil _ _⟩ :=
    ⟨_, Denumerable.ofNat_encode _⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (H.restrict (ball (0 : Plane) R)).encard = N :=
    ⟨_, (hfin R).cast_ncard_eq.symm⟩
  refine ⟨(j₀ + 1) + (N + 1), fun H'' => ?_⟩
  have hwin : ∀ r, window (ratTuple j₀) r = ball (0 : Plane) r := fun r => by
    rw [hj₀, window_origin]
  have hpt : ∀ r ∈ Ioc (0 : ℝ) R, dCCIntegrand H H'' r ≤
      ENNReal.ofReal (Real.exp R) * CoordsMeasurable.integrand H H'' j₀ N r := by
    intro r hr
    have hn : (H.restrict (ball (0 : Plane) r)).encard ≤ ((N + 1 : ℕ) : ℕ∞) := by
      calc _ ≤ (H.restrict (ball (0 : Plane) R)).encard :=
            encard_le_encard (restrict_mono H (ball_subset_ball hr.2))
        _ = (N : ℕ∞) := hN
        _ ≤ _ := by exact_mod_cast Nat.le_succ N
    have h1 := dCCIntegrand_le_restrictionDist (H'' := H'') hr.1.le hn
    unfold CoordsMeasurable.integrand
    rw [hwin r]
    set δr := restrictionDist (CellConfigOps.capped H (N + 1) (ball 0 r))
      (CellConfigOps.capped H'' (N + 1) (ball 0 r))
    calc dCCIntegrand H H'' r ≤ δr := h1
      _ = 1 * δr := (one_mul _).symm
      _ ≤ ENNReal.ofReal (Real.exp R * Real.exp (-r)) * δr := by
          gcongr
          rw [← ENNReal.ofReal_one, ← Real.exp_add]
          exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by linarith [hr.2]))
      _ = ENNReal.ofReal (Real.exp R) * (ENNReal.ofReal (Real.exp (-r)) * δr) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos R).le, mul_assoc]
  have hsplit : CellConfig.dCC H H'' ≤ (∫⁻ r in Ioc (0 : ℝ) R, dCCIntegrand H H'' r) +
      ∫⁻ r in Ioi R, dCCIntegrand H H'' r := by
    rw [dCC_eq, ← Ioc_union_Ioi_eq_Ioi hR.le]
    exact lintegral_union_le _ _ _
  have h1 : (∫⁻ r in Ioc (0 : ℝ) R, dCCIntegrand H H'' r) ≤
      ENNReal.ofReal (Real.exp R) * ((2 : ℝ≥0∞) ^ ((j₀ + 1) + (N + 1)) * dSing H H'') := by
    calc _ ≤ ∫⁻ r in Ioc (0 : ℝ) R,
          ENNReal.ofReal (Real.exp R) * CoordsMeasurable.integrand H H'' j₀ N r :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hpt))
      _ = ENNReal.ofReal (Real.exp R) *
            ∫⁻ r in Ioc (0 : ℝ) R, CoordsMeasurable.integrand H H'' j₀ N r :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp R) *
            ∫⁻ r in Ioi (0 : ℝ), CoordsMeasurable.integrand H H'' j₀ N r :=
          mul_le_mul' le_rfl (lintegral_mono_set Ioc_subset_Ioi_self)
      _ ≤ _ := mul_le_mul' le_rfl (lintegral_le_two_pow_mul_dSing H H'' j₀ N)
  have h2 : (∫⁻ r in Ioi R, dCCIntegrand H H'' r) ≤ ENNReal.ofReal (Real.exp (-R)) := by
    calc _ ≤ ∫⁻ r in Ioi R, ENNReal.ofReal (Real.exp (-r)) :=
          lintegral_mono fun r => by unfold dCCIntegrand; exact min_le_left _ _
      _ = _ := lintegral_exp_neg_Ioi R
  exact hsplit.trans (add_le_add h1 h2)

/-- **`d_sing` small forces `d^CC` small** near a configuration with finite restrictions to all
balls. -/
theorem exists_dSing_lt_imp_dCC_lt {H : CellConfig}
    (hfin : ∀ R : ℝ, (H.restrict (ball (0 : Plane) R)).Finite) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ H'' : CellConfig, dSing H H'' < δ → CellConfig.dCC H H'' < ε := by
  obtain ⟨η, -, hη0, hηε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hη : 0 < η := ENNReal.ofReal_pos.1 hη0
  have hR : 0 < |Real.log (η / 2)| + 1 := by positivity
  have hexpR : Real.exp (-(|Real.log (η / 2)| + 1)) < η / 2 := by
    calc Real.exp (-(|Real.log (η / 2)| + 1)) < Real.exp (Real.log (η / 2)) :=
          Real.exp_lt_exp.2 (by linarith [neg_abs_le (Real.log (η / 2))])
      _ = η / 2 := Real.exp_log (half_pos hη)
  obtain ⟨k, hk⟩ := dCC_le_of_dSing hfin hR
  have hC0 : ENNReal.ofReal (Real.exp (|Real.log (η / 2)| + 1)) * (2 : ℝ≥0∞) ^ k ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' (pow_ne_zero _ two_ne_zero)
  have hCtop : ENNReal.ofReal (Real.exp (|Real.log (η / 2)| + 1)) * (2 : ℝ≥0∞) ^ k ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  refine ⟨ENNReal.ofReal (η / 2) /
      (ENNReal.ofReal (Real.exp (|Real.log (η / 2)| + 1)) * (2 : ℝ≥0∞) ^ k),
    ENNReal.div_pos_iff.2 ⟨(ENNReal.ofReal_pos.2 (half_pos hη)).ne', hCtop⟩, fun H'' hH'' => ?_⟩
  have hA : ENNReal.ofReal (Real.exp (|Real.log (η / 2)| + 1)) * ((2 : ℝ≥0∞) ^ k * dSing H H'') ≤
      ENNReal.ofReal (η / 2) := by
    rw [← mul_assoc]
    calc ENNReal.ofReal (Real.exp (|Real.log (η / 2)| + 1)) * (2 : ℝ≥0∞) ^ k * dSing H H''
        ≤ ENNReal.ofReal (Real.exp (|Real.log (η / 2)| + 1)) * (2 : ℝ≥0∞) ^ k *
            (ENNReal.ofReal (η / 2) /
              (ENNReal.ofReal (Real.exp (|Real.log (η / 2)| + 1)) * (2 : ℝ≥0∞) ^ k)) :=
          mul_le_mul' le_rfl hH''.le
      _ = ENNReal.ofReal (η / 2) := ENNReal.mul_div_cancel hC0 hCtop
  calc CellConfig.dCC H H'' ≤ _ := hk H''
    _ < ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
        ENNReal.add_lt_add_of_le_of_lt (hA.trans_lt ENNReal.ofReal_lt_top).ne hA
          ((ENNReal.ofReal_lt_ofReal_iff (half_pos hη)).2 hexpR)
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (half_pos hη).le (half_pos hη).le, add_halves]
    _ < ε := hηε

/-! ### `d^CC` small forces `d_sing` small -/

/-- **Strict comparison.**  Let `f` be admissible for `d^CC` at radius `ρ` with distortion `< η`,
let the `(r + η)`-neighbourhood of the window `U_{q,r}` lie in `B_ρ(0)`, and suppose `r` stays at
distance `≥ γ > η` from `dist(q_i, K)` for every cell `K` of `H` meeting that neighbourhood near
`q_i`.  Then `f` restricts to a whole-cell matching of `H(U_{q,r})` onto `H''(U_{q,r})`, the two
capped restrictions are both `†` or both ordinary, and their distance (2.1) is at most `η`. -/
theorem restrictionDist_le_of_admissible {H H'' : CellConfig} {ρ η γ r : ℝ}
    {f : Plane ≃ₜ Plane} (hf : CellConfig.AdmissibleAt H H'' ρ f)
    (hfd : CellConfig.distortion H H'' ρ f < ENNReal.ofReal η) (hηγ : η < γ) (q : RatTuple)
    (n : ℕ)
    (hwinρ : ∀ p ∈ q.1, ∀ x : Plane, dist x (ratPoint p) < r + η → x ∈ ball (0 : Plane) ρ)
    (hgood : ∀ p ∈ q.1, ∀ K ∈ H.cells,
      (∃ x ∈ (K : Set Plane), dist x (ratPoint p) < r + η) →
        r ≤ infDist (ratPoint p) (K : Set Plane) - γ ∨
          infDist (ratPoint p) (K : Set Plane) + γ ≤ r) :
    restrictionDist (CellConfigOps.capped H n (window q r))
      (CellConfigOps.capped H'' n (window q r)) ≤ ENNReal.ofReal η := by
  have hfz : ∀ z, dist z (f z) < η := CellConfig.dist_lt_of_distortion_lt hfd
  have hη : 0 < η := lt_of_le_of_lt dist_nonneg (hfz 0)
  have hmemW : ∀ x, x ∈ window q r ↔ ∃ p ∈ q.1, dist x (ratPoint p) < r := by
    intro x
    simp only [window, mem_iUnion, mem_ball, exists_prop]
  have hWρ : ∀ x ∈ window q r, x ∈ ball (0 : Plane) ρ := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := (hmemW x).1 hx
    exact hwinρ p hp x (by linarith)
  have hρ : ∀ K ∈ H.restrict (window q r), K ∈ H.restrict (ball (0 : Plane) ρ) :=
    fun K hK => restrict_mono H hWρ hK
  have hρ'' : ∀ L ∈ H''.restrict (window q r), L ∈ H''.restrict (ball (0 : Plane) ρ) :=
    fun L hL => restrict_mono H'' hWρ hL
  -- (A) images of cells of `H` meeting the window meet the window
  have hA : ∀ K ∈ H.restrict (window q r), CellConfig.mapCell f K ∈ H''.restrict (window q r) := by
    intro K hK
    obtain ⟨hKc, x, hxK, hxW⟩ := hK
    obtain ⟨p, hp, hxp⟩ := (hmemW x).1 hxW
    have he : infDist (ratPoint p) (K : Set Plane) < r :=
      (infDist_le_dist_of_mem hxK).trans_lt (by rw [dist_comm]; exact hxp)
    have he' : infDist (ratPoint p) (K : Set Plane) < r - η := by
      rcases hgood p hp K hKc ⟨x, hxK, by linarith⟩ with h | h
      · linarith
      · linarith
    obtain ⟨y, hyK, hy⟩ := (infDist_lt_iff K.nonempty).1 he'
    refine ⟨(hf.1 K (hρ K ⟨hKc, x, hxK, hxW⟩)).1, f y, ?_, ?_⟩
    · rw [CellConfig.coe_mapCell_eq_image]
      exact mem_image_of_mem f hyK
    · refine (hmemW (f y)).2 ⟨p, hp, ?_⟩
      calc dist (f y) (ratPoint p) ≤ dist (f y) y + dist y (ratPoint p) := dist_triangle _ _ _
        _ < η + (r - η) := by
            refine add_lt_add ?_ ?_
            · rw [dist_comm]; exact hfz y
            · rw [dist_comm]; exact hy
        _ = r := by ring
  -- (B) preimages of cells of `H''` meeting the window meet the window
  have hB : ∀ L ∈ H''.restrict (window q r),
      CellConfig.mapCell f.symm L ∈ H.restrict (window q r) := by
    intro L hL
    have hKρ := hf.2.1 L (hρ'' L hL)
    obtain ⟨hLc, y, hyL, hyW⟩ := hL
    obtain ⟨p, hp, hyp⟩ := (hmemW y).1 hyW
    have hxK : f.symm y ∈ (CellConfig.mapCell f.symm L : Set Plane) := by
      rw [CellConfig.coe_mapCell_eq_image]
      exact mem_image_of_mem f.symm hyL
    have hxy : dist (f.symm y) y < η := by
      have := hfz (f.symm y)
      rwa [f.apply_symm_apply] at this
    have hxp : dist (f.symm y) (ratPoint p) < r + η := by
      calc dist (f.symm y) (ratPoint p) ≤ dist (f.symm y) y + dist y (ratPoint p) :=
            dist_triangle _ _ _
        _ < η + r := add_lt_add hxy hyp
        _ = r + η := by ring
    have he : infDist (ratPoint p) (CellConfig.mapCell f.symm L : Set Plane) < r + η :=
      (infDist_le_dist_of_mem hxK).trans_lt (by rw [dist_comm]; exact hxp)
    have he' : infDist (ratPoint p) (CellConfig.mapCell f.symm L : Set Plane) < r := by
      rcases hgood p hp _ hKρ.1 ⟨f.symm y, hxK, hxp⟩ with h | h
      · linarith
      · linarith
    obtain ⟨z, hzK, hz⟩ := (infDist_lt_iff (CellConfig.mapCell f.symm L).nonempty).1 he'
    exact ⟨hKρ.1, z, hzK, (hmemW z).2 ⟨p, hp, by rw [dist_comm]; exact hz⟩⟩
  -- (C) the restriction of `H''` is the image of that of `H`
  have hinj : Function.Injective (CellConfig.mapCell f) :=
    Function.LeftInverse.injective (CellConfig.mapCell_symm_mapCell f)
  have himage : H''.restrict (window q r) = CellConfig.mapCell f '' H.restrict (window q r) := by
    ext L
    constructor
    · intro hL
      exact ⟨_, hB L hL, CellConfig.mapCell_mapCell_symm f L⟩
    · rintro ⟨K, hK, rfl⟩
      exact hA K hK
  have henc : (H''.restrict (window q r)).encard = (H.restrict (window q r)).encard := by
    rw [himage, Set.InjOn.encard_image fun a _ b _ h => hinj h]
  -- (D) the matching
  have hmatch : MatchesWhole (CellConfigOps.restrictConfig H (window q r))
      (CellConfigOps.restrictConfig H'' (window q r)) f := by
    refine ⟨fun K hK => hA K hK, fun L hL => hB L hL, fun K hK K' hK' => ?_⟩
    rw [restrictConfig_adj_iff hK hK', restrictConfig_adj_iff (hA K hK) (hA K' hK')]
    constructor
    · exact hf.2.2.1 K (hρ K hK) K' (hρ K' hK')
    · intro h
      have := hf.2.2.2 _ (hf.1 K (hρ K hK)) _ (hf.1 K' (hρ K' hK')) h
      rwa [CellConfig.mapCell_symm_mapCell, CellConfig.mapCell_symm_mapCell] at this
  have hwd : wholeDistortion (CellConfigOps.restrictConfig H (window q r))
      (CellConfigOps.restrictConfig H'' (window q r)) f ≤ CellConfig.distortion H H'' ρ f := by
    unfold wholeDistortion CellConfig.distortion
    refine add_le_add (iSup_mono fun z => (edist_comm (f z) z).le) ?_
    refine iSup₂_le fun K hK => iSup₂_le fun K' hK' => iSup_le fun hadj => ?_
    refine le_iSup₂_of_le K (hρ K hK) (le_iSup₂_of_le K' (hρ K' hK')
      (le_iSup_of_le ((restrictConfig_adj_iff hK hK').1 hadj) (le_of_eq ?_)))
    rw [CoordsMeasurable.restrictConfig_c_of_mem hK hK',
      CoordsMeasurable.restrictConfig_c_of_mem (hA K hK) (hA K' hK')]
  -- (E) the capped restrictions
  unfold CellConfigOps.capped
  by_cases hn : (H.restrict (window q r)).encard ≤ n
  · have hn'' : (H''.restrict (window q r)).encard ≤ n := by rw [henc]; exact hn
    rw [if_pos hn, if_pos hn'']
    exact (min_le_right _ _).trans ((iInf₂_le f hmatch).trans (hwd.trans hfd.le))
  · have hn'' : ¬ (H''.restrict (window q r)).encard ≤ n := by rw [henc]; exact hn
    rw [if_neg hn, if_neg hn'']
    exact zero_le

/-- **The `(j,N)` term of `d_sing` is small when `d^CC` is small**, near a configuration with
finite restrictions to all balls. -/
theorem exists_dCC_lt_imp_lintegral_integrand_le {H : CellConfig}
    (hfin : ∀ R : ℝ, (H.restrict (ball (0 : Plane) R)).Finite) (j N : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∃ ε₀ : ℝ≥0∞, 0 < ε₀ ∧ ∀ H'' : CellConfig, CellConfig.dCC H H'' < ε₀ →
      ∫⁻ r in Ioi (0 : ℝ), CoordsMeasurable.integrand H H'' j N r ≤ ENNReal.ofReal (3 * τ) := by
  -- the centres of the test window
  obtain ⟨Q, hQ⟩ := ((List.finite_toSet (ratTuple j).1).image fun p => ‖ratPoint p‖).bddAbove
  have hQp : ∀ p ∈ (ratTuple j).1, ‖ratPoint p‖ ≤ Q := fun p hp => hQ ⟨p, hp, rfl⟩
  -- the radius cutoff
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = |Real.log τ| + 1 := ⟨_, rfl⟩
  have hR₀ : 0 < R₀ := by rw [hR₀def]; positivity
  have hexpR₀ : Real.exp (-R₀) ≤ τ := by
    calc Real.exp (-R₀) ≤ Real.exp (Real.log τ) :=
          Real.exp_le_exp.2 (by rw [hR₀def]; linarith [neg_abs_le (Real.log τ)])
      _ = τ := Real.exp_log hτ
  have hR' : 0 < |Q| + R₀ + 2 := by positivity
  -- the finitely many exceptional radii
  have hC : (H.restrict (ball (0 : Plane) (|Q| + R₀ + 2))).Finite := hfin _
  obtain ⟨E, hEdef⟩ : ∃ E : Set ℝ, E = ⋃ p ∈ {p | p ∈ (ratTuple j).1},
      (fun K : Cell => infDist (ratPoint p) (K : Set Plane)) ''
        H.restrict (ball (0 : Plane) (|Q| + R₀ + 2)) := ⟨_, rfl⟩
  have hE : E.Finite := by
    rw [hEdef]
    exact (List.finite_toSet _).biUnion fun p _ => hC.image _
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = hE.toFinset.card := ⟨_, rfl⟩
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = τ / (2 * ((M : ℝ) + 1)) := ⟨_, rfl⟩
  have hγ : 0 < γ := by rw [hγdef]; positivity
  have hγM : 2 * γ * ((M : ℝ) + 1) = τ := by
    rw [hγdef, mul_div_assoc', div_mul_eq_mul_div, div_eq_iff (by positivity)]
    ring
  have hMγ : (M : ℝ) * (2 * γ) ≤ τ := by nlinarith
  obtain ⟨bad, hbaddef⟩ : ∃ bad : Set ℝ, bad = ⋃ e ∈ E, Ioo (e - γ) (e + γ) := ⟨_, rfl⟩
  have hbad : MeasurableSet bad := by
    rw [hbaddef]
    exact MeasurableSet.biUnion hE.countable fun _ _ => measurableSet_Ioo
  have hvolbad : volume bad ≤ ENNReal.ofReal τ := by
    have hbad' : bad = ⋃ e ∈ hE.toFinset, Ioo (e - γ) (e + γ) := by
      rw [hbaddef]
      simp only [Set.Finite.mem_toFinset]
    calc volume bad = volume (⋃ e ∈ hE.toFinset, Ioo (e - γ) (e + γ)) := by rw [hbad']
      _ ≤ ∑ e ∈ hE.toFinset, volume (Ioo (e - γ) (e + γ)) := measure_biUnion_finset_le _ _
      _ = ∑ e ∈ hE.toFinset, ENNReal.ofReal (2 * γ) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Real.volume_Ioo]
          congr 1
          ring
      _ = ENNReal.ofReal ((M : ℝ) * (2 * γ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hMdef, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal τ := ENNReal.ofReal_le_ofReal hMγ
  -- the matching error
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (γ / 2) (min τ (1 / 2)) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact lt_min (half_pos hγ) (lt_min hτ (by norm_num))
  have hηγ : η < γ := by rw [hηdef]; exact (min_le_left _ _).trans_lt (half_lt_self hγ)
  have hητ : η ≤ τ := by rw [hηdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hηh : η ≤ 1 / 2 := by rw [hηdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ε₀, hε₀, hext⟩ := CellConfig.exists_admissible_of_dCC_lt hR' hη
  refine ⟨ε₀, hε₀, fun H'' hH'' => ?_⟩
  obtain ⟨ρ, hρR', f, hf, hfd⟩ := hext H H'' hH''
  have hnorm : ∀ r ≤ R₀, ∀ p ∈ (ratTuple j).1, ∀ x : Plane,
      dist x (ratPoint p) < r + η → ‖x‖ < |Q| + R₀ + 2 := by
    intro r hr p hp x hx
    have h3 : ‖x‖ ≤ dist x (ratPoint p) + ‖ratPoint p‖ := by
      simpa [dist_zero_right] using dist_triangle x (ratPoint p) 0
    linarith [hQp p hp, le_abs_self Q]
  -- the pointwise bound
  have hpt : ∀ r ∈ Ioi (0 : ℝ), CoordsMeasurable.integrand H H'' j N r ≤
      (ENNReal.ofReal τ * ENNReal.ofReal (Real.exp (-r)) + bad.indicator 1 r) +
        (Ioi R₀).indicator (fun r => ENNReal.ofReal (Real.exp (-r))) r := by
    intro r hr
    by_cases h1 : R₀ < r
    · calc _ ≤ ENNReal.ofReal (Real.exp (-r)) := integrand_le_exp H H'' j N r
        _ = (Ioi R₀).indicator (fun r => ENNReal.ofReal (Real.exp (-r))) r :=
            (indicator_of_mem (show r ∈ Ioi R₀ from h1)
              (fun r => ENNReal.ofReal (Real.exp (-r)))).symm
        _ ≤ _ := le_add_self
    by_cases h2 : r ∈ bad
    · calc _ ≤ ENNReal.ofReal (Real.exp (-r)) := integrand_le_exp H H'' j N r
        _ ≤ 1 := ofReal_exp_neg_le_one (le_of_lt hr)
        _ = bad.indicator 1 r := (indicator_of_mem h2 (1 : ℝ → ℝ≥0∞)).symm
        _ ≤ _ := le_add_self.trans le_self_add
    replace h1 : r ≤ R₀ := not_lt.1 h1
    have hwinρ : ∀ p ∈ (ratTuple j).1, ∀ x : Plane,
        dist x (ratPoint p) < r + η → x ∈ ball (0 : Plane) ρ := by
      intro p hp x hx
      rw [mem_ball_zero_iff]
      linarith [hnorm r h1 p hp x hx]
    have hgood : ∀ p ∈ (ratTuple j).1, ∀ K ∈ H.cells,
        (∃ x ∈ (K : Set Plane), dist x (ratPoint p) < r + η) →
          r ≤ infDist (ratPoint p) (K : Set Plane) - γ ∨
            infDist (ratPoint p) (K : Set Plane) + γ ≤ r := by
      rintro p hp K hK ⟨x, hxK, hx⟩
      have hKC : K ∈ H.restrict (ball (0 : Plane) (|Q| + R₀ + 2)) :=
        ⟨hK, x, hxK, mem_ball_zero_iff.2 (hnorm r h1 p hp x hx)⟩
      have heE : infDist (ratPoint p) (K : Set Plane) ∈ E := by
        rw [hEdef]
        exact mem_iUnion₂.2 ⟨p, hp, K, hKC, rfl⟩
      have hnot : r ∉ Ioo (infDist (ratPoint p) (K : Set Plane) - γ)
          (infDist (ratPoint p) (K : Set Plane) + γ) := fun hr' =>
        h2 (by rw [hbaddef]; exact mem_iUnion₂.2 ⟨_, heE, hr'⟩)
      rw [mem_Ioo, not_and_or, not_lt, not_lt] at hnot
      exact hnot
    have hδ := restrictionDist_le_of_admissible hf hfd hηγ (ratTuple j) (N + 1) hwinρ hgood
    calc CoordsMeasurable.integrand H H'' j N r
        = ENNReal.ofReal (Real.exp (-r)) *
            restrictionDist (CellConfigOps.capped H (N + 1) (window (ratTuple j) r))
              (CellConfigOps.capped H'' (N + 1) (window (ratTuple j) r)) := rfl
      _ ≤ ENNReal.ofReal (Real.exp (-r)) * ENNReal.ofReal τ :=
          mul_le_mul' le_rfl (hδ.trans (ENNReal.ofReal_le_ofReal hητ))
      _ = ENNReal.ofReal τ * ENNReal.ofReal (Real.exp (-r)) := mul_comm _ _
      _ ≤ _ := le_self_add.trans le_self_add
  -- integrate the bound
  have hme : Measurable fun r : ℝ => ENNReal.ofReal (Real.exp (-r)) :=
    (Real.measurable_exp.comp measurable_neg).ennreal_ofReal
  have hm1 : Measurable fun r : ℝ => ENNReal.ofReal τ * ENNReal.ofReal (Real.exp (-r)) :=
    measurable_const.mul hme
  have hm2 : Measurable fun r : ℝ => bad.indicator (1 : ℝ → ℝ≥0∞) r :=
    measurable_one.indicator hbad
  have hm12 : Measurable fun r : ℝ =>
      ENNReal.ofReal τ * ENNReal.ofReal (Real.exp (-r)) + bad.indicator (1 : ℝ → ℝ≥0∞) r :=
    hm1.add hm2
  calc ∫⁻ r in Ioi (0 : ℝ), CoordsMeasurable.integrand H H'' j N r
      ≤ ∫⁻ r in Ioi (0 : ℝ), ((ENNReal.ofReal τ * ENNReal.ofReal (Real.exp (-r)) +
          bad.indicator 1 r) +
          (Ioi R₀).indicator (fun r => ENNReal.ofReal (Real.exp (-r))) r) :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpt))
    _ = (ENNReal.ofReal τ * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-r))) +
          (∫⁻ r in Ioi (0 : ℝ), bad.indicator 1 r) +
          ∫⁻ r in Ioi (0 : ℝ),
            (Ioi R₀).indicator (fun r => ENNReal.ofReal (Real.exp (-r))) r := by
        rw [lintegral_add_left hm12, lintegral_add_left hm1,
          lintegral_const_mul _ hme]
    _ ≤ ENNReal.ofReal τ + ENNReal.ofReal τ + ENNReal.ofReal τ := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · refine le_of_eq ?_
          rw [lintegral_exp_neg_Ioi, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]
        · calc (∫⁻ r in Ioi (0 : ℝ), bad.indicator 1 r) ≤ ∫⁻ r, bad.indicator 1 r :=
                setLIntegral_le_lintegral _ _
            _ = volume bad := lintegral_indicator_one hbad
            _ ≤ _ := hvolbad
        · calc (∫⁻ r in Ioi (0 : ℝ),
                (Ioi R₀).indicator (fun r => ENNReal.ofReal (Real.exp (-r))) r)
              ≤ ∫⁻ r, (Ioi R₀).indicator
                  (fun r => ENNReal.ofReal (Real.exp (-r))) r :=
                setLIntegral_le_lintegral _ _
            _ = ∫⁻ r in Ioi R₀, ENNReal.ofReal (Real.exp (-r)) :=
                lintegral_indicator measurableSet_Ioi _
            _ = ENNReal.ofReal (Real.exp (-R₀)) := lintegral_exp_neg_Ioi _
            _ ≤ _ := ENNReal.ofReal_le_ofReal hexpR₀
    _ = ENNReal.ofReal (3 * τ) := by
        rw [← ENNReal.ofReal_add hτ.le hτ.le, ← ENNReal.ofReal_add (add_pos hτ hτ).le hτ.le]
        congr 1
        ring

/-- The weights of `d_sing`, indexed by `(j,N)`. -/
noncomputable def weight (p : ℕ × ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ ((p.1 + 1) + (p.2 + 1))

/-- The `(j,N)` integral of `d_sing`. -/
noncomputable def termIntegral (H H' : CellConfig) (p : ℕ × ℕ) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ), CoordsMeasurable.integrand H H' p.1 p.2 r

theorem dSing_eq_tsum (H H' : CellConfig) :
    dSing H H' = ∑' p : ℕ × ℕ, weight p * termIntegral H H' p :=
  (ENNReal.tsum_prod' (f := fun p : ℕ × ℕ => weight p * termIntegral H H' p)).symm

theorem tsum_weight : ∑' p : ℕ × ℕ, weight p = 1 := by
  have h1 : ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + 1) = 1 := by
    rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
  have hw : ∀ p : ℕ × ℕ, weight p = (2 : ℝ≥0∞)⁻¹ ^ (p.1 + 1) * (2 : ℝ≥0∞)⁻¹ ^ (p.2 + 1) :=
    fun p => pow_add _ _ _
  rw [ENNReal.tsum_prod']
  simp only [hw, ENNReal.tsum_mul_left, h1, mul_one]

theorem weight_ne_top (p : ℕ × ℕ) : weight p ≠ ∞ :=
  ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero)

/-- Each term of `d_sing` tends to zero as `d^CC(H,·)` does. -/
theorem tendsto_termIntegral {H : CellConfig}
    (hfin : ∀ R : ℝ, (H.restrict (ball (0 : Plane) R)).Finite) (p : ℕ × ℕ) :
    Tendsto (fun H'' => termIntegral H H'' p)
      (Filter.comap (fun H'' => CellConfig.dCC H H'') (𝓝 0)) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨t, -, ht0, htε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have ht : 0 < t := ENNReal.ofReal_pos.1 ht0
  obtain ⟨ε₀, hε₀, hspec⟩ :=
    exists_dCC_lt_imp_lintegral_integrand_le hfin p.1 p.2 (div_pos ht three_pos)
  refine Filter.mem_comap.2 ⟨Iio ε₀, Iio_mem_nhds hε₀, fun H'' hH'' => ?_⟩
  refine (hspec H'' hH'').trans ?_
  rw [show 3 * (t / 3) = t by ring]
  exact htε.le

/-- **`d^CC` small forces `d_sing` small** near a configuration with finite restrictions to all
balls. -/
theorem exists_dCC_lt_imp_dSing_lt {H : CellConfig}
    (hfin : ∀ R : ℝ, (H.restrict (ball (0 : Plane) R)).Finite) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ H'' : CellConfig, CellConfig.dCC H H'' < δ → dSing H H'' < ε := by
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- the tail of the weights
  have hsum : ∑' p : ℕ × ℕ, weight p ≠ ∞ := by rw [tsum_weight]; exact ENNReal.one_ne_top
  obtain ⟨T, hT⟩ := ((ENNReal.tendsto_tsum_compl_atTop_zero hsum).eventually
    (gt_mem_nhds hε2)).exists
  -- the finitely many leading terms
  have hS : Tendsto (fun H'' => ∑ p ∈ T, weight p * termIntegral H H'' p)
      (Filter.comap (fun H'' => CellConfig.dCC H H'') (𝓝 0)) (𝓝 0) := by
    have h := tendsto_finset_sum T fun p _ =>
      ENNReal.Tendsto.const_mul (tendsto_termIntegral hfin p) (Or.inr (weight_ne_top p))
    have h0 : ∑ p ∈ T, weight p * (0 : ℝ≥0∞) = 0 := by simp
    rwa [h0] at h
  obtain ⟨t, ht, hsub⟩ := Filter.mem_comap.1 (hS.eventually (gt_mem_nhds hε2))
  obtain ⟨δ, hδ, hδt⟩ := ENNReal.nhds_zero_basis.mem_iff.1 ht
  refine ⟨δ, hδ, fun H'' hH'' => ?_⟩
  have hSH : ∑ p ∈ T, weight p * termIntegral H H'' p < ε / 2 := hsub (hδt hH'')
  have htail : ∑' p : ↥(T : Set (ℕ × ℕ))ᶜ, weight p < ε / 2 := hT
  calc dSing H H'' = ∑' p : ℕ × ℕ, weight p * termIntegral H H'' p := dSing_eq_tsum H H''
    _ = ∑ p ∈ T, weight p * termIntegral H H'' p +
          ∑' p : ↥(T : Set (ℕ × ℕ))ᶜ, weight p * termIntegral H H'' p :=
        (ENNReal.sum_add_tsum_compl T _).symm
    _ ≤ ∑ p ∈ T, weight p * termIntegral H H'' p + ∑' p : ↥(T : Set (ℕ × ℕ))ᶜ, weight p :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum fun p =>
          mul_le_of_le_one_right' (lintegral_integrand_le_one _ _ _ _))
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hSH htail
    _ = ε := ENNReal.add_halves ε

end GMSTopology

end ReflectedGMS.GeomTop

assert_no_sorry ReflectedGMS.GeomTop.GMSTopology.exists_dSing_lt_imp_dCC_lt
assert_no_sorry ReflectedGMS.GeomTop.GMSTopology.exists_dCC_lt_imp_dSing_lt
#print axioms ReflectedGMS.GeomTop.GMSTopology.exists_dSing_lt_imp_dCC_lt
#print axioms ReflectedGMS.GeomTop.GMSTopology.exists_dCC_lt_imp_dSing_lt
