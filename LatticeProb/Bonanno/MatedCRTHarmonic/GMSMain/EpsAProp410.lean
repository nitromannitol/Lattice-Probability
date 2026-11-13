/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsAProp410 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsACase0

/-!
# [18] Proposition 4.10 at every real mesh `ε ∈ (0, 1)`, every radius `ρ ∈ (0, 1)` and every `C > 1`

Source: [18] Proposition 2.10 and Proposition 4.10,
"for `ε ∈ (0, 1)`". The preceding results establish Proposition 4.10 for the bundle's γ-cone curve at the dyadic meshes and
`(ρ, C) = (3/4, 100)`; the last step applies at every `ρ`. The recentring step ([18] (4.43)–(4.44), Cases 0–2:
`BundleSec4.cone_le_case2M`, `BundleSec4.case2_smallRoot_failSet_leM`, `GMS4FO.zeroCone_failSet_le`,
`GMS4FO.le_cond_sum_of_forall_slice`, `GMS4FO.globalGood_of_three`) takes any mesh `ε > 0`; the dyadic mesh entered
only through the zero-cone Case 0 input (real-mesh form in `GMSMain.EpsACase0`) and through the "small meshes"
threshold `GMS4FO.eventually_mesh_rpow_le` (here: a threshold `ε₀ > 0`, with probability `≤ 1 ≤ Cfail ε^α` above it).
The test constant `C > 1` enters only the area bound of `B_κ(∂D)`, the tolerance
constant `K = 3C + (4C + C²)A₀` and the failure rate.

* `epsA_prop410Bad_le` — one real mesh (G4FO's (4.43)–(4.44) and Cases 0–2), ambient radius `ρ`, test constant `Cb`;
* `epsA_prop410_explicit` — explicit exponents `β = α = α₀/(16 p′)` (independent of `ρ` and `Cb` given `α₀`);
* **`EpsAProp410At P η ρ C`** — `BundleSec4.Prop410At` with `∀ ε ∈ (0, 1)` in place of `∀ k`;
* **`epsA_prop410At`** — `EpsAProp410At P η ρ C` for the γ-cone curve `η` of every frozen coupling, every
  `ρ ∈ (0, 1)`, every `C > 1` (no premise);
* `epsA_bundle_prop410At` — the dyadic `BundleSec4.Prop410At P η ρ C` for every `C > 1`;
* **`epsA_t13_prop210At`** — `BundleSec4.Prop210At` (Proposition 2.10 on MTC's dyadic family, T13I's
  `GMSMain.t13_prop210At` form) at every `(ρ, C)`, `C > 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4FO

/-! ### Elementary geometry at radius `ρ` (geometry for the ambient radius) -/

/-- The three test domains of (4.44) lie in `B_{ρ+g}(0)` when `Dm ⊂ B_ρ(0)` and `κ ≤ g`. -/
theorem epsA_pairDom_subset {Dm : Set ℂ} {ρ g κ : ℝ} (hDsub : Dm ⊆ ball (0 : ℂ) ρ) (hg : 0 < g) (hκ : κ ≤ g)
    (j : Fin 3) : pairDom Dm κ j ⊆ ball (0 : ℂ) (ρ + g) := by
  have h1 : Dm ⊆ ball (0 : ℂ) (ρ + g) := hDsub.trans (ball_subset_ball (by linarith))
  fin_cases j
  · exact h1
  · exact h1
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx
    have hycl : y ∈ closedBall (0 : ℂ) ρ :=
      (closure_mono hDsub |>.trans closure_ball_subset_closedBall) (frontier_subset_closure hy)
    rw [mem_closedBall, dist_zero_right] at hycl
    rw [mem_ball, dist_zero_right]
    calc ‖x‖ ≤ ‖x - y‖ + ‖y‖ := norm_le_norm_sub_add x y
      _ < κ + ρ := by rw [← dist_eq_norm]; linarith
      _ ≤ ρ + g := by linarith

/-- A subset of the unit disk has area at most `4`. -/
theorem epsA_volume_le_four {Dm : Set ℂ} {ρ : ℝ} (hDsub : Dm ⊆ ball (0 : ℂ) ρ) (hρ1 : ρ ≤ 1) :
    volume Dm ≤ ENNReal.ofReal 4 := by
  refine (measure_mono (hDsub.trans (ball_subset_ball hρ1))).trans ?_
  rw [Complex.volume_ball, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := Real.pi_lt_d2
  nlinarith

theorem epsA_closedBall_subset_of_mem {z : ℂ} {ρ g : ℝ} (hz : z ∈ ball (0 : ℂ) (ρ + g)) {r : ℝ}
    (hr : 4 * r ≤ g) : closedBall z (4 * r) ⊆ ball (0 : ℂ) (ρ + 2 * g) := by
  intro w hw
  rw [mem_closedBall] at hw
  rw [mem_ball, dist_zero_right] at hz ⊢
  calc ‖w‖ ≤ ‖w - z‖ + ‖z‖ := norm_le_norm_sub_add w z
    _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
    _ < ρ + 2 * g := by linarith

/-- The tolerance of (4.44) with the area bound `4` (any domain in the unit disk) and test constant `Cb`. -/
def epsATolTotal (Cb ε α₀ β ξ A₀ : ℝ) : ℝ :=
  ε ^ α₀ * (Cb * ε ^ (-β)) + Cb * ε ^ (-β) * ε ^ ξ * (A₀ * 4 + ε ^ α₀ * 1) +
    Cb * ε ^ (-β) * (A₀ * (Cb * ε ^ ξ) + ε ^ α₀ * 1)

/-- The tolerance of (4.44) is `O(ε^{3ξ/4})` when `β = ξ/4 ≤ α₀/4`. -/
theorem epsATolTotal_le {Cb ε α₀ ξ A₀ : ℝ} (hCb : 0 ≤ Cb) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξα : ξ ≤ α₀) :
    epsATolTotal Cb ε α₀ (ξ / 4) ξ A₀ ≤ (3 * Cb + (4 * Cb + Cb ^ 2) * A₀) * ε ^ (3 * ξ / 4) := by
  have hea : ε ^ (-(ξ / 4)) * ε ^ ξ = ε ^ (3 * ξ / 4) := by
    rw [← Real.rpow_add hε0]; congr 1; ring
  have hαe : ε ^ α₀ * ε ^ (-(ξ / 4)) ≤ ε ^ (3 * ξ / 4) := by
    rw [← Real.rpow_add hε0]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by linarith)
  have hα1 : ε ^ α₀ ≤ 1 := Real.rpow_le_one hε0.le hε1 (by linarith [hξα, hξ0])
  have hα0 : 0 ≤ ε ^ α₀ := (Real.rpow_pos_of_pos hε0 _).le
  have ha0 : 0 ≤ ε ^ (3 * ξ / 4) := (Real.rpow_pos_of_pos hε0 _).le
  have key : epsATolTotal Cb ε α₀ (ξ / 4) ξ A₀ = Cb * (ε ^ α₀ * ε ^ (-(ξ / 4))) +
      Cb * (ε ^ (-(ξ / 4)) * ε ^ ξ) * (A₀ * 4 + ε ^ α₀) +
      Cb ^ 2 * A₀ * (ε ^ (-(ξ / 4)) * ε ^ ξ) + Cb * (ε ^ α₀ * ε ^ (-(ξ / 4))) := by
    unfold epsATolTotal; ring
  rw [key, hea]
  have h1 : Cb * (ε ^ α₀ * ε ^ (-(ξ / 4))) ≤ Cb * ε ^ (3 * ξ / 4) := mul_le_mul_of_nonneg_left hαe hCb
  have h2 : Cb * ε ^ (3 * ξ / 4) * (A₀ * 4 + ε ^ α₀) ≤ Cb * ε ^ (3 * ξ / 4) * (A₀ * 4 + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hCb ha0)
  nlinarith

/-- **Failure of the source estimate forces failure of one recentred good event** ([18] (4.43)–(4.44)), with the
area bound `4`. -/
theorem epsA_exists_fail_of_target {c : C(ℝ, ℂ)} {ε : ℝ} (hε : 0 ≤ ε) {Dm : Set ℂ} (hDo : IsOpen Dm)
    {f : ℂ → ℝ} {M κ A₀ α₀ tol r Cb : ℝ} {R : Set ℂ} (hM : 0 ≤ M) (hκ : 0 ≤ κ) (hA₀ : 0 ≤ A₀)
    (hCb : 0 ≤ Cb)
    (hfM : ∀ z ∈ Dm, f z ≤ M) (hlip : ∀ z ∈ Dm, ∀ w ∈ Dm, |f z - f w| ≤ M * dist z w)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < κ) (hVD : volume Dm ≤ ENNReal.ofReal 4)
    (hVT : volume (thickening κ (frontier Dm)) ≤ ENNReal.ofReal (Cb * κ)) (hα₀ε : 0 ≤ ε ^ α₀)
    (htol : ε ^ α₀ * M + M * κ * (A₀ * 4 + ε ^ α₀ * 1) + M * (A₀ * (Cb * κ) + ε ^ α₀ * 1) ≤ tol)
    (hbad : ¬ ((∫⁻ z in Dm, ENNReal.ofReal (f z) * GMS4b.uStar ε c z) ≤
      ENNReal.ofReal A₀ * (∫⁻ z in Dm, ENNReal.ofReal (f z)) + ENNReal.ofReal tol)) :
    ∃ j : Fin 3, ¬ GlobalGood c ε ((fun z => z - z₀) '' pairDom Dm κ j)
      (fun u => pairFun f j (u + z₀)) A₀ (ε ^ α₀ * pairBd M j) ((fun z => z - z₀) '' R) r := by
  by_contra hall
  push Not at hall
  have hU : AEMeasurable (fun u => GMS4b.uStar ε c u) volume := by
    have h := GMS4b.measurable_uStar hε
    have e : Measurable ((fun p : C(ℝ, ℂ) × ℂ => GMS4b.uStar ε p.1 p.2) ∘ fun u => (c, u)) :=
      h.comp (measurable_const.prodMk measurable_id)
    exact e.aemeasurable
  have hgood := globalGood_of_three (η := c) (R := (∅ : Set ℂ)) hDo hM hκ hM hA₀ (by norm_num)
    (by positivity) (mul_nonneg hα₀ε hM) (by simpa using hα₀ε) (by simpa using hα₀ε) hfM hlip hz₀ hU hVD hVT
    htol (empty_subset _) (hall 0) (hall 1) (hall 2)
  exact hbad hgood.2

/-- Small real meshes: for `x > 0` and `c > 0` there is `ε₀ ∈ (0, 1]` with `ε^x ≤ c` on `(0, ε₀)`. -/
theorem epsA_exists_rpow_le {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε ^ x ≤ c := by
  refine ⟨min 1 (c ^ (1 / x)), lt_min one_pos (Real.rpow_pos_of_pos hc _), min_le_left _ _,
    fun ε hε0 hε => ?_⟩
  have hε' : ε < c ^ (1 / x) := hε.trans_le (min_le_right _ _)
  calc ε ^ x ≤ (c ^ (1 / x)) ^ x := Real.rpow_le_rpow hε0.le hε'.le hx.le
    _ = c := by rw [← Real.rpow_mul hc.le, one_div_mul_cancel hx.ne', Real.rpow_one]

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] Proposition 4.10 at one real mesh `ε`, ambient radius `ρ ∈ (0, 1)`, test constant `Cb`** (`prop410Bad_le_at_meshM` with `3/4, 13/16, 7/8, 15/16` replaced by `ρ, ρ + g, ρ + 2g, ρ + 3g`, `g = (1 − ρ)/8`,
and the dyadic mesh replaced by `ε`). -/
theorem epsA_prop410Bad_le (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)] (hL : BundleSec4.Lemma43MeasurableM D)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {q α₀ A₀ C₀ Cb : ℝ} (hA₀ : 0 ≤ A₀) (hC₀ : 0 ≤ C₀)
    (h0 : ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 → ∀ (Dm : Set ℂ) (g : ℂ → ℝ) (M : ℝ), IsOpen Dm →
      Dm ⊆ ball (0 : ℂ) (ρ + (1 - ρ) / 8) → ContinuousOn g Dm → (∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M) →
        P {ω | ¬ GlobalGood (η₀ ω) ε Dm g A₀ (ε ^ α₀ * M)
          (ball (0 : ℂ) (ρ + (1 - ρ) / 8)) (ε ^ q)} ≤ ENNReal.ofReal (C₀ * ε ^ α₀))
    {p q' : ℝ} (hpq : p.HolderConjugate q') {ε : ℝ} {β α : ℝ} {Dm : Set ℂ}
    {f : ℂ → ℝ} (hadm : GMS4.Prop210Admissible ε ρ Cb β Dm f)
    (hκs : ε ^ (α₀ / (4 * q')) ≤ (1 - ρ) / 8) (hrs : 4 * ε ^ q ≤ (1 - ρ) / 8)
    (htol : epsATolTotal Cb ε α₀ β (α₀ / (4 * q')) A₀ ≤ ε ^ α) :
    P (BundleSec4.Prop410Bad η ε Dm f A₀ (ε ^ α)) ≤
      3 * (GMSCase1.case1Moment D hγ p ^ (1 / p) *
        ENNReal.ofReal (C₀ ^ (1 / q') * ε ^ (α₀ / (2 * q')))) := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨hε0, hε1, -, -, hCb1, -, hDo, -, hDsub, hthick, hfb, hlip⟩ := hadm
  have hCb : 0 ≤ Cb := by linarith
  set g : ℝ := (1 - ρ) / 8 with hgdef
  have hg : 0 < g := by rw [hgdef]; linarith
  have hq'0 : 0 < q' := hpq.symm.pos
  have hκ0 : 0 < ε ^ (α₀ / (4 * q')) := Real.rpow_pos_of_pos hε0 _
  have hκ1 : ε ^ (α₀ / (4 * q')) ≤ 1 := hκs.trans (by rw [hgdef]; linarith)
  have hr0 : 0 ≤ ε ^ q := (Real.rpow_pos_of_pos hε0 _).le
  have hM0 : 0 ≤ Cb * ε ^ (-β) := by positivity
  have hα₀ε : 0 ≤ ε ^ α₀ := (Real.rpow_pos_of_pos hε0 _).le
  have hRV : ∀ z ∈ ball (0 : ℂ) (ρ + g), closedBall z (4 * ε ^ q) ⊆ ball (0 : ℂ) (ρ + 2 * g) :=
    fun z hz => epsA_closedBall_subset_of_mem hz hrs
  have hfM : ∀ z ∈ Dm, f z ≤ Cb * ε ^ (-β) := fun z hz => (hfb z hz).2
  have hfc : ContinuousOn f Dm := continuousOn_of_lipschitz hM0 hlip
  have hVT : volume (thickening (ε ^ (α₀ / (4 * q'))) (frontier Dm)) ≤
      ENNReal.ofReal (Cb * ε ^ (α₀ / (4 * q'))) :=
    hthick _ ⟨hκ0, lt_of_le_of_lt hκs (by rw [hgdef]; linarith)⟩
  have hV1 : (ballO (0 : ℂ) (ρ + 2 * g) : Set ℂ) ⊆ ball (0 : ℂ) 1 :=
    ball_subset_ball (by rw [hgdef]; linarith)
  -- admissibility of the three pairs
  have htolj : ∀ j : Fin 3, 0 ≤ ε ^ α₀ * pairBd (Cb * ε ^ (-β)) j :=
    fun j => mul_nonneg hα₀ε (BundleSec4.bundle_pairBd_nonneg hM0 j)
  have hgbj : ∀ j : Fin 3, ∃ M : ℝ, ∀ z ∈ pairDom Dm (ε ^ (α₀ / (4 * q'))) j,
      0 ≤ pairFun f j z ∧ pairFun f j z ≤ M :=
    fun j => ⟨_, pairFun_bounds hfb _ j⟩
  -- the three local failure events on `Ω × ℂ`
  let S : Fin 3 → Set (Ω × ℂ) := fun j => {v | (restrictTo (ballO (0 : ℂ) (ρ + 2 * g))
    (GMSCase1.wpField X₀ v.1 + CellScaling.ofFunC (fun w => -γ * Real.log ‖w - v.2‖)), ηL v.1) ∈
      failSet γ (ballO (0 : ℂ) (ρ + 2 * g)) ε
        (pairDom Dm (ε ^ (α₀ / (4 * q'))) j)
        (pairFun f j) A₀ (ε ^ α₀ * pairBd (Cb * ε ^ (-β)) j)
        (ball (0 : ℂ) (ρ + g)) (ε ^ q)}
  -- step A: one root
  have hA : ∀ z₀ ∈ ball (0 : ℂ) (ε ^ (α₀ / (4 * q'))),
      P (BundleSec4.Prop410Bad η ε Dm f A₀ (ε ^ α)) ≤ ∑ j, P ((fun ω => (ω, z₀)) ⁻¹' S j) := by
    intro z₀ hz₀
    have hz₀' : ‖z₀‖ < ε ^ (α₀ / (4 * q')) := by rwa [mem_ball, dist_zero_right] at hz₀
    have hsub : BundleSec4.Prop410Bad η ε Dm f A₀ (ε ^ α) ⊆
        ⋃ j : Fin 3, {ω | ¬ GlobalGood (η ω) ε
          ((fun z => z - z₀) '' pairDom Dm (ε ^ (α₀ / (4 * q'))) j)
          (fun u => pairFun f j (u + z₀)) A₀ (ε ^ α₀ * pairBd (Cb * ε ^ (-β)) j)
          ((fun z => z - z₀) '' ball (0 : ℂ) (ρ + g)) (ε ^ q)} := by
      intro ω hω
      obtain ⟨j, hj⟩ := epsA_exists_fail_of_target (c := η ω) (R := ball (0 : ℂ) (ρ + g))
        (r := ε ^ q) hε0.le hDo hM0 hκ0.le hA₀ hCb hfM hlip hz₀'
        (epsA_volume_le_four hDsub hρ1.le) hVT hα₀ε
        (htol.trans' (le_of_eq (by unfold epsATolTotal; ring))) hω
      exact mem_iUnion.2 ⟨j, hj⟩
    refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    have hnz : ‖z₀‖ + (ρ + 3 * g) ≤ 1 := by rw [hgdef] at hκs ⊢; linarith
    have hr01 : ρ + 2 * g + ‖z₀‖ ≤ ρ + 3 * g := by linarith
    exact BundleSec4.cone_le_case2M D hγ hL (r₀ := ρ + 2 * g) (by linarith) hnz hr01 hε0
      hr0 (epsA_pairDom_subset hDsub hg hκs j) hRV (isOpen_pairDom hDo _ j) (continuousOn_pairFun hfc _ j)
      (hgbj j) hA₀ (htolj j) isOpen_ball
  -- step B: average over the root
  have hB := le_cond_sum_of_forall_slice P hκ0 hκ1 S hA
  refine hB.trans ?_
  -- step C: Cases 0–2 for each pair
  have hC : ∀ j : Fin 3,
      (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω (ε ^ (α₀ / (4 * q')))]
      (S j) ≤ GMSCase1.case1Moment D hγ p ^ (1 / p) *
        ENNReal.ofReal (C₀ ^ (1 / q') * ε ^ (α₀ / (2 * q'))) := by
    intro j
    have hbad0 := (zeroCone_failSet_le D hγ (V := ballO (0 : ℂ) (ρ + 2 * g)) isBounded_ball hε0 hr0
      (epsA_pairDom_subset hDsub hg hκs j) hRV ((isOpen_pairDom hDo _ j).measurableSet)
      (g := pairFun f j) (A := A₀)
      (tol := ε ^ α₀ * pairBd (Cb * ε ^ (-β)) j)).trans
      (h0 ε ⟨hε0, hε1⟩ _ _ _ (isOpen_pairDom hDo _ j) (epsA_pairDom_subset hDsub hg hκs j)
        (continuousOn_pairFun hfc _ j) (pairFun_bounds hfb _ j))
    have h := BundleSec4.case2_smallRoot_failSet_leM D hγ hL (V₀ := ballO (0 : ℂ) (ρ + 2 * g))
      hV1 hε0 (isOpen_pairDom hDo _ j) (continuousOn_pairFun hfc _ j)
      (hgbj j) hA₀ (htolj j) isOpen_ball (epsA_pairDom_subset hDsub hg hκs j) hr0 hRV hpq hκ0.le hκ1 hbad0
    rw [mul_div_assoc, GMSCase1.case1_rate_div_eq hC₀ hε0 hq'0] at h
    exact h
  calc ∑ j, (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω (ε ^ (α₀ / (4 * q')))] (S j)
      ≤ ∑ _j : Fin 3, GMSCase1.case1Moment D hγ p ^ (1 / p) *
          ENNReal.ofReal (C₀ ^ (1 / q') * ε ^ (α₀ / (2 * q'))) :=
        Finset.sum_le_sum fun j _ => hC j
    _ = _ := by simp

/-- **[18] Proposition 4.10 at `(ρ, Cb)`, every real mesh, explicit exponents**: from the zero-cone Case 0 at
`ρ + (1 − ρ)/8` (real-mesh form) with window exponent `q`, exponent `α₀`, threshold `A₀`, and
`Lemma43MeasurableM`, for a Case 1 moment exponent `p ∈ (1, 4/γ²)`, Proposition 4.10 holds with
`β = α = α₀/(16 p′)` (`p′` the conjugate exponent) and threshold `A₀`. -/
theorem epsA_prop410_explicit (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {q α₀ A₀ C₀ : ℝ} (hq : 0 < q) (hα₀ : 0 < α₀) (hA₀ : 0 ≤ A₀) (hC₀ : 0 ≤ C₀)
    (h0 : ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 → ∀ (Dm : Set ℂ) (g : ℂ → ℝ) (M : ℝ), IsOpen Dm →
      Dm ⊆ ball (0 : ℂ) (ρ + (1 - ρ) / 8) → ContinuousOn g Dm → (∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M) →
        P {ω | ¬ GlobalGood (η₀ ω) ε Dm g A₀ (ε ^ α₀ * M)
          (ball (0 : ℂ) (ρ + (1 - ρ) / 8)) (ε ^ q)} ≤ ENNReal.ofReal (C₀ * ε ^ α₀))
    (hL : BundleSec4.Lemma43MeasurableM D) {p : ℝ} (hp1 : 1 < p) (hp4 : p < 4 / γ ^ 2) {Cb : ℝ} (hCb : 1 < Cb) :
    ∃ Cfail : ℝ, 0 ≤ Cfail ∧ ∀ (ε : ℝ) (Dm : Set ℂ) (f : ℂ → ℝ),
      GMS4.Prop210Admissible ε ρ Cb (α₀ / (4 * p.conjExponent) / 4) Dm f →
        P (BundleSec4.Prop410Bad η ε Dm f A₀ (ε ^ (α₀ / (4 * p.conjExponent) / 4))) ≤
          ENNReal.ofReal (Cfail * ε ^ (α₀ / (4 * p.conjExponent) / 4)) := by
  have : Fact (0 < 2 * Real.pi * igChi γ) := ⟨GMSCase.igPeriod_pos D⟩
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp1
  set q' := p.conjExponent with hq'def
  have hq'0 : 0 < q' := hpq.symm.pos
  have hq'1 : 1 < q' := hpq.symm.lt
  have hMfin : GMSCase1.case1Moment D hγ p ^ (1 / p) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (GMSCase1.case1Moment_lt_top D hγ (by linarith) hp4).ne
  set ξ := α₀ / (4 * q') with hξdef
  have hξ : 0 < ξ := by positivity
  have hξα : ξ ≤ α₀ := by
    rw [hξdef, div_le_iff₀ (by positivity)]
    nlinarith
  have h2ξ : α₀ / (2 * q') = 2 * ξ := by rw [hξdef]; field_simp; ring
  set K := 3 * Cb + (4 * Cb + Cb ^ 2) * A₀ with hK
  have hK0 : 0 < K := by positivity
  have hg : 0 < (1 - ρ) / 8 := by linarith
  -- small meshes: one threshold `ε₀` for the three smallness conditions
  obtain ⟨ε₁, hε₁0, -, hε₁⟩ := epsA_exists_rpow_le hξ hg
  obtain ⟨ε₂, hε₂0, -, hε₂⟩ := epsA_exists_rpow_le hq (by positivity : (0 : ℝ) < (1 - ρ) / 32)
  obtain ⟨ε₃, hε₃0, -, hε₃⟩ := epsA_exists_rpow_le (by positivity : 0 < ξ / 2) (inv_pos.2 hK0)
  set ε₀ : ℝ := min ε₁ (min ε₂ ε₃) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min hε₁0 (lt_min hε₂0 hε₃0)
  set Mreal := (GMSCase1.case1Moment D hγ p ^ (1 / p)).toReal with hMreal
  set Cfail := max (3 * Mreal * C₀ ^ (1 / q')) ((ε₀ ^ (ξ / 4))⁻¹) with hCfail
  have hCinv : 0 ≤ (ε₀ ^ (ξ / 4))⁻¹ := (inv_pos.2 (Real.rpow_pos_of_pos hε₀ _)).le
  refine ⟨Cfail, le_max_of_le_right hCinv, fun ε Dm f hadm => ?_⟩
  have hε0 : 0 < ε := hadm.1
  have hε1 : ε < 1 := hadm.2.1
  rcases lt_or_ge ε ε₀ with hε | hε
  · have hκs : ε ^ ξ ≤ (1 - ρ) / 8 := hε₁ ε hε0 (hε.trans_le (min_le_left _ _))
    have hrs : ε ^ q ≤ (1 - ρ) / 32 :=
      hε₂ ε hε0 (hε.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    have hKs : ε ^ (ξ / 2) ≤ K⁻¹ :=
      hε₃ ε hε0 (hε.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    have htol : epsATolTotal Cb ε α₀ (ξ / 4) ξ A₀ ≤ ε ^ (ξ / 4) := by
      refine (epsATolTotal_le (by linarith) hε0 hε1.le hξ.le hξα).trans ?_
      have hsplit : ε ^ (3 * ξ / 4) = ε ^ (ξ / 2) * ε ^ (ξ / 4) := by
        rw [← Real.rpow_add hε0]; congr 1; ring
      rw [hsplit, ← mul_assoc]
      have h1 : K * ε ^ (ξ / 2) ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hKs hK0.le
        rwa [mul_inv_cancel₀ hK0.ne'] at this
      calc K * ε ^ (ξ / 2) * ε ^ (ξ / 4)
          ≤ 1 * ε ^ (ξ / 4) := mul_le_mul_of_nonneg_right h1 (Real.rpow_pos_of_pos hε0 _).le
        _ = ε ^ (ξ / 4) := one_mul _
    have hbound := epsA_prop410Bad_le D hγ hL hρ0 hρ1 hA₀ hC₀ h0 hpq hadm hκs (by linarith) htol
    refine hbound.trans ?_
    rw [h2ξ, ← ENNReal.ofReal_toReal hMfin, ← hMreal, ← ENNReal.ofReal_mul (by positivity),
      show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpow : ε ^ (2 * ξ) ≤ ε ^ (ξ / 4) :=
      Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
    have hM0 : 0 ≤ Mreal := ENNReal.toReal_nonneg
    have hC0' : 0 ≤ C₀ ^ (1 / q') := Real.rpow_nonneg hC₀ _
    calc 3 * (Mreal * (C₀ ^ (1 / q') * ε ^ (2 * ξ)))
        = 3 * Mreal * C₀ ^ (1 / q') * ε ^ (2 * ξ) := by ring
      _ ≤ Cfail * ε ^ (ξ / 4) :=
        mul_le_mul (le_max_left _ _) hpow (Real.rpow_pos_of_pos hε0 _).le
          (le_max_of_le_right hCinv)
  · -- the large meshes `ε ≥ ε₀`: the bound exceeds one
    have hpos : 0 < ε₀ ^ (ξ / 4) := Real.rpow_pos_of_pos hε₀ _
    have hge : ε₀ ^ (ξ / 4) ≤ ε ^ (ξ / 4) := Real.rpow_le_rpow hε₀.le hε (by positivity)
    calc P (BundleSec4.Prop410Bad η ε Dm f A₀ (ε ^ (ξ / 4))) ≤ 1 := prob_le_one
      _ = ENNReal.ofReal ((ε₀ ^ (ξ / 4))⁻¹ * ε₀ ^ (ξ / 4)) := by
        rw [inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (Cfail * ε ^ (ξ / 4)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul (le_max_right _ _) hge hpos.le
          (le_max_of_le_right hCinv))

end Coupling

/-- **One fixed-parameter instance of [18] Proposition 4.10 at every real mesh** for the area-parametrized curve
`η` at ambient radius `ρ` and test constant `C` (`BundleSec4.Prop410At` with `∀ ε ∈ (0, 1)` in place of the dyadic
meshes): `∃ β, A, α, Cfail`, for every `ε ∈ (0, 1)` and every pair `(V, f)` admissible at `(ε, ρ, C, β)`, the
failure of `∫⁻_V f u_*^ε ≤ A ∫⁻_V f + ε^α` has outer probability `≤ Cfail ε^α`. -/
def EpsAProp410At {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (ρ C : ℝ) : Prop :=
  ∃ β A α Cfail : ℝ, 0 < β ∧ 0 < α ∧ 0 ≤ A ∧ 0 ≤ Cfail ∧
    ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 → ∀ (V : Set ℂ) (f : ℂ → ℝ), GMS4.Prop210Admissible ε ρ C β V f →
      P (BundleSec4.Prop410Bad η ε V f A (ε ^ α)) ≤ ENNReal.ofReal (Cfail * ε ^ α)

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] Proposition 4.10 at `(ρ, C)`, every real mesh, from the real-mesh zero-cone Case 0 at
`ρ + (1 − ρ)/8` and `Lemma43MeasurableM`**, for every `ρ ∈ (0, 1)` and `C > 1`. -/
theorem epsA_prop410At_of_inputs (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ρ C : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hC : 1 < C)
    (h0 : EpsAZeroConeCase0 D (ρ + (1 - ρ) / 8)) (hL : BundleSec4.Lemma43MeasurableM D) :
    EpsAProp410At P η ρ C := by
  obtain ⟨q, α₀, A₀, C₀, hq, hα₀, hA₀, hC₀, h0⟩ := h0
  obtain ⟨p, hp1, hp4⟩ := GMSCase1.exists_case1_exponent hγ
  obtain ⟨Cfail, hCfail, h⟩ := epsA_prop410_explicit D hγ hρ0 hρ1 hq hα₀ hA₀ hC₀ h0 hL hp1 hp4 hC
  have hq' : 0 < p.conjExponent := (Real.HolderConjugate.conjExponent hp1).symm.pos
  exact ⟨_, A₀, _, Cfail, by positivity, by positivity, hA₀, hCfail, fun ε _ => h ε⟩

/-- **[18] Proposition 4.10 for the bundle's γ-cone curve at every real mesh `ε ∈ (0, 1)`, every `ρ ∈ (0, 1)` and
every `C > 1`, for every frozen coupling on a standard Borel space** (no premise): the real-mesh zero-cone Case 0
(`epsA_zeroConeCase0_holds`) and L43M's `GMS4cM.lemma43MeasurableM_holds`. -/
theorem epsA_prop410At (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2) {ρ C : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hC : 1 < C) :
    EpsAProp410At P η ρ C :=
  epsA_prop410At_of_inputs D hγ hρ0 hρ1 hC
    (epsA_zeroConeCase0_holds D hstd hγ ⟨by linarith, by linarith⟩) (GMS4cM.lemma43MeasurableM_holds D hγ)

end Coupling

end MatedCRTHarmonic.GMSMain
