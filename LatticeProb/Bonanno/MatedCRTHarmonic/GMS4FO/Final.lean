/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4FO.Final at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.Assembly
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.FixedInstance
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.Prop410

/-!
# [18] Proposition 4.10 for the γ-cone of the frozen coupling

Source: [18, Proposition 4.10].

* `le_cond_sum_of_forall_slice`: averaging a per-root bound over the marked root `z₀ ∼ λ[· | B_κ(0)]`;
* `target_subset_three`: for `|z₀| < κ`, failure of the source estimate for `(D, f)` forces failure of one of the
  three recentred good events ([18] (4.43)–(4.44), `globalGood_of_three`);
* `prop410Bad_le_at_mesh`: at a dyadic mesh `ε` (small enough), with `κ = ε^{α₀/(4q)}`,
  `P[∫_D f u^ε_* > A₀ ∫_D f + ε^α] ≤ 3 · E[μ_{h₀}(𝔻)/π]^{p}^{1/p} · (C₀^{1/q} ε^{α₀/(2q)})`;
* **`prop410At_of_inputs`**: `BundleSec4.Prop410At P η (3/4) 100` from the two named inputs `ZeroConeCase0At D (13/16)`
  and `Lemma43Measurable D`; the companion map conclusion and `exists_cellModel_of_matingOfTrees_of_inputs`:
  both conditional mated-CRT map conclusions from the two inputs, for every coupling.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4FO

open MatedCRTHarmonic LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT

/-! ### Averaging over the marked root -/

/-- A bound valid for every root in `B_κ(0)` holds for the conditional rooted law. -/
theorem le_cond_sum_of_forall_slice {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {n : ℕ} (S : Fin n → Set (Ω × ℂ))
    {a : ℝ≥0∞} (h : ∀ z ∈ ball (0 : ℂ) κ, a ≤ ∑ j, P ((fun ω => (ω, z)) ⁻¹' S j)) :
    a ≤ ∑ j, (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω κ] (S j) := by
  have hcond : (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω κ] =
      P.prod (Canon.rootMeasure[|ball (0 : ℂ) κ]) :=
    GMSCase.prod_cond_univ_prod P Canon.rootMeasure (ball (0 : ℂ) κ)
  have hmass : Canon.rootMeasure (ball (0 : ℂ) κ) = ENNReal.ofReal (κ ^ 2) :=
    GMS4.GMSA.normalizedLebesgueOnRootingDisk_ball κ hκ0.le hκ1
  have hne : Canon.rootMeasure (ball (0 : ℂ) κ) ≠ 0 := by
    rw [hmass]
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have : IsProbabilityMeasure (Canon.rootMeasure[|ball (0 : ℂ) κ]) := cond_isProbabilityMeasure hne
  rw [hcond]
  have hT : ∀ j, (P.prod (Canon.rootMeasure[|ball (0 : ℂ) κ])) (S j) =
      ∫⁻ z, P ((fun ω => (ω, z)) ⁻¹' toMeasurable (P.prod (Canon.rootMeasure[|ball (0 : ℂ) κ])) (S j))
        ∂(Canon.rootMeasure[|ball (0 : ℂ) κ]) := fun j => by
    rw [← measure_toMeasurable (S j), Measure.prod_apply_symm (measurableSet_toMeasurable _ _)]
  simp_rw [hT]
  rw [← lintegral_finsetSum _ (fun j _ => measurable_measure_prodMk_right (measurableSet_toMeasurable _ _))]
  calc a = ∫⁻ _z, a ∂(Canon.rootMeasure[|ball (0 : ℂ) κ]) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ _ := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_cond_mem (μ := Canon.rootMeasure) (measurableSet_ball (x := (0 : ℂ)) (ε := κ))]
        with z hz
      refine (h z hz).trans (Finset.sum_le_sum fun j _ => measure_mono ?_)
      exact preimage_mono (subset_toMeasurable _ _)

/-! ### The three recentred test pairs -/

/-- The tolerance of [18] (4.44) with `L = M = 100 ε^{−β}`, `κ = ε^ξ`, `vol D ≤ 2` and `vol B_κ(∂D) ≤ 100 κ`. -/
def tolTotal (ε α₀ β ξ A₀ : ℝ) : ℝ :=
  ε ^ α₀ * (100 * ε ^ (-β)) + 100 * ε ^ (-β) * ε ^ ξ * (A₀ * 2 + ε ^ α₀ * 1) +
    100 * ε ^ (-β) * (A₀ * (100 * ε ^ ξ) + ε ^ α₀ * 1)

/-- The three deterministic test domains of (4.44): `D`, `D`, `B_κ(∂D)`. -/
def pairDom (Dm : Set ℂ) (κ : ℝ) : Fin 3 → Set ℂ := ![Dm, Dm, thickening κ (frontier Dm)]

/-- The three test functions of (4.44): `f`, `1`, `1`. -/
def pairFun (f : ℂ → ℝ) : Fin 3 → ℂ → ℝ := ![f, fun _ => 1, fun _ => 1]

/-- Their sup bounds. -/
def pairBd (M : ℝ) : Fin 3 → ℝ := ![M, 1, 1]

theorem continuousOn_of_lipschitz {Dm : Set ℂ} {f : ℂ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z ∈ Dm, ∀ w ∈ Dm, |f z - f w| ≤ L * dist z w) : ContinuousOn f Dm := by
  refine Metric.continuousOn_iff.2 fun z hz e he => ?_
  refine ⟨e / (L + 1), by positivity, fun w hw hwz => ?_⟩
  have hL1 : 0 < L + 1 := by linarith
  calc dist (f w) (f z) = |f w - f z| := Real.dist_eq _ _
    _ ≤ L * dist w z := hlip w hw z hz
    _ ≤ (L + 1) * dist w z := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < (L + 1) * (e / (L + 1)) := mul_lt_mul_of_pos_left hwz hL1
    _ = e := by field_simp
theorem pairDom_subset {Dm : Set ℂ} (hDsub : Dm ⊆ ball (0 : ℂ) (3 / 4)) {κ : ℝ} (hκ : κ ≤ 1 / 32)
    (j : Fin 3) : pairDom Dm κ j ⊆ ball (0 : ℂ) (13 / 16) := by
  have h1 : Dm ⊆ ball (0 : ℂ) (13 / 16) := hDsub.trans (ball_subset_ball (by norm_num))
  fin_cases j
  · exact h1
  · exact h1
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx
    have hycl : y ∈ closedBall (0 : ℂ) (3 / 4) :=
      (closure_mono hDsub |>.trans closure_ball_subset_closedBall) (frontier_subset_closure hy)
    rw [mem_closedBall, dist_zero_right] at hycl
    rw [mem_ball, dist_zero_right]
    calc ‖x‖ ≤ ‖x - y‖ + ‖y‖ := norm_le_norm_sub_add x y
      _ < κ + 3 / 4 := by rw [← dist_eq_norm]; linarith
      _ ≤ 13 / 16 := by linarith

theorem isOpen_pairDom {Dm : Set ℂ} (hDo : IsOpen Dm) (κ : ℝ) (j : Fin 3) : IsOpen (pairDom Dm κ j) := by
  fin_cases j
  · exact hDo
  · exact hDo
  · exact isOpen_thickening

theorem continuousOn_pairFun {Dm : Set ℂ} {f : ℂ → ℝ} (hf : ContinuousOn f Dm) (κ : ℝ) (j : Fin 3) :
    ContinuousOn (pairFun f j) (pairDom Dm κ j) := by
  fin_cases j
  · exact hf
  · exact continuousOn_const
  · exact continuousOn_const

theorem pairFun_bounds {Dm : Set ℂ} {f : ℂ → ℝ} {M : ℝ} (hfb : ∀ z ∈ Dm, 0 ≤ f z ∧ f z ≤ M) (κ : ℝ)
    (j : Fin 3) : ∀ z ∈ pairDom Dm κ j, 0 ≤ pairFun f j z ∧ pairFun f j z ≤ pairBd M j := by
  fin_cases j
  · exact hfb
  · intro z _; norm_num [pairFun, pairBd]
  · intro z _; norm_num [pairFun, pairBd]

/-- **Failure of the source estimate forces failure of one recentred good event** ([18] (4.43)–(4.44)). -/
theorem exists_fail_of_target {c : C(ℝ, ℂ)} {ε : ℝ} (hε : 0 ≤ ε) {Dm : Set ℂ} (hDo : IsOpen Dm)
    {f : ℂ → ℝ} {M κ A₀ α₀ tol r : ℝ} {R : Set ℂ} (hM : 0 ≤ M) (hκ : 0 ≤ κ) (hA₀ : 0 ≤ A₀)
    (hfM : ∀ z ∈ Dm, f z ≤ M) (hlip : ∀ z ∈ Dm, ∀ w ∈ Dm, |f z - f w| ≤ M * dist z w)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < κ) (hVD : volume Dm ≤ ENNReal.ofReal 2)
    (hVT : volume (thickening κ (frontier Dm)) ≤ ENNReal.ofReal (100 * κ)) (hα₀ε : 0 ≤ ε ^ α₀)
    (htol : ε ^ α₀ * M + M * κ * (A₀ * 2 + ε ^ α₀ * 1) + M * (A₀ * (100 * κ) + ε ^ α₀ * 1) ≤ tol)
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

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

theorem volume_le_two {Dm : Set ℂ} (hDsub : Dm ⊆ ball (0 : ℂ) (3 / 4)) : volume Dm ≤ ENNReal.ofReal 2 := by
  refine (measure_mono hDsub).trans ?_
  rw [Complex.volume_ball, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := Real.pi_lt_d2
  nlinarith

theorem closedBall_subset_of_mem {z : ℂ} (hz : z ∈ ball (0 : ℂ) (13 / 16)) {r : ℝ} (hr : 4 * r ≤ 1 / 32) :
    closedBall z (4 * r) ⊆ ball (0 : ℂ) (7 / 8) := by
  intro w hw
  rw [mem_closedBall] at hw
  rw [mem_ball, dist_zero_right] at hz ⊢
  calc ‖w‖ ≤ ‖w - z‖ + ‖z‖ := norm_le_norm_sub_add w z
    _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
    _ < 7 / 8 := by linarith

/-- **[18] Proposition 4.10 at one dyadic mesh** (for small meshes), from the two named inputs. -/
theorem prop410Bad_le_at_mesh (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)] (hL : Lemma43Measurable D)
    {q α₀ A₀ C₀ : ℝ} (hA₀ : 0 ≤ A₀) (hC₀ : 0 ≤ C₀)
    (h0 : ∀ k : ℕ, 1 ≤ k → ∀ (Dm : Set ℂ) (g : ℂ → ℝ) (M : ℝ), IsOpen Dm →
      Dm ⊆ ball (0 : ℂ) (13 / 16) → ContinuousOn g Dm → (∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M) →
        P {ω | ¬ GlobalGood (η₀ ω) (CellFamily.mesh k) Dm g A₀ (CellFamily.mesh k ^ α₀ * M)
          (ball (0 : ℂ) (13 / 16)) (CellFamily.mesh k ^ q)} ≤ ENNReal.ofReal (C₀ * CellFamily.mesh k ^ α₀))
    {p q' : ℝ} (hpq : p.HolderConjugate q') {k : ℕ} (hk : 1 ≤ k) {β α : ℝ} {Dm : Set ℂ}
    {f : ℂ → ℝ} (hadm : GMS4.Prop210Admissible (CellFamily.mesh k) (3 / 4) 100 β Dm f)
    (hκs : CellFamily.mesh k ^ (α₀ / (4 * q')) ≤ 1 / 32) (hrs : 4 * CellFamily.mesh k ^ q ≤ 1 / 32)
    (htol : tolTotal (CellFamily.mesh k) α₀ β (α₀ / (4 * q')) A₀ ≤ CellFamily.mesh k ^ α) :
    P (BundleSec4.Prop410Bad η (CellFamily.mesh k) Dm f A₀ (CellFamily.mesh k ^ α)) ≤
      3 * (GMSCase1.case1Moment D hγ p ^ (1 / p) *
        ENNReal.ofReal (C₀ ^ (1 / q') * CellFamily.mesh k ^ (α₀ / (2 * q')))) := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨hε0, hε1, -, -, -, -, hDo, -, hDsub, hthick, hfb, hlip⟩ := hadm
  have hq'0 : 0 < q' := hpq.symm.pos
  have hκ0 : 0 < CellFamily.mesh k ^ (α₀ / (4 * q')) := Real.rpow_pos_of_pos hε0 _
  have hκ1 : CellFamily.mesh k ^ (α₀ / (4 * q')) ≤ 1 := hκs.trans (by norm_num)
  have hr0 : 0 ≤ CellFamily.mesh k ^ q := (Real.rpow_pos_of_pos hε0 _).le
  have hM0 : 0 ≤ 100 * CellFamily.mesh k ^ (-β) := by positivity
  have hα₀ε : 0 ≤ CellFamily.mesh k ^ α₀ := (Real.rpow_pos_of_pos hε0 _).le
  have hRV : ∀ z ∈ ball (0 : ℂ) (13 / 16), closedBall z (4 * CellFamily.mesh k ^ q) ⊆ ball (0 : ℂ) (7 / 8) :=
    fun z hz => closedBall_subset_of_mem hz hrs
  have hfM : ∀ z ∈ Dm, f z ≤ 100 * CellFamily.mesh k ^ (-β) := fun z hz => (hfb z hz).2
  have hfc : ContinuousOn f Dm := continuousOn_of_lipschitz hM0 hlip
  have hVT : volume (thickening (CellFamily.mesh k ^ (α₀ / (4 * q'))) (frontier Dm)) ≤
      ENNReal.ofReal (100 * CellFamily.mesh k ^ (α₀ / (4 * q'))) :=
    hthick _ ⟨hκ0, lt_of_le_of_lt hκs (by norm_num)⟩
  -- the three local failure events on `Ω × ℂ`
  let S : Fin 3 → Set (Ω × ℂ) := fun j => {v | (restrictTo (ballO (0 : ℂ) (7 / 8))
    (GMSCase1.wpField X₀ v.1 + CellScaling.ofFunC (fun w => -γ * Real.log ‖w - v.2‖)), ηL v.1) ∈
      failSet γ (ballO (0 : ℂ) (7 / 8)) (CellFamily.mesh k) (pairDom Dm (CellFamily.mesh k ^ (α₀ / (4 * q'))) j)
        (pairFun f j) A₀ (CellFamily.mesh k ^ α₀ * pairBd (100 * CellFamily.mesh k ^ (-β)) j)
        (ball (0 : ℂ) (13 / 16)) (CellFamily.mesh k ^ q)}
  -- step A: one root
  have hA : ∀ z₀ ∈ ball (0 : ℂ) (CellFamily.mesh k ^ (α₀ / (4 * q'))),
      P (BundleSec4.Prop410Bad η (CellFamily.mesh k) Dm f A₀ (CellFamily.mesh k ^ α)) ≤
        ∑ j, P ((fun ω => (ω, z₀)) ⁻¹' S j) := by
    intro z₀ hz₀
    have hz₀' : ‖z₀‖ < CellFamily.mesh k ^ (α₀ / (4 * q')) := by rwa [mem_ball, dist_zero_right] at hz₀
    have hsub : BundleSec4.Prop410Bad η (CellFamily.mesh k) Dm f A₀ (CellFamily.mesh k ^ α) ⊆
        ⋃ j : Fin 3, {ω | ¬ GlobalGood (η ω) (CellFamily.mesh k)
          ((fun z => z - z₀) '' pairDom Dm (CellFamily.mesh k ^ (α₀ / (4 * q'))) j)
          (fun u => pairFun f j (u + z₀)) A₀ (CellFamily.mesh k ^ α₀ * pairBd (100 * CellFamily.mesh k ^ (-β)) j)
          ((fun z => z - z₀) '' ball (0 : ℂ) (13 / 16)) (CellFamily.mesh k ^ q)} := by
      intro ω hω
      obtain ⟨j, hj⟩ := exists_fail_of_target (c := η ω) (R := ball (0 : ℂ) (13 / 16))
        (r := CellFamily.mesh k ^ q) hε0.le hDo hM0 hκ0.le hA₀ hfM hlip hz₀' (volume_le_two hDsub) hVT hα₀ε
        (htol.trans' (le_of_eq (by unfold tolTotal; ring))) hω
      exact mem_iUnion.2 ⟨j, hj⟩
    refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    have hnz : ‖z₀‖ + 15 / 16 ≤ 1 := by linarith
    have hr01 : 7 / 8 + ‖z₀‖ ≤ 15 / 16 := by linarith
    exact cone_le_case2 D hγ hL (r₀ := 7 / 8) (by norm_num) hnz hr01 hε0
      hr0 (pairDom_subset hDsub hκs j) hRV ((isOpen_pairDom hDo _ j).measurableSet)
  -- step B: average over the root
  have hB := le_cond_sum_of_forall_slice P hκ0 hκ1 S hA
  refine hB.trans ?_
  -- step C: Cases 0–2 for each pair
  have hC : ∀ j : Fin 3, (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω (CellFamily.mesh k ^ (α₀ / (4 * q')))]
      (S j) ≤ GMSCase1.case1Moment D hγ p ^ (1 / p) *
        ENNReal.ofReal (C₀ ^ (1 / q') * CellFamily.mesh k ^ (α₀ / (2 * q'))) := by
    intro j
    have hbad0 := (zeroCone_failSet_le D hγ (V := ballO (0 : ℂ) (7 / 8)) isBounded_ball hε0 hr0
      (pairDom_subset hDsub hκs j) hRV ((isOpen_pairDom hDo _ j).measurableSet)
      (g := pairFun f j) (A := A₀) (tol := CellFamily.mesh k ^ α₀ * pairBd (100 * CellFamily.mesh k ^ (-β)) j)).trans
      (h0 k hk _ _ _ (isOpen_pairDom hDo _ j) (pairDom_subset hDsub hκs j) (continuousOn_pairFun hfc _ j)
        (pairFun_bounds hfb _ j))
    have h := case2_smallRoot_failSet_le D hγ hL (V₀ := ballO (0 : ℂ) (7 / 8))
      (ball_subset_ball (by norm_num)) hpq hκ0.le hκ1 hbad0
    rw [mul_div_assoc, GMSCase1.case1_rate_div_eq hC₀ hε0 hq'0] at h
    exact h
  calc ∑ j, (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω (CellFamily.mesh k ^ (α₀ / (4 * q')))] (S j)
      ≤ ∑ _j : Fin 3, GMSCase1.case1Moment D hγ p ^ (1 / p) *
          ENNReal.ofReal (C₀ ^ (1 / q') * CellFamily.mesh k ^ (α₀ / (2 * q'))) :=
        Finset.sum_le_sum fun j _ => hC j
    _ = _ := by simp

end Coupling

/-! ### Numerics -/
theorem mesh_rpow_eq (k : ℕ) (x : ℝ) : CellFamily.mesh k ^ x = ((2 : ℝ) ^ (-x)) ^ k := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  rw [CellFamily.mesh, ← Real.rpow_intCast, ← Real.rpow_mul h2, ← Real.rpow_natCast, ← Real.rpow_mul h2]
  congr 1
  push_cast
  ring

theorem eventually_mesh_rpow_le {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, CellFamily.mesh k ^ x ≤ c := by
  have h0 : 0 ≤ (2 : ℝ) ^ (-x) := by positivity
  have h1 : (2 : ℝ) ^ (-x) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  filter_upwards [ht.eventually (eventually_le_nhds hc)] with k hk
  rw [mesh_rpow_eq]
  exact hk

/-- The tolerance of (4.44) is `O(ε^{3ξ/4})` when `β = ξ/4 ≤ α₀/4`. -/
theorem tolTotal_le {ε α₀ ξ A₀ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hξ0 : 0 ≤ ξ) (hξα : ξ ≤ α₀) :
    tolTotal ε α₀ (ξ / 4) ξ A₀ ≤ (300 + 10200 * A₀) * ε ^ (3 * ξ / 4) := by
  have hea : ε ^ (-(ξ / 4)) * ε ^ ξ = ε ^ (3 * ξ / 4) := by
    rw [← Real.rpow_add hε0]; congr 1; ring
  have hαe : ε ^ α₀ * ε ^ (-(ξ / 4)) ≤ ε ^ (3 * ξ / 4) := by
    rw [← Real.rpow_add hε0]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by linarith)
  have hα1 : ε ^ α₀ ≤ 1 := Real.rpow_le_one hε0.le hε1 (by linarith [hξα, hξ0])
  have hα0 : 0 ≤ ε ^ α₀ := (Real.rpow_pos_of_pos hε0 _).le
  have ha0 : 0 ≤ ε ^ (3 * ξ / 4) := (Real.rpow_pos_of_pos hε0 _).le
  have key : tolTotal ε α₀ (ξ / 4) ξ A₀ = 100 * (ε ^ α₀ * ε ^ (-(ξ / 4))) +
      100 * (ε ^ (-(ξ / 4)) * ε ^ ξ) * (A₀ * 2 + ε ^ α₀) +
      10000 * A₀ * (ε ^ (-(ξ / 4)) * ε ^ ξ) + 100 * (ε ^ α₀ * ε ^ (-(ξ / 4))) := by
    unfold tolTotal; ring
  rw [key, hea]
  nlinarith [mul_le_mul_of_nonneg_left hα1 ha0]

theorem mesh_anti {k k₀ : ℕ} (h : k ≤ k₀) : CellFamily.mesh k₀ ≤ CellFamily.mesh k := by
  unfold CellFamily.mesh
  exact zpow_le_zpow_right₀ (by norm_num) (by omega)

/-! ### The final theorem -/

section Final

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}


end Final

end MatedCRTHarmonic.GMS4FO
