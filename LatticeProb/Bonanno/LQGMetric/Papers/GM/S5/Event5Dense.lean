/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Event5Dense at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event4Meas

/-!
# GM Lemma 5.9: conditions (4), (5), (7), (8), (9) of `E_r` are measurable (task P2-M2M8)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, Lemma 5.9
(`lem-geo-event-msrble`, l. 3293–3302; GM: "by inspection"), conditions (4), (5), (7), (8), (9)
of `E_r` (l. 3243–3262). Own elementary argument (GM give none), with the tools of decisions
D43/D48/D51:

* `BorelOnLen D E`: `E` agrees with a Borel set on the Borel set `D⁻¹' lenSet` of fields whose
  metric is a boundedly compact length metric; `nullMeasurableSet_of_borelOnLen`: then `E` is
  null-measurable for the law of every field with `D_h ∈ lenSet` a.s.;
* `borelOnLen_forall_internal`: a two-sided bound on `D(p x, q x; V)` for all `x` in a set `A`
  (`p, q` continuous into the open `V`) only needs to be checked on a countable dense subset of `A`
  (continuity of internal metrics of length metrics, LM Lemma 1.1, `continuousOn_internal`), where
  `internal = chainInf` is Borel (`internal_eq_chainInf`);
* `borelOnLen_forall_internalDiam`: bounds on internal diameters of a countable family of open sets
  (the tubes `U x y` and `W_r^x` are drawn from finite families, `sqTubes`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint LocalEvent

/-- `E` agrees with a Borel set on the fields whose `D`-metric lies in `lenSet` -/
def BorelOnLen (D : DistC → ContMetric) (E : Set DistC) : Prop :=
  ∃ B : Set DistC, MeasurableSet B ∧ ∀ g, D g ∈ lenSet → (g ∈ E ↔ g ∈ B)

lemma borelOnLen_of_measurableSet (D : DistC → ContMetric) {E : Set DistC}
    (hE : MeasurableSet E) : BorelOnLen D E :=
  ⟨E, hE, fun _ _ => Iff.rfl⟩

lemma BorelOnLen.inter {D : DistC → ContMetric} {E F : Set DistC} (hE : BorelOnLen D E)
    (hF : BorelOnLen D F) : BorelOnLen D (E ∩ F) := by
  obtain ⟨B, hB, hBE⟩ := hE
  obtain ⟨C, hC, hCF⟩ := hF
  exact ⟨B ∩ C, hB.inter hC, fun g hg => and_congr (hBE g hg) (hCF g hg)⟩

lemma BorelOnLen.biInter {D : DistC → ContMetric} {ι : Type*} {I : Set ι} (hI : I.Countable)
    {E : ι → Set DistC} (hE : ∀ i ∈ I, BorelOnLen D (E i)) : BorelOnLen D (⋂ i ∈ I, E i) := by
  classical
  choose B hB hBE using hE
  let B' : ι → Set DistC := fun i => if hi : i ∈ I then B i hi else univ
  refine ⟨⋂ i ∈ I, B' i, MeasurableSet.biInter hI fun i hi => ?_, fun g hg => ?_⟩
  · simp only [B', hi, dite_true]; exact hB i hi
  · simp only [mem_iInter]
    refine forall₂_congr fun i hi => ?_
    simp only [B', hi, dite_true]
    exact hBE i hi g hg

/-- a set that is Borel on `D⁻¹' lenSet` is null-measurable for the law of a field with
`D_h ∈ lenSet` a.s. -/
lemma nullMeasurableSet_of_borelOnLen {D : DistC → ContMetric} (hDm : Measurable D)
    {E : Set DistC} (hE : BorelOnLen D E) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : Measurable h) (hlen : ∀ᵐ ω ∂P, D (h ω) ∈ lenSet) :
    NullMeasurableSet E (P.map h) := by
  obtain ⟨B, hB, hBE⟩ := hE
  refine hB.nullMeasurableSet.congr ?_
  filter_upwards [(ae_map_iff hh.aemeasurable (measurableSet_lenSet.preimage hDm)).2 hlen]
    with g hg
  exact propext (hBE g hg).symm

/-- `L59MeasOf F` from `BorelOnLen D (F …)` (with `DFGPSLem3_8` for `D_h ∈ lenSet` a.s.) -/
lemma l59MeasOf_of_borelOnLen (h38 : DFGPSLem3_8)
    {F : (DistC → ContMetric) → (DistC → ContMetric) → EData → (ℂ → ℂ → Set ℂ) →
      (Set ℂ → TestC) → (Set ℂ → TestC) → ℝ → Set DistC}
    (H : ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ}, PairSetting γ D D' c →
      ∀ (S : EData), S.Ranges → ∀ (r : ℝ), 0 < r → ∀ (U : ℂ → ℂ → Set ℂ)
        (fb gb : Set ℂ → TestC), IsTubeFam S U r → BorelOnLen D (F D D' S U fb gb r)) :
    L59MeasOf F := by
  intro γ D D' c cs Cs hPS _ _ _ S _ _ _ _ hS r hr U fb gb hU _ Ω _ P _ h hh
  obtain ⟨hγ0, hγ2, hD, -⟩ := id hPS
  exact nullMeasurableSet_of_borelOnLen hD.measurable (H hPS S hS r hr U fb gb hU)
    hh.measurable (ae_mem_lenSet h38 hγ0 hγ2 hD P h hh)

/-- **countable reduction for internal metrics**: a two-sided bound on `D(p x, q x; V)` for all
`x ∈ A` is Borel on `lenSet` -/
theorem borelOnLen_forall_internal {D : DistC → ContMetric} (hDm : Measurable D) {X : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] {A : Set X} {V : Set ℂ} (hV : IsOpen V)
    {p q : X → ℂ} (hp : ContinuousOn p A) (hq : ContinuousOn q A) (hpV : MapsTo p A V)
    (hqV : MapsTo q A V) {lo hi : DistC → ℝ≥0∞} (hlo : Measurable lo) (hhi : Measurable hi) :
    BorelOnLen D {g | ∀ x ∈ A, lo g ≤ (D g).internal V (p x) (q x) ∧
      (D g).internal V (p x) (q x) ≤ hi g} := by
  obtain ⟨T, hTc, hTA, hAT⟩ := TopologicalSpace.exists_countable_dense_subset A
  refine ⟨⋂ x ∈ T, {g | lo g ≤ (D g).chainInf V (p x) (q x) ∧
    (D g).chainInf V (p x) (q x) ≤ hi g}, MeasurableSet.biInter hTc fun x _ => ?_,
    fun g hg => ?_⟩
  · have m := measurable_chainInf_comp hDm (measurable_const (a := p x))
      (measurable_const (a := q x)) V
    exact (measurableSet_le hlo m).inter (measurableSet_le m hhi)
  have hL := isLength_of_mem_lenSet hg
  simp only [mem_ofPred_eq, mem_iInter, ← (D g).internal_eq_chainInf hL hV]
  refine ⟨fun H x hx => H x (hTA hx), fun H x hx => ?_⟩
  have hf : ContinuousOn (fun x => (D g).internal V (p x) (q x)) A :=
    ((D g).continuousOn_internal hL hV).comp (hp.prodMk hq) fun x hx => ⟨hpV hx, hqV hx⟩
  have h1 := ((hf x hx).mono hTA).mem_closure_image (hAT hx)
  exact closure_minimal (by rintro _ ⟨y, hy, rfl⟩; exact H y hy) isClosed_Icc h1

/-- **internal diameters of a countable family of open sets** -/
theorem borelOnLen_forall_internalDiam {D : DistC → ContMetric} (hDm : Measurable D)
    {ι : Type*} {I : Set ι} {V : ι → Set ℂ} (hc : (V '' I).Countable)
    (hV : ∀ i ∈ I, IsOpen (V i)) {hi : DistC → ℝ≥0∞} (hhi : Measurable hi) :
    BorelOnLen D {g | ∀ i ∈ I, internalDiam (D g) (V i) (V i) ≤ hi g} := by
  have e : {g | ∀ i ∈ I, internalDiam (D g) (V i) (V i) ≤ hi g} =
      ⋂ W ∈ V '' I, {g | ∀ z ∈ W ×ˢ W, 0 ≤ (D g).internal W z.1 z.2 ∧
        (D g).internal W z.1 z.2 ≤ hi g} := by
    ext g
    simp only [mem_ofPred_eq, mem_iInter, mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, internalDiam, iSup₂_le_iff, zero_le, true_and, mem_prod,
      Prod.forall]
    exact ⟨fun H i hi a b ha hb => H i hi a ha b hb, fun H i hi a ha b hb => H i hi a b ha hb⟩
  rw [e]
  refine BorelOnLen.biInter hc fun W hW => ?_
  obtain ⟨i, hi, rfl⟩ := hW
  exact borelOnLen_forall_internal hDm (hV i hi) continuous_fst.continuousOn
    continuous_snd.continuousOn (fun z hz => hz.1) (fun z hz => hz.2) measurable_const hhi

/-- `g ↦ k · 𝔠_r e^{ξ h_r(0)}` (as an extended real) is measurable -/
lemma measurable_ofReal_scaleFac (k ξ : ℝ) (c : ℝ → ℝ) (r : ℝ) :
    Measurable fun g : DistC => ENNReal.ofReal (k * scaleFac ξ c g r 0) :=
  ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_const.mul
    (Real.measurable_exp.comp (measurable_const.mul (measurable_circleAvg_left r 0)))))

lemma mem_annulus_iff_e5 {r₁ r₂ : ℝ} {w : ℂ} :
    w ∈ (annulus 0 r₁ r₂ : Set ℂ) ↔ r₁ < ‖w‖ ∧ ‖w‖ < r₂ := by
  show r₁ < ‖w - 0‖ ∧ ‖w - 0‖ < r₂ ↔ _
  rw [sub_zero]

lemma theta_lt_one_e5 {S : EData} (hS : S.Ranges) : 0 < S.θ ∧ S.θ < 1 := by
  obtain ⟨-, -, hb, -, hε, -, hζ, -, hθ, -⟩ := hS
  exact ⟨hθ.1, by linarith [hθ.2, hζ.2, hε.2, hb.2, hε.1, hζ.1]⟩

/-! ## Conditions (4), (7), (8) -/

/-- **condition (8) is Borel on `lenSet`** -/
theorem borelOnLen_eventC8 {D : DistC → ContMetric} (hDm : Measurable D) (D' : DistC → ContMetric)
    {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r) (U : ℂ → ℂ → Set ℂ)
    (fb gb : Set ℂ → TestC) : BorelOnLen D (eventC8 D D' S U fb gb r) := by
  obtain ⟨hθ0, hθ1⟩ := theta_lt_one_e5 hS
  have e : eventC8 D D' S U fb gb r = {g | ∀ x ∈ sphere (0 : ℂ) (2 * r),
      0 ≤ (D g).internal (annulus 0 r (4 * r)) ((3 / 2 : ℂ) * x) (((3 / 2 - S.θ : ℝ) : ℂ) * x) ∧
      (D g).internal (annulus 0 r (4 * r)) ((3 / 2 : ℂ) * x) (((3 / 2 - S.θ : ℝ) : ℂ) * x) ≤
        ENNReal.ofReal (Real.exp (-S.ξ * S.Kf) * scaleFac S.ξ S.c g r 0)} := by
    ext g; simp only [eventC8, mem_ofPred_eq, zero_le, true_and]
  rw [e]
  refine borelOnLen_forall_internal hDm (annulus 0 r (4 * r)).isOpen
    (p := fun x => (3 / 2 : ℂ) * x) (q := fun x => ((3 / 2 - S.θ : ℝ) : ℂ) * x)
    (continuous_const.mul continuous_id).continuousOn
    (continuous_const.mul continuous_id).continuousOn (fun x hx => ?_) (fun x hx => ?_)
    measurable_const (measurable_ofReal_scaleFac _ _ _ _)
  · rw [mem_sphere, dist_zero_right] at hx
    rw [mem_annulus_iff_e5, norm_mul, hx, show ‖(3 / 2 : ℂ)‖ = 3 / 2 by norm_num]
    constructor <;> linarith
  · rw [mem_sphere, dist_zero_right] at hx
    rw [mem_annulus_iff_e5, norm_mul, hx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    constructor <;> nlinarith

/-- **condition (7) is Borel on `lenSet`** -/
theorem borelOnLen_eventC7 {D : DistC → ContMetric} (hDm : Measurable D) (D' : DistC → ContMetric)
    (S : EData) (r : ℝ) (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC) :
    BorelOnLen D (eventC7 D D' S U fb gb r) := by
  have e : eventC7 D D' S U fb gb r = {g | ∀ z ∈ {z : ℂ × ℂ | z.1 ∈ (annulus 0 (r / 4) (4 * r) :
      Set ℂ) ∧ z.2 ∈ (annulus 0 (r / 4) (4 * r) : Set ℂ) ∧ S.ζ * r ≤ ‖z.1 - z.2‖},
      ENNReal.ofReal (S.a * scaleFac S.ξ S.c g r 0) ≤
        (D g).internal (annulus 0 (r / 4) (4 * r)) z.1 z.2 ∧
      (D g).internal (annulus 0 (r / 4) (4 * r)) z.1 z.2 ≤ ⊤} := by
    ext g
    simp only [eventC7, mem_ofPred_eq, le_top, and_true, Prod.forall, and_imp]
    exact ⟨fun H a b ha hb => H a ha b hb, fun H a ha b hb => H a b ha hb⟩
  rw [e]
  exact borelOnLen_forall_internal hDm (annulus 0 (r / 4) (4 * r)).isOpen
    continuous_fst.continuousOn continuous_snd.continuousOn (fun z hz => hz.1)
    (fun z hz => hz.2.1) (measurable_ofReal_scaleFac _ _ _ _) measurable_const

/-- **condition (4) is Borel on `lenSet`** -/
theorem borelOnLen_eventC4 {D : DistC → ContMetric} (hDm : Measurable D) (D' : DistC → ContMetric)
    {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r) (U : ℂ → ℂ → Set ℂ)
    (fb gb : Set ℂ → TestC) : BorelOnLen D (eventC4 D D' S U fb gb r) := by
  have hδ : 0 < S.δ * r := mul_pos hS.2.1.1 hr
  set A : Set (ℂ × ℂ) := {z | z.1 ∈ sphere (0 : ℂ) (2 * r) ∧ z.2 ∈ sphere (0 : ℂ) (2 * r) ∧
    ‖z.1 - z.2‖ < S.δ * r}
  have e : eventC4 D D' S U fb gb r = {g | ∀ z ∈ A,
      0 ≤ (D g).internal (annulus 0 r (4 * r)) ((3 / 2 : ℂ) * z.1) ((3 / 2 : ℂ) * z.2) ∧
      (D g).internal (annulus 0 r (4 * r)) ((3 / 2 : ℂ) * z.1) ((3 / 2 : ℂ) * z.2) ≤
        ENNReal.ofReal (S.Δ * scaleFac S.ξ S.c g r 0)} ∩
      {g | ENNReal.ofReal (S.Δ * scaleFac S.ξ S.c g r 0) ≤
        setDist (D g) (sphere 0 (2 * r)) (sphere 0 (3 * r))} := by
    have hx : ((2 * r : ℝ) : ℂ) ∈ sphere (0 : ℂ) (2 * r) := by
      rw [mem_sphere, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    ext g
    simp only [eventC4, mem_ofPred_eq, mem_inter_iff, zero_le, true_and, A, Prod.forall, and_imp]
    constructor
    · intro H
      exact ⟨fun x y hx hy hxy => (H x hx y hy hxy).1,
        (H _ hx _ hx (by rw [sub_self, norm_zero]; exact hδ)).2⟩
    · rintro ⟨H1, H2⟩ x hx y hy hxy
      exact ⟨H1 x y hx hy hxy, H2⟩
  rw [e]
  have hmap : ∀ w ∈ sphere (0 : ℂ) (2 * r), (3 / 2 : ℂ) * w ∈ (annulus 0 r (4 * r) : Set ℂ) := by
    intro w hw
    rw [mem_sphere, dist_zero_right] at hw
    rw [mem_annulus_iff_e5, norm_mul, hw, show ‖(3 / 2 : ℂ)‖ = 3 / 2 by norm_num]
    constructor <;> linarith
  refine (borelOnLen_forall_internal hDm (annulus 0 r (4 * r)).isOpen
    (continuous_const.mul continuous_fst).continuousOn
    (continuous_const.mul continuous_snd).continuousOn (fun z hz => hmap _ hz.1)
    (fun z hz => hmap _ hz.2.1) measurable_const (measurable_ofReal_scaleFac _ _ _ _)).inter
    (borelOnLen_of_measurableSet D (measurableSet_le (measurable_ofReal_scaleFac _ _ _ _)
      ((measurable_setDist _ _).comp hDm)))

/-! ## Conditions (5), (9) -/

/-- **condition (5) is Borel on `lenSet`** (the tubes `U x y` come from a finite family) -/
theorem borelOnLen_eventC5 {D : DistC → ContMetric} (hDm : Measurable D) (D' : DistC → ContMetric)
    {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r) {U : ℂ → ℂ → Set ℂ} (hU : IsTubeFam S U r)
    (fb gb : Set ℂ → TestC) : BorelOnLen D (eventC5 D D' S U fb gb r) := by
  set I : Set (ℂ × ℂ) := {z | z.1 ∈ sphere (0 : ℂ) (2 * r) ∧ z.2 ∈ sphere (0 : ℂ) (2 * r) ∧
    S.δ * r ≤ ‖z.1 - z.2‖}
  have e : eventC5 D D' S U fb gb r = {g | ∀ z ∈ I,
      internalDiam (D g) (U z.1 z.2) (U z.1 z.2) ≤ ENNReal.ofReal (S.A * scaleFac S.ξ S.c g r 0)} := by
    ext g; simp only [eventC5, mem_ofPred_eq, I, Prod.forall, and_imp]
    exact ⟨fun H a b ha hb => H a ha b hb, fun H a ha b hb => H a b ha hb⟩
  rw [e]
  have hε0 : 0 < S.ε₀ * r := mul_pos hS.2.2.2.2.1.1 hr
  have hT := sqTubes_finite_m2m2 (S.ε₀ * r) (squareSet_finite_m2m2 (R := 3 * r) hε0
    (X := {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r}) (fun w hw => by
      rw [mem_ball, dist_zero_right]; linarith [hw.2]))
  refine borelOnLen_forall_internalDiam hDm (V := fun z : ℂ × ℂ => U z.1 z.2)
    (hT.countable.mono ?_) (fun z hz => (hU z.1 hz.1 z.2 hz.2.1 hz.2.2).1)
    (measurable_ofReal_scaleFac _ _ _ _)
  rintro _ ⟨z, hz, rfl⟩
  exact tube_mem_sqTubes_m2m2 (hU z.1 hz.1 z.2 hz.2.1 hz.2.2).2.2.2.1

/-- **condition (9) is Borel on `lenSet`** (the tubes `W_r^x` come from a finite family) -/
theorem borelOnLen_eventC9 {D : DistC → ContMetric} (hDm : Measurable D) (D' : DistC → ContMetric)
    {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r) (U : ℂ → ℂ → Set ℂ)
    (fb gb : Set ℂ → TestC) : BorelOnLen D (eventC9 D D' S U fb gb r) := by
  obtain ⟨hθ0, hθ1⟩ := theta_lt_one_e5 hS
  have hθ2 : S.θ ≤ 1 / 2 := by
    obtain ⟨-, -, hb, -, hε, -, hζ, -, hθ, -⟩ := hS
    linarith [hθ.2, hζ.2, hε.2, hb.2]
  have hT := sqTubes_finite_m2m2 (S.θ * r) (squareSet_finite_m2m2 (R := 4 * r)
    (mul_pos hθ0 hr) (X := closedBall 0 (3 * r)) (closedBall_subset_ball (by linarith)))
  refine borelOnLen_forall_internalDiam hDm (I := sphere (0 : ℂ) (2 * r))
    (V := lineTube S.θ r) (hT.countable.mono ?_) (fun _ _ => isOpen_interior)
    (measurable_ofReal_scaleFac _ _ _ _)
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_sphere, dist_zero_right] at hx
  exact lineTube_mem_sqTubes_m2m2 hθ0.le hθ2 hx

/-! ## `L59MeasOf` -/

theorem l59MeasOf_eventC4 (h38 : DFGPSLem3_8) : L59MeasOf eventC4 :=
  l59MeasOf_of_borelOnLen h38 fun hPS _ hS _ hr U fb gb _ =>
    borelOnLen_eventC4 hPS.2.2.1.measurable _ hS hr U fb gb

theorem l59MeasOf_eventC5 (h38 : DFGPSLem3_8) : L59MeasOf eventC5 :=
  l59MeasOf_of_borelOnLen h38 fun hPS _ hS _ hr _ fb gb hU =>
    borelOnLen_eventC5 hPS.2.2.1.measurable _ hS hr hU fb gb

theorem l59MeasOf_eventC7 (h38 : DFGPSLem3_8) : L59MeasOf eventC7 :=
  l59MeasOf_of_borelOnLen h38 fun hPS S _ r _ U fb gb _ =>
    borelOnLen_eventC7 hPS.2.2.1.measurable _ S r U fb gb

theorem l59MeasOf_eventC8 (h38 : DFGPSLem3_8) : L59MeasOf eventC8 :=
  l59MeasOf_of_borelOnLen h38 fun hPS _ hS _ hr U fb gb _ =>
    borelOnLen_eventC8 hPS.2.2.1.measurable _ hS hr U fb gb

theorem l59MeasOf_eventC9 (h38 : DFGPSLem3_8) : L59MeasOf eventC9 :=
  l59MeasOf_of_borelOnLen h38 fun hPS _ hS _ hr U fb gb _ =>
    borelOnLen_eventC9 hPS.2.2.1.measurable _ hS hr U fb gb

end LQGMetric.GM
