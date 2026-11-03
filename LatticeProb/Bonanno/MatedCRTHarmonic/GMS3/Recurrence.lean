/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS3.Recurrence at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Walk

/-!
# Voltage, effective conductance and the energy criterion for recurrence

Source: GMS [18], proof of Theorem 1.4 ([18]: Dirichlet's
principle "[LP16, Exercise 2.13]" and the recurrence criterion "[LP16, Theorem 2.3]").

Let `G` be a connected locally finite multigraph, `a` a vertex and `U ∋ a` a finite vertex set; put
`W = Uᶜ`.

* `nbhd G U`: `U` together with all neighbours of `U` (the finite vertex set carrying every edge that meets
  `U`).
* `voltage G a U x = P_x[T_a ≤ T_W]` (first visit to `{a} ∪ W` at `a`): it is `1` at `a`, `0` off `U`, and
  discrete harmonic on `U \ {a}` (`voltage_self`, `voltage_of_notMem`, `lap_voltage`).
* `effCond G a U = deg(a) · P_a[T_W < T_a^+]`: the effective conductance from `a` to `W` (the inverse of
  the effective resistance `effRes`).
* `effCond_eq_energy`: `effCond G a U = Energy(voltage; G(nbhd U))`;
  `effCond_le_energy` (**Dirichlet's principle**): `effCond G a U ≤ Energy(g; G(nbhd U))` for every `g`
  with `g(a) = 1` and `g = 0` off `U`.
* `noReturn_le_escProb`: `P_a[T_a^+ = ⊤] ≤ P_a[T_W < T_a^+]`.
* `recurrent_of_forall_energy_le` (**energy criterion**): if for every `δ > 0` some finitely supported
  `g` with `g(a) = 1` has energy `≤ δ`, then `G` is recurrent (the frozen `LFMultigraph.Recurrent`: from
  every vertex the walk visits every vertex almost surely).
* `recurrent_of_effCond_le` / `recurrent_of_tendsto_effRes` (**exhaustion criterion**): if
  `effCond G a (U k) → 0`, i.e. the effective resistance from `a` to the complements of finite sets
  `U k ∋ a` tends to `∞`, then `G` is recurrent. No monotonicity or exhaustion property of `U k` is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology Classical

namespace MatedCRTHarmonic.GMS3

open Markov Harmonic HarmonicInfinity LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-! ### Neighbourhoods -/

/-- `U` together with the heads of all darts leaving `U`. -/
def nbhd (U : Finset V) : Finset V :=
  U ∪ U.biUnion fun x => (G.outDarts x).image G.dtgt

theorem subset_nbhd (U : Finset V) : U ⊆ nbhd G U := Finset.subset_union_left

theorem dtgt_mem_nbhd {U : Finset V} {x : V} (hx : x ∈ U) {d : G.Dart} (hd : d ∈ G.outDarts x) :
    G.dtgt d ∈ nbhd G U :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image_of_mem _ hd⟩)

/-- For adjacent `u, w`, `(g u − g w)² ≤ Energy(g; G(nbhd U))` when `g` vanishes off `U`. -/
theorem sq_sub_le_energy_nbhd {U : Finset V} {g : V → ℝ} (hg : ∀ x ∉ U, g x = 0) {u w : V}
    (huw : G.adj.Adj u w) : (g u - g w) ^ 2 ≤ energy G (nbhd G U) g := by
  by_cases hu : u ∈ U
  · obtain ⟨d, hd1, hd2⟩ := exists_dart_of_adj G huw
    have hw : w ∈ nbhd G U := hd2 ▸ dtgt_mem_nbhd G hu ((mem_outDarts G).mpr hd1)
    obtain ⟨-, ⟨e, he1, he2⟩ | ⟨e, he1, he2⟩⟩ := (adj_iff G).mp huw
    · have he : e ∈ edgesIn G (nbhd G U) :=
        (mem_edgesIn G).mpr ⟨he1 ▸ subset_nbhd G U hu, he2 ▸ hw⟩
      simpa only [he1, he2] using sq_sub_le_energy G he g
    · have he : e ∈ edgesIn G (nbhd G U) :=
        (mem_edgesIn G).mpr ⟨he1 ▸ hw, he2 ▸ subset_nbhd G U hu⟩
      have := sq_sub_le_energy G he g
      rw [he1, he2] at this
      rwa [← neg_sub, neg_sq]
  by_cases hw : w ∈ U
  · obtain ⟨d, hd1, hd2⟩ := exists_dart_of_adj G huw.symm
    have hu' : u ∈ nbhd G U := hd2 ▸ dtgt_mem_nbhd G hw ((mem_outDarts G).mpr hd1)
    obtain ⟨-, ⟨e, he1, he2⟩ | ⟨e, he1, he2⟩⟩ := (adj_iff G).mp huw
    · have he : e ∈ edgesIn G (nbhd G U) :=
        (mem_edgesIn G).mpr ⟨he1 ▸ hu', he2 ▸ subset_nbhd G U hw⟩
      simpa only [he1, he2] using sq_sub_le_energy G he g
    · have he : e ∈ edgesIn G (nbhd G U) :=
        (mem_edgesIn G).mpr ⟨he1 ▸ subset_nbhd G U hw, he2 ▸ hu'⟩
      have := sq_sub_le_energy G he g
      rw [he1, he2] at this
      rwa [← neg_sub, neg_sq]
  rw [hg u hu, hg w hw, sub_self, sq, mul_zero]
  exact energy_nonneg G _ g

/-- Along a walk of length `n`, `|g u − g w| ≤ n · √Energy(g; G(nbhd U))` when `g` vanishes off `U`. -/
theorem abs_sub_le_length_mul_sqrt_energy {U : Finset V} {g : V → ℝ} (hg : ∀ x ∉ U, g x = 0) :
    ∀ {u w : V} (p : G.adj.Walk u w),
      |g u - g w| ≤ p.length * Real.sqrt (energy G (nbhd G U) g) := by
  intro u w p
  induction p with
  | nil => simp
  | @cons u v w huv q ih =>
    have hstep : |g u - g v| ≤ Real.sqrt (energy G (nbhd G U) g) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (sq_sub_le_energy_nbhd G hg huv)
    calc |g u - g w| ≤ |g u - g v| + |g v - g w| := abs_sub_le _ _ _
      _ ≤ Real.sqrt (energy G (nbhd G U) g) + q.length * Real.sqrt (energy G (nbhd G U) g) :=
          add_le_add hstep ih
      _ = (SimpleGraph.Walk.cons huv q).length * Real.sqrt (energy G (nbhd G U) g) := by
          rw [SimpleGraph.Walk.length_cons]; push_cast; ring

/-! ### Hitting `{a} ∪ Uᶜ` -/

/-- On a connected graph the walk from every vertex visits `{a} ∪ Uᶜ` a.s. (`U` finite, `a ∈ U`). -/
theorem walkLaw_hitTime_insert_ne_top (hconn : G.adj.Connected) {U : Finset V} {a : V} (y : V) :
    G.walkLaw y {ω | hitTime (insert a ((U : Set V)ᶜ)) (G.vertexPath ω) ≠ ⊤} = 1 := by
  have hset : insert a ((U : Set V)ᶜ) = ((U : Set V) \ {a})ᶜ := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_compl_iff, Finset.mem_coe, Set.mem_sdiff,
      Set.mem_singleton_iff, not_and, not_not]
    tauto
  rw [hset]
  refine walkLaw_hitTime_compl_ne_top G ((U.finite_toSet).sdiff) (fun x _ => ⟨a, ?_, ?_⟩) y
  · simp
  · exact hconn.preconnected x a

/-- On the event that `I` is visited, the first visit lies in `I`: `P_x(X_{T_I} ∈ W) = P_x(X_{T_I} ∈ I ∩ W)`. -/
theorem hitDist_inter_self (I W : Set V) (x : V) : hitDist G I x W = hitDist G I x (I ∩ W) := by
  rw [hitDist_eq_hitLaw, hitDist_eq_hitLaw]
  unfold hitLaw
  congr 1
  ext ω
  simp only [hitEvent, Set.mem_ofPred_eq, Set.preimage_inter, Set.mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, stopState_hitTime_mem h1, h2⟩
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩

/-! ### The voltage -/

/-- The **voltage** `x ↦ P_x[T_a ≤ T_W]` between `a` (value `1`) and `W = Uᶜ` (value `0`). -/
def voltage (a : V) (U : Finset V) (x : V) : ℝ :=
  (hitDist G (insert a ((U : Set V)ᶜ)) x {a}).toReal

theorem voltage_self (a : V) (U : Finset V) : voltage G a U a = 1 := by
  unfold voltage
  rw [hitDist_of_mem G (Set.mem_insert a _), Set.indicator_of_mem (Set.mem_singleton a),
    Pi.one_apply, ENNReal.toReal_one]

theorem voltage_of_notMem {a : V} {U : Finset V} (ha : a ∈ U) {x : V} (hx : x ∉ U) :
    voltage G a U x = 0 := by
  unfold voltage
  have hxa : x ∉ ({a} : Set V) := by
    rintro rfl
    exact hx ha
  rw [hitDist_of_mem G (Set.mem_insert_of_mem a (by simpa using hx)),
    Set.indicator_of_notMem hxa, ENNReal.toReal_zero]

theorem voltage_nonneg (a : V) (U : Finset V) (x : V) : 0 ≤ voltage G a U x :=
  ENNReal.toReal_nonneg

theorem voltage_le_one (a : V) (U : Finset V) (x : V) : voltage G a U x ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hitDist_le_one G _ _ x)

/-- `(deg x)⁻¹ ∑` of `toReal` values is the `toReal` of the ENNReal average. -/
theorem toReal_inv_deg_mul_sum (x : V) (F : G.Dart → ℝ≥0∞) (hF : ∀ d, F d ≠ ⊤) :
    ((G.deg x : ℝ≥0∞)⁻¹ * ∑ d ∈ G.outDarts x, F d).toReal =
      (G.deg x : ℝ)⁻¹ * ∑ d ∈ G.outDarts x, (F d).toReal := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum fun d _ => hF d]

/-- If `x ∉ I`, then `x ↦ P_x(X_{T_I} ∈ W)` is discrete harmonic at `x`. -/
theorem lap_hitDist {I : Set V} {x : V} (hx : x ∉ I) (W : Set V) :
    lap G (fun y => (hitDist G I y W).toReal) x = 0 := by
  rw [lap_eq]
  have h := congrArg ENNReal.toReal (hitDist_eq_avg G hx W)
  rw [toReal_inv_deg_mul_sum G x _ fun d => hitDist_ne_top G _ _ _] at h
  have hdeg : (G.deg x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (deg_ne_zero G x)
  rw [h, ← mul_assoc, mul_inv_cancel₀ hdeg, one_mul, sub_self]

theorem lap_voltage {a : V} {U : Finset V} {x : V} (hxU : x ∈ U) (hxa : x ≠ a) :
    lap G (voltage G a U) x = 0 := by
  refine lap_hitDist G ?_ {a}
  simp only [Set.mem_insert_iff, Set.mem_compl_iff, Finset.mem_coe, not_or, not_not]
  exact ⟨hxa, hxU⟩

/-- `P_y(T_W < T_a) = 1 − voltage(y)`. -/
theorem toReal_hitDist_compl_eq (hconn : G.adj.Connected) {a : V} {U : Finset V} (ha : a ∈ U)
    (y : V) : (hitDist G (insert a ((U : Set V)ᶜ)) y ((U : Set V)ᶜ)).toReal = 1 - voltage G a U y := by
  have h1 := hitDist_add_compl_eq_one G (walkLaw_hitTime_insert_ne_top G hconn (U := U) (a := a) y)
    {a}
  have h2 : hitDist G (insert a ((U : Set V)ᶜ)) y ({a} : Set V)ᶜ =
      hitDist G (insert a ((U : Set V)ᶜ)) y ((U : Set V)ᶜ) := by
    rw [hitDist_inter_self G _ ({a} : Set V)ᶜ, hitDist_inter_self G _ ((U : Set V)ᶜ)]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_compl_iff, Finset.mem_coe,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact absurd h h'
      · exact ⟨Or.inr h, h⟩
    · rintro ⟨-, h⟩
      refine ⟨Or.inr h, ?_⟩
      rintro rfl
      exact h ha
  rw [h2] at h1
  unfold voltage
  have hfin1 := hitDist_ne_top G (insert a ((U : Set V)ᶜ)) {a} y
  have hfin2 := hitDist_ne_top G (insert a ((U : Set V)ᶜ)) ((U : Set V)ᶜ) y
  have := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_one] at this
  linarith

/-! ### Effective conductance -/

/-- The **effective conductance** from `a` to `Uᶜ`: `deg(a) · P_a[T_{Uᶜ} < T_a^+]`. -/
def effCond (a : V) (U : Finset V) : ℝ :=
  G.deg a * (escProb G a ((U : Set V)ᶜ)).toReal

/-- The **effective resistance** from `a` to `Uᶜ` (`= Gr_{T_{Uᶜ}}(a, a) / deg(a)`, `Green.lean`). -/
def effRes (a : V) (U : Finset V) : ℝ := (effCond G a U)⁻¹

theorem escProb_ne_top (a : V) (W : Set V) : escProb G a W ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one

theorem effCond_eq_lap (hconn : G.adj.Connected) {a : V} {U : Finset V} (ha : a ∈ U) :
    effCond G a U = lap G (voltage G a U) a := by
  unfold effCond
  rw [escProb_eq_avg, toReal_inv_deg_mul_sum G a _ fun d => hitDist_ne_top G _ _ _, ← mul_assoc,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (deg_ne_zero G a)), one_mul]
  unfold lap
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [toReal_hitDist_compl_eq G hconn ha, voltage_self]

/-- **Effective conductance is the energy of the voltage.** -/
theorem effCond_eq_energy (hconn : G.adj.Connected) {a : V} {U : Finset V} (ha : a ∈ U) :
    effCond G a U = energy G (nbhd G U) (voltage G a U) := by
  rw [energy_eq_sum_mul_lap G (voltage G a U) (fun x hx => voltage_of_notMem G ha hx)
    (subset_nbhd G U) (fun x hx d hd => dtgt_mem_nbhd G hx hd),
    Finset.sum_eq_single_of_mem a ha (fun x hx hxa => by rw [lap_voltage G hx hxa, mul_zero]),
    voltage_self, one_mul, effCond_eq_lap G hconn ha]

theorem effCond_nonneg (hconn : G.adj.Connected) {a : V} {U : Finset V} (ha : a ∈ U) :
    0 ≤ effCond G a U := by
  rw [effCond_eq_energy G hconn ha]
  exact energy_nonneg G _ _

/-- **Dirichlet's principle** ([18]; [LP16, Exercise 2.13]): the effective conductance from
`a` to `Uᶜ` is at most the energy of every `g` with `g(a) = 1` and `g = 0` off `U`. -/
theorem effCond_le_energy (hconn : G.adj.Connected) {a : V} {U : Finset V} (ha : a ∈ U)
    {g : V → ℝ} (hga : g a = 1) (hg : ∀ x ∉ U, g x = 0) :
    effCond G a U ≤ energy G (nbhd G U) g := by
  rw [effCond_eq_energy G hconn ha]
  refine energy_le_of_harmonic G (B := insert a ((U : Set V)ᶜ)) ?_ ?_ ?_
  · intro x _ hxB d hd
    have hxU : x ∈ U := by
      by_contra h
      exact hxB (Set.mem_insert_of_mem a (by simpa using h))
    exact dtgt_mem_nbhd G hxU hd
  · intro x _ hxB
    have hxU : x ∈ U := by
      by_contra h
      exact hxB (Set.mem_insert_of_mem a (by simpa using h))
    have hxa : x ≠ a := fun h => hxB (h ▸ Set.mem_insert x _)
    exact lap_voltage G hxU hxa
  · intro x _ hxB
    rcases hxB with rfl | hx
    · rw [hga, voltage_self]
    · have hx' : x ∉ U := by simpa using hx
      rw [hg x hx', voltage_of_notMem G ha hx']

/-! ### Return probability -/

/-- The no-return event of the shifted walk is the complement of the return event. -/
theorem returnProb_add_noReturn (a : V) :
    returnProb G a + G.walkLaw a (walkShift 1 ⁻¹' {ω | hitTime (G.stateVertex ⁻¹' {a}) ω = ⊤}) = 1 := by
  unfold returnProb
  have hm := (measurable_walkShift (S := G.State) 1) (measurableSet_hitTime_ne_top' G
    (G.stateVertex ⁻¹' {a}))
  have hc : walkShift 1 ⁻¹' {ω | hitTime (G.stateVertex ⁻¹' {a}) ω = ⊤} =
      (walkShift 1 ⁻¹' {ω | hitTime (G.stateVertex ⁻¹' {a}) ω ≠ ⊤})ᶜ := by
    ext ω; simp
  rw [hc, measure_add_measure_compl hm, measure_univ]

/-- If the walk from `y` visits `{a} ∪ W` a.s., then `P_y(T_a = ⊤) ≤ P_y(X_{T_{{a} ∪ W}} ∈ W)`. -/
theorem walkLaw_hitTime_eq_top_le {a y : V} {W : Set V}
    (hI : G.walkLaw y {ω | hitTime (insert a W) (G.vertexPath ω) ≠ ⊤} = 1) :
    G.walkLaw y {ω | hitTime {a} (G.vertexPath ω) = ⊤} ≤ hitDist G (insert a W) y W := by
  have hnull : G.walkLaw y {ω | hitTime (insert a W) (G.vertexPath ω) = ⊤} = 0 := by
    have hm : MeasurableSet {ω : ℕ → G.State | hitTime (insert a W) (G.vertexPath ω) ≠ ⊤} := by
      simp only [hitTime_vertexPath]
      exact measurableSet_hitTime_ne_top' G (G.stateVertex ⁻¹' insert a W)
    have h := measure_add_measure_compl (μ := G.walkLaw y) hm
    rw [hI, measure_univ] at h
    have hc : {ω : ℕ → G.State | hitTime (insert a W) (G.vertexPath ω) ≠ ⊤}ᶜ =
        {ω | hitTime (insert a W) (G.vertexPath ω) = ⊤} := by
      ext ω; simp
    rw [hc] at h
    have h' : (1 : ℝ≥0∞) + G.walkLaw y {ω | hitTime (insert a W) (G.vertexPath ω) = ⊤} = 1 + 0 := by
      rw [h, add_zero]
    exact (ENNReal.add_right_inj ENNReal.one_ne_top).mp h'
  calc G.walkLaw y {ω | hitTime {a} (G.vertexPath ω) = ⊤}
      ≤ G.walkLaw y ({ω | hitTime (insert a W) (G.vertexPath ω) = ⊤} ∪
          hitEvent (G.stateVertex ⁻¹' insert a W) (G.stateVertex ⁻¹' W)) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq] at hω
        by_cases hT : hitTime (insert a W) (G.vertexPath ω) = ⊤
        · exact Or.inl hT
        · refine Or.inr ⟨hT, ?_⟩
          have hmem := stopState_hitTime_mem (A := G.stateVertex ⁻¹' insert a W) (ω := ω) hT
          rcases hmem with h | h
          · exfalso
            obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hT
            have hst : stopState (hitTime (G.stateVertex ⁻¹' insert a W)) ω = ω n :=
              stopState_eq_of_eq hn.symm
            rw [hst] at h
            have : hitTime {a} (G.vertexPath ω) ≤ n := hitTime_le_of_mem h
            rw [hω] at this
            exact absurd this (by simp)
          · exact h
    _ ≤ G.walkLaw y {ω | hitTime (insert a W) (G.vertexPath ω) = ⊤} +
          G.walkLaw y (hitEvent (G.stateVertex ⁻¹' insert a W) (G.stateVertex ⁻¹' W)) :=
        measure_union_le _ _
    _ = hitDist G (insert a W) y W := by rw [hnull, zero_add]; rfl

/-- **No return implies escape**: `P_a[T_a^+ = ⊤] ≤ P_a[T_{Uᶜ} < T_a^+]` (`U ∋ a` finite, `G`
connected). -/
theorem noReturn_le_escProb (hconn : G.adj.Connected) {a : V} {U : Finset V} :
    G.walkLaw a (walkShift 1 ⁻¹' {ω | hitTime (G.stateVertex ⁻¹' {a}) ω = ⊤}) ≤
      escProb G a ((U : Set V)ᶜ) := by
  rw [walkLaw_walkShift_one G a (measurableSet_hitTime_eq_top MeasurableSet.of_discrete),
    escProb_eq_avg]
  gcongr with d _
  have h := chainLaw_vertexEvent (isNNChain_walk G) (dartState G d)
    (Q := fun X => hitTime {a} X = ⊤)
    (measurableSet_hitTime_eq_top (A := G.stateVertex ⁻¹' {a}) MeasurableSet.of_discrete)
  refine le_of_eq_of_le h ?_
  exact walkLaw_hitTime_eq_top_le G (walkLaw_hitTime_insert_ne_top G hconn _)

/-- The no-return probability is at most `Energy(g)/deg(a)` for every test function `g`. -/
theorem noReturn_le_energy (hconn : G.adj.Connected) {a : V} {U : Finset V} (ha : a ∈ U)
    {g : V → ℝ} (hga : g a = 1) (hg : ∀ x ∉ U, g x = 0) :
    G.walkLaw a (walkShift 1 ⁻¹' {ω | hitTime (G.stateVertex ⁻¹' {a}) ω = ⊤}) ≤
      ENNReal.ofReal (energy G (nbhd G U) g / G.deg a) := by
  refine (noReturn_le_escProb G hconn (U := U)).trans ?_
  rw [← ENNReal.ofReal_toReal (escProb_ne_top G a _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hdeg : (0 : ℝ) < G.deg a := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (deg_ne_zero G a))
  rw [le_div_iff₀ hdeg, mul_comm]
  exact effCond_le_energy G hconn ha hga hg

/-- **Return at `a` from test functions at `a`.** -/
theorem returnProb_eq_one_of_energy (hconn : G.adj.Connected) (a : V)
    (h : ∀ δ > 0, ∃ (U : Finset V) (g : V → ℝ), a ∈ U ∧ g a = 1 ∧ (∀ x ∉ U, g x = 0) ∧
      energy G (nbhd G U) g ≤ δ) : returnProb G a = 1 := by
  have hnr : G.walkLaw a (walkShift 1 ⁻¹' {ω | hitTime (G.stateVertex ⁻¹' {a}) ω = ⊤}) = 0 := by
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_) bot_le
    have hdeg : (0 : ℝ) < G.deg a := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (deg_ne_zero G a))
    obtain ⟨U, g, ha, hga, hg, hE⟩ := h (η * G.deg a) (mul_pos (by exact_mod_cast hη) hdeg)
    refine (noReturn_le_energy G hconn ha hga hg).trans ?_
    rw [zero_add]
    calc ENNReal.ofReal (energy G (nbhd G U) g / G.deg a)
        ≤ ENNReal.ofReal (η * G.deg a / G.deg a) :=
          ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hE hdeg.le)
      _ = η := by rw [mul_div_cancel_right₀ _ hdeg.ne', ENNReal.ofReal_coe_nnreal]
  have := returnProb_add_noReturn G a
  rwa [hnr, add_zero] at this

/-! ### Moving the base point -/

/-- **Transfer of test functions** along a walk: small-energy test functions at `a` give small-energy
test functions at every vertex `y` reachable from `a`. -/
theorem exists_test_of_reachable {a y : V} (hay : G.adj.Reachable a y)
    (h : ∀ δ > 0, ∃ (U : Finset V) (g : V → ℝ), a ∈ U ∧ g a = 1 ∧ (∀ x ∉ U, g x = 0) ∧
      energy G (nbhd G U) g ≤ δ) :
    ∀ δ > 0, ∃ (U : Finset V) (g : V → ℝ), y ∈ U ∧ g y = 1 ∧ (∀ x ∉ U, g x = 0) ∧
      energy G (nbhd G U) g ≤ δ := by
  obtain ⟨p⟩ := hay
  intro δ hδ
  set n : ℝ := (p.length : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set δ₀ : ℝ := min (δ / 4) (1 / (4 * (n + 1) ^ 2)) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min (by positivity) (by positivity)
  obtain ⟨U, g, ha, hga, hg, hE⟩ := h δ₀ hδ₀pos
  have hEnn := energy_nonneg G (nbhd G U) g
  -- `|g a − g y| ≤ 1/2`
  have hdiff : |g a - g y| ≤ 1 / 2 := by
    refine (abs_sub_le_length_mul_sqrt_energy G hg p).trans ?_
    have hsq : Real.sqrt (energy G (nbhd G U) g) ≤ 1 / (2 * (n + 1)) := by
      rw [Real.sqrt_le_left (by positivity)]
      calc energy G (nbhd G U) g ≤ δ₀ := hE
        _ ≤ 1 / (4 * (n + 1) ^ 2) := min_le_right _ _
        _ = (1 / (2 * (n + 1))) ^ 2 := by rw [div_pow, one_pow, mul_pow]; norm_num
    calc (p.length : ℝ) * Real.sqrt (energy G (nbhd G U) g) ≤ n * (1 / (2 * (n + 1))) :=
          mul_le_mul_of_nonneg_left hsq hn0
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
  have hgy : 1 / 2 ≤ g y := by
    rw [hga] at hdiff
    have := (abs_le.mp hdiff).2
    linarith
  have hgy0 : 0 < g y := by linarith
  let clamp : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hclamp : ∀ s t, |clamp s - clamp t| ≤ |s - t| := by
    intro s t
    have h1 : |min 1 s - min 1 t| ≤ |s - t| := abs_min_sub_min_le_max 1 s 1 t |>.trans
      (by simp)
    exact (abs_max_sub_max_le_max 0 (min 1 s) 0 (min 1 t)).trans (by simpa using h1)
  refine ⟨U, clamp ∘ fun x => (g y)⁻¹ * g x, ?_, ?_, ?_, ?_⟩
  · by_contra hyU
    rw [hg y hyU] at hgy
    linarith
  · simp [clamp, inv_mul_cancel₀ hgy0.ne']
  · intro x hx
    simp [clamp, hg x hx]
  · calc energy G (nbhd G U) (clamp ∘ fun x => (g y)⁻¹ * g x)
        ≤ energy G (nbhd G U) (fun x => (g y)⁻¹ * g x) := energy_comp_le G _ _ hclamp
      _ = ((g y)⁻¹) ^ 2 * energy G (nbhd G U) g := energy_const_mul G _ _ _
      _ ≤ 4 * δ₀ := by
          have hinv : ((g y)⁻¹) ^ 2 ≤ 4 := by
            rw [inv_pow, inv_le_comm₀ (by positivity) (by norm_num)]
            nlinarith
          calc ((g y)⁻¹) ^ 2 * energy G (nbhd G U) g ≤ 4 * energy G (nbhd G U) g :=
                mul_le_mul_of_nonneg_right hinv hEnn
            _ ≤ 4 * δ₀ := by linarith
      _ ≤ δ := by
          have := min_le_left (δ / 4) (1 / (4 * (n + 1) ^ 2))
          rw [← hδ₀] at this
          linarith

/-! ### From return everywhere to the frozen recurrence -/

/-- If an average of `n` values `≤ 1` equals `1`, all the values are `1`. -/
theorem eq_one_of_avg_eq_one {ι : Type*} {s : Finset ι} {F : ι → ℝ≥0∞} (hF : ∀ i ∈ s, F i ≤ 1)
    (h : ((s.card : ℝ≥0∞))⁻¹ * ∑ i ∈ s, F i = 1) : ∀ i ∈ s, F i = 1 := by
  have hne : s.card ≠ 0 := by
    rintro h0
    rw [h0, Finset.card_eq_zero.mp h0] at h
    simp at h
  have hsum : ∑ i ∈ s, F i = s.card := by
    have hc : (s.card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hne
    have hc' : (s.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    calc ∑ i ∈ s, F i = (s.card : ℝ≥0∞) * ((s.card : ℝ≥0∞)⁻¹ * ∑ i ∈ s, F i) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hc hc', one_mul]
      _ = s.card := by rw [h, mul_one]
  intro i hi
  by_contra hne1
  have hlt : F i < 1 := lt_of_le_of_ne (hF i hi) hne1
  have h2 : ∑ j ∈ s.erase i, F j ≤ (s.erase i).card := by
    calc ∑ j ∈ s.erase i, F j ≤ ∑ j ∈ s.erase i, (1 : ℝ≥0∞) :=
          Finset.sum_le_sum fun j hj => hF j (Finset.mem_of_mem_erase hj)
      _ = (s.erase i).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have h3 : (s.card : ℝ≥0∞) = 1 + (s.erase i).card := by
    rw [← Finset.card_erase_add_one hi]; push_cast; ring
  have : ∑ j ∈ s, F j < s.card := by
    rw [← Finset.add_sum_erase s F hi, h3]
    calc F i + ∑ j ∈ s.erase i, F j ≤ F i + (s.erase i).card := add_le_add le_rfl h2
      _ < 1 + (s.erase i).card := ENNReal.add_lt_add_right (ENNReal.natCast_ne_top _) hlt
  rw [hsum] at this
  exact lt_irrefl _ this

theorem walkLaw_hitTime_ne_top_of_mem {A : Set V} {x : V} (hx : x ∈ A) :
    G.walkLaw x {ω | hitTime A (G.vertexPath ω) ≠ ⊤} = 1 := by
  have h := chainLaw_hitTime_lt_top_of_mem G.walkKernel (A := G.stateVertex ⁻¹' A)
    (x := startState G x) hx
  simp only [lt_top_iff_ne_top] at h
  exact h

/-- With `W = univ` the hitting distribution is the hitting probability. -/
theorem hitDist_univ (I : Set V) (x : V) :
    hitDist G I x Set.univ = G.walkLaw x {ω | hitTime I (G.vertexPath ω) ≠ ⊤} := by
  unfold hitDist
  congr 1
  ext ω
  simp

/-- **Return everywhere gives the frozen recurrence** on a connected graph: if the walk from every
vertex returns to it a.s., then from every vertex it visits every vertex a.s. -/
theorem recurrent_of_returnProb (hconn : G.adj.Connected) (hret : ∀ y, returnProb G y = 1) :
    G.Recurrent := by
  intro x y
  let h : V → ℝ≥0∞ := fun u => G.walkLaw u {ω | hitTime {y} (G.vertexPath ω) ≠ ⊤}
  have hy : h y = 1 := walkLaw_hitTime_ne_top_of_mem G (Set.mem_singleton y)
  have hstep : ∀ u w, G.adj.Adj u w → h u = 1 → h w = 1 := by
    intro u w huw hu
    obtain ⟨d, hd1, hd2⟩ := exists_dart_of_adj G huw
    have hdmem : d ∈ G.outDarts u := (mem_outDarts G).mpr hd1
    have havg : ((G.outDarts u).card : ℝ≥0∞)⁻¹ * ∑ d ∈ G.outDarts u, h (G.dtgt d) = 1 := by
      by_cases huy : u = y
      · subst huy
        have := returnProb_eq_avg G u
        rw [hret u] at this
        exact this.symm
      · have := hitDist_eq_avg G (I := {y}) (x := u) huy Set.univ
        simp only [hitDist_univ] at this
        rw [← hu]
        exact this.symm
    have := eq_one_of_avg_eq_one (s := G.outDarts u) (fun d _ => prob_le_one) havg d hdmem
    rwa [hd2] at this
  have hprop : ∀ {u v : V} (q : G.adj.Walk u v), h u = 1 → h v = 1 := by
    intro u v q
    induction q with
    | nil => exact id
    | cons huw _ ih => exact fun hu => ih (hstep _ _ huw hu)
  obtain ⟨p⟩ := hconn.preconnected y x
  exact hprop p hy

/-- **Energy criterion for recurrence** ([18] with [LP16, Theorem 2.3]): on a
connected locally finite multigraph, if for every `δ > 0` there are a finite `U ∋ a` and `g` with
`g(a) = 1`, `g = 0` off `U` and `Energy(g; G(nbhd U)) ≤ δ`, then simple random walk is recurrent. -/
theorem recurrent_of_forall_energy_le (hconn : G.adj.Connected) (a : V)
    (h : ∀ δ > 0, ∃ (U : Finset V) (g : V → ℝ), a ∈ U ∧ g a = 1 ∧ (∀ x ∉ U, g x = 0) ∧
      energy G (nbhd G U) g ≤ δ) : G.Recurrent :=
  recurrent_of_returnProb G hconn fun y =>
    returnProb_eq_one_of_energy G hconn y (exists_test_of_reachable G (hconn.preconnected a y) h)

/-- **Exhaustion criterion, conductance form**: if the effective conductances from `a` to the
complements of finite sets `U k ∋ a` become arbitrarily small, `G` is recurrent. -/
theorem recurrent_of_effCond_le (hconn : G.adj.Connected) (a : V) (U : ℕ → Finset V)
    (ha : ∀ k, a ∈ U k) (h : ∀ δ > 0, ∃ k, effCond G a (U k) ≤ δ) : G.Recurrent :=
  recurrent_of_forall_energy_le G hconn a fun δ hδ => by
    obtain ⟨k, hk⟩ := h δ hδ
    exact ⟨U k, voltage G a (U k), ha k, voltage_self G a _,
      fun x hx => voltage_of_notMem G (ha k) hx, (effCond_eq_energy G hconn (ha k)) ▸ hk⟩

/-- **Exhaustion criterion** ([LP16, Theorem 2.3] direction used by [18]): if the effective
resistance from `a` to the complements of finite sets `U k ∋ a` tends to `∞`, `G` is recurrent. -/
theorem recurrent_of_tendsto_effRes (hconn : G.adj.Connected) (a : V) (U : ℕ → Finset V)
    (ha : ∀ k, a ∈ U k) (h : Tendsto (fun k => effRes G a (U k)) atTop atTop) : G.Recurrent := by
  refine recurrent_of_effCond_le G hconn a U ha fun δ hδ => ?_
  obtain ⟨k, hk⟩ := (h.eventually_ge_atTop (δ⁻¹)).exists
  refine ⟨k, ?_⟩
  have hR : 0 < effRes G a (U k) := lt_of_lt_of_le (inv_pos.mpr hδ) hk
  have hC : effCond G a (U k) = (effRes G a (U k))⁻¹ := by unfold effRes; rw [inv_inv]
  rw [hC]
  exact (inv_le_comm₀ hR hδ).mpr hk

end MatedCRTHarmonic.GMS3
