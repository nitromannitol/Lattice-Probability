/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Recurrence.ExcursionEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTargetOrthogonality
import LatticeProb.Bonanno.ReflectedWalk.HarmonicMeasure
import LatticeProb.Bonanno.ReflectedWalk.UniquenessGeneralSide

/-!
# The flux identity for the finite-target energy minimizer

This is the analytic half of the reflected excursion identity
`π(o) · P_o[τ_F < τ_o⁺] = E(h_F)` (manuscript `r:lem:identity`, equation `r:eq:flux`).

Fix a finite nonempty boundary set `A` containing `o` and boundary data `φ` with
`φ(o) = 0` and `φ ≡ 1` on `A \ {o}`.  Testing the energy minimizer `h = h_φ` against the
explicit competitor `u = 1 − 1_{o}` gives

  `E(h) = E(h, u) = ∑_{x} c(o,x) h(x)`,

the flux of `h` out of `o`.  The first equality is the full finite-energy orthogonality
`ReflectedGMS.FullNetworkForm.energyMin_dirichletForm_zero` applied to the admissible
variation `u − h`, which vanishes on all of `A`; the second is the observation that only
the ordered pairs meeting `o` contribute to `E(h, u)`, each unoriented edge `{o,x}`
contributing its two ordered copies to the halved ordered sum of
`ReflectedWalk.ConductanceGraph.dirichletForm`.

Nothing here restricts the competitor class: `h` is the minimizer among **all**
finite-energy functions with the prescribed values on `A`, and `u` has finite energy
`π(o) < ∞` by `ConductanceGraph.summable_c`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ReflectedWalk ReflectedWalk.Theorem16
open scoped NNReal ENNReal

namespace ReflectedGMS.ExcursionEnergy

open Classical in
/-- The manuscript's explicit admissible competitor `u = 1 − 1_{o}`: it vanishes at `o`
and equals `1` everywhere else, and its energy is `π(o)`. -/
noncomputable def unitOffPoint {V : Type*} (o : V) : V → ℝ := fun v => if v = o then 0 else 1

@[simp] theorem unitOffPoint_self {V : Type*} (o : V) : unitOffPoint o o = 0 := by
  unfold unitOffPoint; exact if_pos rfl

theorem unitOffPoint_of_ne {V : Type*} {o v : V} (h : v ≠ o) : unitOffPoint o v = 1 := by
  unfold unitOffPoint; exact if_neg h

section Analysis

variable {V : Type*} (G : ConductanceGraph V)

/-- `u = 1 − 1_{o}` has finite energy: only the ordered pairs meeting `o` contribute, and
the resulting sums are `π(o) = ∑_y c(o,y) < ∞`. -/
theorem hasFiniteEnergy_unitOffPoint (o : V) : G.HasFiniteEnergy (unitOffPoint o) := by
  have hrow_ne : ∀ x : V, x ≠ o → ∀ y : V, y ≠ o →
      G.gradSq (unitOffPoint o) (x, y) = 0 := by
    intro x hx y hy
    show G.c x y * (unitOffPoint o y - unitOffPoint o x) ^ 2 = 0
    rw [unitOffPoint_of_ne hy, unitOffPoint_of_ne hx]
    ring
  have hcol : ∀ x : V, G.gradSq (unitOffPoint o) (x, o) = G.c x o := by
    intro x
    by_cases hx : x = o
    · subst hx
      show G.c x x * (unitOffPoint x x - unitOffPoint x x) ^ 2 = G.c x x
      rw [G.c_self]
      ring
    · show G.c x o * (unitOffPoint o o - unitOffPoint o x) ^ 2 = G.c x o
      rw [unitOffPoint_self, unitOffPoint_of_ne hx]
      ring
  have hrow_o : ∀ y : V, G.gradSq (unitOffPoint o) (o, y) ≤ G.c o y := by
    intro y
    show G.c o y * (unitOffPoint o y - unitOffPoint o o) ^ 2 ≤ G.c o y
    rw [unitOffPoint_self, sub_zero]
    by_cases hy : y = o
    · subst hy
      rw [unitOffPoint_self]
      simpa using G.c_nonneg y y
    · rw [unitOffPoint_of_ne hy]
      simpa using G.c_nonneg o y
  have hsc : Summable (fun x : V => G.c x o) :=
    (G.summable_c o).congr (fun x => G.c_symm o x)
  refine (summable_prod_of_nonneg (Pi.le_def.mpr fun p => G.gradSq_nonneg _ p)).2 ⟨?_, ?_⟩
  · intro x
    by_cases hx : x = o
    · subst hx
      exact Summable.of_nonneg_of_le (fun y => G.gradSq_nonneg _ _) hrow_o (G.summable_c x)
    · exact summable_of_ne_finset_zero (s := {o})
        (fun y hy => hrow_ne x hx y (by simpa using hy))
  · have hne : ∀ x : V, x ≠ o → ∑' y : V, G.gradSq (unitOffPoint o) (x, y) = G.c x o := by
      intro x hx
      rw [tsum_eq_single o (fun y hy => hrow_ne x hx y hy)]
      exact hcol x
    have hsplit : ∀ x : V, ∑' y : V, G.gradSq (unitOffPoint o) (x, y) =
        G.c x o + (∑' y : V, G.gradSq (unitOffPoint o) (x, y) - G.c x o) := by
      intro x; ring
    refine Summable.congr (hsc.add (summable_of_ne_finset_zero (s := {o}) ?_))
      (fun x => (hsplit x).symm)
    intro x hx
    rw [hne x (by simpa using hx), sub_self]

/-- **The flux identity** (manuscript `r:eq:flux`).  For the finite-target energy minimizer
`h = h_φ` with `φ(o) = 0` and `φ ≡ 1` on `A \ {o}`,

  `E(h) = ∑_x c(o,x) h(x)`.

The competitor class behind `h` is the full finite-energy one; no finite-support or
finite-patch restriction is used, and each unoriented edge is counted once by the halved
ordered convention of `ConductanceGraph.Energy`. -/
theorem energy_energyMin_eq_tsum_conductance_mul
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty) {o : V} (hoA : o ∈ A)
    (φ : V → ℝ) (hφo : φ o = 0) (hφ : ∀ y ∈ A, y ≠ o → φ y = 1) :
    G.Energy (G.energyMin hG A φ) = ∑' x : V, G.c o x * G.energyMin hG A φ x := by
  have hfe : G.HasFiniteEnergy (G.energyMin hG A φ) := G.energyMin_hasFiniteEnergy hG hA φ
  have hho : G.energyMin hG A φ o = 0 := by
    rw [G.energyMin_eqOn hG hA φ (Finset.mem_coe.2 hoA), hφo]
  have hufe : G.HasFiniteEnergy (unitOffPoint o) := hasFiniteEnergy_unitOffPoint G o
  -- the admissible variation `u − h` vanishes on the whole boundary set `A`
  have hvar : ∀ v ∈ A, (unitOffPoint o - G.energyMin hG A φ) v = 0 := by
    intro v hv
    by_cases hvo : v = o
    · subst hvo
      simp only [Pi.sub_apply, unitOffPoint_self, hho, sub_self]
    · simp only [Pi.sub_apply, unitOffPoint_of_ne hvo,
        G.energyMin_eqOn hG hA φ (Finset.mem_coe.2 hv), hφ v hv hvo, sub_self]
  have horth : G.dirichletForm (G.energyMin hG A φ) (unitOffPoint o - G.energyMin hG A φ) = 0 :=
    ReflectedGMS.FullNetworkForm.energyMin_dirichletForm_zero G hG hA φ
      (unitOffPoint o - G.energyMin hG A φ) (hufe.sub hfe) hvar
  -- hence `E(h) = E(h, u)`
  have hEu : G.dirichletForm (G.energyMin hG A φ) (unitOffPoint o) =
      G.Energy (G.energyMin hG A φ) := by
    have hdec : unitOffPoint o =
        G.energyMin hG A φ + (unitOffPoint o - G.energyMin hG A φ) := by
      funext x; simp
    rw [G.dirichletForm_comm, hdec,
      G.dirichletForm_add_left hfe (hufe.sub hfe) hfe, G.dirichletForm_self,
      G.dirichletForm_comm (unitOffPoint o - G.energyMin hG A φ), horth, add_zero]
  -- and `E(h, u)` is the flux out of `o`
  have hbd : ∀ x : V, |G.energyMin hG A φ x| ≤ max |A.inf' hA φ| |A.sup' hA φ| := fun x =>
    abs_le_max_abs_abs (G.min_le_energyMin hG hA φ x) (G.energyMin_le_max hG hA φ x)
  have hsum_ch : Summable (fun y : V => G.c o y * G.energyMin hG A φ y) := by
    refine Summable.of_norm_bounded
      ((G.summable_c o).mul_left (max |A.inf' hA φ| |A.sup' hA φ|)) (fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (G.c_nonneg o y), mul_comm]
    exact mul_le_mul_of_nonneg_right (hbd y) (G.c_nonneg o y)
  have hsum_ch' : Summable (fun x : V => G.c x o * G.energyMin hG A φ x) :=
    hsum_ch.congr (fun x => by rw [G.c_symm o x])
  have hrow_ne : ∀ x : V, x ≠ o → ∀ y : V, y ≠ o →
      G.gradProd (G.energyMin hG A φ) (unitOffPoint o) (x, y) = 0 := by
    intro x hx y hy
    show G.c x y * ((G.energyMin hG A φ y - G.energyMin hG A φ x) *
      (unitOffPoint o y - unitOffPoint o x)) = 0
    rw [unitOffPoint_of_ne hy, unitOffPoint_of_ne hx]
    ring
  have hcol : ∀ x : V, G.gradProd (G.energyMin hG A φ) (unitOffPoint o) (x, o) =
      G.c x o * G.energyMin hG A φ x := by
    intro x
    by_cases hx : x = o
    · subst hx
      show G.c x x * ((G.energyMin hG A φ x - G.energyMin hG A φ x) *
        (unitOffPoint x x - unitOffPoint x x)) = G.c x x * G.energyMin hG A φ x
      rw [G.c_self]
      ring
    · show G.c x o * ((G.energyMin hG A φ o - G.energyMin hG A φ x) *
        (unitOffPoint o o - unitOffPoint o x)) = G.c x o * G.energyMin hG A φ x
      rw [hho, unitOffPoint_self, unitOffPoint_of_ne hx]
      ring
  have hrow_o : ∀ y : V, G.gradProd (G.energyMin hG A φ) (unitOffPoint o) (o, y) =
      G.c o y * G.energyMin hG A φ y := by
    intro y
    by_cases hy : y = o
    · subst hy
      show G.c y y * ((G.energyMin hG A φ y - G.energyMin hG A φ y) *
        (unitOffPoint y y - unitOffPoint y y)) = G.c y y * G.energyMin hG A φ y
      rw [G.c_self]
      ring
    · show G.c o y * ((G.energyMin hG A φ y - G.energyMin hG A φ o) *
        (unitOffPoint o y - unitOffPoint o o)) = G.c o y * G.energyMin hG A φ y
      rw [hho, unitOffPoint_self, unitOffPoint_of_ne hy]
      ring
  have hrow : ∀ x : V, x ≠ o →
      ∑' y : V, G.gradProd (G.energyMin hG A φ) (unitOffPoint o) (x, y) =
        G.c x o * G.energyMin hG A φ x := by
    intro x hx
    rw [tsum_eq_single o (fun y hy => hrow_ne x hx y hy)]
    exact hcol x
  have hrest : ∀ x : V, x ≠ o →
      (∑' y : V, G.gradProd (G.energyMin hG A φ) (unitOffPoint o) (x, y)) -
        G.c x o * G.energyMin hG A φ x = 0 := by
    intro x hx
    rw [hrow x hx, sub_self]
  have hresto : (∑' y : V, G.gradProd (G.energyMin hG A φ) (unitOffPoint o) (o, y)) -
      G.c o o * G.energyMin hG A φ o = ∑' y : V, G.c o y * G.energyMin hG A φ y := by
    rw [tsum_congr hrow_o, G.c_self]
    ring
  have hsum_rest : Summable (fun x : V =>
      (∑' y : V, G.gradProd (G.energyMin hG A φ) (unitOffPoint o) (x, y)) -
        G.c x o * G.energyMin hG A φ x) :=
    summable_of_ne_finset_zero (s := {o}) (fun x hx => hrest x (by simpa using hx))
  have hdouble : ∑' (x : V) (y : V), G.gradProd (G.energyMin hG A φ) (unitOffPoint o) (x, y) =
      (∑' y : V, G.c o y * G.energyMin hG A φ y) +
        (∑' y : V, G.c o y * G.energyMin hG A φ y) := by
    have hsplit : ∀ x : V,
        (∑' y : V, G.gradProd (G.energyMin hG A φ) (unitOffPoint o) (x, y)) =
          G.c x o * G.energyMin hG A φ x +
            ((∑' y : V, G.gradProd (G.energyMin hG A φ) (unitOffPoint o) (x, y)) -
              G.c x o * G.energyMin hG A φ x) := by
      intro x; ring
    rw [tsum_congr hsplit, hsum_ch'.tsum_add hsum_rest,
      tsum_eq_single o (fun x hx => hrest x hx), hresto]
    congr 1
    exact tsum_congr (fun x => by rw [G.c_symm x o])
  have hprod : ∑' p : V × V, G.gradProd (G.energyMin hG A φ) (unitOffPoint o) p =
      (∑' y : V, G.c o y * G.energyMin hG A φ y) +
        (∑' y : V, G.c o y * G.energyMin hG A φ y) := by
    rw [(G.summable_gradProd hfe hufe).tsum_prod]
    exact hdouble
  rw [← hEu, ConductanceGraph.dirichletForm, hprod]
  ring

end Analysis

/-! ## The reflected excursion identity

The process half.  At the departure time `σ_o` (the property-(iii) exit time from `o`) the
reflected walk sits at a neighbour `v` of `o` with law `c(o,v)/π(o)`; the strong Markov
property at that vertex-valued time (Lemma 3.10, `strongMarkov_completed`) and property (vi)
through `law_hitEvent` identify the conditional probability of finishing the excursion in `F`
with the harmonic measure of `F` seen from `v`, i.e. with `h_F(v)`.  No infinite-target
hitting distribution and no attainment of an infinite-target hitting time is used: every
hitting statement here concerns the **finite** boundary set `A`. -/

open Classical in
/-- The boundary data `1_F` of the manuscript: `0` at `o` (as `o ∉ F`) and `1` on `F`. -/
noncomputable def targetIndicator {V : Type*} (F : Finset V) : V → ℝ :=
  fun v => if v ∈ F then 1 else 0

theorem targetIndicator_of_mem {V : Type*} {F : Finset V} {v : V} (h : v ∈ F) :
    targetIndicator F v = 1 := by
  unfold targetIndicator; exact if_pos h

theorem targetIndicator_of_notMem {V : Type*} {F : Finset V} {v : V} (h : v ∉ F) :
    targetIndicator F v = 0 := by
  unfold targetIndicator; exact if_neg h

theorem targetIndicator_nonneg {V : Type*} (F : Finset V) (v : V) :
    0 ≤ targetIndicator F v := by
  unfold targetIndicator; split_ifs <;> norm_num

variable {V : Type*}

/-- The first time at or after the departure from `o` at which the process lies in the finite
set `A`.  This is `hittingAfter` started at the property-(iii) exit time `σ_o`. -/
noncomputable def postDepartureHitTime (𝓧 : ProcessFamily V) (o : V) (A : Finset V) :
    𝓧.Ω → WithTop ℝ≥0 :=
  fun ω => hittingAfter 𝓧.X (some '' (A : Set V)) (exitTime 𝓧.X o ω).untopA ω

/-- The excursion event `{τ_F < τ_o⁺}`: the first visit to `A = {o} ∪ F` at or after the
departure from `o` is a visit to `F`.  Equivalently, the walk reaches `F` before returning
to `o`. -/
def departureHitsTarget (𝓧 : ProcessFamily V) (o : V) (A F : Finset V) : Set 𝓧.Ω :=
  {ω | postDepartureHitTime 𝓧 o A ω ≠ ⊤ ∧
      ∃ y ∈ F, stoppedValue 𝓧.X (postDepartureHitTime 𝓧 o A) ω = some y}

section Process

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {𝓧 : ProcessFamily V}
  [Countable V]

/-- The first-departure decomposition of a single terminal vertex: by property (iii) and the
strong Markov property at the departure time, the excursion ends at `y` with probability
`∑_v (c(o,v)/π(o)) hm^v_A(y)`. -/
theorem measure_postDepartureHit_eq [Nontrivial V] (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty) (o y : V) :
    𝓧.P o {ω | postDepartureHitTime 𝓧 o A ω ≠ ⊤ ∧
        stoppedValue 𝓧.X (postDepartureHitTime 𝓧 o A) ω = some y} =
      ∑' v : V, ENNReal.ofReal (G.c o v / G.pi o) *
        ENNReal.ofReal (G.harmonicMeasure hG A v y) := by
  have hii := (h o).2.2.1
  have hRo := (h o).2.2.2.1
  have hτm : AEMeasurable (exitTime 𝓧.X o) (𝓧.P o) :=
    aemeasurable_exitTime 𝓧.measurable_X hii hRo o
  have hτs : IsAEStoppingTime 𝓧.naturalFiltration (𝓧.P o) (exitTime 𝓧.X o) :=
    isAEStoppingTime_exitTime 𝓧.measurable_X hii hRo o
  have hfinτ : ∀ᵐ ω ∂𝓧.P o, exitTime 𝓧.X o ω ≠ ⊤ := by
    have h0 := measure_exitTime_eq_top h o
    rw [ae_iff]
    simpa using h0
  have hfutm : AEMeasurable (futureAt 𝓧.X (exitTime 𝓧.X o)) (𝓧.P o) := by
    refine (aemeasurable_futureAt 𝓧.measurable_X hii hRo hτm.measurable_mk).congr ?_
    filter_upwards [hτm.ae_eq_mk] with ω hω
    funext s
    simp only [futureAt, hω]
  have hFuniv : AEMeasurableSetStopped 𝓧.naturalFiltration (𝓧.P o) (exitTime 𝓧.X o)
      Set.univ := by
    intro t
    obtain ⟨G', hG'm, hG'e⟩ := hτs t
    exact ⟨G', hG'm, by rwa [Set.univ_inter]⟩
  have hSM : ∀ v : V, 𝓧.P o (Set.univ ∩ stopEvent 𝓧.X (exitTime 𝓧.X o) v ∩
      futureAt 𝓧.X (exitTime 𝓧.X o) ⁻¹' hitEvent A y) =
      𝓧.P o (Set.univ ∩ stopEvent 𝓧.X (exitTime 𝓧.X o) v) *
        ENNReal.ofReal (G.harmonicMeasure hG A v y) := by
    intro v
    rw [strongMarkov_completed h o hRo hτm hτs v hFuniv (measurableSet_hitEvent A y),
      law_hitEvent h hG v ((h v).2.2.2.1) hA y]
  have hind : ∀ v : V, 𝓧.P o (Set.univ ∩ stopEvent 𝓧.X (exitTime 𝓧.X o) v) =
      ENNReal.ofReal (G.c o v / G.pi o) := by
    intro v
    obtain ⟨-, -, -, -, hval⟩ := (h o).2.2.2.2.1
    rw [Set.univ_inter, ← hval v]
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hfinτ] with ω hωfin
    simp only [stopEvent, Set.mem_setOf_eq, Set.mem_ofPred_eq, hωfin, ne_eq,
      not_false_eq_true, true_and]
  have hdec : {ω | postDepartureHitTime 𝓧 o A ω ≠ ⊤ ∧
      stoppedValue 𝓧.X (postDepartureHitTime 𝓧 o A) ω = some y} =ᵐ[𝓧.P o]
      ⋃ v : V, (Set.univ ∩ stopEvent 𝓧.X (exitTime 𝓧.X o) v ∩
        futureAt 𝓧.X (exitTime 𝓧.X o) ⁻¹' hitEvent A y) := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [ae_rightRegularAt hii hRo, hfinτ,
      ae_exists_stoppedValue_exitTime h hG o] with ω hω hωfin hωval
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hωfin
    have hτa : exitTime 𝓧.X o ω = (a : WithTop ℝ≥0) := ha.symm
    have hua : (exitTime 𝓧.X o ω).untopA = a := by rw [hτa]; exact untopA_coe a
    have hiff := mem_hitEvent_futureAt_iff hω A y hτa
    have hpd : postDepartureHitTime 𝓧 o A ω = hittingAfter 𝓧.X (some '' (A : Set V)) a ω := by
      simp only [postDepartureHitTime, hua]
    have hsv : stoppedValue 𝓧.X (postDepartureHitTime 𝓧 o A) ω =
        stoppedValue 𝓧.X (hittingAfter 𝓧.X (some '' (A : Set V)) a) ω := by
      simp only [stoppedValue, hpd]
    simp only [Set.mem_setOf_eq, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_univ, true_and, hiff, hpd, hsv]
    constructor
    · rintro ⟨hne', hsvy⟩
      obtain ⟨v, hv⟩ := hωval
      exact ⟨v, ⟨hωfin, hv⟩, hne', hsvy⟩
    · rintro ⟨v, -, hne', hsvy⟩
      exact ⟨hne', hsvy⟩
  rw [measure_congr hdec,
    measure_iUnion₀ (f := fun v : V => Set.univ ∩ stopEvent 𝓧.X (exitTime 𝓧.X o) v ∩
        futureAt 𝓧.X (exitTime 𝓧.X o) ⁻¹' hitEvent A y)
      (fun v v' hvv' => ((disjoint_stopEvent hvv').mono
        (Set.inter_subset_left.trans Set.inter_subset_right)
        (Set.inter_subset_left.trans Set.inter_subset_right)).aedisjoint)
      (fun v => ((MeasurableSet.univ.nullMeasurableSet).inter
        (nullMeasurableSet_stopEvent' 𝓧.measurable_X hii hRo hτm v)).inter
        (nullMeasurableSet_preimage_of_aemeasurable hfutm (measurableSet_hitEvent A y)))]
  exact tsum_congr fun v => by rw [hSM v, hind v]

/-- The per-vertex excursion events are null-measurable. -/
theorem nullMeasurableSet_postDepartureHit [Nontrivial V] (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty) (o y : V) :
    NullMeasurableSet {ω | postDepartureHitTime 𝓧 o A ω ≠ ⊤ ∧
      stoppedValue 𝓧.X (postDepartureHitTime 𝓧 o A) ω = some y} (𝓧.P o) := by
  have hii := (h o).2.2.1
  have hRo := (h o).2.2.2.1
  have hτm : AEMeasurable (exitTime 𝓧.X o) (𝓧.P o) :=
    aemeasurable_exitTime 𝓧.measurable_X hii hRo o
  have hfutm : AEMeasurable (futureAt 𝓧.X (exitTime 𝓧.X o)) (𝓧.P o) := by
    refine (aemeasurable_futureAt 𝓧.measurable_X hii hRo hτm.measurable_mk).congr ?_
    filter_upwards [hτm.ae_eq_mk] with ω hω
    funext s
    simp only [futureAt, hω]
  have hfinτ : ∀ᵐ ω ∂𝓧.P o, exitTime 𝓧.X o ω ≠ ⊤ := by
    have h0 := measure_exitTime_eq_top h o
    rw [ae_iff]
    simpa using h0
  have hdec : {ω | postDepartureHitTime 𝓧 o A ω ≠ ⊤ ∧
      stoppedValue 𝓧.X (postDepartureHitTime 𝓧 o A) ω = some y} =ᵐ[𝓧.P o]
      ⋃ v : V, (Set.univ ∩ stopEvent 𝓧.X (exitTime 𝓧.X o) v ∩
        futureAt 𝓧.X (exitTime 𝓧.X o) ⁻¹' hitEvent A y) := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [ae_rightRegularAt hii hRo, hfinτ,
      ae_exists_stoppedValue_exitTime h hG o] with ω hω hωfin hωval
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hωfin
    have hτa : exitTime 𝓧.X o ω = (a : WithTop ℝ≥0) := ha.symm
    have hua : (exitTime 𝓧.X o ω).untopA = a := by rw [hτa]; exact untopA_coe a
    have hiff := mem_hitEvent_futureAt_iff hω A y hτa
    have hpd : postDepartureHitTime 𝓧 o A ω = hittingAfter 𝓧.X (some '' (A : Set V)) a ω := by
      simp only [postDepartureHitTime, hua]
    have hsv : stoppedValue 𝓧.X (postDepartureHitTime 𝓧 o A) ω =
        stoppedValue 𝓧.X (hittingAfter 𝓧.X (some '' (A : Set V)) a) ω := by
      simp only [stoppedValue, hpd]
    simp only [Set.mem_setOf_eq, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_univ, true_and, hiff, hpd, hsv]
    constructor
    · rintro ⟨hne', hsvy⟩
      obtain ⟨v, hv⟩ := hωval
      exact ⟨v, ⟨hωfin, hv⟩, hne', hsvy⟩
    · rintro ⟨v, -, hne', hsvy⟩
      exact ⟨hne', hsvy⟩
  refine NullMeasurableSet.congr (NullMeasurableSet.iUnion fun v =>
    ((MeasurableSet.univ.nullMeasurableSet).inter
      (nullMeasurableSet_stopEvent' 𝓧.measurable_X hii hRo hτm v)).inter
      (nullMeasurableSet_preimage_of_aemeasurable hfutm (measurableSet_hitEvent A y))) hdec.symm

/-- **The reflected excursion identity** (manuscript `r:lem:identity`, `r:eq:identity`):

  `π(o) · P_o[τ_F < τ_o⁺] = E(h_F)`,

with `h_F` the energy minimizer with boundary values `0` at `o` and `1` on `F`, minimal among
**all** finite-energy competitors with those values.  `A` is the finite boundary set
`{o} ∪ F`, described by the three membership hypotheses. -/
theorem pi_mul_measure_departureHitsTarget_eq_energy (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) {A F : Finset V} (hFne : F.Nonempty) {o : V}
    (hoA : o ∈ A) (hoF : o ∉ F) (hFA : ∀ y ∈ F, y ∈ A) (hAF : ∀ y ∈ A, y ≠ o → y ∈ F) :
    G.pi o * (𝓧.P o (departureHitsTarget 𝓧 o A F)).toReal =
      G.Energy (G.energyMin hG A (targetIndicator F)) := by
  obtain ⟨y₀, hy₀⟩ := hFne
  haveI : Nontrivial V := ⟨⟨y₀, o, fun hy => hoF (hy ▸ hy₀)⟩⟩
  have hA : A.Nonempty := ⟨o, hoA⟩
  have hπ : 0 < G.pi o := G.pi_pos_of_connected hG o
  have hπ0 : G.pi o ≠ 0 := ne_of_gt hπ
  have hφo : targetIndicator F o = 0 := targetIndicator_of_notMem hoF
  have hφ : ∀ y ∈ A, y ≠ o → targetIndicator F y = 1 := fun y hy hyo =>
    targetIndicator_of_mem (hAF y hy hyo)
  -- the minimizer is nonnegative and its boundary sum is the harmonic measure of `F`
  have hhnn : ∀ v : V, 0 ≤ G.energyMin hG A (targetIndicator F) v := by
    intro v
    refine le_trans ?_ (G.min_le_energyMin hG hA (targetIndicator F) v)
    exact Finset.le_inf' hA _ fun a _ => targetIndicator_nonneg F a
  have hhsum : ∀ v : V, G.energyMin hG A (targetIndicator F) v =
      ∑ y ∈ F, G.harmonicMeasure hG A v y := by
    intro v
    rw [G.energyMin_eq_sum_harmonicMeasure hG hA (targetIndicator F) v]
    rw [← Finset.sum_subset (fun y hy => hFA y hy)
      (fun y hyA hyF => by rw [targetIndicator_of_notMem hyF, zero_mul])]
    exact Finset.sum_congr rfl fun y hy => by rw [targetIndicator_of_mem hy, one_mul]
  -- the excursion event splits over its terminal vertex
  have hsplit : departureHitsTarget 𝓧 o A F =
      ⋃ y ∈ F, {ω | postDepartureHitTime 𝓧 o A ω ≠ ⊤ ∧
        stoppedValue 𝓧.X (postDepartureHitTime 𝓧 o A) ω = some y} := by
    ext ω
    simp only [departureHitsTarget, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    tauto
  have hmeas : 𝓧.P o (departureHitsTarget 𝓧 o A F) =
      ∑ y ∈ F, 𝓧.P o {ω | postDepartureHitTime 𝓧 o A ω ≠ ⊤ ∧
        stoppedValue 𝓧.X (postDepartureHitTime 𝓧 o A) ω = some y} := by
    rw [hsplit]
    refine measure_biUnion_finset₀ ?_ (fun y _ =>
      nullMeasurableSet_postDepartureHit h hG hA o y)
    intro y _ y' _ hyy'
    refine Disjoint.aedisjoint (Set.disjoint_left.2 ?_)
    rintro ω ⟨-, hy⟩ ⟨-, hy'⟩
    exact hyy' (Option.some_inj.1 (hy.symm.trans hy'))
  -- summability of the real first-step decomposition
  have hcpi : ∀ {v : V}, 0 ≤ G.c o v / G.pi o := fun {v} =>
    div_nonneg (G.c_nonneg o v) (G.pi_nonneg o)
  have hsummable : ∀ y : V, Summable (fun v : V =>
      G.c o v / G.pi o * G.harmonicMeasure hG A v y) := by
    intro y
    refine Summable.of_nonneg_of_le (fun v => mul_nonneg hcpi
      (G.harmonicMeasure_nonneg hG hA v y)) (fun v => ?_) ((G.summable_c o).div_const (G.pi o))
    have : G.c o v / G.pi o * G.harmonicMeasure hG A v y ≤ G.c o v / G.pi o * 1 :=
      mul_le_mul_of_nonneg_left (G.harmonicMeasure_le_one hG hA v y) hcpi
    simpa using this
  have hsummableF : Summable (fun v : V =>
      G.c o v / G.pi o * G.energyMin hG A (targetIndicator F) v) := by
    have hs := summable_sum (f := fun (y : V) (v : V) =>
      G.c o v / G.pi o * G.harmonicMeasure hG A v y) (s := F) (fun y _ => hsummable y)
    refine Summable.congr hs (fun v => ?_)
    rw [hhsum v, Finset.mul_sum]
  -- assemble in `ℝ≥0∞`
  have hENN : 𝓧.P o (departureHitsTarget 𝓧 o A F) =
      ENNReal.ofReal (∑' v : V, G.c o v / G.pi o * G.energyMin hG A (targetIndicator F) v) := by
    rw [hmeas]
    have hy : ∀ y ∈ F, 𝓧.P o {ω | postDepartureHitTime 𝓧 o A ω ≠ ⊤ ∧
        stoppedValue 𝓧.X (postDepartureHitTime 𝓧 o A) ω = some y} =
        ∑' v : V, ENNReal.ofReal (G.c o v / G.pi o * G.harmonicMeasure hG A v y) := by
      intro y _
      rw [measure_postDepartureHit_eq h hG hA o y]
      exact tsum_congr fun v =>
        (ENNReal.ofReal_mul hcpi).symm
    rw [Finset.sum_congr rfl hy,
      ← Summable.tsum_finsetSum (fun y _ => ENNReal.summable),
      ENNReal.ofReal_tsum_of_nonneg
        (fun v => mul_nonneg hcpi (hhnn v)) hsummableF]
    refine tsum_congr fun v => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun y _ => mul_nonneg hcpi (G.harmonicMeasure_nonneg hG hA v y))]
    rw [hhsum v, Finset.mul_sum]
  -- back to the reals, and then the flux identity
  rw [hENN, ENNReal.toReal_ofReal (tsum_nonneg fun v => mul_nonneg hcpi (hhnn v))]
  have hdiv : (∑' v : V, G.c o v / G.pi o * G.energyMin hG A (targetIndicator F) v) =
      (∑' v : V, G.c o v * G.energyMin hG A (targetIndicator F) v) / G.pi o := by
    rw [← tsum_div_const]
    exact tsum_congr fun v => by ring
  rw [hdiv, energy_energyMin_eq_tsum_conductance_mul G hG hA hoA (targetIndicator F) hφo hφ]
  field_simp

/-- **The finite-energy bound** (manuscript `r:eq:finitebound`): the excursion probability is
at most `E(f)/π(o)` for **every** finite-energy competitor `f` with `f(o) = 0` and `f ≡ 1`
on `F`.  No decay at infinity, finite support, or vanishing at other ends is imposed on `f`. -/
theorem measure_departureHitsTarget_le_energy_div (h : IsReflectedWalk G w hmin 𝓧)
    (hG : G.toSimpleGraph.Connected) {A F : Finset V} (hFne : F.Nonempty) {o : V}
    (hoA : o ∈ A) (hoF : o ∉ F) (hFA : ∀ y ∈ F, y ∈ A) (hAF : ∀ y ∈ A, y ≠ o → y ∈ F)
    {f : V → ℝ} (hf : G.HasFiniteEnergy f) (hfo : f o = 0) (hfF : ∀ y ∈ F, f y = 1) :
    (𝓧.P o (departureHitsTarget 𝓧 o A F)).toReal ≤ G.Energy f / G.pi o := by
  obtain ⟨y₀, hy₀⟩ := hFne
  haveI : Nontrivial V := ⟨⟨y₀, o, fun hy => hoF (hy ▸ hy₀)⟩⟩
  have hA : A.Nonempty := ⟨o, hoA⟩
  have hπ : 0 < G.pi o := G.pi_pos_of_connected hG o
  have hfA : Set.EqOn f (targetIndicator F) ↑A := by
    intro v hv
    by_cases hvo : v = o
    · subst hvo
      rw [hfo, targetIndicator_of_notMem hoF]
    · rw [hfF v (hAF v (Finset.mem_coe.1 hv) hvo),
        targetIndicator_of_mem (hAF v (Finset.mem_coe.1 hv) hvo)]
  have hmin' : G.Energy (G.energyMin hG A (targetIndicator F)) ≤ G.Energy f :=
    G.energyMin_le_energy hG hA (targetIndicator F) hf hfA
  have hid := pi_mul_measure_departureHitsTarget_eq_energy h hG ⟨y₀, hy₀⟩ hoA hoF hFA hAF
  rw [le_div_iff₀ hπ, mul_comm]
  exact hid.trans_le hmin'

end Process

end ReflectedGMS.ExcursionEnergy
