/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SojournSquaredJumpIdentity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.SojournExitLaw
import LatticeProb.Bonanno.ReflectedGMS.Forms.ExponentialTruncatedMean
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexCarreDuChamp

/-!
# The squared jump of one sojourn versus its occupation of the horizon

For a sojourn at `x` started at the completed stopping time `τ` and ending at the exit time
`ρ`, and a horizon `T`, the expected squared edge jump `(u(X_ρ) − u(x))²` **counted only if the
sojourn ends before `T`** equals the carré du champ `Γ(u)(x)` times the expected Lebesgue length
of `[τ, ρ) ∩ [0, T]`:

  `E_z[(u(X_ρ) − u x)² · 1_{ρ ≤ T}; X_τ = x] = Γ(u)(x) · E_z[|[τ,ρ) ∩ [0,T]|; X_τ = x]`.

This is exact for every horizon and every start.  Given the joint law of `(τ, ρ − τ, X_ρ)`
(`SojournExitLaw.lintegral_exitTriple`) it reduces, `τ = s` being frozen, to the one-variable
identity `∑_v (c(x,v)/π(x)) (u v − u x)² · P(L ≤ T − s) = Γ(u)(x) · E[min(L, T − s)]` for
`L ~ Exponential(π(x)/m(x))`, which is `ExponentialTruncatedMean` together with
`Γ(u)(x) = (π(x)/m(x)) · ∑_v (c(x,v)/π(x)) (u v − u x)²`.

This is the **lower** half of the energy budget for the nonvertex-time continuity of the
full-energy potential paths.  No compensator, Lévy system or bracket is asserted.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.SojournSquaredJumpIdentity

open ReflectedWalk ReflectedWalk.Theorem16 SojournExitLaw ExponentialTruncatedMean

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-! ## The two functionals of the exit triple -/

/-- The squared jump of `u` from `x` into a state, zero at the collapsed end state. -/
noncomputable def stateJumpSq (u : V → ℝ) (x : V) : Option V → ℝ≥0∞
  | some v => ENNReal.ofReal ((u v - u x) ^ 2)
  | none => 0

theorem measurable_stateJumpSq (u : V → ℝ) (x : V) : Measurable (stateJumpSq u x) :=
  measurable_of_countable _

/-- The exit-probability-weighted squared jump `∑_v (c(x,v)/π(x)) (u v − u x)²`. -/
noncomputable def exitJumpSq (G : ConductanceGraph V) (u : V → ℝ) (x : V) : ℝ≥0∞ :=
  ∑' v : V, ENNReal.ofReal (G.c x v / G.pi x) * ENNReal.ofReal ((u v - u x) ^ 2)

/-- `∑_v (c(x,v)/π(x)) (u v − u x)² = Γ(u)(x) · (m x / π x)`. -/
theorem exitJumpSq_eq (G : ConductanceGraph V) (hG : G.toSimpleGraph.Connected) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) {u : V → ℝ} (hu : G.HasFiniteEnergy u) (x : V) :
    exitJumpSq G u x =
      ENNReal.ofReal (vertexCarreDuChamp G m u x) * ENNReal.ofReal (1 / (G.pi x / m x)) := by
  have hπ : 0 < G.pi x := G.pi_pos_of_connected hG x
  have hm0 : m x ≠ 0 := (hm x).ne'
  have hπ0 : G.pi x ≠ 0 := hπ.ne'
  have hsum := summable_vertexCarreDuChamp_row G m hu x
  rw [← ENNReal.ofReal_mul (vertexCarreDuChamp_nonneg G m hm u x), vertexCarreDuChamp,
    ← hsum.tsum_mul_right, ENNReal.ofReal_tsum_of_nonneg ?_ (hsum.mul_right _)]
  · refine tsum_congr fun v => ?_
    rw [← ENNReal.ofReal_mul (div_nonneg (G.c_nonneg x v) hπ.le)]
    congr 1
    field_simp
  · intro v
    exact mul_nonneg (mul_nonneg (div_nonneg (G.c_nonneg x v) (hm x).le) (sq_nonneg _))
      (div_nonneg zero_le_one (div_nonneg hπ.le (hm x).le))

theorem exitJumpSq_ne_top (G : ConductanceGraph V) (hG : G.toSimpleGraph.Connected) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) {u : V → ℝ} (hu : G.HasFiniteEnergy u) (x : V) :
    exitJumpSq G u x ≠ ∞ := by
  rw [exitJumpSq_eq G hG m hm hu x]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- `(u(exit) − u x)² · 1_{start + holding ≤ T}`, as a functional of the exit triple. -/
noncomputable def jumpFunctional (u : V → ℝ) (x : V) (T : ℝ≥0) :
    ℝ≥0∞ × (ℝ≥0∞ × Option V) → ℝ≥0∞ :=
  fun p => stateJumpSq u x p.2.2 * (Iic (T : ℝ≥0∞)).indicator 1 (p.1 + p.2.1)

/-- The Lebesgue length of `[start, start + holding) ∩ [0, T]`, as a functional of the exit
triple. -/
noncomputable def lengthFunctional (T : ℝ≥0) : ℝ≥0∞ × (ℝ≥0∞ × Option V) → ℝ≥0∞ :=
  fun p => min (p.1 + p.2.1) (T : ℝ≥0∞) - min p.1 (T : ℝ≥0∞)

theorem measurable_jumpFunctional (u : V → ℝ) (x : V) (T : ℝ≥0) :
    Measurable (jumpFunctional u x T) := by
  have hadd : Measurable (fun p : ℝ≥0∞ × (ℝ≥0∞ × Option V) => p.1 + p.2.1) :=
    measurable_fst.add (measurable_fst.comp measurable_snd)
  exact ((measurable_stateJumpSq u x).comp (measurable_snd.comp measurable_snd)).mul
    ((measurable_one.indicator measurableSet_Iic).comp hadd)

theorem measurable_lengthFunctional (T : ℝ≥0) :
    Measurable (lengthFunctional (V := V) T) := by
  have hadd : Measurable (fun p : ℝ≥0∞ × (ℝ≥0∞ × Option V) => p.1 + p.2.1) :=
    measurable_fst.add (measurable_fst.comp measurable_snd)
  exact (hadd.min measurable_const).sub (measurable_fst.min measurable_const)

/-! ## The one-variable identity -/

/-- `s + l ≤ T ↔ l ≤ T − s` for `s ≤ T` finite. -/
theorem add_le_iff_le_sub {s l T : ℝ≥0∞} (hsT : s ≤ T) (hs : s ≠ ∞) :
    s + l ≤ T ↔ l ≤ T - s := by
  constructor
  · intro h
    calc l = s + l - s := (ENNReal.add_sub_cancel_left hs).symm
      _ ≤ T - s := tsub_le_tsub_right h s
  · intro h
    calc s + l ≤ s + (T - s) := add_le_add le_rfl h
      _ = T := add_tsub_cancel_of_le hsT

/-- `min (s + l) T − min s T = min l (T − s)` for `s ≤ T` finite. -/
theorem min_add_sub_min {s l T : ℝ≥0∞} (hsT : s ≤ T) (hs : s ≠ ∞) :
    min (s + l) T - min s T = min l (T - s) := by
  rw [min_eq_left hsT]
  have hmin : min (s + l) T = s + min l (T - s) := by
    rw [← min_add_add_left, add_tsub_cancel_of_le hsT]
  rw [hmin, ENNReal.add_sub_cancel_left hs]

/-- The holding-time law of property (iii), typed as a measure on `ℝ≥0∞` so that all
arithmetic below uses the `ℝ≥0∞` instances. -/
noncomputable def holdingLaw (r : ℝ) : Measure ℝ≥0∞ := (expMeasure r).map toWithTop

theorem lintegral_min_holdingLaw {r : ℝ} (hr : 0 < r) (c : ℝ≥0) :
    (∫⁻ l, min l (c : ℝ≥0∞) ∂holdingLaw r) =
      ENNReal.ofReal (1 / r) * holdingLaw r (Iic (c : ℝ≥0∞)) :=
  lintegral_min_map_toWithTop_expMeasure hr c

/-- The inner identity, with the start time frozen at `a`. -/
theorem lintegral_inner_eq (G : ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (m : V → ℝ) (hm : ∀ v, 0 < m v) {u : V → ℝ} (hu : G.HasFiniteEnergy u) (x : V) (T : ℝ≥0)
    (a : ℝ≥0∞) :
    (∫⁻ l, ∑' v : V, ENNReal.ofReal (G.c x v / G.pi x) * jumpFunctional u x T (a, (l, some v))
        ∂holdingLaw (G.pi x / m x)) =
      ENNReal.ofReal (vertexCarreDuChamp G m u x) *
        ∫⁻ l, ∑' v : V, ENNReal.ofReal (G.c x v / G.pi x) * lengthFunctional T (a, (l, some v))
          ∂holdingLaw (G.pi x / m x) := by
  have hw : 0 < G.pi x / m x := div_pos (G.pi_pos_of_connected hG x) (hm x)
  have hJ : ∀ (l : ℝ≥0∞) (v : V), ENNReal.ofReal (G.c x v / G.pi x) *
      jumpFunctional u x T (a, (l, some v)) =
      (ENNReal.ofReal (G.c x v / G.pi x) * ENNReal.ofReal ((u v - u x) ^ 2)) *
        (Iic (T : ℝ≥0∞)).indicator 1 (a + l) := by
    intro l v
    simp only [jumpFunctional, stateJumpSq, mul_assoc]
  have hLen : ∀ l : ℝ≥0∞, (∑' v : V, ENNReal.ofReal (G.c x v / G.pi x) *
      lengthFunctional T (a, (l, some v))) = min (a + l) (T : ℝ≥0∞) - min a (T : ℝ≥0∞) := by
    intro l
    simp only [lengthFunctional]
    rw [ENNReal.tsum_mul_right, tsum_ofReal_exit_eq_one G hG x, one_mul]
  simp_rw [hJ, ENNReal.tsum_mul_right, hLen]
  change (∫⁻ l, exitJumpSq G u x * (Iic (T : ℝ≥0∞)).indicator 1 (a + l)
    ∂holdingLaw (G.pi x / m x)) = _
  rw [lintegral_const_mul' _ _ (exitJumpSq_ne_top G hG m hm hu x)]
  have hind : ∀ l : ℝ≥0∞, (Iic (T : ℝ≥0∞)).indicator (1 : ℝ≥0∞ → ℝ≥0∞) (a + l) =
      ({l : ℝ≥0∞ | a + l ≤ (T : ℝ≥0∞)} : Set ℝ≥0∞).indicator (1 : ℝ≥0∞ → ℝ≥0∞) l := by
    intro l
    by_cases hl : a + l ≤ (T : ℝ≥0∞)
    · have h1 : (Iic (T : ℝ≥0∞)).indicator (1 : ℝ≥0∞ → ℝ≥0∞) (a + l) = 1 :=
        indicator_of_mem (mem_Iic.2 hl) _
      have h2 : ({l : ℝ≥0∞ | a + l ≤ (T : ℝ≥0∞)} : Set ℝ≥0∞).indicator
          (1 : ℝ≥0∞ → ℝ≥0∞) l = 1 :=
        indicator_of_mem (show l ∈ {l : ℝ≥0∞ | a + l ≤ (T : ℝ≥0∞)} from hl) _
      rw [h1, h2]
    · have h1 : (Iic (T : ℝ≥0∞)).indicator (1 : ℝ≥0∞ → ℝ≥0∞) (a + l) = 0 :=
        indicator_of_notMem (fun hh => hl (mem_Iic.1 hh)) _
      have h2 : ({l : ℝ≥0∞ | a + l ≤ (T : ℝ≥0∞)} : Set ℝ≥0∞).indicator
          (1 : ℝ≥0∞ → ℝ≥0∞) l = 0 :=
        indicator_of_notMem (show l ∉ {l : ℝ≥0∞ | a + l ≤ (T : ℝ≥0∞)} from hl) _
      rw [h1, h2]
  simp_rw [hind]
  have hmeas : MeasurableSet {l : ℝ≥0∞ | a + l ≤ (T : ℝ≥0∞)} :=
    (measurable_const.add measurable_id) measurableSet_Iic
  rw [lintegral_indicator_one hmeas]
  rcases le_or_gt a (T : ℝ≥0∞) with haT | haT
  · -- the sojourn starts before the horizon
    have ha : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top haT
    -- take the witness through the `ℝ≥0∞` coercion (not `WithTop.ne_top_iff_exists`, whose
    -- `WithTop.some` is defeq to but syntactically different from `(· : ℝ≥0∞)`, which blocks `rw`)
    obtain ⟨b, rfl⟩ : ∃ b : ℝ≥0, (b : ℝ≥0∞) = a := ⟨a.toNNReal, ENNReal.coe_toNNReal ha⟩
    have hbT : b ≤ T := ENNReal.coe_le_coe.1 haT
    have hset : {l : ℝ≥0∞ | (b : ℝ≥0∞) + l ≤ (T : ℝ≥0∞)} = Iic ((T - b : ℝ≥0) : ℝ≥0∞) := by
      ext l
      simp only [mem_setOf_eq, mem_Iic]
      rw [ENNReal.coe_sub]
      exact add_le_iff_le_sub haT ha
    have hlen : ∀ l : ℝ≥0∞, min ((b : ℝ≥0∞) + l) (T : ℝ≥0∞) - min (b : ℝ≥0∞) (T : ℝ≥0∞) =
        min l ((T - b : ℝ≥0) : ℝ≥0∞) := by
      intro l
      rw [min_add_sub_min haT ha, ENNReal.coe_sub]
    simp_rw [hlen]
    rw [hset, lintegral_min_holdingLaw hw (T - b), exitJumpSq_eq G hG m hm hu x, mul_assoc]
  · -- the sojourn starts after the horizon: both sides vanish
    have hset : {l : ℝ≥0∞ | a + l ≤ (T : ℝ≥0∞)} = ∅ := by
      ext l
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le haT le_self_add
    have hlen : ∀ l : ℝ≥0∞, min (a + l) (T : ℝ≥0∞) - min a (T : ℝ≥0∞) = 0 := by
      intro l
      rw [min_eq_right (haT.le.trans le_self_add), min_eq_right haT.le, tsub_self]
    simp_rw [hlen]
    rw [hset, measure_empty, mul_zero, lintegral_zero, mul_zero]

/-! ## The per-sojourn identity -/

section Process

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF) (hG : G.toSimpleGraph.Connected)
  (hm : ∀ v, 0 < m v) (z x : V)
  {τ : PF.Ω → WithTop ℝ≥0} (hτm : AEMeasurable τ (PF.P z))
  (hτ : IsAEStoppingTime PF.naturalFiltration (PF.P z) τ)
  {u : V → ℝ} (hu : G.HasFiniteEnergy u) (T : ℝ≥0)

include h hG hm hτm hτ hu

/-- **The expected squared edge jump of a sojourn ending before the horizon equals the carré du
champ times the expected length of the sojourn inside the horizon.** -/
theorem lintegral_sojourn_jumpSq_eq :
    (∫⁻ ω in stopEvent PF.X τ x,
        stateJumpSq u x (stoppedValue PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) ω) *
          (Iic (T : ℝ≥0∞)).indicator 1
            (hitAfter PF.X {s : Option V | s ≠ some x} τ ω : ℝ≥0∞) ∂PF.P z) =
      ENNReal.ofReal (vertexCarreDuChamp G m u x) *
        ∫⁻ ω in stopEvent PF.X τ x,
          (min (hitAfter PF.X {s : Option V | s ≠ some x} τ ω : ℝ≥0∞) (T : ℝ≥0∞) -
            min (τ ω : ℝ≥0∞) (T : ℝ≥0∞)) ∂PF.P z := by
  have hτρ : ∀ ω, (τ ω : ℝ≥0∞) + ((hitAfter PF.X {s : Option V | s ≠ some x} τ ω : ℝ≥0∞) -
      (τ ω : ℝ≥0∞)) = (hitAfter PF.X {s : Option V | s ≠ some x} τ ω : ℝ≥0∞) :=
    fun ω => add_tsub_cancel_of_le (le_hitAfter ω)
  -- `exitTriple` lives in `WithTop ℝ≥0` and the functionals in `ℝ≥0∞`; the two are definitionally
  -- equal but not reducibly so, hence the explicit `show` (a `rw` under `simp only [exitTriple]`
  -- produces a goal that is not type-correct at reducible transparency).
  have hL : ∀ ω, stateJumpSq u x (stoppedValue PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) ω) *
      (Iic (T : ℝ≥0∞)).indicator 1 (hitAfter PF.X {s : Option V | s ≠ some x} τ ω : ℝ≥0∞) =
      jumpFunctional u x T (exitTriple PF.X x τ ω) := by
    intro ω
    show stateJumpSq u x (stoppedValue PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) ω) *
        (Iic (T : ℝ≥0∞)).indicator 1 (hitAfter PF.X {s : Option V | s ≠ some x} τ ω : ℝ≥0∞) =
        stateJumpSq u x (stoppedValue PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) ω) *
          (Iic (T : ℝ≥0∞)).indicator 1
            ((τ ω : ℝ≥0∞) + ((hitAfter PF.X {s : Option V | s ≠ some x} τ ω : ℝ≥0∞) -
              (τ ω : ℝ≥0∞)))
    rw [hτρ ω]
  have hR : ∀ ω, (min (hitAfter PF.X {s : Option V | s ≠ some x} τ ω : ℝ≥0∞) (T : ℝ≥0∞) -
      min (τ ω : ℝ≥0∞) (T : ℝ≥0∞)) = lengthFunctional T (exitTriple PF.X x τ ω) := by
    intro ω
    show (min (hitAfter PF.X {s : Option V | s ≠ some x} τ ω : ℝ≥0∞) (T : ℝ≥0∞) -
        min (τ ω : ℝ≥0∞) (T : ℝ≥0∞)) =
        min ((τ ω : ℝ≥0∞) + ((hitAfter PF.X {s : Option V | s ≠ some x} τ ω : ℝ≥0∞) -
          (τ ω : ℝ≥0∞))) (T : ℝ≥0∞) - min (τ ω : ℝ≥0∞) (T : ℝ≥0∞)
    rw [hτρ ω]
  rw [lintegral_congr hL, lintegral_congr hR,
    lintegral_exitTriple h hG z x hτm hτ _ (measurable_jumpFunctional u x T),
    lintegral_exitTriple h hG z x hτm hτ _ (measurable_lengthFunctional T),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ω => ?_
  exact lintegral_inner_eq G hG m hm hu x T (τ ω)

end Process

end ReflectedGMS.SojournSquaredJumpIdentity
