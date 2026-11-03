/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T15ACore at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.HarmonicInfinity.Mesoscopic
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Core
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Exit
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.ScaledGridControl

/-!
# T15A: [18] Lemma 3.11 — the deterministic part (grid annuli to every annulus)

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18], Lemma 3.11, in the form used by the proof of Theorem 3.9
(`[18]`, display (3.37)): with high probability, simultaneously for every centre `z` and every radius
`r ∈ [ε^β, ρ]` with `B_{2r}(z) ⊂ B_ρ(0)`, the walk started from any vertex of `V(B_r(z))` **graph-disconnects**
`V(∂B_{r/2}(z))` from `V(∂B_{2r}(z))` before hitting `V(∂B_{2r}(z))`, with quenched probability `≥ p`.

**What Theorem 3.9 needs.** Lemma 3.10 (Wilson's algorithm, `[18]`) and the maximum-principle reading of
Theorem 3.9 both consume *graph* disconnection (every graph path from `y` to `A` meets the trace): a closed chain of
visited cells that only separates topologically is not enough — two unvisited cells touching at a point of the chain
can carry an edge across it (TF3 §3.1, the crossed-diagonal example), and the hitting distribution of `A` leaks along
that edge. So nothing weaker than the frozen `LFMultigraph.Disconnects` serves, and that is what is proved here.

**Graph-disconnection form of (3.36).** The geometric step requires graph disconnection. The
annulus-disconnection estimate (`CellFamily.cellFamily_compl_of_interfaces_bad`) combines the polar-template
itinerary from [18] Lemma 3.8 with Route M template separation. It yields the `ScaledGridControl` event: from every vertex of `V(∂B_r(z))` at the grid annuli `(z, r) ∈ ε^χℤ² × ε^χℤ`, the frozen `AnnularEvent`
(graph disconnection of `V(∂B_{3r/4}(z))` from `V(∂B_{5r/4}(z))` before exiting `V(A_{r/2,3r/2}(z))`, with all cells
in `A_{r/3,5r/3}(z)`) has quenched probability `≥ p`.

This file is deterministic: on one environment where `ScaledGridControl 1 ε χ β q ρ₂ p` holds and the graph is
connected, (3.35) holds at every `(z, r, x)` (`walkLaw_lemma311Event_ge`, `lemma311Holds_of_scaledGridControl`),
under the explicit small-mesh margins `5 ε^q + 13 ε^χ ≤ ε^β` and `2 ε^q + 5 ε^χ < ρ₂ − ρ`. Proof: approximate
`(z, r)` by a grid annulus `(z', r')` with `|z − z'| ≤ ε^χ` and `r + ε^q + ε^χ ≤ r' < r + ε^q + 2ε^χ`; the walk from
`x` first hits `V(∂B_{r'}(z'))` while its cells stay in `B_{r'}(z') ⊂ B_{2r}(z)` (it exits the finite set
`V(B_{r'}(z'))` and cells cross circles); by the strong Markov property the annular event at `(z', r')` follows with
probability `≥ p`; its cells stay in `A_{r'/3,5r'/3}(z') ⊂ B_{2r}(z)`; and disconnecting the `3r'/4`- and
`5r'/4`-circles of `z'` disconnects `V(∂B_{r/2}(z))` from `V(∂B_{2r}(z))` (crossing lemma).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.T15A

open MatedCRTHarmonic Markov

variable {V E : Type*}

/-! ### The walk event of (3.35) -/

/-- **"`X` disconnects `S` from `T` before hitting `T`"** ([18] Lemma 3.10 / (3.35), `[18]`): `X` hits `T`
at a finite time `n`, and the vertices it visits strictly before `n` graph-disconnect `S` from `T` (frozen
`LFMultigraph.Disconnects`). Requiring the hit to be finite costs nothing on the recurrent mated-CRT map and makes the
event depend on a finite path prefix. -/
def DisconnectsBeforeHit (G : LFMultigraph V E) (S T : Set V) (X : ℕ → V) : Prop :=
  ∃ n : ℕ, hitTime T X = n ∧ G.Disconnects {y | ∃ m < n, X m = y} S T

/-- **The walk event of [18] (3.35)** at `(z, r)`: the walk disconnects `V(∂B_{r/2}(z))` from `V(∂B_{2r}(z))` before
hitting `V(∂B_{2r}(z))`. -/
def Lemma311Event (G : LFMultigraph V E) (J : V → Set ℂ) (z : ℂ) (r : ℝ) (X : ℕ → V) : Prop :=
  DisconnectsBeforeHit G (verticesMeeting J (sphere z (r / 2))) (verticesMeeting J (sphere z (2 * r))) X

/-- **The conclusion of [18] Lemma 3.11 on one environment** (`[18]`, display (3.35)): for every centre `z`
and radius `r ∈ [ε^β, ρ]` with `B_{2r}(z) ⊂ B_ρ(0)` and every `x ∈ V(B_r(z))`, the walk event `Lemma311Event` has
quenched probability `≥ p`. (`[18]`'s extra condition `z ∈ B_ρ(0)` follows from `B_{2r}(z) ⊂ B_ρ(0)`.) -/
def Lemma311Holds {o : V} {G : LFMultigraph V E} (H : CellularEmbedding G o) (ε ρ β p : ℝ) : Prop :=
  ∀ (z : ℂ) (r : ℝ), ε ^ β ≤ r → r ≤ ρ → ball z (2 * r) ⊆ ball (0 : ℂ) ρ →
    ∀ x ∈ verticesMeeting H.cell (ball z r),
      ENNReal.ofReal p ≤ G.walkLaw x {ξ | Lemma311Event G H.cell z r (G.vertexPath ξ)}

/-- **The environment event of [18] Lemma 3.11** at mesh `ε = 2⁻ᵏ` for a random cell family (the
`RandomCellFamily`): (3.35) holds on the `k`-th cell configuration. -/
def Lemma311Good (F : CellFamily.RandomCellFamily) (k : ℕ) (ρ β p : ℝ) : Set F.Ω :=
  {ω | Lemma311Holds (F.H k ω) (CellFamily.mesh k) ρ β p}

/-- **[18] Lemma 3.11 for a random cell family at ambient radius `ρ`**, in the project's
bad-event convention : there are `α, β, p > 0` and `C` such that, for every dyadic mesh `ε = 2⁻ᵏ`, the event that (3.35)
fails for some `(z, r, x)` has probability `≤ C ε^α`. -/
def Lemma311Bad (F : CellFamily.RandomCellFamily) (ρ : ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
    ∀ k, F.P (Lemma311Good F k ρ β p)ᶜ ≤ ENNReal.ofReal (C * CellFamily.mesh k ^ α)

/-! ### Monotonicity and measurability (for consumers: [18] Theorem 3.9,/T15C) -/

/-- (3.35) at `(ρ, β, p)` implies (3.35) at any smaller radius `ρ'`, smaller exponent `β'` (fewer radii, as
`ε ≤ 1`) and smaller probability `p'`. -/
theorem Lemma311Holds.mono {o : V} {G : LFMultigraph V E} {H : CellularEmbedding G o} {ε ρ β p ρ' β' p' : ℝ}
    (h : Lemma311Holds H ε ρ β p) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : ρ' ≤ ρ) (hβ : β' ≤ β) (hp : p' ≤ p) :
    Lemma311Holds H ε ρ' β' p' := by
  intro z r hβr hrρ hball x hx
  have hpow : ε ^ β ≤ ε ^ β' := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hβ
  exact (ENNReal.ofReal_le_ofReal hp).trans
    (h z r (hpow.trans hβr) (hrρ.trans hρ) (hball.trans (ball_subset_ball hρ)) x hx)

/-- The environment events are monotone in `(ρ, β, p)`. -/
theorem lemma311Good_mono {F : CellFamily.RandomCellFamily} {k : ℕ} {ρ β p ρ' β' p' : ℝ} (hρ : ρ' ≤ ρ)
    (hβ : β' ≤ β) (hp : p' ≤ p) : Lemma311Good F k ρ β p ⊆ Lemma311Good F k ρ' β' p' := by
  intro ω hω
  have hm0 : 0 < CellFamily.mesh k := zpow_pos (by norm_num) _
  have hm1 : CellFamily.mesh k ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
  exact Lemma311Holds.mono hω hm0 hm1 hρ hβ hp

/-- **Shrinking the constants of `Lemma311Bad`.** [18]'s proof of Theorem 3.9 takes `β < 1/(50(2+γ)²)` "without
loss of generality": any smaller `β`, smaller `α` and smaller radius are allowed. -/
theorem Lemma311Bad.shrink {F : CellFamily.RandomCellFamily} {ρ : ℝ} (h : Lemma311Bad F ρ) {ρ' β₀ α₀ : ℝ}
    (hρ : ρ' ≤ ρ) (hβ₀ : 0 < β₀) (hα₀ : 0 < α₀) :
    ∃ α : ℝ, 0 < α ∧ α ≤ α₀ ∧ ∃ β : ℝ, 0 < β ∧ β ≤ β₀ ∧ ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ k, F.P (Lemma311Good F k ρ' β p)ᶜ ≤ ENNReal.ofReal (C * CellFamily.mesh k ^ α) := by
  obtain ⟨α, hα, β, hβ, p, hp, C, hC⟩ := h
  refine ⟨min α α₀, lt_min hα hα₀, min_le_right _ _, min β β₀, lt_min hβ hβ₀, min_le_right _ _, p, hp,
    max C 0, le_max_right _ _, fun k => ?_⟩
  have hm0 : 0 < CellFamily.mesh k := zpow_pos (by norm_num) _
  have hm1 : CellFamily.mesh k ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
  calc F.P (Lemma311Good F k ρ' (min β β₀) p)ᶜ ≤ F.P (Lemma311Good F k ρ β p)ᶜ :=
        measure_mono (compl_subset_compl.mpr (lemma311Good_mono hρ (min_le_left _ _) le_rfl))
    _ ≤ ENNReal.ofReal (C * CellFamily.mesh k ^ α) := hC k
    _ ≤ ENNReal.ofReal (max C 0 * CellFamily.mesh k ^ min α α₀) := by
        apply ENNReal.ofReal_le_ofReal
        have hpow : CellFamily.mesh k ^ α ≤ CellFamily.mesh k ^ min α α₀ :=
          Real.rpow_le_rpow_of_exponent_ge hm0 hm1 (min_le_left _ _)
        have hpos : 0 ≤ CellFamily.mesh k ^ α := Real.rpow_nonneg hm0.le _
        calc C * CellFamily.mesh k ^ α ≤ max C 0 * CellFamily.mesh k ^ α :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
          _ ≤ max C 0 * CellFamily.mesh k ^ min α α₀ := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)

/-- The walk event `DisconnectsBeforeHit` is measurable on edge-end paths: it is a countable union over the hitting
time `n` of events determined by the first `n + 1` states. -/
theorem measurableSet_disconnectsBeforeHit (G : LFMultigraph V E) [Countable G.State] (S T : Set V) :
    MeasurableSet {ξ : ℕ → G.State | DisconnectsBeforeHit G S T (G.vertexPath ξ)} := by
  have hset : {ξ : ℕ → G.State | DisconnectsBeforeHit G S T (G.vertexPath ξ)} =
      ⋃ n : ℕ, {ξ | hitTime T (G.vertexPath ξ) = n ∧
        G.Disconnects {y | ∃ m < n, G.vertexPath ξ m = y} S T} := by
    ext ξ
    simp only [DisconnectsBeforeHit, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hset]
  refine MeasurableSet.iUnion fun n => GoodScales.measurableSet_of_forall_eq_le n ?_
  rintro ξ ξ' hagree ⟨hn, hd⟩
  have hv : ∀ m ≤ n, G.vertexPath ξ m = G.vertexPath ξ' m :=
    fun m hm => congrArg G.stateVertex (hagree m hm)
  refine ⟨GoodScales.hitTime_eq_of_forall_eq hn hv, ?_⟩
  have htr : {y | ∃ m < n, G.vertexPath ξ' m = y} = {y | ∃ m < n, G.vertexPath ξ m = y} := by
    ext y
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, hv m hm.le⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, (hv m hm.le).symm⟩
  rw [htr]
  exact hd

/-- The walk event of (3.35) is measurable. -/
theorem measurableSet_lemma311Event (G : LFMultigraph V E) [Countable G.State] (J : V → Set ℂ) (z : ℂ) (r : ℝ) :
    MeasurableSet {ξ : ℕ → G.State | Lemma311Event G J z r (G.vertexPath ξ)} :=
  measurableSet_disconnectsBeforeHit G _ _

/-! ### Plane geometry -/

/-- A disk inside `B_ρ(0)` satisfies `‖z‖ + s ≤ ρ`. -/
theorem norm_add_le_of_ball_subset {z : ℂ} {s ρ : ℝ} (hs : 0 < s) (h : ball z s ⊆ ball (0 : ℂ) ρ) :
    ‖z‖ + s ≤ ρ := by
  have hcl : closedBall z s ⊆ closedBall (0 : ℂ) ρ := by
    have h1 := closure_mono h
    rw [closure_ball z hs.ne'] at h1
    exact h1.trans closure_ball_subset_closedBall
  obtain ⟨u, hu1, hu⟩ : ∃ u : ℂ, ‖u‖ = 1 ∧ ‖z + (s : ℂ) * u‖ = ‖z‖ + s := by
    by_cases hz : z = 0
    · refine ⟨1, by simp, ?_⟩
      simp [hz, abs_of_pos hs]
    · have hn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
      refine ⟨z / (‖z‖ : ℂ), ?_, ?_⟩
      · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn, div_self hn.ne']
      · have hzc : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
        have heq : z + (s : ℂ) * (z / (‖z‖ : ℂ)) = (((1 + s / ‖z‖ : ℝ)) : ℂ) * z := by
          push_cast
          field_simp
        rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        field_simp
  have hmem : z + (s : ℂ) * u ∈ closedBall z s := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, hu1, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs]
  have h2 := hcl hmem
  rw [mem_closedBall, dist_zero_right, hu] at h2
  exact h2

/-- A point of the square lattice `sℤ²` within distance `s` of `z`. -/
theorem exists_lattice_near (z : ℂ) {s : ℝ} (hs : 0 < s) :
    ∃ m n : ℤ, ‖z - (s : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)‖ ≤ s := by
  refine ⟨round (z.re / s), round (z.im / s), ?_⟩
  have hcoord : ∀ t : ℝ, |t - s * (round (t / s) : ℝ)| ≤ s / 2 := by
    intro t
    have h := abs_sub_round (t / s)
    have heq : t - s * (round (t / s) : ℝ) = s * (t / s - round (t / s)) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos hs]
    nlinarith
  have hre := hcoord z.re
  have him := hcoord z.im
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h1 : (z - (s : ℂ) * (((round (z.re / s) : ℤ) : ℂ) + ((round (z.im / s) : ℤ) : ℂ) * Complex.I)).re =
      z.re - s * (round (z.re / s) : ℝ) := by
    simp
  have h2 : (z - (s : ℂ) * (((round (z.re / s) : ℤ) : ℂ) + ((round (z.im / s) : ℤ) : ℂ) * Complex.I)).im =
      z.im - s * (round (z.im / s) : ℝ) := by
    simp
  rw [h1, h2]
  linarith

/-- A radius of the grid `sℤ` in `[a, a + s)`. -/
theorem exists_grid_radius (a : ℝ) {s : ℝ} (hs : 0 < s) : ∃ k : ℤ, a ≤ s * k ∧ s * k < a + s := by
  refine ⟨⌈a / s⌉, ?_, ?_⟩
  · have h := Int.le_ceil (a / s)
    calc a = s * (a / s) := by field_simp
      _ ≤ s * (⌈a / s⌉ : ℝ) := by gcongr
  · have h := Int.ceil_lt_add_one (a / s)
    calc s * (⌈a / s⌉ : ℝ) < s * (a / s + 1) := by gcongr
      _ = a + s := by field_simp

/-- **Outward crossing lemma** (the mirror image of `GoodScales.exists_mem_sphere_of_cross`): along an admissible
vertex path, if `J (X a)` has a point at distance `≤ ρ` from `z` and `J (X (a + k))` a point at distance `≥ ρ`, some
`J (X m)` with `a ≤ m ≤ a + k` meets the circle `∂B_ρ(z)`. -/
theorem exists_mem_sphere_of_cross_out {G : LFMultigraph V E} {J : V → Set ℂ} (hJ : G.IsPlaneData J)
    {X : ℕ → V} (hX : ∀ n, GoodScales.StepOK G (X n) (X (n + 1))) {z : ℂ} {ρ : ℝ} :
    ∀ (k a : ℕ), (∃ w ∈ J (X a), dist w z ≤ ρ) → (∃ w ∈ J (X (a + k)), ρ ≤ dist w z) →
      ∃ m, a ≤ m ∧ m ≤ a + k ∧ (J (X m) ∩ sphere z ρ).Nonempty := by
  intro k
  induction k with
  | zero =>
    rintro a ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩
    exact ⟨a, le_rfl, le_rfl,
      GoodScales.inter_sphere_nonempty_of_isPreconnected (hJ.isConnected _).isPreconnected hw₂ hw₁ h₂ h₁⟩
  | succ k ih =>
    rintro a ⟨w₁, hw₁, h₁⟩ hend
    by_cases hfar : ∃ w ∈ J (X a), ρ ≤ dist w z
    · obtain ⟨w₂, hw₂, h₂⟩ := hfar
      exact ⟨a, le_rfl, by omega,
        GoodScales.inter_sphere_nonempty_of_isPreconnected (hJ.isConnected _).isPreconnected hw₂ hw₁ h₂ h₁⟩
    · push Not at hfar
      obtain ⟨w, hwa, hwb⟩ := GoodScales.inter_nonempty_of_stepOK hJ (hX a)
      have hnear : ∃ w ∈ J (X (a + 1)), dist w z ≤ ρ := ⟨w, hwb, (hfar w hwa).le⟩
      have hend' : ∃ w ∈ J (X (a + 1 + k)), ρ ≤ dist w z := by
        rw [show a + 1 + k = a + (k + 1) by omega]
        exact hend
      obtain ⟨m, hm1, hm2, hm⟩ := ih (a + 1) hnear hend'
      exact ⟨m, by omega, by omega, hm⟩

/-- **Disconnection transfer between nested circle pairs.** If `U` disconnects `V(∂B_{a₁}(c))` from
`V(∂B_{a₂}(c))` (`a₁ ≤ a₂`), every plane set of `S` has a point within `a₁` of `c` and every plane set of `T` a point
at distance `≥ a₂` from `c`, then `U` disconnects `S` from `T`. -/
theorem disconnects_of_sphere_pair {G : LFMultigraph V E} {J : V → Set ℂ} (hJ : G.IsPlaneData J)
    {U S T : Set V} {c : ℂ} {a₁ a₂ : ℝ} (ha₁₂ : a₁ ≤ a₂)
    (hdisc : G.Disconnects U (verticesMeeting J (sphere c a₁)) (verticesMeeting J (sphere c a₂)))
    (hS : ∀ a ∈ S, ∃ q ∈ J a, dist q c ≤ a₁) (hT : ∀ b ∈ T, ∃ q ∈ J b, a₂ ≤ dist q c) :
    G.Disconnects U S T := by
  classical
  intro a ha b hb w
  have hanear : ∀ ρ' : ℝ, a₁ ≤ ρ' → ∃ q ∈ J a, dist q c ≤ ρ' := fun ρ' hρ' => by
    obtain ⟨q, hq, hqc⟩ := hS a ha
    exact ⟨q, hq, hqc.trans hρ'⟩
  obtain ⟨t, ht, htS⟩ := HarmonicInfinity.exists_mem_support_sphere hJ w.reverse (ρ := a₂) (hT b hb)
    (hanear a₂ ha₁₂)
  set w₂ := w.reverse.dropUntil t ht with hw₂
  have htfar : ∃ q ∈ J t, a₁ ≤ dist q c := by
    obtain ⟨q, hq, hqs⟩ := htS
    exact ⟨q, hq, by rw [mem_sphere.mp hqs]; exact ha₁₂⟩
  obtain ⟨t', ht', ht'S⟩ := HarmonicInfinity.exists_mem_support_sphere hJ w₂ (ρ := a₁) htfar
    (hanear a₁ le_rfl)
  obtain ⟨v, hv, hvU⟩ := hdisc t' ht'S t htS (w₂.takeUntil t' ht').reverse
  refine ⟨v, ?_, hvU⟩
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
  have hv' : v ∈ w.reverse.support :=
    w.reverse.support_dropUntil_subset_support ht (w₂.support_takeUntil_subset_support ht' hv)
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv'
  exact hv'

/-! ### (3.35) from the grid annular events -/

/-- The cells of the vertices met by an open set `B` of a bounded region form a finite set. -/
theorem verticesMeeting_ball_finite {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o) (c : ℂ) (a : ℝ) :
    (verticesMeeting H.cell (ball c a)).Finite :=
  (H.locallyFinite_cell.finite_nonempty_inter_compact (isCompact_closedBall c a)).subset
    (fun _ ⟨w, hw, hwb⟩ => ⟨w, hw, ball_subset_closedBall hwb⟩)

/-- **[18] (3.35) at one annulus from the grid annular events.** On an environment where the grid
annulus-disconnection event `ScaledGridControl 1 ε χ β q ρ₂ p` holds and the graph is connected, for every `(z, r)` with
`ε^β ≤ r`, `5 ε^q + 13 ε^χ ≤ r`, `B_{2r}(z) ⊂ B_ρ(0)` and `2 ε^q + 5 ε^χ < ρ₂ − ρ`, and every `x ∈ V(B_r(z))`, the walk
from `x` disconnects `V(∂B_{r/2}(z))` from `V(∂B_{2r}(z))` before hitting `V(∂B_{2r}(z))` with probability `≥ p`. -/
theorem walkLaw_lemma311Event_ge {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hconn : G.adj.Connected) {ε χ β q ρ₂ p : ℝ} (hgrid : H.ScaledGridControl 1 ε χ β q ρ₂ p)
    (hs : 0 < ε ^ χ) (hd : 0 ≤ ε ^ q) {z : ℂ} {r ρ : ℝ} (hβr : ε ^ β ≤ r)
    (hsmall : 5 * ε ^ q + 13 * ε ^ χ ≤ r) (hroom : 2 * ε ^ q + 5 * ε ^ χ < ρ₂ - ρ)
    (hball : ball z (2 * r) ⊆ ball (0 : ℂ) ρ) {x : ℤ} (hx : x ∈ verticesMeeting H.cell (ball z r)) :
    ENNReal.ofReal p ≤ G.walkLaw x {ξ | Lemma311Event G H.cell z r (G.vertexPath ξ)} := by
  classical
  have : Countable G.State := GoodScales.countable_state G
  have hJ := CellularFacts.isPlaneData_cell H
  set s := ε ^ χ with hsdef
  set d := ε ^ q with hddef
  have hr0 : 0 < r := by linarith
  have hzρ : ‖z‖ + 2 * r ≤ ρ := norm_add_le_of_ball_subset (by linarith) hball
  have hρρ₂ : ρ < ρ₂ := by linarith
  -- the grid annulus `(z', r')`
  obtain ⟨m, n, hmn⟩ := exists_lattice_near z hs
  obtain ⟨k, hk1, hk2⟩ := exists_grid_radius (r + d + s) hs
  set z' : ℂ := ((1 * ε ^ χ : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I) with hz'
  set r' : ℝ := 1 * ε ^ χ * k with hr'
  have hzz' : dist z z' ≤ s := by
    rw [dist_eq_norm, hz', one_mul]
    exact hmn
  have hr'lo : r + d + s ≤ r' := by rw [hr', one_mul]; exact hk1
  have hr'hi : r' < r + d + 2 * s := by rw [hr', one_mul]; linarith
  have hz'norm : ‖z'‖ ≤ ‖z‖ + s := by
    have h1 : ‖z'‖ ≤ ‖z‖ + ‖z' - z‖ := by
      calc ‖z'‖ = ‖z + (z' - z)‖ := by rw [add_sub_cancel]
        _ ≤ ‖z‖ + ‖z' - z‖ := norm_add_le _ _
    have h2 : ‖z' - z‖ ≤ s := by rw [← dist_eq_norm, dist_comm]; exact hzz'
    linarith
  -- the cell-diameter bound of `ScaledGridControl`
  have hdiam : ∀ v, (H.cell v ∩ ball (0 : ℂ) ρ₂).Nonempty → diam (H.cell v) ≤ d := by
    intro v hv
    have h := hgrid.1 v (by rw [mul_one]; exact hv)
    rwa [one_mul] at h
  -- the grid annular estimate at `(z', r')`
  have hann : ∀ y ∈ verticesMeeting H.cell (sphere z' r'),
      ENNReal.ofReal p ≤ G.walkLaw y {ξ | G.AnnularEvent H.cell z' r' (G.vertexPath ξ)} := by
    have hn0 := norm_nonneg z
    refine hgrid.2 m n k ?_ ?_ ?_ ?_
    · change z' ∈ ball (0 : ℂ) (ρ₂ * 1)
      rw [mem_ball, dist_zero_right, mul_one]
      linarith
    · change 1 * ε ^ β ≤ r'
      rw [one_mul]
      linarith
    · change r' ≤ ρ₂ * 1
      rw [mul_one]
      linarith
    · change ball z' (2 * r') ⊆ ball (0 : ℂ) (ρ₂ * 1)
      apply ball_subset_ball'
      rw [dist_zero_right, mul_one]
      linarith
  -- the start cell lies in `B_{r'}(z')`
  obtain ⟨w₀, hw₀x, hw₀b⟩ := hx
  have hw₀z : dist w₀ z < r := mem_ball.mp hw₀b
  have hxsmall : diam (H.cell x) ≤ d := by
    refine hdiam x ⟨w₀, hw₀x, ?_⟩
    rw [mem_ball, dist_zero_right]
    have : dist w₀ z' < r + s := by linarith [dist_triangle w₀ z z']
    have h1 : ‖w₀‖ ≤ ‖z‖ + dist w₀ z := by
      calc ‖w₀‖ = ‖z + (w₀ - z)‖ := by rw [add_sub_cancel]
        _ ≤ ‖z‖ + ‖w₀ - z‖ := norm_add_le _ _
        _ = ‖z‖ + dist w₀ z := by rw [dist_eq_norm]
    linarith
  have hxin : ∀ u ∈ H.cell x, dist u z' < r' := by
    intro u hu
    have h1 : dist u w₀ ≤ d :=
      (Metric.dist_le_diam_of_mem (H.isCompact_cell x).isBounded hu hw₀x).trans hxsmall
    linarith [dist_triangle u w₀ z, dist_triangle u z z']
  -- the sets and times
  set S₁ : Set ℤ := verticesMeeting H.cell (sphere z' r') with hS₁
  set T : Set ℤ := verticesMeeting H.cell (sphere z (2 * r)) with hT
  set U₁ : Set ℤ := verticesMeeting H.cell (ball z' r') with hU₁
  set U₂ : Set ℤ := verticesMeeting H.cell (ball z (2 * r)) with hU₂
  set σ := hitTime (G.stateVertex ⁻¹' S₁) with hσ
  set Ann : Set (ℕ → G.State) := {ω | G.AnnularEvent H.cell z' r' (G.vertexPath ω)} with hAnn
  have hAnnMeas : MeasurableSet Ann :=
    GoodScales.measurableSet_succEvent (G := G) (J := H.cell) (z := z') (r := fun _ => r') 0
  set P := G.walkLaw x with hP
  have hexit : ∀ U : Set ℤ, U.Finite → ∀ᵐ ω ∂P, hitTime Uᶜ (G.vertexPath ω) ≠ ⊤ := by
    intro U hU
    have h1 := CellFamily.walkLaw_hitTime_compl_ne_top_of_connected hU hconn x
    exact (ae_iff_measure_eq (Harmonic.measurableSet_hitTime_ne_top G Uᶜ).nullMeasurableSet).mpr
      (by rw [h1, measure_univ])
  have hgood : ∀ᵐ ω ∂P, ω 0 = Harmonic.startState G x ∧
      (∀ n, GoodScales.StepOK G (G.vertexPath ω n) (G.vertexPath ω (n + 1))) ∧
      hitTime U₁ᶜ (G.vertexPath ω) ≠ ⊤ ∧ hitTime U₂ᶜ (G.vertexPath ω) ≠ ⊤ := by
    filter_upwards [GoodScales.ae_start_and_stepOK G (Harmonic.startState G x),
      hexit U₁ (verticesMeeting_ball_finite H z' r'), hexit U₂ (verticesMeeting_ball_finite H z (2 * r))]
      with ω h1 h2 h3
    exact ⟨h1.1, h1.2, h2, h3⟩
  -- pathwise geometry on good paths
  have hX0 : ∀ ω : ℕ → G.State, ω 0 = Harmonic.startState G x → G.vertexPath ω 0 = x := by
    intro ω h0
    show G.stateVertex (ω 0) = x
    rw [h0]
    rfl
  obtain ⟨u₀, hu₀⟩ := (H.isConnected_cell x).nonempty
  have hσfin : ∀ ω : ℕ → G.State, ω 0 = Harmonic.startState G x →
      (∀ n, GoodScales.StepOK G (G.vertexPath ω n) (G.vertexPath ω (n + 1))) →
      hitTime U₁ᶜ (G.vertexPath ω) ≠ ⊤ → σ ω < ⊤ := by
    intro ω h0 hstep hE
    obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hE
    have hXe : G.vertexPath ω e ∈ U₁ᶜ := (hitTime_eq_coe_iff.mp he.symm).1
    obtain ⟨u, hu⟩ := (H.isConnected_cell (G.vertexPath ω e)).nonempty
    have hufar : r' ≤ dist u z' := by
      by_contra hlt
      push Not at hlt
      exact hXe ⟨u, hu, mem_ball.mpr hlt⟩
    have hnear : ∃ w ∈ H.cell (G.vertexPath ω 0), dist w z' ≤ r' :=
      ⟨u₀, by rw [hX0 ω h0]; exact hu₀, (hxin u₀ hu₀).le⟩
    obtain ⟨j, -, -, hj⟩ := exists_mem_sphere_of_cross_out hJ hstep e 0 hnear
      ⟨u, by rw [Nat.zero_add]; exact hu, hufar⟩
    exact lt_of_le_of_lt (hitTime_le_of_mem (A := G.stateVertex ⁻¹' S₁) (ω := ω) hj)
      (ENat.natCast_lt_top j)
  have hσ1 : P {ω | σ ω < ⊤} = 1 := by
    refine le_antisymm prob_le_one ?_
    rw [← measure_univ (μ := P)]
    refine measure_mono_ae ?_
    filter_upwards [hgood] with ω ⟨h0, hstep, hE1, _⟩ _
    exact hσfin ω h0 hstep hE1
  -- strong Markov at `σ`
  have hSM : ENNReal.ofReal p ≤ P ({ω | σ ω < ⊤} ∩ stopShift σ ⁻¹' Ann) := by
    have h := le_chainLaw_inter_stopShift_preimage G.walkKernel (Harmonic.startState G x)
      (isStoppingTime_hitTime (A := G.stateVertex ⁻¹' S₁) MeasurableSet.of_discrete)
      (F := Set.univ) MeasurableSet.univ hAnnMeas (p := ENNReal.ofReal p) ?_
    · rw [Set.univ_inter] at h
      have h' : ENNReal.ofReal p * P {ω | σ ω < ⊤} ≤ P ({ω | σ ω < ⊤} ∩ stopShift σ ⁻¹' Ann) := h
      rwa [hσ1, mul_one] at h'
    · rintro ω ⟨-, hlt⟩
      have hmem : stopState σ ω ∈ G.stateVertex ⁻¹' S₁ := stopState_hitTime_mem hlt.ne
      calc ENNReal.ofReal p ≤ G.walkLaw (G.stateVertex (stopState σ ω)) Ann := hann _ hmem
        _ = chainLaw G.walkKernel (stopState σ ω) Ann :=
          GoodScales.chainLaw_vertexEvent_eq G (s := Sum.inl (G.stateVertex (stopState σ ω)))
            (s' := stopState σ ω) rfl (Q := fun X => G.AnnularEvent H.cell z' r' X) hAnnMeas
  refine hSM.trans (measure_mono_ae ?_)
  filter_upwards [hgood] with ω ⟨h0, hstep, _, hE2⟩ ⟨hlt, hAω⟩
  set X := G.vertexPath ω with hX
  have hX0' : X 0 = x := hX0 ω h0
  obtain ⟨s₀, hs₀⟩ := ENat.ne_top_iff_exists.mp (show σ ω < ⊤ from hlt).ne
  have hσX : hitTime S₁ X = s₀ := hs₀.symm
  -- before `σ`: the cells stay in `B_{r'}(z')`
  have hbefore : ∀ j < s₀, ∀ u ∈ H.cell (X j), dist u z' < r' := by
    intro j hj u hu
    by_contra hge
    push Not at hge
    have hnear : ∃ w ∈ H.cell (X 0), dist w z' ≤ r' :=
      ⟨u₀, by rw [hX0']; exact hu₀, (hxin u₀ hu₀).le⟩
    obtain ⟨i, -, hij, hi⟩ := exists_mem_sphere_of_cross_out hJ hstep j 0 hnear
      ⟨u, by rw [Nat.zero_add]; exact hu, hge⟩
    have hle : hitTime S₁ X ≤ i := hitTime_le_of_mem (A := S₁) hi
    rw [hσX] at hle
    have : s₀ ≤ i := by exact_mod_cast hle
    omega
  -- after `σ`: the annular event at `(z', r')`
  have hA' : G.AnnularEvent H.cell z' r' (G.vertexPath (walkShift s₀ ω)) := by
    have h := (show stopShift σ ω ∈ Ann from hAω)
    rw [stopShift_eq_of_eq hs₀.symm] at h
    exact h
  obtain ⟨τ, hτ, hdisc, hcont⟩ := hA'
  have hshift : ∀ i, G.vertexPath (walkShift s₀ ω) i = X (s₀ + i) := fun i => rfl
  -- no vertex up to `σ + τ` meets `∂B_{2r}(z)`
  have hnotT : ∀ j ≤ s₀ + τ, X j ∉ T := by
    rintro j hj ⟨u, hu, huT⟩
    have huz : dist u z = 2 * r := mem_sphere.mp huT
    by_cases hjs : j < s₀
    · have h1 := hbefore j hjs u hu
      linarith [dist_triangle u z' z, dist_comm z z']
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hjs)
      have hi : i ≤ τ := by omega
      have hcell := hcont i hi (by rw [hshift]; exact hu)
      have hu' : dist u z' < 5 * r' / 3 := by
        rw [annulus, Set.mem_sdiff, mem_ball] at hcell
        exact hcell.1
      linarith [dist_triangle u z' z, dist_comm z z']
  -- the walk hits `V(∂B_{2r}(z))` at a finite time, after `σ + τ`
  obtain ⟨e₂, he₂⟩ := ENat.ne_top_iff_exists.mp hE2
  have hTfin : hitTime T X ≠ ⊤ := by
    have hXe : X e₂ ∈ U₂ᶜ := (hitTime_eq_coe_iff.mp he₂.symm).1
    obtain ⟨u, hu⟩ := (H.isConnected_cell (X e₂)).nonempty
    have hufar : 2 * r ≤ dist u z := by
      by_contra hlt'
      push Not at hlt'
      exact hXe ⟨u, hu, mem_ball.mpr hlt'⟩
    have hnear : ∃ w ∈ H.cell (X 0), dist w z ≤ 2 * r :=
      ⟨w₀, by rw [hX0']; exact hw₀x, by linarith⟩
    obtain ⟨j, -, -, hj⟩ := exists_mem_sphere_of_cross_out hJ hstep e₂ 0 hnear
      ⟨u, by rw [Nat.zero_add]; exact hu, hufar⟩
    exact (lt_of_le_of_lt (hitTime_le_of_mem (A := T) (ω := X) hj) (ENat.natCast_lt_top j)).ne
  obtain ⟨nT, hnT⟩ := ENat.ne_top_iff_exists.mp hTfin
  have hnTgt : s₀ + τ < nT := by
    by_contra hle
    push Not at hle
    exact hnotT nT hle (hitTime_eq_coe_iff.mp hnT.symm).1
  refine ⟨nT, hnT.symm, ?_⟩
  -- disconnection: the trace before `σ + τ` contains the annular loop
  have hsub : {y | ∃ i < τ, G.vertexPath (walkShift s₀ ω) i = y} ⊆ {y | ∃ i < nT, X i = y} := by
    rintro y ⟨i, hi, rfl⟩
    exact ⟨s₀ + i, by omega, rfl⟩
  have hdisc' := CellFamily.disconnects_mono hsub hdisc
  refine disconnects_of_sphere_pair hJ (by linarith) hdisc' ?_ ?_
  · rintro a ⟨u, hu, hus⟩
    refine ⟨u, hu, ?_⟩
    have huz : dist u z = r / 2 := mem_sphere.mp hus
    linarith [dist_triangle u z z']
  · rintro b ⟨u, hu, hus⟩
    refine ⟨u, hu, ?_⟩
    have huz : dist u z = 2 * r := mem_sphere.mp hus
    linarith [dist_triangle u z' z, dist_comm z z']

/-- **[18] (3.35) on one environment** (`Lemma311Holds`), from the grid annulus-disconnection event and graph
connectivity, under the small-mesh margins `5 ε^q + 13 ε^χ ≤ ε^β` and `2 ε^q + 5 ε^χ < ρ₂ − ρ`. -/
theorem lemma311Holds_of_scaledGridControl {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hconn : G.adj.Connected) {ε χ β q ρ₂ p ρ : ℝ} (hgrid : H.ScaledGridControl 1 ε χ β q ρ₂ p)
    (hs : 0 < ε ^ χ) (hd : 0 ≤ ε ^ q) (hsmall : 5 * ε ^ q + 13 * ε ^ χ ≤ ε ^ β)
    (hroom : 2 * ε ^ q + 5 * ε ^ χ < ρ₂ - ρ) : Lemma311Holds H ε ρ β p :=
  fun _ _ hβr _ hball _ hx =>
    walkLaw_lemma311Event_ge H hconn hgrid hs hd hβr (hsmall.trans hβr) hroom hball hx

end MatedCRTHarmonic.GMSMain.T15A
