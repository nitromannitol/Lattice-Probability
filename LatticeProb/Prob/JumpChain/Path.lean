import LatticeProb.Prob.JumpChain.Position
import LatticeProb.Prob.Cadlag.Measurable
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Piecewise
import Mathlib.Order.Interval.Set.Monotone

/-!
# Càdlàg realizations of regular jump histories

Positive holding intervals and nonexplosion give right continuity and left limits after
any embedding of the states in a normed group. Each evaluation of the resulting path
is measurable for a countable discrete measurable state space. Ring counts and terminal-ring
flags give measurable strata; a time change matching their ring times aligns the paths.
-/

namespace LatticeProb.JumpChain

open MeasureTheory Set Filter Topology Cadlag

noncomputable section

variable {S E : Type*} [NormedAddCommGroup E]

namespace RegularHistory

/-- Every regular history gives a càdlàg path after an arbitrary state embedding. -/
theorem isCadlag_position (h : RegularHistory S) (ι : S → E) (T : ℝ) :
    IsCadlag T (fun t : Icc (0 : ℝ) T => ι (h.position (Real.toNNReal t))) := by
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := discreteTopology_bot S
  have hι : Continuous ι := continuous_of_discreteTopology
  have hc : Continuous (fun t : Icc (0 : ℝ) T => Real.toNNReal (t : ℝ)) :=
    continuous_real_toNNReal.comp continuous_subtype_val
  constructor
  · intro t _
    have ht : Tendsto (fun s : Icc (0 : ℝ) T => Real.toNNReal (s : ℝ))
        (𝓝[{s | t ≤ s}] t) (𝓝[≥] (Real.toNNReal (t : ℝ))) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hc.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact Real.toNNReal_le_toNNReal hs
    have hp : Tendsto h.position (𝓝[≥] (Real.toNNReal (t : ℝ)))
        (𝓝 (h.position (Real.toNNReal (t : ℝ)))) :=
      h.continuousWithinAt_position_right _
    exact (hι.tendsto _).comp (hp.comp ht)
  · intro t hpos
    obtain ⟨z, hz⟩ := h.exists_leftLimit_position (Real.toNNReal (t : ℝ))
    refine ⟨ι z, (hι.tendsto _).comp (hz.comp ?_)⟩
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hc.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (Real.toNNReal_lt_toNNReal_iff hpos).mpr hs

/-- A regular history as a càdlàg path on the specified closed time interval. -/
def path (h : RegularHistory S) (ι : S → E) (T : ℝ) : D T E :=
  ⟨_, h.isCadlag_position ι T⟩

/-- The path constructor preserves the actual embedded position at each time. -/
@[simp] theorem path_apply (h : RegularHistory S) (ι : S → E) (T : ℝ)
    (t : Icc (0 : ℝ) T) :
    (h.path ι T).1 t = ι (h.position (Real.toNNReal (t : ℝ))) := rfl

/-- At time zero the constructed path takes the embedded initial state. -/
theorem path_initial (h : RegularHistory S) (ι : S → E) (T : ℝ) (hT : 0 ≤ T) :
    (h.path ι T).1 ⟨0, le_rfl, hT⟩ = ι (h.val 0).1 := by
  simp only [path_apply, Real.toNNReal_zero, h.position_zero]

/-- Every evaluation of the constructed path is measurable. -/
theorem measurable_path_eval [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] [MeasurableSpace E]
    (ι : S → E) (T : ℝ) (t : Icc (0 : ℝ) T) :
    Measurable (fun h : RegularHistory S => (h.path ι T).1 t) :=
  (measurable_of_countable ι).comp (measurable_position (Real.toNNReal (t : ℝ)))

/-- With no ring before the horizon, the entire path is the initial constant path. -/
theorem path_eq_const_of_ringCount_eq_zero (h : RegularHistory S) (ι : S → E)
    (T : ℝ) (hn : h.ringCount (Real.toNNReal T) = 0) :
    h.path ι T = const T (ι (h.val 0).1) := by
  apply Subtype.ext
  funext t
  have ht : Real.toNNReal (t : ℝ) ≤ Real.toNNReal T :=
    Real.toNNReal_le_toNNReal t.property.2
  have hcount : h.ringCount (Real.toNNReal (t : ℝ)) = 0 := by
    have := h.ringCount_le ht
    omega
  simp only [path_apply, position, hcount, const_apply]

/-- At a nonpositive horizon the path is constant, including the empty time interval. -/
theorem path_eq_const_of_nonpos (h : RegularHistory S) (ι : S → E)
    {T : ℝ} (hT : T ≤ 0) : h.path ι T = const T (ι (h.val 0).1) := by
  apply h.path_eq_const_of_ringCount_eq_zero
  rw [Real.toNNReal_of_nonpos hT, h.ringCount_zero]

/-- The full J1-valued path map is measurable at every nonpositive horizon. -/
theorem measurable_path_of_nonpos [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (ι : S → E) {T : ℝ} (hT : T ≤ 0) :
    Measurable (fun h : RegularHistory S => h.path ι T) := by
  have hstate : Measurable (fun h : RegularHistory S => (h.val 0).1) :=
    ((measurable_pi_apply 0).comp measurable_subtype_coe).fst
  have hm := (measurable_of_countable (fun s : S => const T (ι s))).comp hstate
  convert hm using 1
  funext h
  exact h.path_eq_const_of_nonpos ι hT

/-- Fixing the ring count and the terminal-ring flag gives a measurable stratum. -/
theorem measurableSet_path_stratum [MeasurableSpace S] (T : ℝ) (n : ℕ)
    (terminal : Bool) :
    MeasurableSet {h : RegularHistory S |
      h.ringCount (Real.toNNReal T) = n ∧ (jumpTime h.val n = T ↔ terminal = true)} := by
  have hn := measurableSet_eq_fun (measurable_ringCount (S := S) (Real.toNNReal T))
    (measurable_const (a := n))
  have ht : MeasurableSet {h : RegularHistory S | jumpTime h.val n = T} :=
    measurableSet_eq_fun
    ((measurable_jumpTime (S := S) n).comp measurable_subtype_coe)
    (measurable_const (a := T))
  cases terminal
  · simp only [Bool.false_eq_true, iff_false]
    exact hn.inter ht.compl
  · simp only [iff_true]
    exact hn.inter ht

/-- The finite tuple of states used before a fixed ring index is measurable. -/
theorem measurable_state_prefix [MeasurableSpace S] (n : ℕ) :
    Measurable (fun h : RegularHistory S => fun k : Fin (n + 1) => (h.val k).1) := by
  apply measurable_pi_lambda
  intro k
  exact ((measurable_pi_apply k.val).comp measurable_subtype_coe).fst

/-- Each clock stratum can be further partitioned by its finite state tuple measurably. -/
theorem measurableSet_path_stratum_states [MeasurableSpace S]
    [MeasurableSingletonClass S] (T : ℝ) (n : ℕ) (terminal : Bool)
    (states : Fin (n + 1) → S) :
    MeasurableSet {h : RegularHistory S |
      (h.ringCount (Real.toNNReal T) = n ∧
        (jumpTime h.val n = T ↔ terminal = true)) ∧
      (fun k : Fin (n + 1) => (h.val k).1) = states} :=
  (measurableSet_path_stratum T n terminal).inter
    ((measurable_state_prefix n) (measurableSet_singleton states))

/-- Matching the finitely many ring times by a time change matches the entire paths.
Only states up to the horizon and positive ring times up to the horizon are used. -/
theorem path_apply_timeChange (h g : RegularHistory S) (ι : S → E) (T : ℝ)
    (l : Icc (0 : ℝ) T ≃o Icc (0 : ℝ) T)
    (hn : h.ringCount (Real.toNNReal T) = g.ringCount (Real.toNNReal T))
    (hstates : ∀ k ≤ g.ringCount (Real.toNNReal T), (h.val k).1 = (g.val k).1)
    (hclocks : ∀ k, 0 < k → k ≤ g.ringCount (Real.toNNReal T) →
      ∀ t : Icc (0 : ℝ) T, (t : ℝ) = jumpTime g.val k →
        (l t : ℝ) = jumpTime h.val k)
    (t : Icc (0 : ℝ) T) : (h.path ι T).1 (l t) = (g.path ι T).1 t := by
  have hT : 0 ≤ T := t.property.1.trans t.property.2
  have hTcoe : (Real.toNNReal T : ℝ) = T := Real.coe_toNNReal T hT
  have htcoe : (Real.toNNReal (t : ℝ) : ℝ) = t :=
    Real.coe_toNNReal _ t.property.1
  have hltcoe : (Real.toNNReal (l t : ℝ) : ℝ) = l t :=
    Real.coe_toNNReal _ (l t).property.1
  let k := g.ringCount (Real.toNNReal (t : ℝ))
  have hk : k ≤ g.ringCount (Real.toNNReal T) :=
    g.ringCount_le (Real.toNNReal_le_toNNReal t.property.2)
  have hring : ∀ j, 0 < j → j ≤ g.ringCount (Real.toNNReal T) →
      ∃ s : Icc (0 : ℝ) T, (s : ℝ) = jumpTime g.val j ∧
        (l s : ℝ) = jumpTime h.val j := by
    intro j hj hjn
    have hjT : jumpTime g.val j ≤ T := by
      rw [← hTcoe]
      exact (g.strictMono_jumpTime.monotone hjn).trans (g.jumpTime_ringCount_le _)
    let s : Icc (0 : ℝ) T := ⟨jumpTime g.val j, g.jumpTime_nonneg j, hjT⟩
    exact ⟨s, rfl, hclocks j hj hjn s rfl⟩
  have hlo : jumpTime h.val k ≤ Real.toNNReal (l t : ℝ) := by
    rw [hltcoe]
    by_cases hk0 : k = 0
    · rw [hk0, jumpTime_zero]
      exact (l t).property.1
    obtain ⟨s, hs, hls⟩ := hring k (Nat.pos_of_ne_zero hk0) hk
    rw [← hls]
    apply l.monotone
    change (s : ℝ) ≤ t
    rw [hs, ← htcoe]
    exact g.jumpTime_ringCount_le _
  have hhi : (Real.toNNReal (l t : ℝ) : ℝ) < jumpTime h.val (k + 1) := by
    rw [hltcoe]
    by_cases hkn : k < g.ringCount (Real.toNNReal T)
    · obtain ⟨s, hs, hls⟩ := hring (k + 1) (by omega) (by omega)
      rw [← hls]
      apply l.strictMono
      change (t : ℝ) < s
      rw [hs, ← htcoe]
      exact g.lt_jumpTime_ringCount_succ _
    · have heq : k = h.ringCount (Real.toNNReal T) := by omega
      rw [heq]
      exact (l t).property.2.trans_lt (by
        simpa only [hTcoe] using h.lt_jumpTime_ringCount_succ (Real.toNNReal T))
  rw [path_apply, path_apply, h.position_eq_of_interval _ k hlo hhi]
  change ι (h.val k).1 = ι (g.val k).1
  rw [hstates k hk]

/-- A uniformly small time change matching ring times bounds the J1 path distance. -/
theorem skorokhodDist_path_le_of_timeChange (h g : RegularHistory S) (ι : S → E)
    (T r : ℝ) (hr : 0 ≤ r) (l : Icc (0 : ℝ) T ≃o Icc (0 : ℝ) T)
    (hn : h.ringCount (Real.toNNReal T) = g.ringCount (Real.toNNReal T))
    (hstates : ∀ k ≤ g.ringCount (Real.toNNReal T), (h.val k).1 = (g.val k).1)
    (hclocks : ∀ k, 0 < k → k ≤ g.ringCount (Real.toNNReal T) →
      ∀ t : Icc (0 : ℝ) T, (t : ℝ) = jumpTime g.val k →
        (l t : ℝ) = jumpTime h.val k)
    (htime : ∀ t, |(l t : ℝ) - t| ≤ r) :
    skorokhodDist (h.path ι T) (g.path ι T) ≤ r := by
  apply skorokhodDist_le_of_mem
  refine ⟨hr, l, htime, ?_⟩
  intro t
  rw [h.path_apply_timeChange g ι T l hn hstates hclocks t, sub_self, norm_zero]
  exact hr

/-- The affine map matching two ordered pairs of real endpoints. -/
def affineTime (a b c d x : ℝ) : ℝ := c + (x - a) * ((d - c) / (b - a))

/-- Affine interpolation takes the left endpoint to the prescribed value. -/
theorem affineTime_left (a b c d : ℝ) : affineTime a b c d a = c := by
  simp only [affineTime, sub_self, zero_mul, add_zero]

/-- Affine interpolation takes the right endpoint to the prescribed value. -/
theorem affineTime_right {a b : ℝ} (hab : a < b) (c d : ℝ) :
    affineTime a b c d b = d := by
  dsimp [affineTime]
  field_simp [ne_of_gt (sub_pos.mpr hab)]
  ring

/-- An affine interpolation between ordered endpoints is continuous. -/
theorem continuous_affineTime (a b c d : ℝ) : Continuous (affineTime a b c d) := by
  unfold affineTime
  fun_prop

/-- An affine interpolation between strictly ordered endpoints is strictly increasing. -/
theorem strictMono_affineTime {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    StrictMono (affineTime a b c d) := by
  intro x y hxy
  dsimp [affineTime]
  exact add_lt_add_right
    (mul_lt_mul_of_pos_right (sub_lt_sub_right hxy a)
      (div_pos (sub_pos.mpr hcd) (sub_pos.mpr hab))) c

/-- The displacement on an affine segment is bounded by the endpoint displacements. -/
theorem abs_affineTime_sub_le {a b c d r x : ℝ} (hab : a < b)
    (hx : x ∈ Icc a b) (ha : |c - a| ≤ r) (hb : |d - b| ≤ r) :
    |affineTime a b c d x - x| ≤ r := by
  have hden : 0 < b - a := sub_pos.mpr hab
  have hw0 : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hx.1) hden.le
  have hw1 : (x - a) / (b - a) ≤ 1 := (div_le_one hden).mpr (by linarith [hx.2])
  have heq : affineTime a b c d x - x =
      (1 - (x - a) / (b - a)) * (c - a) + ((x - a) / (b - a)) * (d - b) := by
    dsimp [affineTime]
    field_simp [ne_of_gt hden]
    ring
  rw [heq, abs_le]
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  constructor
  · have := mul_le_mul_of_nonneg_left ha'.1 (sub_nonneg.mpr hw1)
    have := mul_le_mul_of_nonneg_left hb'.1 hw0
    nlinarith
  · have := mul_le_mul_of_nonneg_left ha'.2 (sub_nonneg.mpr hw1)
    have := mul_le_mul_of_nonneg_left hb'.2 hw0
    nlinarith

/-- Finite increasing knot vectors admit continuous increasing interpolation with
uniform displacement controlled by the displacements of their knots. -/
theorem exists_time_interpolation (n : ℕ) (s t : ℕ → ℝ) (r : ℝ)
    (hs : ∀ k ≤ n, s k < s (k + 1)) (ht : ∀ k ≤ n, t k < t (k + 1))
    (hr : ∀ k ≤ n + 1, |t k - s k| ≤ r) :
    ∃ f : ℝ → ℝ, Continuous f ∧ StrictMono f ∧
      (∀ k ≤ n + 1, f (s k) = t k) ∧
      ∀ x ∈ Icc (s 0) (s (n + 1)), |f x - x| ≤ r := by
  induction n with
  | zero =>
    refine ⟨affineTime (s 0) (s 1) (t 0) (t 1), continuous_affineTime _ _ _ _,
      strictMono_affineTime (hs 0 le_rfl) (ht 0 le_rfl), ?_, ?_⟩
    · intro k hk
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · exact affineTime_left _ _ _ _
      · exact affineTime_right (hs 0 le_rfl) _ _
    · intro x hx
      exact abs_affineTime_sub_le (hs 0 le_rfl) hx (hr 0 (by omega)) (hr 1 le_rfl)
  | succ n ih =>
    obtain ⟨f, hf, hfm, hfk, hfb⟩ := ih
      (fun k hk => hs k (by omega)) (fun k hk => ht k (by omega))
      (fun k hk => hr k (by omega))
    let g := affineTime (s (n + 1)) (s (n + 2)) (t (n + 1)) (t (n + 2))
    have hg : Continuous g := continuous_affineTime _ _ _ _
    have hgm : StrictMono g := strictMono_affineTime (hs _ le_rfl) (ht _ le_rfl)
    have hgl : g (s (n + 1)) = t (n + 1) := affineTime_left _ _ _ _
    have hgr : g (s (n + 2)) = t (n + 2) := affineTime_right (hs _ le_rfl) _ _
    have hsm : MonotoneOn s (Iic (n + 2)) :=
      (strictMonoOn_Iic_of_lt_succ (fun k hk => hs k (by omega))).monotoneOn
    refine ⟨fun x => if x ≤ s (n + 1) then f x else g x, ?_, ?_, ?_, ?_⟩
    · exact hf.if_le hg continuous_id continuous_const (fun x hx => by
        rw [show x = s (n + 1) from hx, hfk _ le_rfl, hgl])
    · apply hfm.ite' hgm (fun x y hxy hy => hxy.le.trans hy)
      intro x y hx hy _
      calc
        f x ≤ f (s (n + 1)) := hfm.monotone hx
        _ = g (s (n + 1)) := (hfk _ le_rfl).trans hgl.symm
        _ < g y := hgm (lt_of_not_ge hy)
    · intro k hk
      dsimp only
      by_cases hkn : k ≤ n + 1
      · rw [if_pos (hsm (by simp only [mem_Iic]; omega)
          (by simp only [mem_Iic]; omega) hkn), hfk k hkn]
      · have heq : k = n + 2 := by omega
        subst k
        rw [if_neg (not_le.mpr (hs _ le_rfl)), hgr]
    · intro x hx
      dsimp only
      split_ifs with hxn
      · exact hfb x ⟨hx.1, hxn⟩
      · exact abs_affineTime_sub_le (hs _ le_rfl) ⟨(lt_of_not_ge hxn).le, hx.2⟩
          (hr _ (by omega)) (hr _ le_rfl)

/-- Interpolation of finite knot vectors with common endpoints gives an interval
order isomorphism, with the same uniform displacement bound. -/
theorem exists_timeChange_of_knots (n : ℕ) (s t : ℕ → ℝ) (T r : ℝ)
    (hs : ∀ k ≤ n, s k < s (k + 1)) (ht : ∀ k ≤ n, t k < t (k + 1))
    (hs0 : s 0 = 0) (ht0 : t 0 = 0) (hsT : s (n + 1) = T)
    (htT : t (n + 1) = T) (hr : ∀ k ≤ n + 1, |t k - s k| ≤ r) :
    ∃ l : Icc (0 : ℝ) T ≃o Icc (0 : ℝ) T,
      (∀ k ≤ n + 1, ∀ u : Icc (0 : ℝ) T, (u : ℝ) = s k → (l u : ℝ) = t k) ∧
      ∀ u, |(l u : ℝ) - u| ≤ r := by
  obtain ⟨f, hf, hfm, hfk, hfb⟩ := exists_time_interpolation n s t r hs ht hr
  have hf0 : f 0 = 0 := by simpa only [hs0, ht0] using hfk 0 (by omega)
  have hfT : f T = T := by simpa only [hsT, htT] using hfk (n + 1) le_rfl
  let F : Icc (0 : ℝ) T → Icc (0 : ℝ) T := fun u =>
    ⟨f u, by constructor
             · exact hf0.symm.le.trans (hfm.monotone u.property.1)
             · exact (hfm.monotone u.property.2).trans hfT.le⟩
  have hFm : StrictMono F := fun _ _ h => hfm h
  have hFs : Function.Surjective F := by
    intro y
    have hT : 0 ≤ T := y.property.1.trans y.property.2
    have hy : (y : ℝ) ∈ Icc (f 0) (f T) := by
      simpa only [hf0, hfT] using y.property
    obtain ⟨x, hx, hfx⟩ := hf.continuousOn.surjOn_Icc
      (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)
      (show T ∈ Icc (0 : ℝ) T from ⟨hT, le_rfl⟩) hy
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  refine ⟨hFm.orderIsoOfSurjective F hFs, ?_, ?_⟩
  · intro k hk u hu
    change f u = t k
    rw [hu, hfk k hk]
  · intro u
    exact hfb u (by simpa only [hs0, hsT] using u.property)

/-- Histories with equal ring counts and terminal flags admit a time change
matching every ring before the horizon, controlled by their clock discrepancies. -/
theorem exists_timeChange_of_ringCount (h g : RegularHistory S) {T r : ℝ}
    (hT : 0 < T) (hr : 0 ≤ r)
    (hn : h.ringCount (Real.toNNReal T) = g.ringCount (Real.toNNReal T))
    (hterminal : jumpTime h.val (h.ringCount (Real.toNNReal T)) = T ↔
      jumpTime g.val (g.ringCount (Real.toNNReal T)) = T)
    (hclose : ∀ k ≤ g.ringCount (Real.toNNReal T),
      |jumpTime h.val k - jumpTime g.val k| ≤ r) :
    ∃ l : Icc (0 : ℝ) T ≃o Icc (0 : ℝ) T,
      (∀ k, 0 < k → k ≤ g.ringCount (Real.toNNReal T) →
        ∀ u : Icc (0 : ℝ) T, (u : ℝ) = jumpTime g.val k →
          (l u : ℝ) = jumpTime h.val k) ∧
      ∀ u, |(l u : ℝ) - u| ≤ r := by
  let n := g.ringCount (Real.toNNReal T)
  have hng : g.ringCount (Real.toNNReal T) = n := rfl
  have hnh : h.ringCount (Real.toNNReal T) = n := hn
  have hgle : jumpTime g.val n ≤ T := by
    simpa only [Real.coe_toNNReal _ hT.le] using g.jumpTime_ringCount_le (Real.toNNReal T)
  have hhle : jumpTime h.val n ≤ T := by
    simpa only [hnh, Real.coe_toNNReal _ hT.le] using
      h.jumpTime_ringCount_le (Real.toNNReal T)
  by_cases hend : jumpTime g.val n = T
  · have hnpos : 0 < n := by
      by_contra hnpos
      have hn0 : n = 0 := by omega
      rw [hn0, jumpTime_zero] at hend
      linarith
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    have hhend : jumpTime h.val n = T := by
      rw [← hnh]
      exact hterminal.mpr hend
    obtain ⟨l, hl, hb⟩ := exists_timeChange_of_knots m
      (jumpTime g.val) (jumpTime h.val) T r
      (fun k _ => g.strictMono_jumpTime (Nat.lt_succ_self k))
      (fun k _ => h.strictMono_jumpTime (Nat.lt_succ_self k))
      (jumpTime_zero _) (jumpTime_zero _)
      (by simpa only [hm] using hend) (by simpa only [hm] using hhend)
      (fun k hk => hclose k (by simpa only [hng, hm] using hk))
    exact ⟨l, fun k _ hk u hu => hl k (by simpa only [hng, hm] using hk) u hu, hb⟩
  · have hhend : jumpTime h.val n ≠ T := by
      intro heq
      apply hend
      exact hterminal.mp (by simpa only [hnh] using heq)
    let s : ℕ → ℝ := fun k => if k ≤ n then jumpTime g.val k else T
    let t : ℕ → ℝ := fun k => if k ≤ n then jumpTime h.val k else T
    have hs : ∀ k ≤ n, s k < s (k + 1) := by
      intro k hk
      dsimp [s]
      rw [if_pos hk]
      split_ifs with hk'
      · exact g.strictMono_jumpTime (Nat.lt_succ_self k)
      · have : k = n := by omega
        subst k
        exact lt_of_le_of_ne hgle hend
    have ht : ∀ k ≤ n, t k < t (k + 1) := by
      intro k hk
      dsimp [t]
      rw [if_pos hk]
      split_ifs with hk'
      · exact h.strictMono_jumpTime (Nat.lt_succ_self k)
      · have : k = n := by omega
        subst k
        exact lt_of_le_of_ne hhle hhend
    obtain ⟨l, hl, hb⟩ := exists_timeChange_of_knots n s t T r hs ht
      (by simp only [s, Nat.zero_le, if_true, jumpTime_zero])
      (by simp only [t, Nat.zero_le, if_true, jumpTime_zero])
      (by simp only [s, Nat.not_succ_le_self, if_false])
      (by simp only [t, Nat.not_succ_le_self, if_false]) (by
        intro k hk
        dsimp [s, t]
        split_ifs with hkn
        · exact hclose k hkn
        · simpa only [sub_self, abs_zero] using hr)
    refine ⟨l, ?_, hb⟩
    intro k _ hk u hu
    have hk' : k ≤ n := hk
    have hs' : (u : ℝ) = s k := by simpa only [s, if_pos hk'] using hu
    simpa only [t, if_pos hk'] using hl k (by omega) u hs'

/-- On a common state and terminal stratum, clock discrepancies control J1 distance. -/
theorem skorokhodDist_path_le_of_clocks (h g : RegularHistory S) (ι : S → E)
    {T r : ℝ} (hT : 0 < T) (hr : 0 ≤ r)
    (hn : h.ringCount (Real.toNNReal T) = g.ringCount (Real.toNNReal T))
    (hterminal : jumpTime h.val (h.ringCount (Real.toNNReal T)) = T ↔
      jumpTime g.val (g.ringCount (Real.toNNReal T)) = T)
    (hstates : ∀ k ≤ g.ringCount (Real.toNNReal T), (h.val k).1 = (g.val k).1)
    (hclose : ∀ k ≤ g.ringCount (Real.toNNReal T),
      |jumpTime h.val k - jumpTime g.val k| ≤ r) :
    skorokhodDist (h.path ι T) (g.path ι T) ≤ r := by
  obtain ⟨l, hl, hb⟩ := h.exists_timeChange_of_ringCount g hT hr hn hterminal hclose
  exact h.skorokhodDist_path_le_of_timeChange g ι T r hr l hn hstates hl hb

/-- Each finite clock sum is continuous in the product topology on histories. -/
theorem continuous_jumpTime [TopologicalSpace S] (n : ℕ) :
    Continuous (fun h : RegularHistory S => jumpTime h.val n) := by
  unfold jumpTime
  exact continuous_finsetSum _ (fun k _ =>
    ((continuous_apply k).comp continuous_subtype_val).snd)

/-- Fixing the ring count, terminal flag and finite state tuple makes the path map
continuous in the product topology of its clock coordinates. -/
theorem continuous_path_stratum_states [TopologicalSpace S] (ι : S → E)
    {T : ℝ} (hT : 0 < T) (n : ℕ) (terminal : Bool) (states : Fin (n + 1) → S) :
    Continuous (fun h : {h : RegularHistory S |
      (h.ringCount (Real.toNNReal T) = n ∧
        (jumpTime h.val n = T ↔ terminal = true)) ∧
      (fun k : Fin (n + 1) => (h.val k).1) = states} => h.val.path ι T) := by
  apply continuous_iff_continuousAt.mpr
  intro g
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hclocks : ∀ k ∈ Finset.range (n + 1), ∀ᶠ h in 𝓝 g,
      |jumpTime h.val.val k - jumpTime g.val.val k| < ε / 2 := by
    intro k _
    have hc : Continuous (fun h : {h : RegularHistory S |
        (h.ringCount (Real.toNNReal T) = n ∧
          (jumpTime h.val n = T ↔ terminal = true)) ∧
        (fun k : Fin (n + 1) => (h.val k).1) = states} => jumpTime h.val.val k) :=
      (continuous_jumpTime (S := S) k).comp continuous_subtype_val
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.mp hc.continuousAt) (ε / 2) (half_pos hε)
  filter_upwards [(Finset.eventually_all _).mpr hclocks] with h hh
  have hn : h.val.ringCount (Real.toNNReal T) = g.val.ringCount (Real.toNNReal T) :=
    h.property.1.1.trans g.property.1.1.symm
  have ht : jumpTime h.val.val (h.val.ringCount (Real.toNNReal T)) = T ↔
      jumpTime g.val.val (g.val.ringCount (Real.toNNReal T)) = T := by
    rw [h.property.1.1, g.property.1.1]
    exact h.property.1.2.trans g.property.1.2.symm
  have hs : ∀ k ≤ g.val.ringCount (Real.toNNReal T),
      (h.val.val k).1 = (g.val.val k).1 := by
    intro k hk
    have hk' : k < n + 1 := by rw [g.property.1.1] at hk; omega
    exact (congrFun h.property.2 ⟨k, hk'⟩).trans
      (congrFun g.property.2 ⟨k, hk'⟩).symm
  rw [dist_eq_skorokhodDist]
  apply lt_of_le_of_lt
    (h.val.skorokhodDist_path_le_of_clocks g.val ι hT (half_pos hε).le hn ht hs ?_)
    (half_lt_self hε)
  intro k hk
  apply (hh k (Finset.mem_range.mpr ?_)).le
  rw [g.property.1.1] at hk
  omega

/-- The J1-valued path map is measurable on every fixed finite state and clock stratum. -/
theorem measurable_path_stratum_states [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (ι : S → E) {T : ℝ} (hT : 0 < T)
    (n : ℕ) (terminal : Bool) (states : Fin (n + 1) → S) :
    Measurable (fun h : {h : RegularHistory S |
      (h.ringCount (Real.toNNReal T) = n ∧
        (jumpTime h.val n = T ↔ terminal = true)) ∧
      (fun k : Fin (n + 1) => (h.val k).1) = states} => h.val.path ι T) := by
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := discreteTopology_bot S
  exact (continuous_path_stratum_states ι hT n terminal states).measurable

/-- Moving a terminal jump into the interior costs its full jump size in J1 distance.
Thus jump-time continuity cannot include perturbations off the terminal face. -/
theorem skorokhodDist_terminal_jump (T a : ℝ) (ha : 0 ≤ a) (haT : a < T)
    (u v : E) :
    skorokhodDist (jump T T u v) (jump T a u v) = ‖u - v‖ := by
  apply le_antisymm
  · apply skorokhodDist_le_uniform (norm_nonneg _)
    intro t
    simp only [jump_apply]
    split_ifs <;> first
      | exact le_rfl
      | exact (norm_sub_rev _ _).le
      | simpa only [sub_self, norm_zero] using norm_nonneg (u - v)
  · apply le_csInf (admissibleBounds_nonempty _ _)
    rintro r ⟨_, l, _, hspace⟩
    let t : Icc (0 : ℝ) T := ⟨a, ha, haT.le⟩
    let e : Icc (0 : ℝ) T := ⟨T, ha.trans haT.le, le_rfl⟩
    have hte : t < e := haT
    have hle : l e = e := timeChange_apply_terminal l e rfl
    have hlt : (l t : ℝ) < T := by
      have := l.strictMono hte
      rw [hle] at this
      exact this
    have hb := hspace t
    change ‖(jump T T u v).1 (l t) - (if a < a then u else v)‖ ≤ r at hb
    simpa only [jump_apply, hlt, if_true, lt_self_iff_false, if_false] using hb

end RegularHistory

/-- The regular chain path is measurable for the J1 Borel sigma algebra at every horizon. -/
theorem measurable_path [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    (ι : S → E) (T : ℝ) : Measurable (fun h : RegularHistory S => h.path ι T) := by
  classical
  by_cases hT : T ≤ 0
  · exact RegularHistory.measurable_path_of_nonpos ι hT
  have hTpos : 0 < T := lt_of_not_ge hT
  let A (n : ℕ) (terminal : Bool) (states : Fin (n + 1) → S) :=
    {h : RegularHistory S |
      (h.ringCount (Real.toNNReal T) = n ∧
        (jumpTime h.val n = T ↔ terminal = true)) ∧
      (fun k : Fin (n + 1) => (h.val k).1) = states}
  intro U hU
  have heq : (fun h : RegularHistory S => h.path ι T) ⁻¹' U =
      ⋃ n, ⋃ terminal, ⋃ states : Fin (n + 1) → S,
        Subtype.val '' {h : A n terminal states | h.val.path ι T ∈ U} := by
    ext h
    constructor
    · intro hh
      let n := h.ringCount (Real.toNNReal T)
      let terminal := decide (jumpTime h.val n = T)
      let states : Fin (n + 1) → S := fun k => (h.val k).1
      have ha : h ∈ A n terminal states := by
        exact ⟨⟨rfl, by simp only [terminal, decide_eq_true_eq]⟩, rfl⟩
      exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨terminal,
        mem_iUnion.mpr ⟨states, ⟨⟨h, ha⟩, hh, rfl⟩⟩⟩⟩
    · intro hh
      obtain ⟨n, hh⟩ := mem_iUnion.mp hh
      obtain ⟨terminal, hh⟩ := mem_iUnion.mp hh
      obtain ⟨states, g, hg, heq⟩ := mem_iUnion.mp hh
      exact heq ▸ hg
  rw [heq]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun terminal =>
    MeasurableSet.iUnion fun states =>
      (RegularHistory.measurableSet_path_stratum_states T n terminal states).subtype_image
        (RegularHistory.measurable_path_stratum_states ι hTpos n terminal states hU)

end

end LatticeProb.JumpChain
