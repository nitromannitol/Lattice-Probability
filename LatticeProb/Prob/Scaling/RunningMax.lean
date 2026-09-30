/-
**The running maximum of a jointly continuous field, and its basic properties.**

General-purpose, no probability: for `f : ℝ → (Fin d → ℝ) → ℝ` jointly continuous in `(s,x)`,
`runningMax f s x := sSup {f u x | 0 ≤ u ≤ max s 0}` (the running maximum over the time-window
`[0,s]`, clamped so the definition makes sense for every real `s`, matching `f 0 x` for
`s ≤ 0`).

Under a pathwise additive representation of an optimal-stopping value as the running maximum of
a continuum field `Z`, `Uc(s,x) = sup_{τ≤s} E_x[Z(τ,x)] = runningMax Z s x`, and under this
closed form monotonicity, joint continuity and (given pointwise measurability of `Z` itself)
pointwise measurability are all provable directly, none of them depending on any further
probabilistic input beyond `Z`'s own continuity. This module proves those three properties for
the closed form alone, so that given such an identity `Uc = runningMax Z`, those clauses follow
immediately.

Moved from Parking-Sharpness.
-/
import Mathlib

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb.Scaling.RunningMax

variable {d : ℕ}

/-! ### Definition -/

/-- **The running maximum of `f` over `[0, s]`** (`s` clamped to `[0,∞)` via `max s 0`, so the
definition is total). -/
def runningMax (f : ℝ → (Fin d → ℝ) → ℝ) (s : ℝ) (x : Fin d → ℝ) : ℝ :=
  sSup ((fun u => f u x) '' Set.Icc (0 : ℝ) (max s 0))

variable {f : ℝ → (Fin d → ℝ) → ℝ}

/-- The map `u ↦ f u x` restricted to the time coordinate, continuous whenever the joint map is. -/
theorem continuous_apply_right (hf : Continuous fun p : ℝ × (Fin d → ℝ) => f p.1 p.2)
    (x : Fin d → ℝ) : Continuous fun u => f u x :=
  hf.comp (continuous_id.prodMk continuous_const)

/-- The image of a compact time window under `u ↦ f u x` is compact. -/
theorem isCompact_image_Icc (hf : Continuous fun p : ℝ × (Fin d → ℝ) => f p.1 p.2) (T : ℝ)
    (x : Fin d → ℝ) : IsCompact ((fun u => f u x) '' Set.Icc (0 : ℝ) T) :=
  isCompact_Icc.image (continuous_apply_right hf x)

/-- The image of a compact time window under `u ↦ f u x` is bounded above. -/
theorem bddAbove_image_Icc (hf : Continuous fun p : ℝ × (Fin d → ℝ) => f p.1 p.2) (T : ℝ)
    (x : Fin d → ℝ) : BddAbove ((fun u => f u x) '' Set.Icc (0 : ℝ) T) :=
  (isCompact_image_Icc hf T x).bddAbove

/-- The image of a nonempty time window `[0, T]` under `u ↦ f u x` is nonempty. -/
theorem nonempty_image_Icc (T : ℝ) (hT : 0 ≤ T) (x : Fin d → ℝ) :
    ((fun u => f u x) '' Set.Icc (0 : ℝ) T).Nonempty :=
  ⟨f 0 x, 0, Set.mem_Icc.mpr ⟨le_refl 0, hT⟩, rfl⟩

/-! ### Basic values -/

/-- **The running maximum at a nonpositive time is the value at `0`.** -/
theorem runningMax_of_le {s : ℝ} (hs : s ≤ 0) (x : Fin d → ℝ) : runningMax f s x = f 0 x := by
  unfold runningMax
  rw [max_eq_right hs, Set.Icc_self, Set.image_singleton, csSup_singleton]

/-- The running maximum at time `0` is the value at `0`. -/
theorem runningMax_zero (x : Fin d → ℝ) : runningMax f 0 x = f 0 x :=
  runningMax_of_le (le_refl 0) x

/-- **Every value of `f` on the window is at most the running maximum.** -/
theorem le_runningMax (hf : Continuous fun p : ℝ × (Fin d → ℝ) => f p.1 p.2) {s u : ℝ}
    (hu0 : 0 ≤ u) (hus : u ≤ max s 0) (x : Fin d → ℝ) : f u x ≤ runningMax f s x :=
  le_csSup (bddAbove_image_Icc hf _ x) ⟨u, Set.mem_Icc.mpr ⟨hu0, hus⟩, rfl⟩

/-! ### Monotonicity -/

/-- **`runningMax f · x` is monotone**, for every `x`, unconditionally: more of the window is
available at a larger horizon. -/
theorem runningMax_mono (hf : Continuous fun p : ℝ × (Fin d → ℝ) => f p.1 p.2) (x : Fin d → ℝ) :
    Monotone fun s => runningMax f s x := by
  intro s s' hss'
  unfold runningMax
  have hsub : Set.Icc (0 : ℝ) (max s 0) ⊆ Set.Icc (0 : ℝ) (max s' 0) :=
    Set.Icc_subset_Icc_right (max_le_max hss' (le_refl 0))
  exact csSup_le_csSup (bddAbove_image_Icc hf _ x) (nonempty_image_Icc _ (le_max_right s 0) x)
    (Set.image_mono hsub)

/-! ### The two-sided comparison, the key lemma for continuity -/

/-- Elementary: `|a - b| ≤ |a - s₀| + |b - s₀|`. -/
private theorem abs_sub_le_abs_sub_add_abs_sub (a b s₀ : ℝ) :
    |a - b| ≤ |a - s₀| + |b - s₀| := by
  calc |a - b| = |(a - s₀) - (b - s₀)| := by ring_nf
    _ ≤ |a - s₀| + |b - s₀| := abs_sub _ _

/-- **The core estimate**: for `a, b` and `y, z` both within `δ` of a fixed reference point
`(s₀, x₀)`, `runningMax f a y` exceeds `runningMax f b z` by at most `ε`.  Symmetric in
`(a,y) ↔ (b,z)`, so applying it both ways (against the same `δ`, obtained once) gives joint
continuity of `runningMax f` directly. -/
theorem runningMax_le_add (hf : Continuous fun p : ℝ × (Fin d → ℝ) => f p.1 p.2) (s₀ : ℝ)
    (x₀ : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a b : ℝ, ∀ y z : Fin d → ℝ,
      |a - s₀| < δ → dist y x₀ < δ → |b - s₀| < δ → dist z x₀ < δ →
      runningMax f a y ≤ runningMax f b z + ε := by
  set K : Set (ℝ × (Fin d → ℝ)) :=
    Set.Icc (0 : ℝ) (max s₀ 0 + 2) ×ˢ Metric.closedBall x₀ 2 with hKdef
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall x₀ 2)
  have hUC : UniformContinuousOn (fun p : ℝ × (Fin d → ℝ) => f p.1 p.2) K :=
    hK.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  refine ⟨min δ₀ 1 / 2, by positivity, ?_⟩
  intro a b y z ha hy hb hz
  have hδ1 : min δ₀ 1 / 2 ≤ 1 / 2 := by
    have := min_le_right δ₀ (1:ℝ); linarith
  have hδδ0 : min δ₀ 1 / 2 ≤ δ₀ / 2 := by
    have := min_le_left δ₀ (1:ℝ); linarith
  have ha1 := ha.trans_le hδ1
  have hb1 := hb.trans_le hδ1
  have hy1 := hy.trans_le hδ1
  have hz1 := hz.trans_le hδ1
  have haδ := ha.trans_le hδδ0
  have hbδ := hb.trans_le hδδ0
  have hyδ := hy.trans_le hδδ0
  have hzδ := hz.trans_le hδδ0
  have hcomp : |a - b| ≤ |a - s₀| + |b - s₀| := by
    have h1 := abs_sub_le_abs_sub_add_abs_sub a b s₀
    have h2 : |s₀ - b| = |b - s₀| := abs_sub_comm s₀ b
    linarith
  have hab1 : |a - b| < 1 := by linarith
  have habδ : |a - b| < δ₀ := by linarith
  have hyz1 : dist y z < 1 := by
    have h := dist_triangle y x₀ z; rw [dist_comm x₀ z] at h; linarith
  have hyzδ : dist y z < δ₀ := by
    have h := dist_triangle y x₀ z; rw [dist_comm x₀ z] at h; linarith
  have hmaxa : max a 0 < max s₀ 0 + 2 := by
    rcases le_total a 0 with h | h
    · have h0 : (0:ℝ) ≤ max s₀ 0 := le_max_right s₀ 0
      simpa [max_eq_right h] using lt_of_le_of_lt h0 (by linarith)
    · have hslt : a < s₀ + 1 := by
        have := abs_lt.mp ha1; linarith [this.2]
      have hlt : a < max s₀ 0 + 2 := lt_of_lt_of_le hslt (by linarith [le_max_left s₀ 0])
      simpa [max_eq_left h] using hlt
  have hmaxb : max b 0 < max s₀ 0 + 2 := by
    rcases le_total b 0 with h | h
    · have h0 : (0:ℝ) ≤ max s₀ 0 := le_max_right s₀ 0
      simpa [max_eq_right h] using lt_of_le_of_lt h0 (by linarith)
    · have hslt : b < s₀ + 1 := by
        have := abs_lt.mp hb1; linarith [this.2]
      have hlt : b < max s₀ 0 + 2 := lt_of_lt_of_le hslt (by linarith [le_max_left s₀ 0])
      simpa [max_eq_left h] using hlt
  have hymem : y ∈ Metric.closedBall x₀ 2 := by
    simp only [Metric.mem_closedBall]; linarith
  have hzmem : z ∈ Metric.closedBall x₀ 2 := by
    simp only [Metric.mem_closedBall]; linarith
  show sSup ((fun u => f u y) '' Set.Icc (0 : ℝ) (max a 0)) ≤ runningMax f b z + ε
  refine csSup_le (nonempty_image_Icc _ (le_max_right a 0) y) ?_
  rintro w ⟨u, hu, rfl⟩
  obtain ⟨hu0, hua⟩ := Set.mem_Icc.mp hu
  set u' : ℝ := min u (max b 0) with hu'def
  have hu'0 : 0 ≤ u' := le_min hu0 (le_max_right b 0)
  have hu'le : u' ≤ max b 0 := min_le_right _ _
  have hdiff : |u - u'| ≤ |a - b| := by
    rcases le_total u (max b 0) with h | h
    · simp [hu'def, min_eq_left h]
    · have hu'eq : u' = max b 0 := min_eq_right h
      have hub : u - u' ≤ max a 0 - max b 0 := by rw [hu'eq]; linarith [hua]
      have hlb : 0 ≤ u - u' := by rw [hu'eq]; linarith
      have hmm : |max a 0 - max b 0| ≤ |a - b| := abs_max_sub_max_le_abs a b 0
      calc |u - u'| = u - u' := abs_of_nonneg hlb
        _ ≤ max a 0 - max b 0 := hub
        _ ≤ |max a 0 - max b 0| := le_abs_self _
        _ ≤ |a - b| := hmm
  have huK : (u, y) ∈ K := by
    refine Set.mk_mem_prod ?_ hymem
    exact Set.mem_Icc.mpr ⟨hu0, hua.trans hmaxa.le⟩
  have hu'K : (u', z) ∈ K := by
    refine Set.mk_mem_prod ?_ hzmem
    exact Set.mem_Icc.mpr ⟨hu'0, by linarith [hu'le, hmaxb.le]⟩
  have hdist : dist (u, y) (u', z) < δ₀ := by
    rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · calc dist u u' = |u - u'| := Real.dist_eq u u'
        _ ≤ |a - b| := hdiff
        _ < δ₀ := habδ
    · exact hyzδ
  have hfeq := hδ₀ (u, y) huK (u', z) hu'K hdist
  have hle : f u y ≤ f u' z + ε := by
    have heq := (Real.dist_eq (f u y) (f u' z)) ▸ hfeq
    have h2 := (abs_sub_lt_iff.mp heq).1
    linarith
  refine hle.trans ?_
  have : f u' z ≤ runningMax f b z := le_runningMax hf hu'0 hu'le z
  linarith

/-- **Joint continuity of the running maximum**, for `f` jointly continuous with `f 0 · `
arbitrary (no boundedness, no further hypothesis). -/
theorem continuous_runningMax (hf : Continuous fun p : ℝ × (Fin d → ℝ) => f p.1 p.2) :
    Continuous fun p : ℝ × (Fin d → ℝ) => runningMax f p.1 p.2 := by
  rw [Metric.continuous_iff]
  rintro ⟨s₀, x₀⟩ ε hε
  obtain ⟨δ, hδpos, hδ⟩ := runningMax_le_add hf s₀ x₀ (half_pos hε)
  refine ⟨δ, hδpos, ?_⟩
  rintro ⟨s, x⟩ hdist
  rw [Prod.dist_eq] at hdist
  have hs : |s - s₀| < δ := lt_of_le_of_lt (le_max_left _ _) hdist
  have hx : dist x x₀ < δ := lt_of_le_of_lt (le_max_right _ _) hdist
  have hself0 : |s₀ - s₀| < δ := by simpa using hδpos
  have hselfx0 : dist x₀ x₀ < δ := by simpa using hδpos
  have h1 : runningMax f s x ≤ runningMax f s₀ x₀ + ε / 2 := hδ s s₀ x x₀ hs hx hself0 hselfx0
  have h2 : runningMax f s₀ x₀ ≤ runningMax f s x + ε / 2 := hδ s₀ s x₀ x hself0 hselfx0 hs hx
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-! ### Measurability -/

/-- **The clamp of a real number into `[0, T]`.** -/
def clampFn (u T : ℝ) : ℝ := max 0 (min u T)

/-- The clamp always lands in `[0, T]`. -/
theorem clampFn_mem_Icc (u T : ℝ) (hT : 0 ≤ T) : clampFn u T ∈ Set.Icc (0 : ℝ) T :=
  ⟨le_max_left _ _, max_le hT (min_le_right u T)⟩

/-- The clamp fixes points already in `[0, T]`. -/
theorem clampFn_eq_self {u T : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ T) : clampFn u T = u := by
  unfold clampFn; rw [min_eq_left h1, max_eq_right h0]

/-- The clamp is `1`-Lipschitz. -/
theorem abs_clampFn_sub_clampFn_le (u v T : ℝ) : |clampFn u T - clampFn v T| ≤ |u - v| := by
  unfold clampFn
  have hmin : |min u T - min v T| ≤ |u - v| := by
    have := abs_min_sub_min_le_max u T v T
    simpa using this
  calc |max 0 (min u T) - max 0 (min v T)|
      = |max (min u T) 0 - max (min v T) 0| := by rw [max_comm 0 (min u T), max_comm 0 (min v T)]
    _ ≤ |min u T - min v T| := abs_max_sub_max_le_abs _ _ 0
    _ ≤ |u - v| := hmin

/-- **A countable, dense-when-clamped enumeration of the reals**, from `ℚ`'s denumerability. -/
def denseSeq (n : ℕ) : ℝ := (((Denumerable.eqv ℚ).symm n : ℚ) : ℝ)

/-- The enumeration `denseSeq` has dense range in `ℝ`. -/
theorem denseRange_denseSeq : DenseRange denseSeq := by
  have hsurj : Function.Surjective ((Denumerable.eqv ℚ).symm) :=
    (Denumerable.eqv ℚ).symm.surjective
  have heq : Set.range denseSeq = Set.range ((↑) : ℚ → ℝ) := by
    apply Set.eq_of_subset_of_subset
    · rintro _ ⟨n, rfl⟩; exact ⟨(Denumerable.eqv ℚ).symm n, rfl⟩
    · rintro _ ⟨q, rfl⟩
      obtain ⟨n, hn⟩ := hsurj q
      exact ⟨n, by unfold denseSeq; rw [hn]⟩
  unfold DenseRange
  rw [heq]
  exact Rat.denseRange_cast

/-- Every point of `[0, T]` is a closure point of the clamped dense sequence restricted to
`[0, T]`. -/
theorem mem_closure_range_clamp (T : ℝ) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) T) :
    p ∈ closure (Set.range fun n => clampFn (denseSeq n) T) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := Metric.denseRange_iff.mp denseRange_denseSeq p ε hε
  refine ⟨clampFn (denseSeq n) T, ⟨n, rfl⟩, ?_⟩
  have heq : clampFn p T = p := clampFn_eq_self hp.1 hp.2
  calc dist p (clampFn (denseSeq n) T) = |p - clampFn (denseSeq n) T| := Real.dist_eq _ _
    _ = |clampFn p T - clampFn (denseSeq n) T| := by rw [heq]
    _ ≤ |p - denseSeq n| := abs_clampFn_sub_clampFn_le p (denseSeq n) T
    _ = dist p (denseSeq n) := (Real.dist_eq _ _).symm
    _ < ε := hn

/-- **`runningMax` equals the countable supremum of `f` over the clamped dense sequence.** -/
theorem runningMax_eq_iSup_clamp (hf : Continuous fun p : ℝ × (Fin d → ℝ) => f p.1 p.2)
    (s : ℝ) (x : Fin d → ℝ) :
    runningMax f s x = ⨆ n : ℕ, f (clampFn (denseSeq n) (max s 0)) x := by
  have hT : (0:ℝ) ≤ max s 0 := le_max_right s 0
  have hg : Continuous fun u => f u x := continuous_apply_right hf x
  have hbdd : BddAbove (Set.range fun n : ℕ => f (clampFn (denseSeq n) (max s 0)) x) := by
    refine ⟨runningMax f s x, ?_⟩
    rintro y ⟨n, rfl⟩
    exact le_runningMax hf (clampFn_mem_Icc (denseSeq n) (max s 0) hT).1
      (clampFn_mem_Icc (denseSeq n) (max s 0) hT).2 x
  apply le_antisymm
  · unfold runningMax
    refine csSup_le (nonempty_image_Icc _ hT x) ?_
    rintro y ⟨u, hu, rfl⟩
    obtain ⟨hu0, huT⟩ := Set.mem_Icc.mp hu
    -- `f u x` is a limit of `f (clampFn (denseSeq n) T) x` along a sequence with values `≤` the iSup
    have hmemclos := mem_closure_range_clamp (max s 0) u ⟨hu0, huT⟩
    rw [mem_closure_iff_seq_limit] at hmemclos
    obtain ⟨v, hv, hvlim⟩ := hmemclos
    have hcont : Filter.Tendsto (fun k => f (v k) x) Filter.atTop (nhds (f u x)) :=
      (hg.tendsto u).comp hvlim
    refine le_of_tendsto hcont (Filter.Eventually.of_forall fun k => ?_)
    obtain ⟨n, hn⟩ := hv k
    rw [← hn]
    exact le_ciSup hbdd n
  · refine ciSup_le fun n => ?_
    exact le_runningMax hf (clampFn_mem_Icc (denseSeq n) (max s 0) hT).1
      (clampFn_mem_Icc (denseSeq n) (max s 0) hT).2 x

/-- **Pointwise measurability of `runningMax` in an auxiliary sample `ω'`**, given pointwise
measurability of `f` itself at each fixed time (no joint measurability, no continuity in `ω'`
needed): the countable-supremum form makes it a countable `iSup` of measurable functions. -/
theorem measurable_runningMax {Ω' : Type*} [MeasurableSpace Ω'] (F : Ω' → ℝ → (Fin d → ℝ) → ℝ)
    (hFc : ∀ ω', Continuous fun p : ℝ × (Fin d → ℝ) => F ω' p.1 p.2)
    (x : Fin d → ℝ) (hFm : ∀ r, Measurable fun ω' => F ω' r x) (s : ℝ) :
    Measurable fun ω' => runningMax (F ω') s x := by
  have heq : (fun ω' => runningMax (F ω') s x)
      = fun ω' => ⨆ n : ℕ, F ω' (clampFn (denseSeq n) (max s 0)) x := by
    funext ω'; exact runningMax_eq_iSup_clamp (hFc ω') s x
  rw [heq]
  exact Measurable.iSup fun n => hFm (clampFn (denseSeq n) (max s 0))

end LatticeProb.Scaling.RunningMax

end
