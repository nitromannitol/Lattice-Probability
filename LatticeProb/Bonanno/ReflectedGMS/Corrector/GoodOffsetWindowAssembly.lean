/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.GoodOffsetWindowAssembly at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.UniformCorrectorSublinearity

/-!
# Window-by-window assembly of the good grid

This module performs the selection step of the manuscript's proof of `s:eq:sublinear`
(section 6, "From good lines to all cells") that was left open both by
`Corrector/LocalPatchLineBounds.lean` (which selects a good offset in **one** window) and
by `Corrector/UniformCorrectorSublinearity.lean` (which consumes a **whole grid** of
selected offsets):

> Divide `[-2R,2R]` into `4N` intervals of length `α R`.  The interior of each interval
> contains a horizontal coordinate outside both the variation-bad set and `N_h`, and a
> vertical coordinate outside both its variation-bad set and `N_v`. ...  Choose one of
> each in every interval interior. ...  Consecutive selected coordinates are at distance
> at most `2 α R`, and the extreme lines surround `clB R` with a positive macroscopic
> margin.

Nothing about the single-window selection is reproved.  The selector used is the already
checked `ReflectedGMS.exists_good_offsets_lineOscillation_le_rectanglePatch`, whose
Markov step on the variation-bad set is
`ReflectedGMS.exists_notMem_and_le_of_setLIntegral_lt`; it is applied once per window,
with the *same* patch smallness hypothesis for every window, since all windows have the
same length `w`.  The selected coordinates are taken in the window *interiors*, as in the
manuscript.

What is supplied here is the assembly.

* `exists_forward_gap_of_windows` / `exists_backward_gap_of_windows` — the elementary
  consequence of "one selected coordinate per window of length `w`": between the two
  extreme selected coordinates, every real `u` has a selected coordinate in `[u, u + 2w]`
  and a selected coordinate in `[u - 2w, u]`.  The factor `2` is sharp for an arbitrary
  choice inside each window, and it is exactly the manuscript's "consecutive selected
  coordinates are at distance at most `2 α R`": taking the window length `w = α R / 2`
  gives the gap `g = α R` and hence, through
  `ReflectedGMS.exists_gridRectangle_of_notMem_gridCells`, grid rectangles with sides at
  most `2 α R`, which is the manuscript's display.

* `exists_goodOffsetGrid_of_patchSmallness` — the assembly itself: the two offset sets
  `xs`, `ys`, the four boundary coordinates `A`, `B`, `C`, `D` (the extreme selected
  lines, so that `A, B ∈ xs` and `C, D ∈ ys`, as the consumer's gap hypotheses at the
  endpoints of `[A,B]` and `[C,D]` require), the four gap hypotheses
  `hxfwd`/`hxbwd`/`hyfwd`/`hybwd` with `g = 2w`, and the two families of line-oscillation
  bounds, in the exact form `ReflectedGMS.goodGrid_uniform_interior_control` and
  `ReflectedGMS.exists_gridRectangle_of_notMem_gridCells` consume.  The location clauses
  record the manuscript's "the extreme lines surround `clB R` with a positive macroscopic
  margin": the grid rectangle `[A,B] × [C,D]` contains `[A₀ + w, A₀ + (n-1) w]²` and is
  contained in `[A₀, A₀ + n w]²`.

* `exists_goodGrid_uniform_interior_control` — the selection composed with the already
  checked deterministic good-grid step, i.e. the two ingredients the manuscript feeds
  into the variational maximum principle: the skeleton bound `s:eq:gridresidual`
  `osc_𝒯 f ≤ 3 t` and the enclosing grid rectangle with sides at most `4 w` for every
  remaining cell of the patch.

The oscillation bounds are selected for the full span `[A₀, A₀ + n w]` of the grid and
then transported to the shorter spans `[A,B]`, `[C,D]` cut out by the extreme selected
lines; this is `horizontalLineOscillation_mono_segment` and its vertical analogue, which
hold because shrinking a segment can only shrink the set of cells meeting it.

No harmonicity, minimality or centroid statement occurs here: this module only selects
offsets.  The representative/centroid distinction and the uniform-in-cells radius
quantifiers of the consumers are untouched.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.GoodOffsetWindowAssembly

variable {V : Type*}

/-! ### Monotonicity of the line oscillations in the segment -/

/-- Shrinking a horizontal segment can only shrink its oscillation: every cell meeting the
shorter segment meets the longer one. -/
theorem horizontalLineOscillation_mono_segment (F : IndexedCells V) (f : V → ℝ)
    {a b a' b' y : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    horizontalLineOscillation F f a b y ≤ horizontalLineOscillation F f a' b' y := by
  have hsub : horizontal a b y ⊆ horizontal a' b' y := fun z hz =>
    ⟨le_trans ha hz.1, le_trans hz.2.1 hb, hz.2.2⟩
  refine iSup_le fun v => iSup_le fun w => ?_
  exact le_iSup_of_le
      ⟨v.1, mem_hittingVertices.mp (mem_hittingVertices_of_hits_subset F hsub v.2)⟩
    (le_iSup_of_le
      ⟨w.1, mem_hittingVertices.mp (mem_hittingVertices_of_hits_subset F hsub w.2)⟩ le_rfl)

/-- Shrinking a vertical segment can only shrink its oscillation. -/
theorem verticalLineOscillation_mono_segment (F : IndexedCells V) (f : V → ℝ)
    {a b a' b' x : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    verticalLineOscillation F f a b x ≤ verticalLineOscillation F f a' b' x := by
  have hsub : vertical x a b ⊆ vertical x a' b' := fun z hz =>
    ⟨hz.1, le_trans ha hz.2.1, le_trans hz.2.2 hb⟩
  refine iSup_le fun v => iSup_le fun w => ?_
  exact le_iSup_of_le
      ⟨v.1, mem_hittingVertices.mp (mem_hittingVertices_of_hits_subset F hsub v.2)⟩
    (le_iSup_of_le
      ⟨w.1, mem_hittingVertices.mp (mem_hittingVertices_of_hits_subset F hsub w.2)⟩ le_rfl)

/-! ### The gap property of one selected coordinate per window -/

/-- **Forward gap.**  If `x k` lies in the `k`-th window `[A₀ + k w, A₀ + (k+1) w]` for
every `k < n`, then every `u` between the two extreme selected coordinates has a selected
coordinate in `[u, u + 2w]`.  This is the forward half of the manuscript's "consecutive
selected coordinates are at distance at most `2 α R`". -/
theorem exists_forward_gap_of_windows {A₀ w : ℝ} (hw : 0 ≤ w) {n : ℕ} (hn : 0 < n)
    (x : ℕ → ℝ) (hlow : ∀ k, k < n → A₀ + (k : ℝ) * w ≤ x k)
    (hhigh : ∀ k, k < n → x k ≤ A₀ + ((k : ℝ) + 1) * w)
    {u : ℝ} (hu0 : x 0 ≤ u) (hu1 : u ≤ x (n - 1)) :
    ∃ k, k < n ∧ u ≤ x k ∧ x k ≤ u + 2 * w := by
  classical
  have hex : ∃ k, k < n ∧ u ≤ x k := ⟨n - 1, by omega, hu1⟩
  obtain ⟨k, hkn, hku, hmin⟩ :
      ∃ k, k < n ∧ u ≤ x k ∧ ∀ m, m < k → ¬(m < n ∧ u ≤ x m) :=
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      fun m hm => Nat.find_min hex hm⟩
  refine ⟨k, hkn, hku, ?_⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    linarith
  · have hk1n : k - 1 < n := by omega
    have hlt : x (k - 1) < u := by
      by_contra hcon
      exact hmin (k - 1) (by omega) ⟨hk1n, not_lt.mp hcon⟩
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hkpos, Nat.cast_one]
    have h1 : A₀ + ((k : ℝ) - 1) * w ≤ x (k - 1) := by
      have h := hlow (k - 1) hk1n
      rwa [hcast] at h
    have h2 : x k ≤ A₀ + ((k : ℝ) + 1) * w := hhigh k hkn
    have hring : A₀ + ((k : ℝ) + 1) * w = A₀ + ((k : ℝ) - 1) * w + 2 * w := by ring
    linarith

/-- **Backward gap.**  The mirror statement: every `u` between the two extreme selected
coordinates has a selected coordinate in `[u - 2w, u]`. -/
theorem exists_backward_gap_of_windows {A₀ w : ℝ} (hw : 0 ≤ w) {n : ℕ} (hn : 0 < n)
    (x : ℕ → ℝ) (hlow : ∀ k, k < n → A₀ + (k : ℝ) * w ≤ x k)
    (hhigh : ∀ k, k < n → x k ≤ A₀ + ((k : ℝ) + 1) * w)
    {u : ℝ} (hu0 : x 0 ≤ u) (hu1 : u ≤ x (n - 1)) :
    ∃ k, k < n ∧ u - 2 * w ≤ x k ∧ x k ≤ u := by
  classical
  obtain ⟨m, hmle, hmP, hmax⟩ :
      ∃ m, m ≤ n - 1 ∧ x m ≤ u ∧ ∀ j, m < j → j ≤ n - 1 → ¬(x j ≤ u) :=
    ⟨Nat.findGreatest (fun k => x k ≤ u) (n - 1), Nat.findGreatest_le _,
      Nat.findGreatest_spec (P := fun k => x k ≤ u) (m := 0) (Nat.zero_le _) hu0,
      fun j hj hjn => Nat.findGreatest_is_greatest (P := fun k => x k ≤ u) hj hjn⟩
  refine ⟨m, by omega, ?_, hmP⟩
  rcases eq_or_lt_of_le hmle with hmeq | hmlt
  · have hum : u ≤ x m := by rw [hmeq]; exact hu1
    linarith
  · have hlt : u < x (m + 1) := not_le.mp (hmax (m + 1) (by omega) (by omega))
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have h1 : x (m + 1) ≤ A₀ + ((m : ℝ) + 1 + 1) * w := by
      have h := hhigh (m + 1) (by omega)
      rwa [hcast] at h
    have h2 : A₀ + (m : ℝ) * w ≤ x m := hlow m (by omega)
    have hring : A₀ + ((m : ℝ) + 1 + 1) * w = A₀ + (m : ℝ) * w + 2 * w := by ring
    linarith

/-! ### The assembled good grid -/

/-- **Window-by-window good-offset selection for the grid.**

Divide `[A₀, A₀ + n w]` into the `n` windows of length `w`.  If the patch mass and the
patch energy of `f` on `Q` are small compared with `t · w` — the quantitative form of the
manuscript's Markov step on the variation-bad set — then each window interior contains a
good horizontal offset and a good vertical offset, and the resulting grid satisfies every
hypothesis of `ReflectedGMS.goodGrid_uniform_interior_control` and of
`ReflectedGMS.exists_gridRectangle_of_notMem_gridCells`, with gap `g = 2w`:

* the extreme selected lines are the sides of the patch, so `xs ⊆ [A,B]` and `ys ⊆ [C,D]`
  while the gap property still holds at the endpoints of those intervals;
* the grid rectangle `[A,B] × [C,D]` contains `[A₀ + w, A₀ + (n-1) w]²` and is contained
  in `[A₀, A₀ + n w]²` — the manuscript's macroscopic margin;
* every selected line carries oscillation at most `t`, for the spans `[A,B]` resp.
  `[C,D]` actually used by the grid;
* every selected coordinate, horizontal or vertical, lies outside the caller's null set
  `Ne`.  Taking `Ne` to contain the coordinate projections of the uncovered set is what
  makes every selected line covered in its entirety under the weakened covering clause of
  `Geometry`, which is what the crossing-cell argument downstream consumes.

With `w = α R / 2`, `A₀ = -2R` and `n w = 4R` this is the manuscript's selection, with
`8N` windows in place of `4N`, giving consecutive selected coordinates at distance at
most `2 α R` exactly as displayed there. -/
theorem exists_goodOffsetGrid_of_patchSmallness [Countable V] (F : IndexedCells V)
    (f : V → ℝ) (hFline : AELineConnected F) (Q : Set Plane) {Ne : Set ℝ}
    (hNe : volume Ne = 0) {A₀ w : ℝ} (hw : 0 < w)
    {n : ℕ} (hn : 0 < n) {t : ℝ≥0∞}
    (hQ : closedPatch A₀ (A₀ + (n : ℝ) * w) A₀ (A₀ + (n : ℝ) * w) ⊆ Q)
    (hsmall : patchDiameterReciprocalConductanceMass F (hittingVertices F Q) ^ (2⁻¹ : ℝ) *
        patchEnergyENN F (hittingVertices F Q) f ^ (2⁻¹ : ℝ) < t * ENNReal.ofReal w) :
    ∃ A B C D : ℝ, ∃ xs ys : Set ℝ,
      A₀ ≤ A ∧ A ≤ A₀ + w ∧ A₀ + ((n : ℝ) - 1) * w ≤ B ∧ B ≤ A₀ + (n : ℝ) * w ∧
      A₀ ≤ C ∧ C ≤ A₀ + w ∧ A₀ + ((n : ℝ) - 1) * w ≤ D ∧ D ≤ A₀ + (n : ℝ) * w ∧
      xs.Nonempty ∧ ys.Nonempty ∧ xs ⊆ Set.Icc A B ∧ ys ⊆ Set.Icc C D ∧
      (∀ u ∈ Set.Icc A B, ∃ x ∈ xs, u ≤ x ∧ x ≤ u + 2 * w) ∧
      (∀ u ∈ Set.Icc A B, ∃ x ∈ xs, u - 2 * w ≤ x ∧ x ≤ u) ∧
      (∀ u ∈ Set.Icc C D, ∃ y ∈ ys, u ≤ y ∧ y ≤ u + 2 * w) ∧
      (∀ u ∈ Set.Icc C D, ∃ y ∈ ys, u - 2 * w ≤ y ∧ y ≤ u) ∧
      (∀ y ∈ ys, horizontalLineOscillation F f A B y ≤ t) ∧
      (∀ x ∈ xs, verticalLineOscillation F f C D x ≤ t) ∧
      (∀ x ∈ xs, x ∉ Ne) ∧ (∀ y ∈ ys, y ∉ Ne) := by
  classical
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hAβ : A₀ < A₀ + (n : ℝ) * w := by nlinarith
  have hn1 : n - 1 < n := by omega
  have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn, Nat.cast_one]
  -- one good horizontal and one good vertical offset in each window interior
  have hsel : ∀ k : ℕ, ∃ z : ℝ × ℝ, k < n →
      (z.1 ∈ Set.Ioo (A₀ + (k : ℝ) * w) (A₀ + ((k : ℝ) + 1) * w) ∧
          horizontalLineOscillation F f A₀ (A₀ + (n : ℝ) * w) z.1 ≤ t) ∧
        ((z.2 ∈ Set.Ioo (A₀ + (k : ℝ) * w) (A₀ + ((k : ℝ) + 1) * w) ∧
          verticalLineOscillation F f A₀ (A₀ + (n : ℝ) * w) z.2 ≤ t) ∧
          (z.2 ∉ Ne ∧ z.1 ∉ Ne)) := by
    intro k
    by_cases hk : k < n
    · have hk1 : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hwin : Set.Ioo (A₀ + (k : ℝ) * w) (A₀ + ((k : ℝ) + 1) * w) ⊆
          Set.Icc A₀ (A₀ + (n : ℝ) * w) := by
        rintro s ⟨hs1, hs2⟩
        have hmono : ((k : ℝ) + 1) * w ≤ (n : ℝ) * w :=
          mul_le_mul_of_nonneg_right hk1 hw.le
        exact ⟨by nlinarith [mul_nonneg hk0 hw.le], by linarith⟩
      have hvol : volume (Set.Ioo (A₀ + (k : ℝ) * w) (A₀ + ((k : ℝ) + 1) * w))
          = ENNReal.ofReal w := by
        rw [Real.volume_Ioo]
        congr 1
        ring
      obtain ⟨⟨y, hy, hyNe, hyosc⟩, ⟨x, hx, hxNe, hxosc⟩⟩ :=
        exists_good_offsets_lineOscillation_le_rectanglePatch F f Q hFline hNe hAβ
          (s := Set.Ioo (A₀ + (k : ℝ) * w) (A₀ + ((k : ℝ) + 1) * w)) measurableSet_Ioo
          (fun y hy s hs => hQ ⟨hs.1, hs.2.1, by rw [hs.2.2]; exact (hwin hy).1,
            by rw [hs.2.2]; exact (hwin hy).2⟩)
          (fun x hx s hs => hQ ⟨by rw [hs.1]; exact (hwin hx).1,
            by rw [hs.1]; exact (hwin hx).2, hs.2.1, hs.2.2⟩)
          (by rw [hvol]; exact hsmall)
      exact ⟨(y, x), fun _ => ⟨⟨hy, hyosc⟩, ⟨hx, hxosc⟩, hxNe, hyNe⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hk⟩
  obtain ⟨yf, xf, hylow, hyhigh, hxlow, hxhigh, hyoscf, hxoscf, hxNef, hyNef⟩ :
      ∃ yf xf : ℕ → ℝ,
        (∀ k, k < n → A₀ + (k : ℝ) * w ≤ yf k) ∧
        (∀ k, k < n → yf k ≤ A₀ + ((k : ℝ) + 1) * w) ∧
        (∀ k, k < n → A₀ + (k : ℝ) * w ≤ xf k) ∧
        (∀ k, k < n → xf k ≤ A₀ + ((k : ℝ) + 1) * w) ∧
        (∀ k, k < n → horizontalLineOscillation F f A₀ (A₀ + (n : ℝ) * w) (yf k) ≤ t) ∧
        (∀ k, k < n → verticalLineOscillation F f A₀ (A₀ + (n : ℝ) * w) (xf k) ≤ t) ∧
        (∀ k, k < n → xf k ∉ Ne) ∧ (∀ k, k < n → yf k ∉ Ne) := by
    choose z hz using hsel
    exact ⟨fun k => (z k).1, fun k => (z k).2,
      fun k hk => ((hz k hk).1.1.1).le, fun k hk => ((hz k hk).1.1.2).le,
      fun k hk => ((hz k hk).2.1.1.1).le, fun k hk => ((hz k hk).2.1.1.2).le,
      fun k hk => (hz k hk).1.2, fun k hk => (hz k hk).2.1.2,
      fun k hk => (hz k hk).2.2.1, fun k hk => (hz k hk).2.2.2⟩
  -- the selected coordinates are ordered by their windows
  have hord : ∀ g : ℕ → ℝ, (∀ k, k < n → A₀ + (k : ℝ) * w ≤ g k) →
      (∀ k, k < n → g k ≤ A₀ + ((k : ℝ) + 1) * w) →
      ∀ k, k < n → g 0 ≤ g k ∧ g k ≤ g (n - 1) := by
    intro g glow ghigh k hk
    constructor
    · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0]
      · have h1 := ghigh 0 hn
        norm_num at h1
        have h2 : A₀ + (k : ℝ) * w ≤ g k := glow k hk
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
        have hmono : (1 : ℝ) * w ≤ (k : ℝ) * w := mul_le_mul_of_nonneg_right hk1 hw.le
        linarith
    · rcases eq_or_lt_of_le (show k ≤ n - 1 by omega) with hkeq | hklt
      · rw [hkeq]
      · have h1 : g k ≤ A₀ + ((k : ℝ) + 1) * w := ghigh k hk
        have h2 : A₀ + ((n : ℝ) - 1) * w ≤ g (n - 1) := by
          have h := glow (n - 1) hn1
          rwa [hcastn] at h
        have hk2 : (k : ℝ) + 2 ≤ (n : ℝ) := by
          have : ((k + 2 : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by
            exact_mod_cast (show k + 2 ≤ n by omega)
          push_cast at this
          linarith
        have hmono : ((k : ℝ) + 1) * w ≤ ((n : ℝ) - 1) * w :=
          mul_le_mul_of_nonneg_right (by linarith) hw.le
        linarith
  have hxord := hord xf hxlow hxhigh
  have hyord := hord yf hylow hyhigh
  have hxA : A₀ ≤ xf 0 := by simpa using hxlow 0 hn
  have hxB : xf (n - 1) ≤ A₀ + (n : ℝ) * w := by
    have h := hxhigh (n - 1) hn1
    rw [hcastn] at h
    linarith
  have hyC : A₀ ≤ yf 0 := by simpa using hylow 0 hn
  have hyD : yf (n - 1) ≤ A₀ + (n : ℝ) * w := by
    have h := hyhigh (n - 1) hn1
    rw [hcastn] at h
    linarith
  refine ⟨xf 0, xf (n - 1), yf 0, yf (n - 1), xf '' Set.Iio n, yf '' Set.Iio n,
    hxA, by simpa using hxhigh 0 hn, ?_, hxB, hyC, by simpa using hyhigh 0 hn, ?_, hyD,
    ⟨xf 0, Set.mem_image_of_mem _ (Set.mem_Iio.mpr hn)⟩,
    ⟨yf 0, Set.mem_image_of_mem _ (Set.mem_Iio.mpr hn)⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hxlow (n - 1) hn1
    rwa [hcastn] at h
  · have h := hylow (n - 1) hn1
    rwa [hcastn] at h
  · rintro s ⟨k, hk, rfl⟩
    exact ⟨(hxord k hk).1, (hxord k hk).2⟩
  · rintro s ⟨k, hk, rfl⟩
    exact ⟨(hyord k hk).1, (hyord k hk).2⟩
  · rintro u ⟨hu0, hu1⟩
    obtain ⟨k, hk, h1, h2⟩ :=
      exists_forward_gap_of_windows hw.le hn xf hxlow hxhigh hu0 hu1
    exact ⟨xf k, Set.mem_image_of_mem _ (Set.mem_Iio.mpr hk), h1, h2⟩
  · rintro u ⟨hu0, hu1⟩
    obtain ⟨k, hk, h1, h2⟩ :=
      exists_backward_gap_of_windows hw.le hn xf hxlow hxhigh hu0 hu1
    exact ⟨xf k, Set.mem_image_of_mem _ (Set.mem_Iio.mpr hk), h1, h2⟩
  · rintro u ⟨hu0, hu1⟩
    obtain ⟨k, hk, h1, h2⟩ :=
      exists_forward_gap_of_windows hw.le hn yf hylow hyhigh hu0 hu1
    exact ⟨yf k, Set.mem_image_of_mem _ (Set.mem_Iio.mpr hk), h1, h2⟩
  · rintro u ⟨hu0, hu1⟩
    obtain ⟨k, hk, h1, h2⟩ :=
      exists_backward_gap_of_windows hw.le hn yf hylow hyhigh hu0 hu1
    exact ⟨yf k, Set.mem_image_of_mem _ (Set.mem_Iio.mpr hk), h1, h2⟩
  · rintro s ⟨k, hk, rfl⟩
    exact le_trans (horizontalLineOscillation_mono_segment F f hxA hxB) (hyoscf k hk)
  · rintro s ⟨k, hk, rfl⟩
    exact le_trans (verticalLineOscillation_mono_segment F f hyC hyD) (hxoscf k hk)
  · rintro s ⟨k, hk, rfl⟩
    exact hxNef k hk
  · rintro s ⟨k, hk, rfl⟩
    exact hyNef k hk

end ReflectedGMS.GoodOffsetWindowAssembly
