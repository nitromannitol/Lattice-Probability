/-
Moved from nitromannitol/Divisible-Sandpile-Percolation, Apache-2.0; copyright
2026 Ahmed Bou-Rabee and Yuval Peres.  Sources:

* `Sandpile/Support/BoxPathCount.lean` (`boxWalkLists` through
  `measure_boxPathEvent_le`); `card_boxFinset` is proved fresh below rather
  than imported from `Sandpile/Support/IncrementBall.lean` (where the source
  states it, at line 169 of an otherwise heavily odometer-specific 700+ line
  file that this module must not depend on): the statement and its four-line
  proof are unchanged, only the file it lives in.  `Sandpile.boxFinset`/
  `boxDist`/`mem_boxFinset` (`Sandpile/Support/Kernel.lean`) are not moved:
  `Sandpile.boxFinset` is byte-identical to the already-existing
  `LatticeProb.boxFinset` (`LatticeProb/ParticleHole.lean`), so the hypothesis
  of `walk_support_mem_boxWalkLists` below is restated with the library's own
  `boxFinset`/`mem_boxFinset_iff` in place of `Sandpile.boxDist`;
* `Sandpile/Support/RswArithmetic.lean` (`eventually_rpow_neg_le`,
  `card_double_square_le_cube`);
* `Sandpile/Support/BoundedBottleneck.lean`, only its opening section
  (`BoundedReach` through `finiteMaximum_mem`).  That file also imports
  `Sandpile.Support.SoftComposition` for a second, later section
  (`abs_softMaximum_sub_finiteMaximum` onward, smooth/softmax approximation of
  `finiteMaximum` along a bisected walk), which is not moved here: nothing in
  the section taken below uses it (confirmed by reading every declaration),
  and it is a companion to the separate `LatticeProb.Analysis.SoftMaximum`
  harvest of `Sandpile/Support/SoftMaximum.lean`.

`Sandpile/Support/RectangleMonotonicity.lean`'s `crossingValue_width_height_
mono`/`measurableSet_planarCrossingEvent`/`planarCrossingEvent_width_height_
mono`, and the deeper `RectangleDuality`/`RectangleComparison`/
`RectangleTranspose`/`RectangleIntersection`/`GridReachability`/`GridDuality`/
`GridCorners`/`RswHardStep`/`RswMeanLower`/`RswSquareHalf(Scale)`/`RswTail`
files the original harvest survey listed alongside these, are **not** moved:
reading their transitive imports shows every one of them reaches, through
`Sandpile/Support/CrossingWitness.lean`, `RectangleBottleneck.lean`,
`KernelPermutation.lean`, `PlanarLaw.lean`, `GaussianIncrement.lean` or
`FarOscillation.lean`, into the paper's own Gaussian continuum-field
comparison and increment-bound machinery, contrary to the survey's claim that
the family depends "on Mathlib (`SimpleGraph`, `Finset`, `MeasurableSet`)
only". Extracting them would need a substantial, non-mechanical rewrite
against a cleaner set of hypotheses, which is out of scope for this move; see
the harvest report for the full dependency trace.
-/
import LatticeProb.ParticleHoleLemmas
import LatticeProb.Prob.Percolation.Crossing

/-!
# RSW amplification arithmetic, bounded-degree path counting, and walk bottlenecks

Three self-contained pieces of the standard RSW (Russo-Seymour-Welsh)
amplification toolkit:

* `card_boxFinset`, `boxWalkLists`, ..., `measure_boxPathEvent_le`: a union
  bound over the finitely many self-avoiding paths of bounded step size
  through a finite set of sites, used to bound the probability that some path
  of "good" vertices exists by the number of candidate paths times the
  probability that any one fixed set of vertices is simultaneously good;
* `eventually_rpow_neg_le`, `card_double_square_le_cube`: two arithmetic
  facts behind the polynomial/exponential trade-off of an RSW amplification
  argument;
* `BoundedReach`, `walkBottleneck`, `walkMidpoints`, `finiteMaximum`: a
  Sudakov-Fernique-style toolkit for the minimum of a real field along a walk
  of length at most `2 ^ n`, including the bisection identity
  `walkBottleneck (p.append q) F = min (walkBottleneck p F) (walkBottleneck q F)`
  that makes such a walk's midpoints exactly the vertices reachable from both
  endpoints within half the depth.
-/

open MeasureTheory Set LatticeProb
open scoped ENNReal

namespace LatticeProb.Percolation

/-! ### The cardinality of a box -/

/-- The sup-norm box of radius `r` about `x` has `(2r+1)^d` sites. -/
theorem card_boxFinset {d : ℕ} (x : Site d) (r : ℕ) :
    (boxFinset x r).card = (2 * r + 1) ^ d := by
  classical
  rw [boxFinset, Fintype.card_piFinset]
  have hfac : ∀ i : Fin d, (Finset.Icc (x i - r) (x i + r)).card = 2 * r + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-! ### Enumerating bounded-step lattice paths -/

noncomputable section

/-- The lists of length `n + 1` starting at `a`, each step moving to a
sup-norm neighbour. -/
def boxWalkLists {d : ℕ} : ℕ → Site d → Finset (List (Site d))
  | 0, a => {[a]}
  | n + 1, a => (boxFinset a 1).biUnion (fun b => (boxWalkLists n b).image (List.cons a))

theorem card_boxWalkLists_le {d : ℕ} (n : ℕ) (a : Site d) :
    (boxWalkLists n a).card ≤ (3 ^ d) ^ n := by
  induction n generalizing a with
  | zero => simp [boxWalkLists]
  | succ n ih =>
    calc
      _ ≤ ∑ b ∈ boxFinset a 1, ((boxWalkLists n b).image (List.cons a)).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ boxFinset a 1, (3 ^ d) ^ n :=
        Finset.sum_le_sum (fun b _ => Finset.card_image_le.trans (ih b))
      _ = _ := by simp [card_boxFinset, pow_succ, Nat.mul_comm]

theorem length_of_mem_boxWalkLists {d : ℕ} {n : ℕ} {a : Site d} {Γ : List (Site d)}
    (hΓ : Γ ∈ boxWalkLists n a) : Γ.length = n + 1 := by
  induction n generalizing a Γ with
  | zero =>
    have he : Γ = [a] := by simpa [boxWalkLists] using hΓ
    simp [he]
  | succ n ih =>
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp hΓ
    obtain ⟨Γ', hΓ', rfl⟩ := Finset.mem_image.mp hb
    simp only [List.length_cons, ih hΓ']

/-- The support of a walk each of whose steps lands in the sup-norm unit ball
of its start is one of the enumerated bounded-step lists. -/
theorem walk_support_mem_boxWalkLists {d : ℕ} {G : SimpleGraph (Site d)}
    (hstep : ∀ a b, G.Adj a b → b ∈ boxFinset a 1) {a b : Site d} (p : G.Walk a b) :
    p.support ∈ boxWalkLists p.length a := by
  induction p with
  | nil => simp [boxWalkLists]
  | @cons a b c hab p ih =>
    exact Finset.mem_biUnion.mpr ⟨b, hstep a b hab,
      Finset.mem_image.mpr ⟨p.support, ih, rfl⟩⟩

/-- The bounded-step lists of length `n + 1` starting somewhere in `S`. -/
def boxWalkListFamily {d : ℕ} (n : ℕ) (S : Finset (Site d)) : Finset (List (Site d)) :=
  S.biUnion (boxWalkLists n)

theorem card_boxWalkListFamily_le {d : ℕ} (n : ℕ) (S : Finset (Site d)) :
    (boxWalkListFamily n S).card ≤ S.card * (3 ^ d) ^ n := by
  calc
    _ ≤ ∑ a ∈ S, (boxWalkLists n a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ S, (3 ^ d) ^ n := Finset.sum_le_sum (fun a _ => card_boxWalkLists_le n a)
    _ = _ := by simp

theorem length_of_mem_boxWalkListFamily {d : ℕ} {n : ℕ} {S : Finset (Site d)} {Γ : List (Site d)}
    (hΓ : Γ ∈ boxWalkListFamily n S) : Γ.length = n + 1 := by
  obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hΓ
  exact length_of_mem_boxWalkLists ha

theorem walk_support_mem_boxWalkListFamily {d : ℕ} {G : SimpleGraph (Site d)}
    (hstep : ∀ a b, G.Adj a b → b ∈ boxFinset a 1) {a b : Site d} (p : G.Walk a b)
    (S : Finset (Site d)) (ha : a ∈ S) : p.support ∈ boxWalkListFamily p.length S :=
  Finset.mem_biUnion.mpr ⟨a, ha, walk_support_mem_boxWalkLists hstep p⟩

/-- The event that some self-avoiding, bounded-step path of length `n + 1`
starting in `S` lies entirely in the events `E`. -/
def boxPathEvent {d : ℕ} {Ω : Type*} (n : ℕ) (S : Finset (Site d)) (E : Site d → Set Ω) : Set Ω :=
  {ω | ∃ Γ ∈ boxWalkListFamily n S, Γ.Nodup ∧ ∀ a ∈ Γ, ω ∈ E a}

/-- **The union bound behind an RSW-style path-existence argument.**  If every
fixed set of `m ≤ n + 1` vertices is simultaneously good with probability at
most `p`, then the probability that some bounded-step path of length `n + 1`
starting in `S` is entirely good is at most the number of candidate paths
times `p`. -/
theorem measure_boxPathEvent_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n m : ℕ) (hm : m ≤ n + 1) (S : Finset (Site d)) (E : Site d → Set Ω) {p : ℝ≥0∞}
    (hT : ∀ T : Finset (Site d), m ≤ T.card → μ {ω | ∀ a ∈ T, ω ∈ E a} ≤ p) :
    μ (boxPathEvent n S E) ≤ (S.card : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) ^ n * p := by
  classical
  let A (Γ : List (Site d)) := {ω | Γ.Nodup ∧ ∀ a ∈ Γ, ω ∈ E a}
  have hA (Γ : List (Site d)) (hΓ : Γ ∈ boxWalkListFamily n S) : μ (A Γ) ≤ p := by
    by_cases hn : Γ.Nodup
    · have he : A Γ = {ω | ∀ a ∈ Γ.toFinset, ω ∈ E a} := by
        ext ω
        simp only [A, mem_setOf_eq, hn, true_and, List.mem_toFinset]
      rw [he]
      apply hT
      rw [List.toFinset_card_of_nodup hn, length_of_mem_boxWalkListFamily hΓ]
      exact hm
    · have he : A Γ = ∅ := by ext ω; simp [A, hn]
      rw [he, measure_empty]
      exact bot_le
  have he : boxPathEvent n S E = ⋃ Γ ∈ boxWalkListFamily n S, A Γ := by
    ext ω
    simp only [boxPathEvent, A, mem_setOf_eq, mem_iUnion, exists_prop]
  rw [he]
  calc
    _ ≤ ∑ Γ ∈ boxWalkListFamily n S, μ (A Γ) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _Γ ∈ boxWalkListFamily n S, p := Finset.sum_le_sum hA
    _ = ((boxWalkListFamily n S).card : ℝ≥0∞) * p := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply mul_le_mul_left
      exact_mod_cast card_boxWalkListFamily_le n S

end

/-! ### RSW amplification arithmetic -/

/-- For every positive `c` the power `r ^ (-c)` is eventually at most any
fixed positive bound. -/
theorem eventually_rpow_neg_le {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    ∀ᶠ r : ℕ in Filter.atTop, (r : ℝ) ^ (-c) ≤ q := by
  have h1 : Filter.Tendsto (fun r : ℕ => Real.log r) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : ∀ᶠ r : ℕ in Filter.atTop, -Real.log q ≤ c * Real.log r := by
    filter_upwards [h1.eventually_ge_atTop (-Real.log q / c)] with r hr
    have hdiv : -Real.log q ≤ c * Real.log r := by
      have := (div_le_iff₀ hc).mp hr
      linarith [this]
    exact hdiv
  have h2 : ∀ᶠ r : ℕ in Filter.atTop, (2 : ℝ) ≤ r := by
    filter_upwards [Filter.eventually_ge_atTop 2] with r hr
    exact_mod_cast hr
  filter_upwards [hlim, h2] with r _ hr2
  have hrpos : (0 : ℝ) < r := by
    have : (2 : ℝ) ≤ r := hr2
    linarith
  have hqexp : q = Real.exp (Real.log q) := (Real.exp_log hq).symm
  have hrw : (r : ℝ) ^ (-c) = Real.exp (-c * Real.log r) := by
    rw [Real.rpow_def_of_pos hrpos]; ring_nf
  rw [hrw, hqexp]
  exact Real.exp_le_exp.mpr (by linarith)

/-- For `r ≥ 7` the square `planeRectangle (2*r) (2*r)` has at most `r ^ 3`
sites. -/
theorem card_double_square_le_cube {r : ℕ} (hr : 7 ≤ r) :
    (planeRectangle (2 * r) (2 * r)).card ≤ r ^ 3 := by
  rw [card_planeRectangle]
  have hrw : r ^ 3 = r * r * r := by norm_num [Nat.pow_succ]
  rw [hrw]
  have h1 : (2 * r + 1) * (2 * r + 1) = 4 * r * r + 4 * r + 1 := by ring
  have h2 : 4 * r * r + 4 * r + 1 ≤ r * r * r := by nlinarith
  rw [h1]; exact h2

/-! ### Bisected walk-bottlenecks -/

variable {V : Type*} (G : SimpleGraph V)

/-- `a` and `b` are joined by a walk of length at most `2 ^ n`. -/
def BoundedReach (n : ℕ) (a b : V) : Prop := ∃ p : G.Walk a b, p.length ≤ 2 ^ n

theorem boundedReach_zero (a b : V) : BoundedReach G 0 a b ↔ a = b ∨ G.Adj a b := by
  constructor
  · rintro ⟨p, hp⟩
    simp only [pow_zero] at hp
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with h | h
    · exact Or.inl (SimpleGraph.Walk.eq_of_length_eq_zero h)
    · exact Or.inr (SimpleGraph.Walk.adj_of_length_eq_one h)
  · rintro (rfl | h)
    · exact ⟨.nil, by simp⟩
    · exact ⟨h.toWalk, by simp⟩

/-- A walk of length at most `2 ^ (n+1)` splits at its midpoint into two
walks of length at most `2 ^ n`, and conversely. -/
theorem boundedReach_succ (n : ℕ) (a b : V) :
    BoundedReach G (n + 1) a b ↔ ∃ c, BoundedReach G n a c ∧ BoundedReach G n c b := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.getVert (2 ^ n), ⟨p.take (2 ^ n), ?_⟩, ⟨p.drop (2 ^ n), ?_⟩⟩
    · simp only [SimpleGraph.Walk.take_length]
      exact min_le_left _ _
    · simp only [SimpleGraph.Walk.drop_length]
      rw [pow_succ] at hp
      omega
  · rintro ⟨c, ⟨p, hp⟩, ⟨q, hq⟩⟩
    refine ⟨p.append q, ?_⟩
    rw [SimpleGraph.Walk.length_append, pow_succ]
    omega

section Bottleneck

variable {G} [DecidableEq V]

/-- The minimum of `F` along the walk `p`. -/
noncomputable def walkBottleneck {a b : V} (p : G.Walk a b) (F : V → ℝ) : ℝ :=
  p.support.toFinset.inf' ⟨a, List.mem_toFinset.mpr p.start_mem_support⟩ F

theorem le_walkBottleneck_iff {a b : V} (p : G.Walk a b) (F : V → ℝ) (c : ℝ) :
    c ≤ walkBottleneck p F ↔ ∀ z ∈ p.support, c ≤ F z := by
  simp [walkBottleneck, Finset.le_inf'_iff]

theorem walkBottleneck_le {a b z : V} (p : G.Walk a b) (F : V → ℝ) (hz : z ∈ p.support) :
    walkBottleneck p F ≤ F z :=
  (le_walkBottleneck_iff p F _).mp le_rfl z hz

theorem walkBottleneck_mem {a b : V} (p : G.Walk a b) (F : V → ℝ) :
    ∃ z ∈ p.support, walkBottleneck p F = F z := by
  obtain ⟨z, hz, he⟩ := Finset.exists_mem_eq_inf'
    (s := p.support.toFinset) ⟨a, List.mem_toFinset.mpr p.start_mem_support⟩ F
  exact ⟨z, List.mem_toFinset.mp hz, he⟩

theorem walkBottleneck_nil (a : V) (F : V → ℝ) : walkBottleneck (.nil (G := G) (u := a)) F = F a := by
  simp [walkBottleneck]

/-- The bisection identity: the bottleneck of a concatenated walk is the
minimum of the two pieces' bottlenecks. -/
theorem walkBottleneck_append {a b c : V} (p : G.Walk a b) (q : G.Walk b c) (F : V → ℝ) :
    walkBottleneck (p.append q) F = min (walkBottleneck p F) (walkBottleneck q F) := by
  apply le_antisymm
  · apply le_min
    · apply (le_walkBottleneck_iff p F _).mpr
      intro z hz
      exact walkBottleneck_le (p.append q) F (p.support_subset_support_append_left q hz)
    · apply (le_walkBottleneck_iff q F _).mpr
      intro z hz
      exact walkBottleneck_le (p.append q) F (p.support_subset_support_append_right q hz)
  · apply (le_walkBottleneck_iff (p.append q) F _).mpr
    intro z hz
    rcases (SimpleGraph.Walk.mem_support_append_iff p q).mp hz with hz | hz
    · exact (min_le_left _ _).trans (walkBottleneck_le p F hz)
    · exact (min_le_right _ _).trans (walkBottleneck_le q F hz)

theorem walkBottleneck_take_drop {a b : V} (p : G.Walk a b) (F : V → ℝ) (n : ℕ) :
    walkBottleneck p F = min (walkBottleneck (p.take n) F) (walkBottleneck (p.drop n) F) := by
  rw [← walkBottleneck_append, SimpleGraph.Walk.append_take_drop_eq]

theorem walkBottleneck_le_bypass {a b : V} (p : G.Walk a b) (F : V → ℝ) :
    walkBottleneck p F ≤ walkBottleneck p.bypass F := by
  apply (le_walkBottleneck_iff p.bypass F _).mpr
  intro z hz
  exact walkBottleneck_le p F (p.support_bypass_subset_support hz)

theorem walkBottleneck_eq_csInf {a b : V} (p : G.Walk a b) (F : V → ℝ) :
    walkBottleneck p F = sInf (F '' {z : V | z ∈ p.support}) := by
  unfold walkBottleneck
  rw [Finset.inf'_eq_csInf_image]
  congr 2
  ext z
  simp

theorem walkBottleneck_of_length_le_one {a b : V} (p : G.Walk a b) (F : V → ℝ)
    (hp : p.length ≤ 1) : walkBottleneck p F = min (F a) (F b) := by
  cases p with
  | nil => simp [walkBottleneck]
  | cons h p =>
    cases p with
    | nil => simp [walkBottleneck, Finset.inf'_insert]
    | cons h' p => simp at hp

end Bottleneck

variable [Fintype V]

/-- The vertices reachable from both `a` and `b` within `2 ^ n` steps: the
candidate midpoints of a walk of length at most `2 ^ (n+1)` from `a` to `b`. -/
noncomputable def walkMidpoints (n : ℕ) (a b : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun c => BoundedReach G n a c ∧ BoundedReach G n c b)

theorem mem_walkMidpoints (n : ℕ) (a b c : V) :
    c ∈ walkMidpoints G n a b ↔ BoundedReach G n a c ∧ BoundedReach G n c b := by
  classical
  simp [walkMidpoints]

theorem walkMidpoints_nonempty {n : ℕ} {a b : V} (h : BoundedReach G (n + 1) a b) :
    (walkMidpoints G n a b).Nonempty := by
  obtain ⟨c, hc⟩ := (boundedReach_succ G n a b).mp h
  exact ⟨c, (mem_walkMidpoints G n a b c).mpr hc⟩

section Maximum

variable {I : Type*} [Fintype I] [Nonempty I]

/-- The maximum of a real function on a nonempty finite type. -/
noncomputable def finiteMaximum (f : I → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty f

theorem le_finiteMaximum (f : I → ℝ) (i : I) : f i ≤ finiteMaximum f :=
  Finset.le_sup' f (Finset.mem_univ i)

theorem finiteMaximum_le_iff (f : I → ℝ) (c : ℝ) : finiteMaximum f ≤ c ↔ ∀ i, f i ≤ c := by
  simp [finiteMaximum, Finset.sup'_le_iff]

theorem finiteMaximum_mem (f : I → ℝ) : ∃ i, finiteMaximum f = f i := by
  obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty f
  exact ⟨i, h⟩

end Maximum

end LatticeProb.Percolation
