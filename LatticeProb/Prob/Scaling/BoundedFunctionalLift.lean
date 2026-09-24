/-
A generic McShane-type Lipschitz extension of a functional built from an integral, needed to
apply an equicontinuity criterion to a random field whose realizations are NOT continuous.

A functional `Φ0 g := F (∫ x in K, g x * h x)` built directly from an integral is Lipschitz for
the sup distance only between functions that are measurable and bounded on `K` (`Nice`): for a
wild non-measurable `g` the Bochner integral silently returns the junk value `0`, so `Φ0`'s
value at `g` can be far from its value at a "nice" function pointwise close to `g`, breaking
any Lipschitz bound that does not restrict to `Nice` inputs.

The fix is a genuine Lipschitz extension of `Φ0` off `Nice` to ALL of `E → ℝ`, as an infimal
convolution against a unit-capped sup distance restricted to `K`, where the convolution ranges
only over `Nice` comparison functions.

`E` is an arbitrary type, `K` an arbitrary set, `Nice` a plain abstract predicate; no
model-specific object appears in any statement.

Moved from Parking-Sharpness.
-/
import Mathlib

open MeasureTheory

noncomputable section

namespace LatticeProb.Scaling.BoundedFunctionalLift

variable {E : Type*}

/-! ### The unit-capped and plain sup distances restricted to a set -/

/-- The unit-capped sup distance between two functions, restricted to `K`.  Well-defined (via
`Real.iSup`, whose junk value on an unbounded or empty family is `0`) for functions of any size,
continuous or not, measurable or not. -/
def capDistOn (K : Set E) (v w : E → ℝ) : ℝ := ⨆ p ∈ K, min 1 |v p - w p|

/-- The unit-capped sup distance is nonnegative. -/
theorem capDistOn_nonneg (K : Set E) (v w : E → ℝ) : 0 ≤ capDistOn K v w :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => le_min zero_le_one (abs_nonneg _)

/-- The unit-capped sup distance is at most `1`. -/
theorem capDistOn_le_one (K : Set E) (v w : E → ℝ) : capDistOn K v w ≤ 1 :=
  Real.iSup_le (fun _ => Real.iSup_le (fun _ => min_le_left _ _) zero_le_one) zero_le_one

/-- Each summand of the unit-capped sup distance, before the outer supremum over `K`, is bounded
above by `1`. -/
theorem bddAbove_capDistOn_summand (K : Set E) (v w : E → ℝ) (p : E) :
    BddAbove (Set.range fun _ : p ∈ K => min 1 |v p - w p|) :=
  ⟨1, by rintro _ ⟨_, rfl⟩; exact min_le_left _ _⟩

/-- The outer supremum defining the unit-capped sup distance is bounded above by `1`. -/
theorem bddAbove_capDistOn_outer (K : Set E) (v w : E → ℝ) :
    BddAbove (Set.range fun p : E => ⨆ _ : p ∈ K, min 1 |v p - w p|) :=
  ⟨1, by rintro _ ⟨p, rfl⟩; exact Real.iSup_le (fun _ => min_le_left _ _) zero_le_one⟩

/-- Every pointwise capped gap at a point of `K` is bounded by the unit-capped sup distance. -/
theorem le_capDistOn {K : Set E} {v w : E → ℝ} {p : E} (hp : p ∈ K) :
    min 1 |v p - w p| ≤ capDistOn K v w := by
  calc min 1 |v p - w p| = ⨆ _ : p ∈ K, min 1 |v p - w p| :=
        (ciSup_pos (f := fun _ : p ∈ K => min 1 |v p - w p|) hp).symm
    _ ≤ ⨆ q ∈ K, min 1 |v q - w q| := le_ciSup (bddAbove_capDistOn_outer K v w) p

/-- The unit-capped sup distance of a function to itself is zero. -/
theorem capDistOn_self (K : Set E) (v : E → ℝ) : capDistOn K v v = 0 := by
  refine le_antisymm (Real.iSup_le (fun _ => Real.iSup_le (fun _ => ?_) le_rfl) le_rfl)
    (capDistOn_nonneg K v v)
  simp

/-- The unit-capped sup distance is symmetric. -/
theorem capDistOn_comm (K : Set E) (v w : E → ℝ) : capDistOn K v w = capDistOn K w v := by
  unfold capDistOn; simp_rw [abs_sub_comm]

/-- The unit cap is subadditive on nonnegative reals: `min 1 (a + b) ≤ min 1 a + min 1 b`. -/
theorem min_one_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min 1 (a + b) ≤ min 1 a + min 1 b := by
  rcases le_total 1 a with h | h
  · have h1 : min 1 a = 1 := min_eq_left h
    have h2 : (0 : ℝ) ≤ min 1 b := le_min zero_le_one hb
    rw [h1]; linarith [min_le_left (1 : ℝ) (a + b)]
  rcases le_total 1 b with h' | h'
  · have h1 : min 1 b = 1 := min_eq_left h'
    have h2 : (0 : ℝ) ≤ min 1 a := le_min zero_le_one ha
    rw [h1]; linarith [min_le_left (1 : ℝ) (a + b)]
  · rw [min_eq_right h, min_eq_right h']; exact min_le_right _ _

/-- The unit-capped sup distance satisfies the triangle inequality. -/
theorem capDistOn_le_add (K : Set E) (v w u : E → ℝ) :
    capDistOn K v w ≤ capDistOn K v u + capDistOn K u w := by
  refine Real.iSup_le (fun p => Real.iSup_le (fun hp => ?_)
    (add_nonneg (capDistOn_nonneg K v u) (capDistOn_nonneg K u w)))
    (add_nonneg (capDistOn_nonneg K v u) (capDistOn_nonneg K u w))
  have hstep : |v p - w p| ≤ |v p - u p| + |u p - w p| := by
    have := abs_sub_le (v p) (u p) (w p); linarith
  calc min 1 |v p - w p| ≤ min 1 (|v p - u p| + |u p - w p|) := min_le_min le_rfl hstep
    _ ≤ min 1 |v p - u p| + min 1 |u p - w p| :=
        min_one_add_le _ _ (abs_nonneg _) (abs_nonneg _)
    _ ≤ capDistOn K v u + capDistOn K u w :=
        add_le_add (le_capDistOn hp) (le_capDistOn hp)

/-- The plain (uncapped) sup distance between two functions, restricted to `K`.  Only meaningful
(non-junk) when `v - w` is bounded on `K`. -/
def supDistOn (K : Set E) (v w : E → ℝ) : ℝ := ⨆ p ∈ K, |v p - w p|

/-- The plain sup distance is nonnegative. -/
theorem supDistOn_nonneg (K : Set E) (v w : E → ℝ) : 0 ≤ supDistOn K v w :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _

/-- The outer supremum defining the plain sup distance is bounded above by any uniform bound
`M` on the pointwise gaps on `K`. -/
theorem bddAbove_supDistOn_outer {K : Set E} {v w : E → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ p ∈ K, |v p - w p| ≤ M) :
    BddAbove (Set.range fun p : E => ⨆ _ : p ∈ K, |v p - w p|) :=
  ⟨M, by rintro _ ⟨p, rfl⟩; exact Real.iSup_le (fun hp => hb p hp) hM⟩

/-- Every pointwise gap at a point of `K` is bounded by the plain sup distance, given a uniform
bound `M` on the pointwise gaps. -/
theorem le_supDistOn {K : Set E} {v w : E → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ p ∈ K, |v p - w p| ≤ M) {p : E} (hp : p ∈ K) : |v p - w p| ≤ supDistOn K v w := by
  calc |v p - w p| = ⨆ _ : p ∈ K, |v p - w p| :=
        (ciSup_pos (f := fun _ : p ∈ K => |v p - w p|) hp).symm
    _ ≤ ⨆ q ∈ K, |v q - w q| := le_ciSup (bddAbove_supDistOn_outer hM hb) p

/-- **If `capDistOn K v w < 1` then it equals the plain sup distance**, and in particular the
plain sup distance is itself below `1`.  No boundedness hypothesis: a capped distance strictly
below `1` forces every pointwise gap on `K` below `1`, so the cap never engages. -/
theorem capDistOn_eq_supDistOn_of_lt_one {K : Set E} {v w : E → ℝ} (h : capDistOn K v w < 1) :
    capDistOn K v w = supDistOn K v w ∧ supDistOn K v w < 1 := by
  have hbstrict : ∀ p ∈ K, |v p - w p| < 1 := by
    intro p hp
    rcases lt_or_ge (|v p - w p|) 1 with h' | h'
    · exact h'
    · exfalso
      have h1 : min 1 |v p - w p| = 1 := min_eq_left h'
      have h2 : (1 : ℝ) ≤ capDistOn K v w := h1 ▸ le_capDistOn hp
      linarith
  have heq : capDistOn K v w = supDistOn K v w := by
    unfold capDistOn supDistOn
    refine iSup_congr fun p => iSup_congr fun hp => ?_
    exact min_eq_right (hbstrict p hp).le
  refine ⟨heq, ?_⟩
  rw [← heq]; exact h

/-! ### The McShane lift, as an infimal convolution against `capDistOn`, over `Nice` comparisons -/

/-- The defining set of the McShane lift at `v`: the infimal convolution ranges only over `Nice`
comparison functions `G` (this is what keeps the lift sound when `Φ0` is only Lipschitz on
`Nice` inputs; letting `G` range over ALL of `E → ℝ` would reintroduce the junk-value hazard,
since a wild non-measurable `G` pointwise close to a nice `H` can have `Φ0 G` far from `Φ0 H`). -/
def liftPhiOnSet (K : Set E) (Φ0 : (E → ℝ) → ℝ) (Nice : (E → ℝ) → Prop) (L0 : ℝ) (v : E → ℝ) :
    Set ℝ :=
  {y : ℝ | ∃ G : E → ℝ, Nice G ∧ y = Φ0 G + L0 * capDistOn K v G}

/-- The defining set of the McShane lift is nonempty, witnessed by any `Nice` comparison
function. -/
theorem liftPhiOnSet_nonempty {K : Set E} {Φ0 : (E → ℝ) → ℝ} {Nice : (E → ℝ) → Prop}
    {G0 : E → ℝ} (hG0 : Nice G0) (L0 : ℝ) (v : E → ℝ) :
    (liftPhiOnSet K Φ0 Nice L0 v).Nonempty :=
  ⟨Φ0 G0 + L0 * capDistOn K v G0, G0, hG0, rfl⟩

/-- The defining set of the McShane lift is bounded below, given a uniform bound `M0` on
`Φ0`. -/
theorem bddBelow_liftPhiOnSet (K : Set E) (Φ0 : (E → ℝ) → ℝ) (Nice : (E → ℝ) → Prop) {M0 : ℝ}
    (hΦ0 : ∀ G, |Φ0 G| ≤ M0) {L0 : ℝ} (hL0 : 0 ≤ L0) (v : E → ℝ) :
    BddBelow (liftPhiOnSet K Φ0 Nice L0 v) := by
  refine ⟨-M0, ?_⟩
  rintro y ⟨G, -, rfl⟩
  have h1 : -M0 ≤ Φ0 G := neg_le_of_abs_le (hΦ0 G)
  have h2 : 0 ≤ L0 * capDistOn K v G := mul_nonneg hL0 (capDistOn_nonneg K v G)
  linarith

/-- **The McShane lift restricted to `K`, over `Nice` comparisons**: the infimal convolution of
`Φ0` against `L0` times the unit-capped distance on `K`. -/
def liftPhiOn (K : Set E) (Φ0 : (E → ℝ) → ℝ) (Nice : (E → ℝ) → Prop) (L0 : ℝ) (v : E → ℝ) : ℝ :=
  sInf (liftPhiOnSet K Φ0 Nice L0 v)

/-- The lift is bounded above by the value of the infimal convolution at any `Nice`
comparison function. -/
theorem liftPhiOn_le (K : Set E) (Φ0 : (E → ℝ) → ℝ) (Nice : (E → ℝ) → Prop) {M0 L0 : ℝ}
    (hΦ0 : ∀ G, |Φ0 G| ≤ M0) (hL0 : 0 ≤ L0) (v : E → ℝ) {G : E → ℝ} (hG : Nice G) :
    liftPhiOn K Φ0 Nice L0 v ≤ Φ0 G + L0 * capDistOn K v G :=
  csInf_le (bddBelow_liftPhiOnSet K Φ0 Nice hΦ0 hL0 v) ⟨G, hG, rfl⟩

/-- For every `ε > 0` there is a `Nice` comparison function whose infimal-convolution value
is within `ε` of the lift. -/
theorem exists_liftPhiOn_near (K : Set E) (Φ0 : (E → ℝ) → ℝ) (Nice : (E → ℝ) → Prop)
    {G0 : E → ℝ} (hG0 : Nice G0) (L0 : ℝ) (v : E → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : E → ℝ, Nice G ∧ Φ0 G + L0 * capDistOn K v G < liftPhiOn K Φ0 Nice L0 v + ε := by
  obtain ⟨y, hy, hylt⟩ := exists_lt_of_csInf_lt (liftPhiOnSet_nonempty hG0 L0 v)
    (lt_add_of_pos_right (liftPhiOn K Φ0 Nice L0 v) hε)
  obtain ⟨G, hG, rfl⟩ := hy
  exact ⟨G, hG, hylt⟩

/-- The lift at `v` is bounded by the lift at `w` plus `L0` times the unit-capped sup distance
between `v` and `w`: the half of the Lipschitz bound `abs_liftPhiOn_sub_le` proves directly. -/
theorem liftPhiOn_le_add (K : Set E) (Φ0 : (E → ℝ) → ℝ) (Nice : (E → ℝ) → Prop) {G0 : E → ℝ}
    (hG0 : Nice G0) {M0 L0 : ℝ} (hΦ0 : ∀ G, |Φ0 G| ≤ M0) (hL0 : 0 ≤ L0) (v w : E → ℝ) :
    liftPhiOn K Φ0 Nice L0 v ≤ liftPhiOn K Φ0 Nice L0 w + L0 * capDistOn K v w := by
  refine le_of_forall_sub_le fun ε hε => ?_
  obtain ⟨G, hG, hGlt⟩ := exists_liftPhiOn_near K Φ0 Nice hG0 L0 w hε
  have h1 : liftPhiOn K Φ0 Nice L0 v ≤ Φ0 G + L0 * capDistOn K v G :=
    liftPhiOn_le K Φ0 Nice hΦ0 hL0 v hG
  have h2 : capDistOn K v G ≤ capDistOn K v w + capDistOn K w G := capDistOn_le_add K v G w
  have h3 : Φ0 G + L0 * capDistOn K v G ≤
      (Φ0 G + L0 * capDistOn K w G) + L0 * capDistOn K v w := by nlinarith
  linarith

/-- **The lift is `L0`-Lipschitz for `capDistOn K`, on ALL functions `E → ℝ`.** -/
theorem abs_liftPhiOn_sub_le (K : Set E) (Φ0 : (E → ℝ) → ℝ) (Nice : (E → ℝ) → Prop) {G0 : E → ℝ}
    (hG0 : Nice G0) {M0 L0 : ℝ} (hΦ0 : ∀ G, |Φ0 G| ≤ M0) (hL0 : 0 ≤ L0) (v w : E → ℝ) :
    |liftPhiOn K Φ0 Nice L0 v - liftPhiOn K Φ0 Nice L0 w| ≤ L0 * capDistOn K v w := by
  rw [abs_sub_le_iff]
  refine ⟨by linarith [liftPhiOn_le_add K Φ0 Nice hG0 hΦ0 hL0 v w], ?_⟩
  have h := liftPhiOn_le_add K Φ0 Nice hG0 hΦ0 hL0 w v
  rw [capDistOn_comm K w v] at h
  linarith

/-- **The lift is bounded by `M0 + L0`, on ALL functions `E → ℝ`.** -/
theorem abs_liftPhiOn_le (K : Set E) (Φ0 : (E → ℝ) → ℝ) (Nice : (E → ℝ) → Prop) {G0 : E → ℝ}
    (hG0 : Nice G0) {M0 L0 : ℝ} (hΦ0 : ∀ G, |Φ0 G| ≤ M0) (hL0 : 0 ≤ L0) (v : E → ℝ) :
    |liftPhiOn K Φ0 Nice L0 v| ≤ M0 + L0 := by
  have hupper : liftPhiOn K Φ0 Nice L0 v ≤ Φ0 G0 + L0 * capDistOn K v G0 :=
    liftPhiOn_le K Φ0 Nice hΦ0 hL0 v hG0
  have hb1 : Φ0 G0 + L0 * capDistOn K v G0 ≤ M0 + L0 := by
    have h0 := abs_le.mp (hΦ0 G0)
    have hc := capDistOn_le_one K v G0
    have hc0 := capDistOn_nonneg K v G0
    nlinarith
  have hlower : -M0 ≤ liftPhiOn K Φ0 Nice L0 v :=
    le_csInf (liftPhiOnSet_nonempty hG0 L0 v) (by
      rintro y ⟨G, -, rfl⟩
      have h1 : -M0 ≤ Φ0 G := neg_le_of_abs_le (hΦ0 G)
      have h2 : 0 ≤ L0 * capDistOn K v G := mul_nonneg hL0 (capDistOn_nonneg K v G)
      linarith)
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-! ### The lift recovers `Φ0` exactly on `Nice` inputs -/

/-- **The lift recovers `Φ0` exactly on any `Nice` function**, at `L0 := L0' + 2 * M0` for a
`Φ0` bounded EVERYWHERE by `M0` and `L0'`-Lipschitz for `supDistOn K` BETWEEN `Nice` functions:
the far regime (`capDistOn K H G = 1`), where the unit cap saturates, needs boundedness alone
(the plain `hΦ0`, unconditional on `G`), and that is exactly what the `2 * M0` term supplies;
the near regime (`capDistOn K H G < 1`) uses `hΦ0lip`, which needs `G` `Nice` (this is exactly
where restricting `liftPhiOnSet` to `Nice` comparisons pays off: the `G` produced by `rintro` in
the proof below is guaranteed `Nice`, matching what `hΦ0lip` requires). -/
theorem liftPhiOn_eq_of_nice (K : Set E) (Φ0 : (E → ℝ) → ℝ) (Nice : (E → ℝ) → Prop) {M0 L0' : ℝ}
    (hΦ0 : ∀ G, |Φ0 G| ≤ M0)
    {H : E → ℝ} (hH : Nice H)
    (hΦ0lip : ∀ G : E → ℝ, Nice G → |Φ0 H - Φ0 G| ≤ L0' * supDistOn K H G)
    (hL0' : 0 ≤ L0') :
    liftPhiOn K Φ0 Nice (L0' + 2 * M0) H = Φ0 H := by
  set L0 := L0' + 2 * M0 with hL0def
  have hM0nn : 0 ≤ M0 := le_trans (abs_nonneg _) (hΦ0 H)
  have hL0 : 0 ≤ L0 := by rw [hL0def]; linarith
  refine le_antisymm ?_ ?_
  · have hself : capDistOn K H H = 0 := capDistOn_self K H
    have hle := liftPhiOn_le K Φ0 Nice hΦ0 hL0 H hH
    rw [hself, mul_zero, add_zero] at hle
    exact hle
  · refine le_csInf (liftPhiOnSet_nonempty hH L0 H) ?_
    rintro y ⟨G, hG, rfl⟩
    rcases eq_or_lt_of_le (capDistOn_le_one K H G) with hd | hd
    · -- far regime: `capDistOn K H G = 1`, boundedness alone suffices
      have h1 := abs_le.mp (hΦ0 H)
      have h2 := abs_le.mp (hΦ0 G)
      have hcap : L0 * capDistOn K H G = L0 := by rw [hd, mul_one]
      nlinarith [hcap]
    · -- near regime: `capDistOn K H G < 1`, so it equals the genuine sup distance
      obtain ⟨heq, hlt1⟩ := capDistOn_eq_supDistOn_of_lt_one hd
      have hlip := hΦ0lip G hG
      have hsupnn : 0 ≤ supDistOn K H G := supDistOn_nonneg K H G
      have hLL : L0' * supDistOn K H G ≤ L0 * supDistOn K H G :=
        mul_le_mul_of_nonneg_right (by linarith) hsupnn
      rw [heq]
      linarith [abs_le.mp hlip]

/-! ### A uniform-continuity modulus for the lift, from the Lipschitz bound alone -/

/-- **A uniform change of size `δ` on `K` bounds `capDistOn` by `min 1 δ`.** -/
theorem capDistOn_le_of_forall {K : Set E} {v w : E → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ z ∈ K, |v z - w z| ≤ δ) : capDistOn K v w ≤ min 1 δ :=
  Real.iSup_le
    (fun z => Real.iSup_le (fun hz => min_le_min le_rfl (h z hz)) (le_min zero_le_one hδ))
    (le_min zero_le_one hδ)

/-- **The lift is uniformly continuous for the sup distance on `K`, on ALL functions `E → ℝ`,
stated in the exact `hΦu` shape `LatticeProb.tendsto_integral_of_fdd_of_equicontinuous'` needs**:
no continuity hypothesis on either side, derived directly from the global Lipschitz bound
`abs_liftPhiOn_sub_le` (which already holds on all of `E → ℝ`, not merely on `Nice` functions). -/
theorem hΦu_of_lipschitz (K : Set E) (Φ0 : (E → ℝ) → ℝ) (Nice : (E → ℝ) → Prop) {M0 L0 : ℝ}
    (hΦ0 : ∀ G, |Φ0 G| ≤ M0) (hL0 : 0 ≤ L0) {G0 : E → ℝ} (hG0 : Nice G0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v w : E → ℝ,
      (∀ z ∈ K, |v z - w z| ≤ δ) → |liftPhiOn K Φ0 Nice L0 v - liftPhiOn K Φ0 Nice L0 w| ≤ ε := by
  intro ε hε
  refine ⟨ε / (L0 + 1), by positivity, fun v w hvw => ?_⟩
  have hcap : capDistOn K v w ≤ ε / (L0 + 1) :=
    le_trans (capDistOn_le_of_forall (by positivity) hvw) (min_le_right _ _)
  have hb : |liftPhiOn K Φ0 Nice L0 v - liftPhiOn K Φ0 Nice L0 w| ≤ L0 * capDistOn K v w :=
    abs_liftPhiOn_sub_le K Φ0 Nice hG0 hΦ0 hL0 v w
  have h2 : L0 * (ε / (L0 + 1)) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0:ℝ) < L0 + 1)]
    nlinarith
  calc |liftPhiOn K Φ0 Nice L0 v - liftPhiOn K Φ0 Nice L0 w| ≤ L0 * capDistOn K v w := hb
    _ ≤ L0 * (ε / (L0 + 1)) := mul_le_mul_of_nonneg_left hcap hL0
    _ ≤ ε := h2


/-- A uniform change in the original functional gives the same bound on its lift. -/
theorem liftPhiOn_le_add_of_le (K : Set E) (Φ Ψ : (E → ℝ) → ℝ)
    (Nice : (E → ℝ) → Prop) {G0 : E → ℝ} (hG0 : Nice G0)
    {MΦ L0 c : ℝ} (hΦ : ∀ G, |Φ G| ≤ MΦ) (hL0 : 0 ≤ L0)
    (hle : ∀ G, Nice G → Φ G ≤ Ψ G + c) (v : E → ℝ) :
    liftPhiOn K Φ Nice L0 v ≤ liftPhiOn K Ψ Nice L0 v + c := by
  refine le_of_forall_sub_le fun ε hε => ?_
  obtain ⟨G, hG, hnear⟩ := exists_liftPhiOn_near K Ψ Nice hG0 L0 v hε
  have hupper := liftPhiOn_le K Φ Nice hΦ hL0 v hG
  have hcompare := hle G hG
  linarith

/-- The lift preserves a uniform bound on the difference between two functionals. -/
theorem abs_liftPhiOn_sub_le_of_abs_sub_le (K : Set E) (Φ Ψ : (E → ℝ) → ℝ)
    (Nice : (E → ℝ) → Prop) {G0 : E → ℝ} (hG0 : Nice G0)
    {MΦ MΨ L0 c : ℝ} (hΦ : ∀ G, |Φ G| ≤ MΦ) (hΨ : ∀ G, |Ψ G| ≤ MΨ)
    (hL0 : 0 ≤ L0) (hle : ∀ G, Nice G → |Φ G - Ψ G| ≤ c) (v : E → ℝ) :
    |liftPhiOn K Φ Nice L0 v - liftPhiOn K Ψ Nice L0 v| ≤ c := by
  rw [abs_le]
  constructor
  · have h := liftPhiOn_le_add_of_le K Ψ Φ Nice hG0 (c := c) hΨ hL0
      (fun G hG => by linarith [(abs_le.mp (hle G hG)).1]) v
    linarith
  · have h := liftPhiOn_le_add_of_le K Φ Ψ Nice hG0 (c := c) hΦ hL0
      (fun G hG => by linarith [(abs_le.mp (hle G hG)).2]) v
    linarith

/-- A family Lipschitz in its parameter has a lift uniformly continuous jointly in
that parameter and the field. -/
theorem block_modulus_liftPhiOn {B : Type*} [PseudoMetricSpace B]
    (K : Set E) (Φ : B → (E → ℝ) → ℝ) (Nice : (E → ℝ) → Prop)
    {G0 : E → ℝ} (hG0 : Nice G0) {M L0 C : ℝ}
    (hΦ : ∀ b G, |Φ b G| ≤ M) (hL0 : 0 ≤ L0) (hC : 0 ≤ C)
    (hblock : ∀ a b G, Nice G → |Φ a G - Φ b G| ≤ C * dist a b) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : B, ∀ v w : E → ℝ,
      dist a b ≤ δ → (∀ z ∈ K, |v z - w z| ≤ δ) →
      |liftPhiOn K (Φ a) Nice L0 v - liftPhiOn K (Φ b) Nice L0 w| ≤ ε := by
  intro ε hε
  let δ : ℝ := ε / (C + L0 + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, fun a b v w hab hvw => ?_⟩
  have h1 := abs_liftPhiOn_sub_le_of_abs_sub_le K (Φ a) (Φ b) Nice hG0
    (hΦ a) (hΦ b) hL0 (hblock a b) v
  have h2 := abs_liftPhiOn_sub_le K (Φ b) Nice hG0 (hΦ b) hL0 v w
  have hcap : capDistOn K v w ≤ δ :=
    (capDistOn_le_of_forall hδ.le hvw).trans (min_le_right _ _)
  have htriangle := abs_sub_le (liftPhiOn K (Φ a) Nice L0 v)
    (liftPhiOn K (Φ b) Nice L0 v) (liftPhiOn K (Φ b) Nice L0 w)
  have hmul : (C + L0) * δ ≤ ε := by
    dsimp [δ]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < C + L0 + 1)]
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left hab hC
  have h4 := mul_le_mul_of_nonneg_left hcap hL0
  nlinarith

end LatticeProb.Scaling.BoundedFunctionalLift

end
