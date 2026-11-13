/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.FlowSpaceBlockSystem at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ScaledRootChainSystem
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedRegenerationFlowGrid

/-!
# The block fields of `ScaledRootChainSystem`: an obstruction and a construction

`hsys : ScaledRootChainSystem P ν θ S blkFam sel` (`Limit/ScaledRootChainSystem`) asks, besides
the temporal transport, for a family of time blocks satisfying the pointwise fields of
`ConditionalTemporalAveraging.TemporalBlockSystem` (partition, flow covariance, joint
measurability, positive finite length) and the parabolic covariance `ScaleCovariantBlocks`,
**at every point** of the marked carrier `Ω × Grid`.

## 1. The obstruction (checked)

* `false_of_blocks_scaleFixed`: at a point whose blocks are fixed by a nontrivial scaling
  `S_C` (`C ≠ 1`), `blockScale` forces the origin block `B` to satisfy `B = C² B`, which is
  incompatible with `0 < |B| < ∞`.  In particular no block system exists at a fixed point of
  `S_C`.
* `gridZero`, `gridScale_sqrt_two_gridZero`: the marked grid with phase `0`, all origins `0`
  and all digits `0` is fixed by the parabolic grid scaling `gridScale √2 = dilate 2`.
  Consequently **grid-only blocks are impossible** (`false_of_gridOnly_blocks`): a block family
  that reads only the grid coordinate cannot satisfy `blockScale` on any carrier.  A scale
  reference must come from the configuration.
* `reScale_const_of_isSimilarity`, `false_of_blocks_flowSpace_of_selfSimilar`,
  `not_scaledRootChainSystem_flowSpace_of_selfSimilar`: on `FlowSpace × Grid` with
  `gridFlow`/`gridScaleFlow`, if some valid environment `e` is carried to itself by the
  dilation `z ↦ √2 z` (`IsSimilarity √2 0 _ e e`), then `((e, constant paths), gridZero)` is a
  fixed point of `gridScaleFlow √2`, and **`ScaledRootChainSystem P ν gridFlow gridScaleFlow
  blkFam sel` is false for every `P`, `ν`, `blkFam`, `sel`**.  `Code.Valid` does not require the
  tiling to be locally finite, and a dilation-invariant valid environment is argued to exist
  (cells `√2ⁿ K₀`, `K₀` a closed disc joined to the origin by a segment, plus the annular
  complements; see the handoff `outputs/flowspace-block-system-handoff.2026-09-18.md`).  That
  existence is NOT formalized here.

## 2. The construction (checked, carrier-generic)

A **covariant local time scale** `τ : Ω → ℝ → ℝ` (`LocalTimeScale`: flow and parabolic
covariance, a positive lower bound on bounded intervals, right upper semicontinuity, joint
measurability) yields blocks satisfying every non-transport field:

* `Good τ q ω D k s`: the level-`k` dyadic time block `J` through `s` satisfies
  `|J| ≤ 2^q τ(ω, u)` for all `u ∈ J`; this is downward closed along the dyadic chain;
* `scaleBlock τ q (ω, D) s`: the largest good block through `s` (`selLevel`);
* `scaleSel τ (ω, D) n`: a rational parameter whose origin block is the level-`n` root block.

`scaledRootChainSystem_of_localTimeScale` assembles `ScaledRootChainSystem` from the transport
alone, for ANY `P` and `ν`, on any carrier with a covariant local time scale.
`localTimeScale_toy` shows the hypothesis is satisfiable (on a toy carrier).

## 3. The gated construction (checked, carrier-generic)

`LocalTimeScaleOn G`: the same scale, regular only on a measurable gate `G` invariant under the
flow and the scaling.  `gatedBlock`/`gatedSel` (local-scale blocks on `G`, level-`⌊q⌋` dyadic
blocks off `G`) satisfy every non-transport field of `ScaledRootChainSystem` EVERYWHERE except
`blockScale`, which holds on `G × Grid` (`GatedRootChainBlocks`,
`gatedRootChainBlocks_of_localTimeScaleOn`); with `G = univ` this is the ungated system
(`scaledRootChainSystem_of_gatedRootChainBlocks_univ`).  The single consumer of `blockScale`
survives the gating for functionals vanishing off the gate
(`parabolicCovariantReal_blockTransportReal_of_gate`).

## What is not proved

A covariant local time scale on `FlowSpace`: by §1 none exists if a self-similar valid
environment exists (`not_localTimeScale_flowSpace_of_selfSimilar`); a gated one (`τ` = area of
the occupied cell, `G` = paths with finitely many active labels on bounded intervals) is not
built here.  Nothing here certifies `p:lem:timeMTP`, `p:lem:regeninvariant` or either main
theorem.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

open scoped ENNReal

namespace ReflectedGMS.FlowSpaceBlockSystem

open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridTranslation
open ReflectedGMS.UniformGridDilationInvariance
open ReflectedGMS.Temporal.ActualDyadicTemporalBlocks ReflectedGMS.RootBlockGridProbability
open ReflectedGMS.ConditionalTemporalAveraging ReflectedGMS.ScaledConditionalTemporalAveraging
open ReflectedGMS.ParabolicTransport ReflectedGMS.GridAveragedInvariantVersion
open ReflectedGMS.ScaledRootChain
open ReflectedGMS.TwoSidedRegenerationFlow ReflectedGMS.TwoSidedRegenerationFlowGrid
open ReflectedGMS.TrajectoryCoding ReflectedGMS.EnvironmentLaws ReflectedGMS.Code

/-! ## 1. The obstruction -/

/-! ### The grid factor has a dilation-fixed point -/

/-! ### The fixed point on `FlowSpace × Grid` -/

/-! ## 2. The construction from a covariant local time scale -/

section Construction

variable {Ω : Type*}

/-- A positive lower bound on every bounded interval. -/
def LocallyBoundedBelow (f : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, ∃ m : ℝ, 0 < m ∧ ∀ u ∈ Set.Ico a b, m ≤ f u

/-- Right upper semicontinuity: values just to the right of `s` are at most `f s + ε`. -/
def RightUpperSemicontinuous (f : ℝ → ℝ) : Prop :=
  ∀ s ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℝ, s < u → u < s + δ → f u ≤ f s + ε

theorem LocallyBoundedBelow.pos {f : ℝ → ℝ} (h : LocallyBoundedBelow f) (u : ℝ) : 0 < f u := by
  obtain ⟨m, hm, hb⟩ := h u (u + 1)
  exact hm.trans_le (hb u ⟨le_refl u, by linarith⟩)

theorem le_of_forall_pos_le_add_real {a b : ℝ} (h : ∀ ε : ℝ, 0 < ε → a ≤ b + ε) : a ≤ b := by
  rcases le_or_gt a b with hab | hab
  · exact hab
  · have := h ((a - b) / 2) (by linarith)
    linarith

/-! ### Dyadic side lengths along the chain -/

theorem side_mono (D : Grid) {k l : ℤ} (h : k ≤ l) : side D k ≤ side D l := by
  have hkl : (k : ℝ) ≤ l := Int.cast_le.2 h
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

theorem side_add_nat (D : Grid) (k : ℤ) (n : ℕ) : side D (k + n) = 2 ^ n * side D k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : k + ((n + 1 : ℕ) : ℤ) = (k + n) + 1 := by push_cast; ring
    rw [h, DyadicGridTranslation.side_succ, ih, pow_succ]
    ring

theorem side_sub_nat (D : Grid) (k : ℤ) (n : ℕ) : side D (k - n) = side D k / 2 ^ n := by
  have h := side_add_nat D (k - n) n
  rw [sub_add_cancel] at h
  rw [h, mul_div_cancel_left₀ _ (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0))]

theorem two_rpow_pos (q : ℚ) : 0 < (2 : ℝ) ^ (q : ℝ) := Real.rpow_pos_of_pos (by norm_num) _

/-! ### Good blocks -/

/-- The level-`k` dyadic time block through `s` is **good** at parameter `q` when its length is
at most `2^q` times the local time scale at every one of its times. -/
def Good (τ : Ω → ℝ → ℝ) (q : ℚ) (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) : Prop :=
  ∀ u ∈ timeBlockAt D k s, side D k ≤ (2 : ℝ) ^ (q : ℝ) * τ ω u

variable {τ : Ω → ℝ → ℝ}

/-- Goodness passes to finer levels. -/
theorem Good.mono_level {q : ℚ} {ω : Ω} {D : Grid} {k l : ℤ} {s : ℝ} (hkl : k ≤ l)
    (h : Good τ q ω D l s) : Good τ q ω D k s := fun u hu =>
  (side_mono D hkl).trans (h u (timeBlockAt_subset_of_le D hkl s hu))

/-- Goodness passes to larger parameters. -/
theorem Good.mono_q {ω : Ω} (hτ : ∀ u, 0 ≤ τ ω u) {q q' : ℚ} (hq : q ≤ q') {D : Grid} {k : ℤ}
    {s : ℝ} (h : Good τ q ω D k s) : Good τ q' ω D k s := fun u hu =>
  (h u hu).trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hq)) (hτ u))

/-- Fine blocks are good. -/
theorem exists_good {ω : Ω} (hlb : LocallyBoundedBelow (τ ω)) (q : ℚ) (D : Grid) (s : ℝ) :
    ∃ k : ℤ, Good τ q ω D k s := by
  obtain ⟨m, hm, hb⟩ := hlb (timeLowerAt D 0 s) (timeLowerAt D 0 s + side D 0)
  have hx : 0 < (2 : ℝ) ^ (q : ℝ) * m := mul_pos (two_rpow_pos q) hm
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (side D 0 / ((2 : ℝ) ^ (q : ℝ) * m))
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨0 - n, fun u hu => ?_⟩
  have hu0 : u ∈ timeBlockAt D 0 s := timeBlockAt_subset_of_le D (by omega) s hu
  have hmu : m ≤ τ ω u := hb u hu0
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  rw [side_sub_nat]
  rw [div_lt_iff₀ hx] at hn
  calc side D 0 / 2 ^ n ≤ (2 : ℝ) ^ (q : ℝ) * m := by
        rw [div_le_iff₀ h2n]
        calc side D 0 ≤ 2 ^ n * ((2 : ℝ) ^ (q : ℝ) * m) := hn.le
          _ = (2 : ℝ) ^ (q : ℝ) * m * 2 ^ n := by ring
    _ ≤ (2 : ℝ) ^ (q : ℝ) * τ ω u := mul_le_mul_of_nonneg_left hmu (two_rpow_pos q).le

/-- Coarse blocks are not good. -/
theorem exists_not_good (τ : Ω → ℝ → ℝ) (q : ℚ) (ω : Ω) (D : Grid) (s : ℝ) :
    ∃ k : ℤ, ¬ Good τ q ω D k s := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (((2 : ℝ) ^ (q : ℝ) * τ ω s) / side D 0)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨0 + n, fun h => ?_⟩
  have h1 := h s (mem_timeBlockAt_self D _ s)
  rw [side_add_nat] at h1
  rw [div_lt_iff₀ (side_pos D 0)] at hn
  linarith

theorem bddAbove_good (τ : Ω → ℝ → ℝ) (q : ℚ) (ω : Ω) (D : Grid) (s : ℝ) :
    BddAbove {k : ℤ | Good τ q ω D k s} := by
  obtain ⟨k₀, hk₀⟩ := exists_not_good τ q ω D s
  refine ⟨k₀, fun k hk => ?_⟩
  by_contra hlt
  exact hk₀ (Good.mono_level (le_of_lt (not_le.1 hlt)) hk)

/-! ### The selected level and the block -/

/-- **The selected level**: the coarsest good level through `s`. -/
noncomputable def selLevel (τ : Ω → ℝ → ℝ) (q : ℚ) (ω : Ω) (D : Grid) (s : ℝ) : ℤ :=
  sSup {k : ℤ | Good τ q ω D k s}

/-- **The block `J_q(s)`**: the largest good dyadic time block through `s`. -/
noncomputable def scaleBlock (τ : Ω → ℝ → ℝ) (q : ℚ) (p : Ω × Grid) (s : ℝ) : Set ℝ :=
  timeBlockAt p.2 (selLevel τ q p.1 p.2 s) s

theorem good_selLevel {ω : Ω} (hlb : LocallyBoundedBelow (τ ω)) (q : ℚ) (D : Grid) (s : ℝ) :
    Good τ q ω D (selLevel τ q ω D s) s :=
  Int.csSup_mem (exists_good hlb q D s) (bddAbove_good τ q ω D s)

theorem le_selLevel {q : ℚ} {ω : Ω} {D : Grid} {k : ℤ} {s : ℝ} (h : Good τ q ω D k s) :
    k ≤ selLevel τ q ω D s :=
  le_csSup (bddAbove_good τ q ω D s) h

theorem not_good_succ_selLevel (q : ℚ) (ω : Ω) (D : Grid) (s : ℝ) :
    ¬ Good τ q ω D (selLevel τ q ω D s + 1) s := fun h => by
  have := le_selLevel h
  omega

theorem selLevel_eq_of {q : ℚ} {ω : Ω} {D : Grid} {k : ℤ} {s : ℝ} (hk : Good τ q ω D k s)
    (hk1 : ¬ Good τ q ω D (k + 1) s) : selLevel τ q ω D s = k := by
  refine le_antisymm ?_ (le_selLevel hk)
  by_contra hlt
  have hlt' : k < sSup {k : ℤ | Good τ q ω D k s} := not_le.1 hlt
  obtain ⟨a, ha, hka⟩ := exists_lt_of_lt_csSup ⟨k, hk⟩ hlt'
  exact hk1 (Good.mono_level (show k + 1 ≤ a by omega) ha)

theorem selLevel_mono {ω : Ω} (hlb : LocallyBoundedBelow (τ ω)) {q q' : ℚ} (hq : q ≤ q')
    (D : Grid) (s : ℝ) : selLevel τ q ω D s ≤ selLevel τ q' ω D s :=
  le_selLevel (Good.mono_q (fun u => (hlb.pos u).le) hq (good_selLevel hlb q D s))

theorem volume_timeBlockAt (D : Grid) (k : ℤ) (s : ℝ) :
    volume (timeBlockAt D k s) = ENNReal.ofReal (side D k) := by
  rw [timeBlockAt, Real.volume_Ico]
  congr 1
  ring

/-! ### The partition field -/

theorem good_iff_of_mem {q : ℚ} {ω : Ω} {D : Grid} {j l : ℤ} (hjl : j ≤ l) {s t : ℝ}
    (ht : t ∈ timeBlockAt D j s) : Good τ q ω D l t ↔ Good τ q ω D l s := by
  unfold Good
  rw [timeBlockAt_eq_of_mem_of_le D hjl ht]

theorem scaleBlock_eq_of_mem {q : ℚ} {p : Ω × Grid} (hlb : LocallyBoundedBelow (τ p.1)) {s t : ℝ}
    (ht : t ∈ scaleBlock τ q p s) : scaleBlock τ q p t = scaleBlock τ q p s := by
  obtain ⟨ω, D⟩ := p
  have ht' : t ∈ timeBlockAt D (selLevel τ q ω D s) s := ht
  have hgood : Good τ q ω D (selLevel τ q ω D s) t :=
    (good_iff_of_mem le_rfl ht').2 (good_selLevel hlb q D s)
  have hbad : ¬ Good τ q ω D (selLevel τ q ω D s + 1) t := fun h =>
    not_good_succ_selLevel q ω D s ((good_iff_of_mem (by omega) ht').1 h)
  have hsel : selLevel τ q ω D t = selLevel τ q ω D s := selLevel_eq_of hgood hbad
  show timeBlockAt D (selLevel τ q ω D t) t = timeBlockAt D (selLevel τ q ω D s) s
  rw [hsel]
  exact timeBlockAt_eq_of_mem ht'

/-! ### The flow field -/

theorem timeBlockAt_translate_timeVec (D : Grid) (r : ℝ) (k : ℤ) (s : ℝ) :
    timeBlockAt (translate (timeVec r) D) k s = {x : ℝ | x + r ∈ timeBlockAt D k (s + r)} := by
  have h := timeBlockAt_translate D (timeVec r) k (s + r)
  rw [timeVec_zero, add_sub_cancel_right] at h
  exact h

theorem good_shift {θΩ : ℝ → Ω → Ω} (hshift : ∀ (r : ℝ) (ω : Ω) (s : ℝ), τ (θΩ r ω) s = τ ω (s + r))
    (q : ℚ) (r : ℝ) (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) :
    Good τ q (θΩ r ω) (translate (timeVec r) D) k s ↔ Good τ q ω D k (s + r) := by
  unfold Good
  rw [timeBlockAt_translate_timeVec, side_translate]
  constructor
  · intro h v hv
    have h1 := h (v - r) (show v - r + r ∈ timeBlockAt D k (s + r) by rwa [sub_add_cancel])
    rwa [hshift, sub_add_cancel] at h1
  · intro h u hu
    rw [hshift]
    exact h (u + r) hu

theorem selLevel_shift {θΩ : ℝ → Ω → Ω}
    (hshift : ∀ (r : ℝ) (ω : Ω) (s : ℝ), τ (θΩ r ω) s = τ ω (s + r))
    (q : ℚ) (r : ℝ) (ω : Ω) (D : Grid) (s : ℝ) :
    selLevel τ q (θΩ r ω) (translate (timeVec r) D) s = selLevel τ q ω D (s + r) := by
  unfold selLevel
  congr 1
  ext k
  exact good_shift hshift q r ω D k s

theorem scaleBlock_shift {θΩ : ℝ → Ω → Ω} {θ : ℝ → Ω × Grid → Ω × Grid}
    (hθ : ∀ (t : ℝ) (y : Ω) (d : Grid), θ t (y, d) = (θΩ t y, translate (timeVec t) d))
    (hshift : ∀ (r : ℝ) (ω : Ω) (s : ℝ), τ (θΩ r ω) s = τ ω (s + r))
    (q : ℚ) (p : Ω × Grid) (r s : ℝ) :
    scaleBlock τ q (θ r p) s = {x : ℝ | x + r ∈ scaleBlock τ q p (s + r)} := by
  obtain ⟨ω, D⟩ := p
  rw [hθ]
  show timeBlockAt (translate (timeVec r) D)
      (selLevel τ q (θΩ r ω) (translate (timeVec r) D) s) s
    = {x : ℝ | x + r ∈ timeBlockAt D (selLevel τ q ω D (s + r)) (s + r)}
  rw [selLevel_shift hshift, timeBlockAt_translate_timeVec]

/-! ### The scaling field -/

/-- **Dilation covariance of the dyadic time blocks.** -/
theorem timeBlockAt_dilate {a : ℝ} (ha : 0 < a) (D : Grid) (k : ℤ) (s : ℝ) :
    timeBlockAt (dilate a ha D) (k + levelShift a D) (a * s)
      = (fun x : ℝ => a * x) '' timeBlockAt D k s := by
  have hL : k + levelShift a D - levelShift a D = k := by ring
  have horig : timeOrigin (dilate a ha D) (k + levelShift a D) = a * timeOrigin D k := by
    show dilatedOrigin a D (k + levelShift a D) 0 = a * D.origin k 0
    rw [dilatedOrigin, hL]
  have hside : side (dilate a ha D) (k + levelShift a D) = a * side D k := by
    rw [side_dilate ha, hL]
  have hcoord : timeCoord (dilate a ha D) (k + levelShift a D) (a * s) = timeCoord D k s := by
    simp only [timeCoord, horig, hside]
    rw [← mul_sub, mul_div_mul_left _ _ ha.ne']
  have hidx : timeIndexAt (dilate a ha D) (k + levelShift a D) (a * s) = timeIndexAt D k s := by
    simp only [timeIndexAt, hcoord]
  have hlow : timeLowerAt (dilate a ha D) (k + levelShift a D) (a * s)
      = a * timeLowerAt D k s := by
    simp only [timeLowerAt, horig, hside, hidx]
    ring
  rw [timeBlockAt, timeBlockAt, hlow, hside, Set.image_mul_left_Ico ha, mul_add]

theorem good_scale {SΩ : ℝ → Ω → Ω}
    (hscale : ∀ C : ℝ, 0 < C → ∀ (ω : Ω) (s : ℝ), τ (SΩ C ω) (C ^ 2 * s) = C ^ 2 * τ ω s)
    {C : ℝ} (hC : 0 < C) (q : ℚ) (ω : Ω) (D : Grid) (k : ℤ) (s : ℝ) :
    Good τ q (SΩ C ω) (dilate (C ^ 2) (pow_pos hC 2) D) (k + levelShift (C ^ 2) D) (C ^ 2 * s)
      ↔ Good τ q ω D k s := by
  have ha : 0 < C ^ 2 := pow_pos hC 2
  have hL : k + levelShift (C ^ 2) D - levelShift (C ^ 2) D = k := by ring
  unfold Good
  rw [timeBlockAt_dilate ha, side_dilate ha, hL]
  constructor
  · intro h v hv
    have h1 := h (C ^ 2 * v) ⟨v, hv, rfl⟩
    rw [hscale C hC] at h1
    have h2 : C ^ 2 * side D k ≤ C ^ 2 * ((2 : ℝ) ^ (q : ℝ) * τ ω v) := by
      calc C ^ 2 * side D k ≤ (2 : ℝ) ^ (q : ℝ) * (C ^ 2 * τ ω v) := h1
        _ = C ^ 2 * ((2 : ℝ) ^ (q : ℝ) * τ ω v) := by ring
    exact le_of_mul_le_mul_left h2 ha
  · intro h u hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [hscale C hC]
    calc C ^ 2 * side D k ≤ C ^ 2 * ((2 : ℝ) ^ (q : ℝ) * τ ω v) :=
          mul_le_mul_of_nonneg_left (h v hv) ha.le
      _ = (2 : ℝ) ^ (q : ℝ) * (C ^ 2 * τ ω v) := by ring

theorem selLevel_scale {SΩ : ℝ → Ω → Ω}
    (hscale : ∀ C : ℝ, 0 < C → ∀ (ω : Ω) (s : ℝ), τ (SΩ C ω) (C ^ 2 * s) = C ^ 2 * τ ω s)
    {C : ℝ} (hC : 0 < C) (q : ℚ) {ω : Ω} (hlb : LocallyBoundedBelow (τ ω)) (D : Grid) (s : ℝ) :
    selLevel τ q (SΩ C ω) (dilate (C ^ 2) (pow_pos hC 2) D) (C ^ 2 * s)
      = selLevel τ q ω D s + levelShift (C ^ 2) D := by
  refine selLevel_eq_of ((good_scale hscale hC q ω D _ s).2 (good_selLevel hlb q D s)) ?_
  intro h
  have h' : Good τ q (SΩ C ω) (dilate (C ^ 2) (pow_pos hC 2) D)
      ((selLevel τ q ω D s + 1) + levelShift (C ^ 2) D) (C ^ 2 * s) := by
    rwa [show selLevel τ q ω D s + 1 + levelShift (C ^ 2) D
        = selLevel τ q ω D s + levelShift (C ^ 2) D + 1 by ring]
  exact not_good_succ_selLevel q ω D s ((good_scale hscale hC q ω D _ s).1 h')

/-! ### Joint measurability -/

theorem measurable_timeLowerAt (k : ℤ) : Measurable fun y : Grid × ℝ => timeLowerAt y.1 k y.2 := by
  have ho : Measurable fun y : Grid × ℝ => timeOrigin y.1 k :=
    (measurable_gridOrigin k 0).comp measurable_fst
  have hs : Measurable fun y : Grid × ℝ => side y.1 k := (measurable_side k).comp measurable_fst
  have hc : Measurable fun y : Grid × ℝ => timeCoord y.1 k y.2 := (measurable_snd.sub ho).div hs
  have hi : Measurable fun y : Grid × ℝ => ((timeIndexAt y.1 k y.2 : ℤ) : ℝ) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp hc.floor
  exact ho.add (hs.mul hi)

theorem measurableSet_mem_timeBlockAt (k : ℤ) :
    MeasurableSet {z : (Grid × ℝ) × ℝ | z.2 ∈ timeBlockAt z.1.1 k z.1.2} := by
  have hl : Measurable fun z : (Grid × ℝ) × ℝ => timeLowerAt z.1.1 k z.1.2 :=
    (measurable_timeLowerAt k).comp measurable_fst
  have hs : Measurable fun z : (Grid × ℝ) × ℝ => side z.1.1 k :=
    (measurable_side k).comp (measurable_fst.comp measurable_fst)
  exact (measurableSet_le hl measurable_snd).inter (measurableSet_lt measurable_snd (hl.add hs))

theorem good_iff_rat {q : ℚ} {ω : Ω} (husc : RightUpperSemicontinuous (τ ω)) {D : Grid} {k : ℤ}
    {s : ℝ} : Good τ q ω D k s ↔
      ∀ r : ℚ, (r : ℝ) ∈ timeBlockAt D k s → side D k ≤ (2 : ℝ) ^ (q : ℝ) * τ ω r := by
  constructor
  · intro h r hr
    exact h r hr
  · intro h u hu
    obtain ⟨hu1, hu2⟩ := hu
    have h2q := two_rpow_pos q
    refine le_of_forall_pos_le_add_real fun ε hε => ?_
    obtain ⟨δ, hδ, hδu⟩ := husc u (ε / (2 : ℝ) ^ (q : ℝ)) (div_pos hε h2q)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn
      (show u < min (u + δ) (timeLowerAt D k s + side D k) from lt_min (by linarith) hu2)
    have hrJ : (r : ℝ) ∈ timeBlockAt D k s :=
      ⟨by linarith, lt_of_lt_of_le hr2 (min_le_right _ _)⟩
    have h1 := h r hrJ
    have h2 := hδu r hr1 (lt_of_lt_of_le hr2 (min_le_left _ _))
    calc side D k ≤ (2 : ℝ) ^ (q : ℝ) * τ ω r := h1
      _ ≤ (2 : ℝ) ^ (q : ℝ) * (τ ω u + ε / (2 : ℝ) ^ (q : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 h2q.le
      _ = (2 : ℝ) ^ (q : ℝ) * τ ω u + ε := by
          rw [mul_add, mul_div_cancel₀ ε h2q.ne']

/-! ### The temporal block system -/

/-! ### The selection of the root chain -/

/-- The infimum of the local time scale over the level-`k` root block. -/
noncomputable def levelInf (τ : Ω → ℝ → ℝ) (ω : Ω) (D : Grid) (k : ℤ) : ℝ :=
  sInf (τ ω '' timeBlockAt D k 0)

/-- **The selecting parameters**: the level-`n` root block is the block at `scaleSel τ p n`. -/
noncomputable def scaleSel (τ : Ω → ℝ → ℝ) (p : Ω × Grid) (n : ℕ) : ℚ :=
  ((⌈Real.logb 2 (side p.2 n / levelInf τ p.1 p.2 n)⌉ : ℤ) : ℚ)

theorem bddBelow_image {ω : Ω} (hlb : LocallyBoundedBelow (τ ω)) (J : Set ℝ) :
    BddBelow (τ ω '' J) :=
  ⟨0, by
    rintro b ⟨u, -, rfl⟩
    exact (hlb.pos u).le⟩

theorem levelInf_pos {ω : Ω} (hlb : LocallyBoundedBelow (τ ω)) (D : Grid) (k : ℤ) :
    0 < levelInf τ ω D k := by
  obtain ⟨m, hm, hb⟩ := hlb (timeLowerAt D k 0) (timeLowerAt D k 0 + side D k)
  refine hm.trans_le (le_csInf ⟨_, mem_image_of_mem _ (mem_timeBlockAt_self D k 0)⟩ ?_)
  rintro b ⟨u, hu, rfl⟩
  exact hb u hu

theorem levelInf_succ_le {ω : Ω} (hlb : LocallyBoundedBelow (τ ω)) (D : Grid) (k : ℤ) :
    levelInf τ ω D (k + 1) ≤ levelInf τ ω D k :=
  csInf_le_csInf (bddBelow_image hlb _) ⟨_, mem_image_of_mem _ (mem_timeBlockAt_self D k 0)⟩
    (image_mono (timeBlockAt_subset_succ D k 0))

theorem good_iff_le_levelInf {q : ℚ} {ω : Ω} (hlb : LocallyBoundedBelow (τ ω)) (D : Grid)
    (k : ℤ) : Good τ q ω D k 0 ↔ side D k ≤ (2 : ℝ) ^ (q : ℝ) * levelInf τ ω D k := by
  have h2q := two_rpow_pos q
  constructor
  · intro h
    have h1 : side D k / (2 : ℝ) ^ (q : ℝ) ≤ levelInf τ ω D k := by
      refine le_csInf ⟨_, mem_image_of_mem _ (mem_timeBlockAt_self D k 0)⟩ ?_
      rintro b ⟨u, hu, rfl⟩
      rw [div_le_iff₀' h2q]
      exact h u hu
    exact (div_le_iff₀' h2q).1 h1
  · intro h u hu
    exact h.trans (mul_le_mul_of_nonneg_left
      (csInf_le (bddBelow_image hlb _) (mem_image_of_mem _ hu)) h2q.le)

/-- **The selected level at `scaleSel τ p n` is `n`.** -/
theorem selLevel_scaleSel {p : Ω × Grid} (hlb : LocallyBoundedBelow (τ p.1)) (n : ℕ) :
    selLevel τ (scaleSel τ p n) p.1 p.2 0 = n := by
  have hq : ((scaleSel τ p n : ℚ) : ℝ)
      = ((⌈Real.logb 2 (side p.2 n / levelInf τ p.1 p.2 n)⌉ : ℤ) : ℝ) := by
    simp only [scaleSel, Rat.cast_intCast]
  have hm : 0 < levelInf τ p.1 p.2 n := levelInf_pos hlb p.2 n
  have hσ : 0 < side p.2 n := side_pos p.2 n
  have hle : levelInf τ p.1 p.2 ((n : ℤ) + 1) ≤ levelInf τ p.1 p.2 n := levelInf_succ_le hlb p.2 n
  have hg0 := good_iff_le_levelInf (q := scaleSel τ p n) hlb p.2 n
  have hg1 := good_iff_le_levelInf (q := scaleSel τ p n) hlb p.2 ((n : ℤ) + 1)
  rw [hq] at hg0 hg1
  rw [DyadicGridTranslation.side_succ] at hg1
  generalize hc : ⌈Real.logb 2 (side p.2 n / levelInf τ p.1 p.2 n)⌉ = c at hg0 hg1
  have hc1 : Real.logb 2 (side p.2 n / levelInf τ p.1 p.2 n) ≤ (c : ℝ) := by
    rw [← hc]
    exact Int.le_ceil _
  have hc2 : (c : ℝ) < Real.logb 2 (side p.2 n / levelInf τ p.1 p.2 n) + 1 := by
    rw [← hc]
    exact Int.ceil_lt_add_one _
  generalize levelInf τ p.1 p.2 ((n : ℤ) + 1) = m' at hle hg1
  generalize levelInf τ p.1 p.2 n = m at hm hle hg0 hg1 hc1 hc2
  generalize side p.2 n = σ at hσ hg0 hg1 hc1 hc2
  have hx : 0 < σ / m := div_pos hσ hm
  have hx1 : σ / m ≤ (2 : ℝ) ^ (c : ℝ) :=
    calc σ / m = (2 : ℝ) ^ Real.logb 2 (σ / m) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
      _ ≤ (2 : ℝ) ^ (c : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc1
  have hx2 : (2 : ℝ) ^ (c : ℝ) < 2 * (σ / m) :=
    calc (2 : ℝ) ^ (c : ℝ) < (2 : ℝ) ^ (Real.logb 2 (σ / m) + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hc2
      _ = 2 * (σ / m) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one,
            Real.rpow_logb (by norm_num) (by norm_num) hx]
          ring
  have h2c : 0 < (2 : ℝ) ^ (c : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  refine selLevel_eq_of (hg0.2 ((div_le_iff₀ hm).1 hx1)) ?_
  intro h
  have h2 : 2 * σ ≤ (2 : ℝ) ^ (c : ℝ) * m :=
    (hg1.1 h).trans (mul_le_mul_of_nonneg_left hle h2c.le)
  have h3 : (2 : ℝ) ^ (c : ℝ) * m < 2 * σ := by
    have h4 : (2 : ℝ) ^ (c : ℝ) < 2 * σ / m := by
      rw [mul_div_assoc]
      exact hx2
    exact (lt_div_iff₀ hm).1 h4
  linarith

/-- **`selection_root`.** -/
theorem selection_root_scaleSel {p : Ω × Grid} (hlb : LocallyBoundedBelow (τ p.1)) (n : ℕ) :
    rootTimeBlock p.2 (n : ℤ) = scaleBlock τ (scaleSel τ p n) p 0 := by
  show timeBlockAt p.2 (n : ℤ) 0 = timeBlockAt p.2 (selLevel τ (scaleSel τ p n) p.1 p.2 0) 0
  rw [selLevel_scaleSel hlb n]

/-- **`selection_tendsto`.** -/
theorem tendsto_scaleSel {p : Ω × Grid} (hlb : LocallyBoundedBelow (τ p.1)) :
    Tendsto (scaleSel τ p) atTop atTop := by
  refine tendsto_atTop.2 fun Q => eventually_atTop.2
    ⟨(selLevel τ Q p.1 p.2 0).toNat + 1, fun n hn => ?_⟩
  by_contra hlt
  have h1 := selLevel_mono hlb (not_le.1 hlt).le p.2 0
  rw [selLevel_scaleSel hlb n] at h1
  omega

/-! ### The assembly -/

end Construction

/-! ### Satisfiability of `LocalTimeScale` (a toy carrier) -/

/-! ### The consequence on the càdlàg carrier -/

/-! ## 3. The gated construction

On a carrier with scale-fixed points (§1) no block family satisfies `blockScale` everywhere.
The blocks below use the local-scale selection on an invariant measurable gate `G` and the
grid-only blocks of level `⌊q⌋` off it.  Every field of `ScaledRootChainSystem` except
`transport` then holds EVERYWHERE, except `blockScale`, which holds on `G × Grid`
(`GatedRootChainBlocks`).  `parabolicCovariantReal_blockTransportReal_of_gate` shows that the one
consumer of `blockScale` (the parabolic covariance of the manuscript kernel) survives the gating
for functionals vanishing off the gate. -/

section Gated

variable {Ω : Type*}

/-- **A covariant local time scale on an invariant gate `G`**: the covariance is pointwise
everywhere, the regularity only on `G`, and `G` is measurable and invariant under the flow and
every scaling. -/
structure LocalTimeScaleOn [MeasurableSpace Ω] (G : Set Ω) (θΩ SΩ : ℝ → Ω → Ω)
    (τ : Ω → ℝ → ℝ) : Prop where
  measurableSet_gate : MeasurableSet G
  flow_mem : ∀ (r : ℝ) (ω : Ω), θΩ r ω ∈ G ↔ ω ∈ G
  scale_mem : ∀ C : ℝ, 0 < C → ∀ ω : Ω, SΩ C ω ∈ G ↔ ω ∈ G
  shift : ∀ (r : ℝ) (ω : Ω) (s : ℝ), τ (θΩ r ω) s = τ ω (s + r)
  scale : ∀ C : ℝ, 0 < C → ∀ (ω : Ω) (s : ℝ), τ (SΩ C ω) (C ^ 2 * s) = C ^ 2 * τ ω s
  lowerBound : ∀ ω ∈ G, LocallyBoundedBelow (τ ω)
  rightUSC : ∀ ω ∈ G, RightUpperSemicontinuous (τ ω)
  measurable : Measurable fun q : Ω × ℝ => τ q.1 q.2

variable {τ : Ω → ℝ → ℝ}

open Classical in
/-- **The gated blocks**: the local-scale block on the gate, the level-`⌊q⌋` dyadic block off
it. -/
noncomputable def gatedBlock (G : Set Ω) (τ : Ω → ℝ → ℝ) (q : ℚ) (p : Ω × Grid) (s : ℝ) :
    Set ℝ :=
  if p.1 ∈ G then scaleBlock τ q p s else timeBlockAt p.2 ⌊q⌋ s

open Classical in
/-- **The gated selection.** -/
noncomputable def gatedSel (G : Set Ω) (τ : Ω → ℝ → ℝ) (p : Ω × Grid) (n : ℕ) : ℚ :=
  if p.1 ∈ G then scaleSel τ p n else (n : ℚ)

theorem gatedBlock_of_mem {G : Set Ω} {q : ℚ} {p : Ω × Grid} (h : p.1 ∈ G) (s : ℝ) :
    gatedBlock G τ q p s = scaleBlock τ q p s := by
  rw [gatedBlock, if_pos h]

theorem gatedBlock_of_not_mem {G : Set Ω} {q : ℚ} {p : Ω × Grid} (h : p.1 ∉ G) (s : ℝ) :
    gatedBlock G τ q p s = timeBlockAt p.2 ⌊q⌋ s := by
  rw [gatedBlock, if_neg h]

theorem gatedSel_of_mem {G : Set Ω} {p : Ω × Grid} (h : p.1 ∈ G) :
    gatedSel G τ p = scaleSel τ p :=
  funext fun n => by rw [gatedSel, if_pos h]

theorem gatedSel_of_not_mem {G : Set Ω} {p : Ω × Grid} (h : p.1 ∉ G) :
    gatedSel G τ p = fun n : ℕ => (n : ℚ) :=
  funext fun n => by rw [gatedSel, if_neg h]

theorem measurableSet_good_on [MeasurableSpace Ω] {G : Set Ω} (hG : MeasurableSet G)
    (hτm : Measurable fun y : Ω × ℝ => τ y.1 y.2)
    (husc : ∀ ω ∈ G, RightUpperSemicontinuous (τ ω)) (q : ℚ) (k : ℤ) :
    MeasurableSet {y : (Ω × Grid) × ℝ | y.1.1 ∈ G ∧ Good τ q y.1.1 y.1.2 k y.2} := by
  have hset : {y : (Ω × Grid) × ℝ | y.1.1 ∈ G ∧ Good τ q y.1.1 y.1.2 k y.2}
      = ((fun y : (Ω × Grid) × ℝ => y.1.1) ⁻¹' G) ∩
        ⋂ r : ℚ, ({y : (Ω × Grid) × ℝ | (r : ℝ) ∈ timeBlockAt y.1.2 k y.2}ᶜ
          ∪ {y : (Ω × Grid) × ℝ | side y.1.2 k ≤ (2 : ℝ) ^ (q : ℝ) * τ y.1.1 r}) := by
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_iInter, mem_union, mem_compl_iff]
    constructor
    · rintro ⟨hy, hg⟩
      exact ⟨hy, fun r => imp_iff_not_or.1 ((good_iff_rat (husc _ hy)).1 hg r)⟩
    · rintro ⟨hy, hg⟩
      exact ⟨hy, (good_iff_rat (husc _ hy)).2 fun r => imp_iff_not_or.2 (hg r)⟩
  rw [hset]
  refine MeasurableSet.inter (measurable_fst.fst hG) (MeasurableSet.iInter fun r =>
    MeasurableSet.union ?_ ?_)
  · have hmap : Measurable fun y : (Ω × Grid) × ℝ => (((y.1.2, y.2), (r : ℝ)) : (Grid × ℝ) × ℝ) :=
      ((measurable_fst.snd).prodMk measurable_snd).prodMk measurable_const
    exact (hmap (measurableSet_mem_timeBlockAt k)).compl
  · have hs : Measurable fun y : (Ω × Grid) × ℝ => side y.1.2 k :=
      (measurable_side k).comp measurable_fst.snd
    have hτr : Measurable fun y : (Ω × Grid) × ℝ => τ y.1.1 (r : ℝ) :=
      hτm.comp (measurable_fst.fst.prodMk (measurable_const (a := (r : ℝ))))
    exact measurableSet_le hs (hτr.const_mul _)

theorem measurableSet_graph_gatedBlock [MeasurableSpace Ω] {G : Set Ω} {θΩ SΩ : ℝ → Ω → Ω}
    (hτ : LocalTimeScaleOn G θΩ SΩ τ) (q : ℚ) :
    MeasurableSet {x : (Ω × Grid) × ℝ × ℝ | x.2.2 ∈ gatedBlock G τ q x.1 x.2.1} := by
  have hmap : Measurable fun x : (Ω × Grid) × ℝ × ℝ => ((x.1, x.2.1) : (Ω × Grid) × ℝ) :=
    measurable_fst.prodMk measurable_snd.fst
  have hmap2 : Measurable fun x : (Ω × Grid) × ℝ × ℝ =>
      (((x.1.2, x.2.1), x.2.2) : (Grid × ℝ) × ℝ) :=
    ((measurable_fst.snd).prodMk measurable_snd.fst).prodMk measurable_snd.snd
  have hset : {x : (Ω × Grid) × ℝ × ℝ | x.2.2 ∈ gatedBlock G τ q x.1 x.2.1}
      = (⋃ k : ℤ, (((fun x : (Ω × Grid) × ℝ × ℝ => ((x.1, x.2.1) : (Ω × Grid) × ℝ)) ⁻¹'
            {y : (Ω × Grid) × ℝ | y.1.1 ∈ G ∧ Good τ q y.1.1 y.1.2 k y.2})
          ∩ ((fun x : (Ω × Grid) × ℝ × ℝ => ((x.1, x.2.1) : (Ω × Grid) × ℝ)) ⁻¹'
            {y : (Ω × Grid) × ℝ | y.1.1 ∈ G ∧ Good τ q y.1.1 y.1.2 (k + 1) y.2})ᶜ)
          ∩ ((fun x : (Ω × Grid) × ℝ × ℝ => (((x.1.2, x.2.1), x.2.2) : (Grid × ℝ) × ℝ)) ⁻¹'
            {z : (Grid × ℝ) × ℝ | z.2 ∈ timeBlockAt z.1.1 k z.1.2}))
        ∪ (((fun x : (Ω × Grid) × ℝ × ℝ => x.1.1) ⁻¹' G)ᶜ
          ∩ ((fun x : (Ω × Grid) × ℝ × ℝ => (((x.1.2, x.2.1), x.2.2) : (Grid × ℝ) × ℝ)) ⁻¹'
            {z : (Grid × ℝ) × ℝ | z.2 ∈ timeBlockAt z.1.1 ⌊q⌋ z.1.2})) := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, mem_inter_iff, mem_preimage, mem_compl_iff]
    by_cases hx : x.1.1 ∈ G
    · rw [gatedBlock_of_mem (p := x.1) hx]
      constructor
      · intro h
        exact Or.inl ⟨selLevel τ q x.1.1 x.1.2 x.2.1,
          ⟨⟨hx, good_selLevel (hτ.lowerBound _ hx) q x.1.2 x.2.1⟩,
            fun h' => not_good_succ_selLevel q x.1.1 x.1.2 x.2.1 h'.2⟩, h⟩
      · rintro (⟨k, ⟨⟨-, hk⟩, hk1⟩, h⟩ | ⟨hn, -⟩)
        · show x.2.2 ∈ timeBlockAt x.1.2 (selLevel τ q x.1.1 x.1.2 x.2.1) x.2.1
          rw [selLevel_eq_of hk (fun h' => hk1 ⟨hx, h'⟩)]
          exact h
        · exact absurd hx hn
    · rw [gatedBlock_of_not_mem (p := x.1) hx]
      constructor
      · intro h
        exact Or.inr ⟨hx, h⟩
      · rintro (⟨k, ⟨⟨hG, -⟩, -⟩, -⟩ | ⟨-, h⟩)
        · exact absurd hG hx
        · exact h
  rw [hset]
  exact (MeasurableSet.iUnion fun k =>
    ((hmap (measurableSet_good_on hτ.measurableSet_gate hτ.measurable hτ.rightUSC q k)).inter
      (hmap (measurableSet_good_on hτ.measurableSet_gate hτ.measurable hτ.rightUSC q
        (k + 1))).compl).inter (hmap2 (measurableSet_mem_timeBlockAt k))).union
    ((measurable_fst.fst hτ.measurableSet_gate).compl.inter
      (hmap2 (measurableSet_mem_timeBlockAt ⌊q⌋)))

/-- The gated blocks have positive length at EVERY time (they are dyadic blocks). -/
theorem volume_pos_gatedBlock {G : Set Ω} (q : ℚ) (p : Ω × Grid) (s : ℝ) :
    0 < volume (gatedBlock G τ q p s) := by
  by_cases hp : p.1 ∈ G
  · rw [gatedBlock_of_mem hp]
    show 0 < volume (timeBlockAt p.2 _ s)
    rw [volume_timeBlockAt]
    exact ENNReal.ofReal_pos.2 (side_pos _ _)
  · rw [gatedBlock_of_not_mem hp, volume_timeBlockAt]
    exact ENNReal.ofReal_pos.2 (side_pos _ _)

/-- **Every field of `TemporalBlockSystem` for the gated blocks, everywhere.** -/
theorem temporalBlockSystem_gatedBlock [MeasurableSpace Ω] {G : Set Ω} {θΩ SΩ : ℝ → Ω → Ω}
    (hτ : LocalTimeScaleOn G θΩ SΩ τ) {θ : ℝ → Ω × Grid → Ω × Grid}
    (hθ : ∀ (t : ℝ) (y : Ω) (d : Grid), θ t (y, d) = (θΩ t y, translate (timeVec t) d))
    (h0 : ∀ p : Ω × Grid, θ 0 p = p) (hadd : ∀ (a b : ℝ) (p : Ω × Grid), θ a (θ b p) = θ (a + b) p)
    (hmeas : Measurable fun p : (Ω × Grid) × ℝ => θ p.2 p.1) (q : ℚ) :
    TemporalBlockSystem θ (gatedBlock G τ q) where
  flow_zero := h0
  flow_add := hadd
  measurable_flow := hmeas
  self_mem := fun p s => by
    by_cases hp : p.1 ∈ G
    · rw [gatedBlock_of_mem hp]
      exact mem_timeBlockAt_self p.2 _ s
    · rw [gatedBlock_of_not_mem hp]
      exact mem_timeBlockAt_self p.2 _ s
  block_eq := fun p s t ht => by
    by_cases hp : p.1 ∈ G
    · simp only [gatedBlock_of_mem hp] at ht ⊢
      exact scaleBlock_eq_of_mem (hτ.lowerBound _ hp) ht
    · simp only [gatedBlock_of_not_mem hp] at ht ⊢
      exact timeBlockAt_eq_of_mem ht
  shift := fun p r s => by
    obtain ⟨ω, D⟩ := p
    by_cases hp : ω ∈ G
    · have hp' : (θ r (ω, D)).1 ∈ G := by
        rw [hθ]
        exact (hτ.flow_mem r ω).2 hp
      rw [gatedBlock_of_mem hp', scaleBlock_shift hθ hτ.shift q (ω, D) r s]
      simp only [gatedBlock_of_mem (p := (ω, D)) hp]
    · have hp' : (θ r (ω, D)).1 ∉ G := by
        rw [hθ]
        exact fun h => hp ((hτ.flow_mem r ω).1 h)
      rw [gatedBlock_of_not_mem hp']
      simp only [gatedBlock_of_not_mem (p := (ω, D)) hp]
      rw [hθ]
      exact timeBlockAt_translate_timeVec D r ⌊q⌋ s
  measurableSet_graph := measurableSet_graph_gatedBlock hτ q
  volume_pos_ae := fun p => Filter.Eventually.of_forall fun s => volume_pos_gatedBlock q p s
  volume_lt_top := fun p s => by
    by_cases hp : p.1 ∈ G
    · rw [gatedBlock_of_mem hp]
      show volume (timeBlockAt p.2 _ s) < ⊤
      rw [volume_timeBlockAt]
      exact ENNReal.ofReal_lt_top
    · rw [gatedBlock_of_not_mem hp, volume_timeBlockAt]
      exact ENNReal.ofReal_lt_top

theorem gatedBlock_nested {G : Set Ω} (hlb : ∀ ω ∈ G, LocallyBoundedBelow (τ ω)) {q q' : ℚ}
    (hq : q ≤ q') (p : Ω × Grid) : gatedBlock G τ q p 0 ⊆ gatedBlock G τ q' p 0 := by
  by_cases hp : p.1 ∈ G
  · rw [gatedBlock_of_mem hp, gatedBlock_of_mem hp]
    exact timeBlockAt_subset_of_le p.2 (selLevel_mono (hlb _ hp) hq p.2 0) 0
  · rw [gatedBlock_of_not_mem hp, gatedBlock_of_not_mem hp]
    exact timeBlockAt_subset_of_le p.2 (Int.floor_mono hq) 0

/-- **`blockScale` on the gate.** -/
theorem gatedBlock_scale_of_mem {G : Set Ω} {SΩ : ℝ → Ω → Ω} {S : ℝ → Ω × Grid → Ω × Grid}
    (hS : ∀ (C : ℝ) (y : Ω) (d : Grid), S C (y, d) = (SΩ C y, gridScale C d))
    (hSG : ∀ C : ℝ, 0 < C → ∀ ω : Ω, SΩ C ω ∈ G ↔ ω ∈ G)
    (hscale : ∀ C : ℝ, 0 < C → ∀ (ω : Ω) (s : ℝ), τ (SΩ C ω) (C ^ 2 * s) = C ^ 2 * τ ω s)
    (hlb : ∀ ω ∈ G, LocallyBoundedBelow (τ ω)) (q : ℚ) {C : ℝ} (hC : 0 < C) {p : Ω × Grid}
    (hp : p.1 ∈ G) (s : ℝ) :
    gatedBlock G τ q (S C p) (C ^ 2 * s) = (fun x : ℝ => C ^ 2 * x) '' gatedBlock G τ q p s := by
  obtain ⟨ω, D⟩ := p
  have hp' : (S C (ω, D)).1 ∈ G := by
    rw [hS]
    exact (hSG C hC ω).2 hp
  rw [gatedBlock_of_mem hp', gatedBlock_of_mem (p := (ω, D)) hp, hS]
  show timeBlockAt (gridScale C D) (selLevel τ q (SΩ C ω) (gridScale C D) (C ^ 2 * s)) (C ^ 2 * s)
    = (fun x : ℝ => C ^ 2 * x) '' timeBlockAt D (selLevel τ q ω D s) s
  rw [gridScale_of_pos hC, selLevel_scale hscale hC q (hlb ω hp) D s, timeBlockAt_dilate]

theorem gated_selection_root {G : Set Ω} (hlb : ∀ ω ∈ G, LocallyBoundedBelow (τ ω)) (n : ℕ)
    (p : Ω × Grid) : rootTimeBlock p.2 (n : ℤ) = gatedBlock G τ (gatedSel G τ p n) p 0 := by
  by_cases hp : p.1 ∈ G
  · rw [gatedBlock_of_mem hp, gatedSel_of_mem hp]
    exact selection_root_scaleSel (hlb _ hp) n
  · rw [gatedBlock_of_not_mem hp, gatedSel_of_not_mem hp]
    show timeBlockAt p.2 (n : ℤ) 0 = timeBlockAt p.2 ⌊((n : ℕ) : ℚ)⌋ 0
    rw [Int.floor_natCast]

theorem gated_tendsto {G : Set Ω} (hlb : ∀ ω ∈ G, LocallyBoundedBelow (τ ω)) (p : Ω × Grid) :
    Tendsto (gatedSel G τ p) atTop atTop := by
  by_cases hp : p.1 ∈ G
  · rw [gatedSel_of_mem hp]
    exact tendsto_scaleSel (hlb _ hp)
  · rw [gatedSel_of_not_mem hp]
    exact tendsto_natCast_atTop_atTop

end Gated

/-- **The non-transport fields of `ScaledRootChainSystem` with `blockScale` gated**: identical to
the structure's fields except that the parabolic block covariance is required only at points
whose configuration lies in `G`. -/
structure GatedRootChainBlocks {Ω : Type*} [MeasurableSpace Ω] (G : Set Ω)
    (θ S : ℝ → Ω × Grid → Ω × Grid) (blkFam : ℚ → Ω × Grid → ℝ → Set ℝ)
    (sel : Ω × Grid → ℕ → ℚ) : Prop where
  system : ∀ q : ℚ, TemporalBlockSystem θ (blkFam q)
  nested : ∀ q q' : ℚ, q ≤ q' → ∀ p : Ω × Grid, blkFam q p 0 ⊆ blkFam q' p 0
  blockScaleOn : ∀ (q : ℚ) (C : ℝ), 0 < C → ∀ p : Ω × Grid, p.1 ∈ G → ∀ s : ℝ,
    blkFam q (S C p) (C ^ 2 * s) = (fun x : ℝ => C ^ 2 * x) '' blkFam q p s
  selection_tendsto : ∀ p : Ω × Grid, Tendsto (sel p) atTop atTop
  selection_root : ∀ (n : ℕ) (p : Ω × Grid), rootTimeBlock p.2 (n : ℤ) = blkFam (sel p n) p 0

/-- **The gated block data from a gated local time scale**, on any marked carrier. -/
theorem gatedRootChainBlocks_of_localTimeScaleOn {Ω : Type*} [MeasurableSpace Ω] {G : Set Ω}
    {θΩ SΩ : ℝ → Ω → Ω} {τ : Ω → ℝ → ℝ} (hτ : LocalTimeScaleOn G θΩ SΩ τ)
    {θ S : ℝ → Ω × Grid → Ω × Grid}
    (hθ : ∀ (t : ℝ) (y : Ω) (d : Grid), θ t (y, d) = (θΩ t y, translate (timeVec t) d))
    (hS : ∀ (C : ℝ) (y : Ω) (d : Grid), S C (y, d) = (SΩ C y, gridScale C d))
    (h0 : ∀ p : Ω × Grid, θ 0 p = p) (hadd : ∀ (a b : ℝ) (p : Ω × Grid), θ a (θ b p) = θ (a + b) p)
    (hmeas : Measurable fun p : (Ω × Grid) × ℝ => θ p.2 p.1) :
    GatedRootChainBlocks G θ S (gatedBlock G τ) (gatedSel G τ) where
  system := temporalBlockSystem_gatedBlock hτ hθ h0 hadd hmeas
  nested := fun _ _ hq p => gatedBlock_nested hτ.lowerBound hq p
  blockScaleOn := fun q _ hC _ hp s =>
    gatedBlock_scale_of_mem hS hτ.scale_mem hτ.scale hτ.lowerBound q hC hp s
  selection_tendsto := gated_tendsto hτ.lowerBound
  selection_root := fun n p => gated_selection_root hτ.lowerBound n p

/-- **The one consumer of `blockScale` survives the gating.**  The manuscript kernel
`V(ω,s,t) = |J(s)|⁻¹ 1_{t ∈ J(s)} F(θ_t ω)` is parabolically covariant everywhere as soon as the
blocks are covariant on an invariant gate `G` and `F` vanishes off `G` (on `Gᶜ` both sides of
the identity vanish).  Compare `ScaledConditionalTemporalAveraging.parabolicCovariantReal_blockTransportReal`. -/
theorem parabolicCovariantReal_blockTransportReal_of_gate {Ω : Type*} [MeasurableSpace Ω]
    {θ S : ℝ → Ω → Ω} {blk : Ω → ℝ → Set ℝ} {G : Set Ω}
    (hθG : ∀ (r : ℝ) (ω : Ω), θ r ω ∈ G ↔ ω ∈ G)
    (hSG : ∀ C : ℝ, 0 < C → ∀ ω : Ω, S C ω ∈ G ↔ ω ∈ G)
    (hblk : ∀ C : ℝ, 0 < C → ∀ ω ∈ G, ∀ s : ℝ,
      blk (S C ω) (C ^ 2 * s) = (fun x : ℝ => C ^ 2 * x) '' blk ω s)
    (hflow : FlowScaleIntertwine θ S) {F : Ω → ℝ} (hF : ScaleInvariant S F)
    (hFG : ∀ ω : Ω, ω ∉ G → F ω = 0) :
    ParabolicCovariantReal S (blockTransportReal θ blk F) := by
  intro C hC ω s t
  have hC2 : 0 < C ^ 2 := pow_pos hC 2
  by_cases hω : ω ∈ G
  · simp only [blockTransportReal]
    rw [hblk C hC ω hω s, volume_image_mul hC2, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hC2.le, mul_inv]
    by_cases ht : t ∈ blk ω s
    · have ht' : C ^ 2 * t ∈ (fun x : ℝ => C ^ 2 * x) '' blk ω s :=
        (mul_mem_image_mul_iff hC2.ne' _ _).2 ht
      rw [Set.indicator_of_mem ht', Set.indicator_of_mem ht, hflow C hC t ω, hF C hC]
      ring
    · have ht' : C ^ 2 * t ∉ (fun x : ℝ => C ^ 2 * x) '' blk ω s :=
        fun hc => ht ((mul_mem_image_mul_iff hC2.ne' _ _).1 hc)
      rw [Set.indicator_of_notMem ht', Set.indicator_of_notMem ht]
      simp only [mul_zero]
  · have hzero : ∀ ω' : Ω, ω' ∉ G → ∀ s' t' : ℝ, blockTransportReal θ blk F ω' s' t' = 0 := by
      intro ω' hω' s' t'
      have hF0 : (fun u : ℝ => F (θ u ω')) = fun _ => 0 :=
        funext fun u => hFG _ fun h => hω' ((hθG u ω').1 h)
      simp only [blockTransportReal, hF0, Set.indicator_zero, mul_zero]
    rw [hzero ω hω, hzero (S C ω) (fun h => hω ((hSG C hC ω).1 h)), mul_zero]

end ReflectedGMS.FlowSpaceBlockSystem
