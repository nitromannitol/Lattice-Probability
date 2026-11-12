/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Planar.Topology.Jordan.Crossing at commit fdb5cad; only the module paths of local imports are changed. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Planar.Topology.Jordan.Brouwer
import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Jordan curve theorem (Maehara's proof), part: crossing lemma and basic topology of a Jordan curve

Ported from github.com/rkirov/jordan_pick (Apache-2.0, R. Kirov), commit
`b3c9b7cf7358bf81a077d78ad67e6e8247869ddd`, file `JordanPick/JordanCurve.lean`, lines 1–384.
Original proofs kept; changed only where our pin (Lean v4.34.0-rc2, mathlib a4c8ef0a) forces
it. Namespace `JordanCurve` → `MatedCRTHarmonic.Planar.Jordan`; `private` dropped so that the original
file can be split into modules. Source: H. Maehara, *The Jordan curve theorem via the Brouwer
fixed point theorem*, Amer. Math. Monthly 91 (1984) 641–643. -/

/-!
# The (continuous) Jordan Curve Theorem, via Brouwer — Maehara's proof

Target (lean-eval `jordan_curve`, pure Mathlib): a continuous injection
`r : S¹ → ℝ²` has a complement with exactly two connected components.

**Strategy (Maehara, *The Jordan curve theorem via the Brouwer fixed point
theorem*, Amer. Math. Monthly 1984).** Reduce to the Brouwer fixed point theorem,
taken here as an explicit interface `BrouwerFPT` (to be discharged from upstream
Mathlib — PR #36770 is landing Brouwer — or built separately). The reduction uses:

* **Lemma 2 (crossing)** — two transversal paths in a rectangle must meet; proved
  directly from Brouwer via an explicit map of the square to its boundary.
* **Lemma 1** — if `ℝ²∖J` is disconnected, each component has `J` as its
  boundary; via the Tietze extension theorem + Brouwer.
* **Main construction** — using the farthest pair `a,b ∈ J` and the points
  `l,m,p,q` on a vertical segment, show `ℝ²∖J` has exactly one bounded component;
  with the unique unbounded component that gives exactly two.

(Port note: the original file is split here into the modules `Crossing`, `ArcNonSep`,
`Normalize`, `Paths`, `StepA1`, `StepA2`, `StepB1`, `StepB2`, `Main`; the final theorem
`jordan_curve` in `Main` depends only on `propext`, `Classical.choice`, `Quot.sound`.)
-/

namespace MatedCRTHarmonic.Planar.Jordan

open Metric Set Function Bornology

/-- The plane `ℝ²` as used by the eval problem. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **Brouwer fixed point theorem** (interface). Every continuous self-map of a
nonempty convex compact subset of the plane has a fixed point. Discharged
separately (upstream Mathlib PR #36770, or a standalone build). All of Maehara's
argument is `BrouwerFPT → …`. -/
def BrouwerFPT : Prop :=
  ∀ s : Set Plane, Convex ℝ s → IsCompact s → s.Nonempty →
    ∀ f : C(s, s), ∃ x, f x = x

/-- **Lemma 2 (crossing lemma, Maehara).** Two continuous paths in a rectangle
`[a,b]×[c,d]`, one running from the left edge to the right edge (`h`), the other
from the bottom edge to the top edge (`v`), must meet. Proved directly from
Brouwer: if they were disjoint, the explicit normalized map
`F(s,t) = ((v₁ t − h₁ s)/N, (h₂ s − v₂ t)/N)` (with `N` the sup-norm of
`h s − v t`) sends the parameter square `[-1,1]²` to its boundary with no fixed
point. Coordinates are `p 0`, `p 1` of `p : Plane`. -/
theorem crossing (hbr : BrouwerFPT) {a b c d : ℝ} (_hab : a ≤ b) (_hcd : c ≤ d)
    (h v : ℝ → Plane)
    (hh : ContinuousOn h (Icc (-1) 1)) (hv : ContinuousOn v (Icc (-1) 1))
    (hhE : ∀ t ∈ Icc (-1:ℝ) 1, h t 0 ∈ Icc a b ∧ h t 1 ∈ Icc c d)
    (hvE : ∀ t ∈ Icc (-1:ℝ) 1, v t 0 ∈ Icc a b ∧ v t 1 ∈ Icc c d)
    (hh1 : h (-1) 0 = a) (hh2 : h 1 0 = b)
    (hv1 : v (-1) 1 = c) (hv2 : v 1 1 = d) :
    ∃ s ∈ Icc (-1:ℝ) 1, ∃ t ∈ Icc (-1:ℝ) 1, h s = v t := by
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ s ∈ Icc (-1) 1, ∀ t ∈ Icc (-1) 1, h s ≠ v t`
  -- The parameter square `Q = [-1,1]²`.
  set Q : Set Plane := {p | p 0 ∈ Icc (-1:ℝ) 1 ∧ p 1 ∈ Icc (-1:ℝ) 1} with hQdef
  have hQ0 : ∀ p ∈ Q, p 0 ∈ Icc (-1:ℝ) 1 := fun p hp => hp.1
  have hQ1 : ∀ p ∈ Q, p 1 ∈ Icc (-1:ℝ) 1 := fun p hp => hp.2
  -- `Q` is convex.
  have hconv : Convex ℝ Q := by
    have c0 : Convex ℝ {p : Plane | p 0 ∈ Icc (-1:ℝ) 1} := by
      exact (convex_Icc (-1:ℝ) 1).is_linear_preimage (EuclideanSpace.proj (0:Fin 2)).isLinear
    have c1 : Convex ℝ {p : Plane | p 1 ∈ Icc (-1:ℝ) 1} := by
      exact (convex_Icc (-1:ℝ) 1).is_linear_preimage (EuclideanSpace.proj (1:Fin 2)).isLinear
    exact c0.inter c1
  -- `Q` is compact (closed and bounded in a finite-dimensional space).
  have hcomp : IsCompact Q := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have d0 : IsClosed {p : Plane | p 0 ∈ Icc (-1:ℝ) 1} :=
        isClosed_Icc.preimage (EuclideanSpace.proj (0:Fin 2)).continuous
      have d1 : IsClosed {p : Plane | p 1 ∈ Icc (-1:ℝ) 1} :=
        isClosed_Icc.preimage (EuclideanSpace.proj (1:Fin 2)).continuous
      exact d0.inter d1
    · apply (Metric.isBounded_closedBall (x := (0:Plane)) (r := 2)).subset
      intro p hp
      simp only [mem_closedBall, dist_zero_right]
      have h0 : |p 0| ≤ 1 := abs_le.2 ⟨hp.1.1, hp.1.2⟩
      have h1 : |p 1| ≤ 1 := abs_le.2 ⟨hp.2.1, hp.2.2⟩
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
        show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by ring, Real.sqrt_sq]; norm_num]
      apply Real.sqrt_le_sqrt
      nlinarith [abs_nonneg (p 0), abs_nonneg (p 1)]
  have hne0 : Q.Nonempty := by
    refine ⟨0, ?_, ?_⟩ <;>
      · simp only [mem_Icc, show (0:Plane) 0 = 0 from rfl, show (0:Plane) 1 = 0 from rfl]
        norm_num
  -- The sup-norm distance and the normalized boundary map.
  let N : Plane → ℝ := fun p => max |h (p 0) 0 - v (p 1) 0| |h (p 0) 1 - v (p 1) 1|
  let n0 : Plane → ℝ := fun p => (v (p 1) 0 - h (p 0) 0) / N p
  let n1 : Plane → ℝ := fun p => (h (p 0) 1 - v (p 1) 1) / N p
  let F : Plane → Plane := fun p => !₂[n0 p, n1 p]
  have hNnn : ∀ p, 0 ≤ N p := fun p => le_trans (abs_nonneg _) (le_max_left _ _)
  -- `N > 0` on `Q`: otherwise `h (p 0) = v (p 1)`, contradicting `hcon`.
  have hNpos : ∀ p ∈ Q, 0 < N p := by
    intro p hp
    rcases (hNnn p).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hNz : N p = 0 := heq.symm
      have hA0 : |h (p 0) 0 - v (p 1) 0| ≤ N p := le_max_left _ _
      have hB0 : |h (p 0) 1 - v (p 1) 1| ≤ N p := le_max_right _ _
      rw [hNz] at hA0 hB0
      have eA : h (p 0) 0 = v (p 1) 0 := by
        have := le_antisymm hA0 (abs_nonneg _); rwa [abs_eq_zero, sub_eq_zero] at this
      have eB : h (p 0) 1 = v (p 1) 1 := by
        have := le_antisymm hB0 (abs_nonneg _); rwa [abs_eq_zero, sub_eq_zero] at this
      refine hcon (p 0) (hQ0 p hp) (p 1) (hQ1 p hp) ?_
      ext i; fin_cases i
      · exact eA
      · exact eB
  -- Continuity ingredients.
  have hc0 : Continuous (fun p : Plane => p 0) := by fun_prop
  have hc1 : Continuous (fun p : Plane => p 1) := by fun_prop
  have mt0 : MapsTo (fun p : Plane => p 0) Q (Icc (-1:ℝ) 1) := fun p hp => hQ0 p hp
  have mt1 : MapsTo (fun p : Plane => p 1) Q (Icc (-1:ℝ) 1) := fun p hp => hQ1 p hp
  have hHx0 : ContinuousOn (fun p : Plane => h (p 0) 0) Q :=
    (hc0.comp_continuousOn hh).comp hc0.continuousOn mt0
  have hHx1 : ContinuousOn (fun p : Plane => h (p 0) 1) Q :=
    (hc1.comp_continuousOn hh).comp hc0.continuousOn mt0
  have hVx0 : ContinuousOn (fun p : Plane => v (p 1) 0) Q :=
    (hc0.comp_continuousOn hv).comp hc1.continuousOn mt1
  have hVx1 : ContinuousOn (fun p : Plane => v (p 1) 1) Q :=
    (hc1.comp_continuousOn hv).comp hc1.continuousOn mt1
  have hNcont : ContinuousOn N Q :=
    ContinuousOn.sup ((hHx0.sub hVx0).abs) ((hHx1.sub hVx1).abs)
  have hn0c : ContinuousOn n0 Q :=
    (hVx0.sub hHx0).div hNcont (fun p hp => (hNpos p hp).ne')
  have hn1c : ContinuousOn n1 Q :=
    (hHx1.sub hVx1).div hNcont (fun p hp => (hNpos p hp).ne')
  have hFcont : ContinuousOn F Q := by
    have hG : ContinuousOn (fun p : Plane => (![n0 p, n1 p] : Fin 2 → ℝ)) Q := by
      rw [continuousOn_pi]
      intro i; fin_cases i
      · simpa using hn0c
      · simpa using hn1c
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn hG
  -- `F` maps `Q` into `Q`: each coordinate has absolute value `≤ 1`.
  have hbound : ∀ p ∈ Q, |n0 p| ≤ 1 ∧ |n1 p| ≤ 1 := by
    intro p hp
    have hN := hNpos p hp
    refine ⟨?_, ?_⟩
    · show |(v (p 1) 0 - h (p 0) 0) / N p| ≤ 1
      rw [abs_div, abs_of_pos hN, div_le_one hN]
      calc |v (p 1) 0 - h (p 0) 0| = |h (p 0) 0 - v (p 1) 0| := abs_sub_comm _ _
        _ ≤ N p := le_max_left _ _
    · show |(h (p 0) 1 - v (p 1) 1) / N p| ≤ 1
      rw [abs_div, abs_of_pos hN, div_le_one hN]
      exact le_max_right _ _
  have hmaps : MapsTo F Q Q := by
    intro p hp
    obtain ⟨hb0, hb1⟩ := hbound p hp
    exact ⟨mem_Icc.2 (abs_le.1 hb0), mem_Icc.2 (abs_le.1 hb1)⟩
  -- Package as a self-map of `Q` and apply Brouwer.
  let f : C(Q, Q) := ⟨fun p => ⟨F p.1, hmaps p.2⟩, by
    apply Continuous.subtype_mk; exact hFcont.domRestrict⟩
  obtain ⟨x, hx⟩ := hbr Q hconv hcomp hne0 f
  set p₀ : Plane := (x : Plane) with hp0def
  have hp0Q : p₀ ∈ Q := x.2
  have hN := hNpos p₀ hp0Q
  have hfix : F p₀ = p₀ := congrArg Subtype.val hx
  have hfix0 : p₀ 0 = (v (p₀ 1) 0 - h (p₀ 0) 0) / N p₀ := by
    have e : (F p₀) 0 = (v (p₀ 1) 0 - h (p₀ 0) 0) / N p₀ := rfl
    rw [← e, hfix]
  have hfix1 : p₀ 1 = (h (p₀ 0) 1 - v (p₀ 1) 1) / N p₀ := by
    have e : (F p₀) 1 = (h (p₀ 0) 1 - v (p₀ 1) 1) / N p₀ := rfl
    rw [← e, hfix]
  -- The fixed point lies on the boundary: `|p₀ 0| = 1` or `|p₀ 1| = 1`.
  have a0 : |p₀ 0| = |h (p₀ 0) 0 - v (p₀ 1) 0| / N p₀ := by
    conv_lhs => rw [hfix0]
    rw [abs_div, abs_of_pos hN, abs_sub_comm]
  have a1 : |p₀ 1| = |h (p₀ 0) 1 - v (p₀ 1) 1| / N p₀ := by
    conv_lhs => rw [hfix1]
    rw [abs_div, abs_of_pos hN]
  have hbdry : |p₀ 0| = 1 ∨ |p₀ 1| = 1 := by
    rcases le_total |h (p₀ 0) 1 - v (p₀ 1) 1| |h (p₀ 0) 0 - v (p₀ 1) 0| with hle | hle
    · left
      have hNA : N p₀ = |h (p₀ 0) 0 - v (p₀ 1) 0| := max_eq_left hle
      rw [a0, hNA]; exact div_self (by rw [← hNA]; exact hN.ne')
    · right
      have hNB : N p₀ = |h (p₀ 0) 1 - v (p₀ 1) 1| := max_eq_right hle
      rw [a1, hNB]; exact div_self (by rw [← hNB]; exact hN.ne')
  -- Boundary contradiction in each of the four cases.
  rcases hbdry with hb | hb
  · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).1 hb with hpos | hneg
    · -- `p₀ 0 = 1`: then `h (p₀ 0) 0 = b ≥ v (p₀ 1) 0`, so `p₀ 0 ≤ 0`.
      have hh0b : h (p₀ 0) 0 = b := by rw [hpos]; exact hh2
      have hvle : v (p₀ 1) 0 ≤ b := (hvE (p₀ 1) (hQ1 p₀ hp0Q)).1.2
      have : p₀ 0 ≤ 0 := by
        rw [hfix0]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hN.le
      linarith
    · -- `p₀ 0 = -1`: then `h (p₀ 0) 0 = a ≤ v (p₀ 1) 0`, so `p₀ 0 ≥ 0`.
      have hh0a : h (p₀ 0) 0 = a := by rw [hneg]; exact hh1
      have hvge : a ≤ v (p₀ 1) 0 := (hvE (p₀ 1) (hQ1 p₀ hp0Q)).1.1
      have : 0 ≤ p₀ 0 := by rw [hfix0]; exact div_nonneg (by linarith) hN.le
      linarith
  · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).1 hb with hpos | hneg
    · -- `p₀ 1 = 1`: then `v (p₀ 1) 1 = d ≥ h (p₀ 0) 1`, so `p₀ 1 ≤ 0`.
      have hv1d : v (p₀ 1) 1 = d := by rw [hpos]; exact hv2
      have hhle : h (p₀ 0) 1 ≤ d := (hhE (p₀ 0) (hQ0 p₀ hp0Q)).2.2
      have : p₀ 1 ≤ 0 := by
        rw [hfix1]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hN.le
      linarith
    · -- `p₀ 1 = -1`: then `v (p₀ 1) 1 = c ≤ h (p₀ 0) 1`, so `p₀ 1 ≥ 0`.
      have hv1c : v (p₀ 1) 1 = c := by rw [hneg]; exact hv1
      have hhge : c ≤ h (p₀ 0) 1 := (hhE (p₀ 0) (hQ0 p₀ hp0Q)).2.1
      have : 0 ≤ p₀ 1 := by rw [hfix1]; exact div_nonneg (by linarith) hN.le
      linarith

/-! ### Foundational topology of a Jordan curve `J = range r`

A Jordan curve is `J = range r` for `r : S¹ → ℝ²` continuous and injective. Here we
collect the purely topological facts about `J` and its complement that Maehara's
argument needs, independent of Brouwer:

* `J` is compact and closed, its complement `Jᶜ` is open (tasks 1-2);
* `r` is a (closed) embedding, so `J ≃ₜ S¹` (task 3);
* `Jᶜ` has exactly one unbounded connected component (PRELIM (a));
* each connected component of `Jᶜ` is open and path-connected (PRELIM (b)).
-/

/-- The plane has rank `2 > 1`; the engine for connectivity of ball-complements. -/
theorem one_lt_rank_plane : 1 < Module.rank ℝ Plane := by
  have h : Module.rank ℝ Plane = 2 := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num
  rw [h]; norm_num

/-- The exterior `{x | R < ‖x‖}` of a closed ball is connected in the plane
(dimension `2 > 1`). Proved as the continuous image of the connected set
`sphere 0 1 ×ˢ Ioi R` under `(s, t) ↦ t • s`. -/
theorem isConnected_compl_closedBall {R : ℝ} (hR : 0 ≤ R) :
    IsConnected {x : Plane | R < ‖x‖} := by
  have hconn : IsConnected ((sphere (0 : Plane) 1) ×ˢ (Ioi R)) :=
    (isConnected_sphere one_lt_rank_plane 0 zero_le_one).prod isConnected_Ioi
  have himg := hconn.image (fun p : Plane × ℝ => p.2 • p.1)
    (continuous_snd.smul continuous_fst).continuousOn
  have hset : {x : Plane | R < ‖x‖}
      = (fun p : Plane × ℝ => p.2 • p.1) '' ((sphere (0 : Plane) 1) ×ˢ (Ioi R)) := by
    ext x
    simp only [mem_ofPred_eq, mem_image, mem_prod, mem_Ioi, Prod.exists]
    constructor
    · intro hx
      have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hR hx
      refine ⟨‖x‖⁻¹ • x, ‖x‖, ⟨?_, hx⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ (ne_of_gt hxpos)]
      · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hxpos), one_smul]
    · rintro ⟨s, t, ⟨hs, ht⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hs
      rw [norm_smul, hs, mul_one, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hR ht)]
      exact ht
  rw [hset]; exact himg

section JordanCurveData

variable (r : sphere (0 : Plane) 1 → Plane)

/-- **Task 1.** The Jordan curve `J = range r` is compact (continuous image of the
compact circle `S¹`). -/
theorem jordanCurve_isCompact (hcont : Continuous r) : IsCompact (range r) :=
  isCompact_range hcont

/-- **Task 1.** The Jordan curve `J = range r` is closed (compact in a Hausdorff
space). -/
theorem jordanCurve_isClosed (hcont : Continuous r) : IsClosed (range r) :=
  (jordanCurve_isCompact r hcont).isClosed

/-- **Task 2.** The complement of the Jordan curve is open. -/
theorem isOpen_compl_jordanCurve (hcont : Continuous r) : IsOpen (range r)ᶜ :=
  (jordanCurve_isClosed r hcont).isOpen_compl

/-- **Task 3.** A continuous injection of the compact circle into the plane is a
closed embedding. -/
theorem r_isClosedEmbedding (hcont : Continuous r) (hinj : Injective r) :
    Topology.IsClosedEmbedding r :=
  hcont.isClosedEmbedding hinj

/-- **Task 3.** `r` is a topological embedding. -/
theorem r_isEmbedding (hcont : Continuous r) (hinj : Injective r) :
    Topology.IsEmbedding r :=
  (r_isClosedEmbedding r hcont hinj).isEmbedding

/-- **Task 3.** The Jordan curve `J = range r` is homeomorphic to the circle `S¹`. -/
noncomputable def jordanCurveHomeo (hcont : Continuous r) (hinj : Injective r) :
    sphere (0 : Plane) 1 ≃ₜ (range r) :=
  (r_isEmbedding r hcont hinj).toHomeomorph

/-- A radius `R ≥ 0` with `range r ⊆ closedBall 0 R` (compact ⇒ bounded). -/
theorem exists_jordanCurve_bound (hcont : Continuous r) :
    ∃ R : ℝ, 0 ≤ R ∧ range r ⊆ closedBall (0 : Plane) R := by
  obtain ⟨R, hR⟩ := (jordanCurve_isCompact r hcont).isBounded.subset_closedBall 0
  exact ⟨max R 0, le_max_right R 0,
    hR.trans (closedBall_subset_closedBall (le_max_left R 0))⟩

/-- **PRELIM (a).** `Jᶜ` has an unbounded connected component: pick any point in the
cobounded exterior `{x | R < ‖x‖}` of a ball containing `J`; that exterior is
connected, lies in `Jᶜ`, and is unbounded, so the component containing it is
unbounded. -/
theorem exists_unbounded_component (hcont : Continuous r) :
    ∃ x ∈ (range r)ᶜ, ¬ IsBounded (connectedComponentIn (range r)ᶜ x) := by
  obtain ⟨R, hR0, hsub⟩ := exists_jordanCurve_bound r hcont
  have hEconn : IsConnected {z : Plane | R < ‖z‖} := isConnected_compl_closedBall hR0
  have hEsub : {z : Plane | R < ‖z‖} ⊆ (range r)ᶜ := by
    intro z hz hzr
    have := hsub hzr
    rw [mem_closedBall_zero_iff] at this
    exact absurd this (not_le.2 hz)
  have hEnb : ¬ IsBounded {z : Plane | R < ‖z‖} := by
    intro hb
    obtain ⟨M, hM⟩ := hb.subset_closedBall 0
    obtain ⟨z, hz⟩ := NormedSpace.exists_lt_norm ℝ Plane (max M R)
    have hzE : z ∈ {z : Plane | R < ‖z‖} := lt_of_le_of_lt (le_max_right M R) hz
    have hzM := hM hzE
    rw [mem_closedBall_zero_iff] at hzM
    exact absurd (le_max_left M R) (not_le.2 (lt_of_lt_of_le hz hzM))
  obtain ⟨x, hxE⟩ := hEconn.nonempty
  refine ⟨x, hEsub hxE, ?_⟩
  have hEcomp : {z : Plane | R < ‖z‖} ⊆ connectedComponentIn (range r)ᶜ x :=
    hEconn.isPreconnected.subset_connectedComponentIn hxE hEsub
  exact fun hbdd => hEnb (hbdd.subset hEcomp)

/-- **PRELIM (a).** Any two unbounded components of `Jᶜ` coincide: each unbounded
component must meet the connected cobounded exterior `{x | R < ‖x‖}`, which therefore
lies in a single component. -/
theorem unbounded_component_unique (hcont : Continuous r) {x y : Plane}
    (hxu : ¬ IsBounded (connectedComponentIn (range r)ᶜ x))
    (hyu : ¬ IsBounded (connectedComponentIn (range r)ᶜ y)) :
    connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ y := by
  obtain ⟨R, hR0, hsub⟩ := exists_jordanCurve_bound r hcont
  set E : Set Plane := {z : Plane | R < ‖z‖} with hE
  have hEconn : IsConnected E := isConnected_compl_closedBall hR0
  have hEsub : E ⊆ (range r)ᶜ := by
    intro z hz hzr
    have := hsub hzr
    rw [mem_closedBall_zero_iff] at this
    exact absurd this (not_le.2 hz)
  -- An unbounded component meets `E`.
  have meetsE : ∀ z : Plane,
      ¬ IsBounded (connectedComponentIn (range r)ᶜ z) →
      ∃ w ∈ E, w ∈ connectedComponentIn (range r)ᶜ z := by
    intro z hz
    by_contra hcon
    push Not at hcon
    apply hz
    have hsubBall : connectedComponentIn (range r)ᶜ z ⊆ closedBall (0 : Plane) R := by
      intro w hw
      rw [mem_closedBall_zero_iff]
      by_contra hwn
      exact hcon w (not_le.1 hwn) hw
    exact isBounded_closedBall.subset hsubBall
  obtain ⟨p, hpE⟩ := hEconn.nonempty
  have hEcomp : E ⊆ connectedComponentIn (range r)ᶜ p :=
    hEconn.isPreconnected.subset_connectedComponentIn hpE hEsub
  -- Both components equal the component of `p`.
  obtain ⟨wx, hwxE, hwxc⟩ := meetsE x hxu
  obtain ⟨wy, hwyE, hwyc⟩ := meetsE y hyu
  have hx : connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ p := by
    rw [connectedComponentIn_eq hwxc, ← connectedComponentIn_eq (hEcomp hwxE)]
  have hy : connectedComponentIn (range r)ᶜ y = connectedComponentIn (range r)ᶜ p := by
    rw [connectedComponentIn_eq hwyc, ← connectedComponentIn_eq (hEcomp hwyE)]
  rw [hx, hy]

/-- **PRELIM (b).** Each connected component of `Jᶜ` is open (`Jᶜ` is open and the
plane is locally connected). -/
theorem isOpen_component (hcont : Continuous r) (x : Plane) :
    IsOpen (connectedComponentIn (range r)ᶜ x) :=
  (isOpen_compl_jordanCurve r hcont).connectedComponentIn

/-- **PRELIM (b).** Each connected component of `Jᶜ` is path-connected (it is open
and connected in the locally path-connected plane). -/
theorem isPathConnected_component (hcont : Continuous r) {x : Plane}
    (hx : x ∈ (range r)ᶜ) :
    IsPathConnected (connectedComponentIn (range r)ᶜ x) :=
  ((isOpen_component r hcont x).isConnected_iff_isPathConnected).mp
    (isConnected_connectedComponentIn_iff.mpr hx)

end JordanCurveData

end MatedCRTHarmonic.Planar.Jordan
