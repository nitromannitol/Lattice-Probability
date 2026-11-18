import LatticeProb.LQG.ShiftedSidedContact

/-! # Edges of the mated-CRT map as sided contact arcs

In the `ε`-mated-CRT map of a path `ω`, two non-consecutive vertices `x + 1 < y` carry an
`L`-edge iff the side condition holds for the left contour coordinate and an `R`-edge iff it
holds for the right one; consecutive vertices carry exactly one edge. Under the strict side
conditions and for a Peanosphere whose curve has finite fibres and shared segment frontiers,
the side condition of a coordinate holds iff its direct contact image is nontrivial. Hence the
edges joining two non-consecutive vertices are in bijection with the coordinates whose contact
image between the two cells is nontrivial (and then contains a shared frontier arc), and their
number is the sided contact multiplicity. For the coupled curves this holds almost surely at
a fixed mesh, and for an independent phase with an absolutely continuous law on the shifted
grid.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal

namespace MatedCRTHarmonic.RouteM

open MatedCRTHarmonic.MatedCRT

open Classical in
/-- The number of booleans satisfying a predicate. -/
theorem nat_card_subtype_bool (p : Bool → Prop) :
    Nat.card {b : Bool // p b} = (if p false then 1 else 0) + (if p true then 1 else 0) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_bool,
    add_comm]

/-- For non-consecutive vertices, the edge of side `b` is present iff the side condition holds
for the contour coordinate of side `b`. -/
theorem isEdge_iff_sideCond {ε : ℝ} {ω : Path2} {x y : ℤ} (hxy : x + 1 < y) (b : Bool) :
    IsEdge ε ω (x, y, b) ↔ SideCond ε (if b then rCoord ω else lCoord ω) x y := by
  have h1 : x < y := by omega
  have h2 : y ≠ x + 1 := by omega
  have hc : (fun t => if b then (ω t).2 else (ω t).1) = (if b then rCoord ω else lCoord ω) := by
    cases b <;> rfl
  unfold IsEdge
  simp only [h1, h2, true_and, false_and, false_or, ne_eq, not_false_eq_true]
  rw [hc]

/-- Consecutive vertices carry exactly one edge. -/
theorem nat_card_isEdge_succ (ε : ℝ) (ω : Path2) (x : ℤ) :
    Nat.card {b : Bool // IsEdge ε ω (x, x + 1, b)} = 1 := by
  have h : ∀ b : Bool, IsEdge ε ω (x, x + 1, b) ↔ b = false := by
    intro b
    unfold IsEdge
    simp only [lt_add_iff_pos_right, zero_lt_one, true_and, ne_eq, not_true_eq_false,
      false_and, or_false]
  rw [nat_card_subtype_bool]
  simp [h]

/-- Deterministic edge-contact correspondence: under the strict side conditions, for a
Peanosphere whose curve has finite fibres and shared segment frontiers, the edge of side `b`
between non-consecutive vertices is present iff the direct contact image of side `b` is
nontrivial. -/
theorem Peanosphere.isEdge_iff_nontrivial_contact {ω : Path2} {η : ℝ → ℂ}
    (P : Peanosphere ω η) (hfinite : ∀ z : ℂ, (η ⁻¹' {z}).Finite)
    (hfront : ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      η '' Icc a b ∩ η '' Icc c d = frontier (η '' Icc a b) ∩ frontier (η '' Icc c d))
    {ε : ℝ} (hε : 0 < ε) (hs : SideStrict ε ω) {x y : ℤ} (hxy : x + 1 < y) (b : Bool) :
    IsEdge ε ω (x, y, b) ↔
      (η '' directContactTimes ε (if b then rCoord ω else lCoord ω) x y).Nontrivial := by
  rw [isEdge_iff_sideCond hxy b]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [(P.left_sided_contact hfinite hfront hε hxy).2.1]
    exact ⟨DAux.dWin_lt_L hs hxy, fun h => h.le⟩
  · simp only [↓reduceIte]
    rw [(P.right_sided_contact hfinite hfront hε hxy).2.1]
    exact ⟨DAux.dWin_lt_R hs hxy, fun h => h.le⟩

/-- Deterministically, under the hypotheses of `Peanosphere.isEdge_iff_nontrivial_contact`, the
number of edges joining two non-consecutive vertices is the sided contact multiplicity. -/
theorem Peanosphere.nat_card_isEdge_eq_sidedContactMult {ω : Path2} {η : ℝ → ℂ}
    (P : Peanosphere ω η) (hfinite : ∀ z : ℂ, (η ⁻¹' {z}).Finite)
    (hfront : ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      η '' Icc a b ∩ η '' Icc c d = frontier (η '' Icc a b) ∩ frontier (η '' Icc c d))
    {ε : ℝ} (hε : 0 < ε) (hs : SideStrict ε ω) {x y : ℤ} (hxy : x + 1 < y) :
    Nat.card {b : Bool // IsEdge ε ω (x, y, b)} = sidedContactMult ε ω η x y := by
  have hl := P.isEdge_iff_nontrivial_contact hfinite hfront hε hs hxy false
  have hr := P.isEdge_iff_nontrivial_contact hfinite hfront hε hs hxy true
  simp only [Bool.false_eq_true, ↓reduceIte] at hl hr
  rw [nat_card_subtype_bool, sidedContactMult]
  by_cases a : (η '' directContactTimes ε (lCoord ω) x y).Nontrivial <;>
    by_cases b : (η '' directContactTimes ε (rCoord ω) x y).Nontrivial <;>
    simp [a, b, hl, hr]

end MatedCRTHarmonic.RouteM

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- At a fixed positive mesh, almost surely, for all non-consecutive vertices, the edge of each
side is present in the mated-CRT map iff the direct contact image of that side is nontrivial,
and the number of edges is the sided contact multiplicity. -/
theorem ae_isEdge_iff_nontrivial_contact {ε : ℝ} (hε : 0 < ε)
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ x y : ℤ, x + 1 < y →
      (∀ b : Bool, IsEdge ε (bm ω) (x, y, b) ↔
        ((η ω) '' directContactTimes ε (if b then rCoord (bm ω) else lCoord (bm ω)) x y).Nontrivial) ∧
      Nat.card {b : Bool // IsEdge ε (bm ω) (x, y, b)} = sidedContactMult ε (bm ω) (η ω) x y := by
  have hs : ∀ᵐ ω ∂P, SideStrict ε (bm ω) :=
    ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable (ae_sideStrict D.boundaryLawBM ε hε)
  filter_upwards [ae_peanosphere D, GMS4c.ae_bundle_finite_quantum_visits D,
    ae_shared_frontiers_of_coupling D, hs] with ω hP hfinite hf hs
  have hfront := fun a b a' b' h1 h2 h3 => (hf a b a' b' h1 h2 h3).2.1
  intro x y hxy
  exact ⟨hP.isEdge_iff_nontrivial_contact hfinite hfront hε hs hxy,
    hP.nat_card_isEdge_eq_sidedContactMult hfinite hfront hε hs hxy⟩

/-- On the shifted grid with an independent phase of absolutely continuous s-finite law, at a
fixed positive mesh, almost surely for the product of the coupling and the phase law, for all
non-consecutive vertices, the edge of each side is present iff its direct contact image is
nontrivial, and the number of edges is the sided contact multiplicity. -/
theorem ae_prod_isEdge_time_translate_iff_nontrivial_contact
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume) :
    ∀ᵐ p ∂P.prod Q, ∀ x y : ℤ, x + 1 < y →
      (∀ b : Bool, IsEdge ε (timeTranslate (bm p.1) p.2) (x, y, b) ↔
        ((fun t => η p.1 (t + p.2)) '' directContactTimes ε
          (if b then rCoord (timeTranslate (bm p.1) p.2)
            else lCoord (timeTranslate (bm p.1) p.2)) x y).Nontrivial) ∧
      Nat.card {b : Bool // IsEdge ε (timeTranslate (bm p.1) p.2) (x, y, b)} =
        sidedContactMult ε (timeTranslate (bm p.1) p.2) (fun t => η p.1 (t + p.2)) x y := by
  have hm := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).ae
    (ae_time_translate_sided_hypotheses D)
  filter_upwards [hm, ae_prod_shifted_sideStrict_of_coupling D hε Q hQ] with p hh hs
  have hs' : SideStrict ε (timeTranslate (bm p.1) p.2) := hs
  obtain ⟨hP, hfinite, hfront⟩ := hh p.2
  intro x y hxy
  exact ⟨hP.isEdge_iff_nontrivial_contact hfinite hfront hε hs' hxy,
    hP.nat_card_isEdge_eq_sidedContactMult hfinite hfront hε hs' hxy⟩

end MatedCRTHarmonic.MoTInput
