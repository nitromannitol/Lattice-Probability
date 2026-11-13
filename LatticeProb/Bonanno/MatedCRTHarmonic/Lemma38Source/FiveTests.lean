/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Lemma38Source.FiveTests at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.Annulus38
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop210

/-!
# The five Proposition 2.10 tests in [18] Lemma 3.8

At inner radius `ι = s*r`, the tests are the squared logarithmic gradient and constant
function on `A(ι,r)`, the boundary layer on `B(R₁)`, the constant function on
`A(ι/2,9ι)`, and its boundary layer on `B(r)`. The outer-measure union bound below
uses the exact output type of `GMS4.proposition210_holds`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.Lemma38Source

/-- The five domains in the proof of [18] Lemma 3.8, indexed in the order of
`GMS3.lemma38`'s Proposition 2.10 premises. -/
def fiveDomain (z : ℂ) (ι r R₁ : ℝ) (i : Fin 5) : Set ℂ :=
  if i = 0 then GMS3.annulusSet z ι r
  else if i = 1 then GMS3.annulusSet z ι r
  else if i = 2 then ball z R₁
  else if i = 3 then GMS3.annulusSet z (ι / 2) (9 * ι)
  else ball z r

/-- The matching five nonnegative test functions. -/
def fiveTest (z : ℂ) (ι r w : ℝ) (i : Fin 5) : ℂ → ℝ :=
  if i = 0 then fun u => ‖fderiv ℝ (GMS3.logRad z ι r) u‖ ^ 2
  else if i = 1 then fun _ => 1
  else if i = 2 then GMS3.annLayer z ι r w
  else if i = 3 then fun _ => 1
  else GMS3.annLayer z (ι / 2) (9 * ι) w

/-- Union of the failures of precisely the five Proposition 2.10 tests. -/
def fiveBad (F : CellFamily.RandomCellFamily) (k : ℕ) (z : ℂ) (ι r R₁ w A α : ℝ) :
    Set F.Ω :=
  ⋃ i ∈ (Finset.univ : Finset (Fin 5)),
    GMS4.Prop210Bad F k (fiveDomain z ι r R₁ i) (fiveTest z ι r w i)
      (2 * A) (CellFamily.mesh k ^ α)

/-- Outside the finite bad-event union, all five exact premises of `GMS3.lemma38`
hold. No measurability is used. -/
theorem fiveBounds_of_not_fiveBad
    (F : CellFamily.RandomCellFamily) (k : ℕ) (ω : F.Ω) (z : ℂ)
    (ι r R₁ w A α : ℝ)
    (hω : ω ∉ fiveBad F k z ι r R₁ w A α) :
    GMS3.Prop210Bound (F.H k ω) (GMS3.annulusSet z ι r)
      (fun u => ‖fderiv ℝ (GMS3.logRad z ι r) u‖ ^ 2)
      (2 * A) (CellFamily.mesh k ^ α) ∧
    GMS3.Prop210Bound (F.H k ω) (GMS3.annulusSet z ι r)
      (fun _ => 1) (2 * A) (CellFamily.mesh k ^ α) ∧
    GMS3.Prop210Bound (F.H k ω) (ball z R₁)
      (GMS3.annLayer z ι r w) (2 * A) (CellFamily.mesh k ^ α) ∧
    GMS3.Prop210Bound (F.H k ω) (GMS3.annulusSet z (ι / 2) (9 * ι))
      (fun _ => 1) (2 * A) (CellFamily.mesh k ^ α) ∧
    GMS3.Prop210Bound (F.H k ω) (ball z r)
      (GMS3.annLayer z (ι / 2) (9 * ι) w) (2 * A) (CellFamily.mesh k ^ α) := by
  have hgood (i : Fin 5) :
      GMS3.Prop210Bound (F.H k ω) (fiveDomain z ι r R₁ i)
        (fiveTest z ι r w i) (2 * A) (CellFamily.mesh k ^ α) := by
    have hi : ω ∉ GMS4.Prop210Bad F k (fiveDomain z ι r R₁ i)
        (fiveTest z ι r w i) (2 * A) (CellFamily.mesh k ^ α) := by
      intro hbad
      exact hω (Set.mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, hbad⟩)
    simpa only [GMS4.Prop210Bad, GMS4.Prop210Good,
      Set.mem_compl_iff, not_not, Set.mem_ofPred_eq] using hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [fiveDomain, fiveTest] using hgood 0
  · simpa [fiveDomain, fiveTest] using hgood 1
  · simpa [fiveDomain, fiveTest] using hgood 2
  · simpa [fiveDomain, fiveTest] using hgood 3
  · simpa [fiveDomain, fiveTest] using hgood 4

/-- Proposition 2.10's per-test output gives the outer-measure cost of all five
tests. `hadm` is the deterministic admissibility of these explicitly defined pairs. -/
theorem fiveBad_le_of_proposition210
    (F : CellFamily.RandomCellFamily) (k : ℕ) (z : ℂ) (ι r R₁ w : ℝ)
    {rho C₀ beta A α Cfail : ℝ}
    (h210 : ∀ k (D : Set ℂ) (f : ℂ → ℝ),
      GMS4.Prop210Admissible (CellFamily.mesh k) rho C₀ beta D f →
      F.P (GMS4.Prop210Bad F k D f (2 * A) (CellFamily.mesh k ^ α)) ≤
        ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α))
    (hadm : ∀ i : Fin 5, GMS4.Prop210Admissible (CellFamily.mesh k) rho C₀ beta
      (fiveDomain z ι r R₁ i) (fiveTest z ι r w i)) :
    F.P (fiveBad F k z ι r R₁ w A α) ≤
      ENNReal.ofReal (5 * Cfail * CellFamily.mesh k ^ α) := by
  have h := GMS4.finite_union_measure_le_card_mul F.P
    (Finset.univ : Finset (Fin 5))
    (fun i => GMS4.Prop210Bad F k (fiveDomain z ι r R₁ i) (fiveTest z ι r w i)
      (2 * A) (CellFamily.mesh k ^ α))
    (ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α))
    (by intro i _; exact h210 k _ _ (hadm i))
  change F.P (fiveBad F k z ι r R₁ w A α) ≤ _
  calc
    F.P (fiveBad F k z ι r R₁ w A α) ≤
        5 * ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α) := by
          simpa only [fiveBad, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] using h
    _ = ENNReal.ofReal (5 * Cfail * CellFamily.mesh k ^ α) := by
      rw [show (5 : ℝ≥0∞) = ENNReal.ofReal 5 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
      congr 1
      ring

/-- The exact Peanosphere witness at mesh `k` from `CellFamily.PeanosphereG0`. -/
def peanoGood (F : CellFamily.RandomCellFamily) (k : ℕ) : Set F.Ω :=
  {ω | ∃ (path : MatedCRT.Path2) (η : ℝ → ℂ)
    (h : MatedCRT.IsLocallyFinite (CellFamily.mesh k) path)
    (H' : CellularEmbedding (MatedCRT.graph (CellFamily.mesh k) path h) 0),
      RouteM.Peanosphere path η ∧ RouteM.SideStrict (CellFamily.mesh k) path ∧
      (∀ x y, (F.G k ω).adj.Adj x y ↔
        (MatedCRT.graph (CellFamily.mesh k) path h).adj.Adj x y) ∧
      (∀ x, (F.H k ω).cell x = H'.cell x) ∧
      ∀ x, H'.cell x = η '' Set.Icc
        (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x)}

/-- The simultaneous geometric and five-test event at one scale. -/
def fiveInputGood (F : CellFamily.RandomCellFamily) (k : ℕ) (z : ℂ)
    (ι r R₁ w A α ρ₁ δ : ℝ) : Set F.Ω :=
  {ω | GMS3.CellDiamBound (F.H k ω) ρ₁ δ ∧
    ω ∈ peanoGood F k ∧ ω ∉ fiveBad F k z ι r R₁ w A α}

/-- The combined one-scale probability cost: Lemma 2.7's cell event, an almost-sure
Peanosphere witness, and exactly five Proposition 2.10 failures. -/
theorem fiveInputBad_le
    (F : CellFamily.RandomCellFamily) (k : ℕ) (z : ℂ) (ι r R₁ w : ℝ)
    {A α α27 ρ₁ δ C27 Cfail rho C₀ beta : ℝ}
    (h27 : F.P {ω | GMS3.CellDiamBound (F.H k ω) ρ₁ δ}ᶜ ≤
      ENNReal.ofReal (C27 * CellFamily.mesh k ^ α27))
    (hpeano : CellFamily.PeanosphereG0 F)
    (h210 : ∀ k (D : Set ℂ) (f : ℂ → ℝ),
      GMS4.Prop210Admissible (CellFamily.mesh k) rho C₀ beta D f →
      F.P (GMS4.Prop210Bad F k D f (2 * A) (CellFamily.mesh k ^ α)) ≤
        ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α))
    (hadm : ∀ i : Fin 5, GMS4.Prop210Admissible (CellFamily.mesh k) rho C₀ beta
      (fiveDomain z ι r R₁ i) (fiveTest z ι r w i))
    : F.P (fiveInputGood F k z ι r R₁ w A α ρ₁ δ)ᶜ ≤
      ENNReal.ofReal (C27 * CellFamily.mesh k ^ α27) +
      ENNReal.ofReal (5 * Cfail * CellFamily.mesh k ^ α) := by
  let B27 : Set F.Ω := {ω | GMS3.CellDiamBound (F.H k ω) ρ₁ δ}ᶜ
  let BP : Set F.Ω := (peanoGood F k)ᶜ
  let B5 : Set F.Ω := fiveBad F k z ι r R₁ w A α
  have hBP : F.P BP = 0 := by
    exact (ae_iff.mp (hpeano k))
  have hsub : (fiveInputGood F k z ι r R₁ w A α ρ₁ δ)ᶜ ⊆ B27 ∪ BP ∪ B5 := by
    intro ω hω
    by_contra hnot
    have hnot' : ω ∉ B27 ∧ ω ∉ BP ∧ ω ∉ B5 := by
      constructor
      · intro h; exact hnot (Or.inl (Or.inl h))
      constructor
      · intro h; exact hnot (Or.inl (Or.inr h))
      · intro h; exact hnot (Or.inr h)
    apply hω
    exact ⟨by simpa only [B27, Set.mem_compl_iff, not_not, Set.mem_ofPred_eq] using hnot'.1,
      by simpa only [BP, Set.mem_compl_iff, not_not] using hnot'.2.1,
      hnot'.2.2⟩
  have hfive := fiveBad_le_of_proposition210 F k z ι r R₁ w h210 hadm
  calc
    F.P (fiveInputGood F k z ι r R₁ w A α ρ₁ δ)ᶜ ≤ F.P (B27 ∪ BP ∪ B5) :=
      measure_mono hsub
    _ ≤ F.P B27 + F.P BP + F.P B5 := by
      calc
        F.P (B27 ∪ BP ∪ B5) ≤ F.P (B27 ∪ BP) + F.P B5 := measure_union_le _ _
        _ ≤ (F.P B27 + F.P BP) + F.P B5 :=
          add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ENNReal.ofReal (C27 * CellFamily.mesh k ^ α27) +
        ENNReal.ofReal (5 * Cfail * CellFamily.mesh k ^ α) := by
      rw [hBP, add_zero]
      exact add_le_add h27 hfive

/-- Absorb the two polynomial rates into their smaller exponent at dyadic mesh. -/
theorem two_rates_le_min (k : ℕ) {α α27 C27 Cfail : ℝ}
    (hC27 : 0 ≤ C27) (hCfail : 0 ≤ Cfail) :
    ENNReal.ofReal (C27 * CellFamily.mesh k ^ α27) +
      ENNReal.ofReal (5 * Cfail * CellFamily.mesh k ^ α) ≤
      ENNReal.ofReal ((C27 + 5 * Cfail) * CellFamily.mesh k ^ min α27 α) := by
  have hmeshpos := GMSLemma27.mesh_pos k
  have hmeshle : CellFamily.mesh k ≤ 1 := by
    by_cases hk : k = 0
    · subst k
      simp [CellFamily.mesh]
    · exact (GMSLemma27.mesh_lt_one hk).le
  have hpow27 : CellFamily.mesh k ^ α27 ≤ CellFamily.mesh k ^ min α27 α :=
    Real.rpow_le_rpow_of_exponent_ge hmeshpos hmeshle (min_le_left _ _)
  have hpow : CellFamily.mesh k ^ α ≤ CellFamily.mesh k ^ min α27 α :=
    Real.rpow_le_rpow_of_exponent_ge hmeshpos hmeshle (min_le_right _ _)
  have hreal : C27 * CellFamily.mesh k ^ α27 + 5 * Cfail * CellFamily.mesh k ^ α ≤
      (C27 + 5 * Cfail) * CellFamily.mesh k ^ min α27 α := by
    nlinarith [mul_nonneg hC27 (sub_nonneg.mpr hpow27),
      mul_nonneg (show 0 ≤ 5 * Cfail by positivity) (sub_nonneg.mpr hpow)]
  rw [← ENNReal.ofReal_add (mul_nonneg hC27
    (Real.rpow_nonneg hmeshpos.le α27))]
  · exact ENNReal.ofReal_le_ofReal hreal
  · exact mul_nonneg (by positivity) (Real.rpow_nonneg hmeshpos.le α)

/-- On the combined event, G3's 5ι-start version of Lemma 3.8 applies.
This is the radius needed for an entire `[s,5s/4]` grid block. -/
theorem fiveInput_hitDist
    (F : CellFamily.RandomCellFamily) (k : ℕ) (ω : F.Ω)
    {z : ℂ} {ι r R₁ w A α ρ₁ δ κ : ℝ}
    (hinput : ω ∈ fiveInputGood F k z ι r R₁ w A α ρ₁ δ)
    (hι : 0 < ι) (h10 : 10 * ι ≤ r) (hδ0 : 0 ≤ δ)
    (h6 : 6 * δ ≤ ι) (hR₁ : r + δ < R₁)
    (hw : 0 < w) (hδw : δ ≤ w) (hA : 0 ≤ A)
    (hη : 0 ≤ CellFamily.mesh k ^ α) (hκ : 0 < κ)
    (hball : closedBall z R₁ ⊆ ball 0 ρ₁)
    {x : ℤ} (hx : x ∈ verticesMeeting (F.H k ω).cell (ball z (5 * ι))) :
    1 - (6 * Real.sqrt (GMS3.lemma38K ι w (2 * A) (CellFamily.mesh k ^ α)) *
      Real.sqrt (GMS3.lemma34Bound ι r δ w (2 * A) (CellFamily.mesh k ^ α)) / ι +
      2 * κ) ≤
      (HarmonicInfinity.hitDist (F.G k ω)
        (GMS3.vCircle (F.H k ω) z ι ∪ GMS3.vCircle (F.H k ω) z r)
        x (GMS3.vCircle (F.H k ω) z ι)).toReal := by
  obtain ⟨h27, ⟨path, η, h, H', hP, _, hadj, hcell, heval⟩, hfive⟩ := hinput
  have hconn : (F.G k ω).adj.Connected := by
    have heq : (F.G k ω).adj = (MatedCRT.graph (CellFamily.mesh k) path h).adj := by
      ext x y
      exact hadj x y
    rw [heq]
    exact GMS3.matedCRT_connected (CellFamily.mesh k) path h
  have hcal : GMS3.ConnectedAlongLines (F.H k ω) :=
    MesoModel.annulus38_connectedAlongLines_of_peanosphereG0 F k ω path η h H' hP hadj hcell heval
  obtain ⟨hF, h1, hg, h1', hg'⟩ :=
    fiveBounds_of_not_fiveBad F k ω z ι r R₁ w A α hfive
  exact GMS3.lemma38 (H := F.H k ω) hconn hcal hι h10 hδ0 h6 hR₁ hw hδw
    (by positivity) hη hκ hball h27 hF h1 hg h1' hg' hx

/-- Inner-radius monotonicity upgrades the representative's 5ι-start estimate
to every `ι' ∈ [ι,5ι/4]`, while the requested starts meet `B(4ι')`. -/
theorem fiveInput_hitDist_interval
    (F : CellFamily.RandomCellFamily) (k : ℕ) (ω : F.Ω)
    {z : ℂ} {ι ι' r R₁ w A α ρ₁ δ κ : ℝ}
    (hinput : ω ∈ fiveInputGood F k z ι r R₁ w A α ρ₁ δ)
    (hι : 0 < ι) (hιι' : ι ≤ ι') (hι'5 : 4 * ι' ≤ 5 * ι)
    (h10 : 10 * ι ≤ r) (h10' : 10 * ι' ≤ r)
    (hδ0 : 0 ≤ δ) (h6 : 6 * δ ≤ ι) (hR₁ : r + δ < R₁)
    (hw : 0 < w) (hδw : δ ≤ w) (hA : 0 ≤ A)
    (hη : 0 ≤ CellFamily.mesh k ^ α) (hκ : 0 < κ)
    (hball : closedBall z R₁ ⊆ ball 0 ρ₁)
    {x : ℤ} (hx : x ∈ verticesMeeting (F.H k ω).cell (ball z (4 * ι'))) :
    1 - (6 * Real.sqrt (GMS3.lemma38K ι w (2 * A) (CellFamily.mesh k ^ α)) *
      Real.sqrt (GMS3.lemma34Bound ι r δ w (2 * A) (CellFamily.mesh k ^ α)) / ι +
      2 * κ) ≤
      (HarmonicInfinity.hitDist (F.G k ω)
        (GMS3.vCircle (F.H k ω) z ι' ∪ GMS3.vCircle (F.H k ω) z r)
        x (GMS3.vCircle (F.H k ω) z ι')).toReal := by
  obtain ⟨h27, ⟨path, η, h, H', hP, hside, hadj, hcell, heval⟩, hfive⟩ := hinput
  have hconn : (F.G k ω).adj.Connected := by
    have heq : (F.G k ω).adj = (MatedCRT.graph (CellFamily.mesh k) path h).adj := by
      ext a b
      exact hadj a b
    rw [heq]
    exact GMS3.matedCRT_connected (CellFamily.mesh k) path h
  have hdiam : ∀ y, ((F.H k ω).cell y ∩ closedBall z r).Nonempty →
      GMS3.cellDiam (F.H k ω) y ≤ δ := by
    intro y ⟨u, huy, huB⟩
    apply h27 y
    exact ⟨u, huy, hball (closedBall_subset_closedBall (by linarith) huB)⟩
  have hS : GMS3.Lemma38Setup (F.H k ω) z ι r δ :=
    { ι_pos := hι, ten_le := h10, δ_nonneg := hδ0,
      six_le := h6, diam_le := hdiam }
  have hS' : GMS3.Lemma38Setup (F.H k ω) z ι' r δ :=
    { ι_pos := lt_of_lt_of_le hι hιι', ten_le := h10', δ_nonneg := hδ0,
      six_le := le_trans h6 hιι', diam_le := hdiam }
  have hx5 : x ∈ verticesMeeting (F.H k ω).cell (ball z (5 * ι)) := by
    obtain ⟨u, hux, hub⟩ := hx
    refine ⟨u, hux, ?_⟩
    exact (Metric.ball_subset_ball hι'5) hub
  have hxB : ((F.H k ω).cell x ∩ closedBall z r).Nonempty := by
    obtain ⟨u, hux, hub⟩ := hx
    refine ⟨u, hux, ?_⟩
    apply Metric.closedBall_subset_closedBall (show 4 * ι' ≤ r by linarith)
    exact Metric.ball_subset_closedBall hub
  have hbase := fiveInput_hitDist F k ω
    ⟨h27, ⟨path, η, h, H', hP, hside, hadj, hcell, heval⟩,
      hfive⟩ hι h10 hδ0 h6 hR₁ hw hδw hA hη hκ hball hx5
  exact hbase.trans (GMS3.hitDist_in_mono (H := F.H k ω) hconn hS hS' hιι' hxB)

/-- First hitting a disjoint inner set in a two-set union is equivalent to
strictly hitting that set before the outer set. -/
private theorem hitTime_innerBefore_iff {V : Type*} {A B : Set V}
    (hdisj : Disjoint A B) (X : ℕ → V) :
    (Markov.hitTime (A ∪ B) X ≠ ⊤ ∧
      X (Markov.hitTime (A ∪ B) X).toNat ∈ A) ↔
      Markov.hitTime A X < Markov.hitTime B X := by
  classical
  constructor
  · rintro ⟨hfinite, hstop⟩
    let n := (Markov.hitTime (A ∪ B) X).toNat
    have htime : Markov.hitTime (A ∪ B) X = n :=
      (Markov.coe_toNat_hitTime hfinite).symm
    have hfirst := (Markov.hitTime_eq_coe_iff.mp htime).2
    have hA : Markov.hitTime A X = n :=
      (Markov.hitTime_eq_coe_iff.mpr ⟨hstop, fun j hj => by
        have hj' := hfirst j hj
        exact fun ha => hj' (Or.inl ha)⟩)
    have hB : (n : ℕ∞) < Markov.hitTime B X :=
      (Markov.coe_lt_hitTime_iff).2 fun j hj => by
        by_cases hjn : j < n
        · have hj' := hfirst j hjn
          exact fun hb => hj' (Or.inr hb)
        · have hjeq : j = n := by omega
          subst j
          exact fun hb => Set.disjoint_left.mp hdisj hstop hb
    rw [hA]
    exact hB
  · intro hAB
    have hAfinite : Markov.hitTime A X ≠ ⊤ := ne_top_of_lt hAB
    let n := (Markov.hitTime A X).toNat
    have hAtime : Markov.hitTime A X = n := (Markov.coe_toNat_hitTime hAfinite).symm
    have hAfirst := Markov.hitTime_eq_coe_iff.mp hAtime
    have hUnionLower : (n : ℕ∞) ≤ Markov.hitTime (A ∪ B) X :=
      (Markov.le_hitTime_iff).2 fun j hj => by
        by_contra hnot
        have hnot' : ¬ n ≤ j := by exact_mod_cast hnot
        have hjlt : j < n := Nat.lt_of_not_ge hnot'
        have hjA : X j ∉ A := hAfirst.2 j hjlt
        have hBn : (n : ℕ∞) < Markov.hitTime B X := by
          simpa [hAtime] using hAB
        have hjB : X j ∉ B := Markov.notMem_of_lt_hitTime
          (lt_of_le_of_lt (by exact_mod_cast hjlt.le) hBn)
        rcases hj with hj | hj
        · exact False.elim (hjA hj)
        · exact False.elim (hjB hj)
    have hUnioneq : Markov.hitTime (A ∪ B) X = n := by
      apply le_antisymm
      · exact Markov.hitTime_le_of_mem (Set.mem_union_left B hAfirst.1)
      · exact hUnionLower
    refine ⟨by rw [hUnioneq]; exact ENat.natCast_ne_top n, ?_⟩
    rw [hUnioneq]
    exact hAfirst.1

/-- Identify G3's hitting distribution with the corrected `HitsBefore` event.
The setup ensures disjoint inner and outer vertex circles. -/
theorem hitDist_eq_hitsBefore
    (F : CellFamily.RandomCellFamily) (k : ℕ) (ω : F.Ω)
    {z : ℂ} {ι r δ : ℝ}
    (hS : GMS3.Lemma38Setup (F.H k ω) z ι r δ) (x : ℤ) :
    HarmonicInfinity.hitDist (F.G k ω)
      (GMS3.vCircle (F.H k ω) z ι ∪ GMS3.vCircle (F.H k ω) z r)
      x (GMS3.vCircle (F.H k ω) z ι) =
    (F.G k ω).walkLaw x {ω' | CellFamily.HitsBefore (F.H k ω).cell z (ι / r) r
      ((F.G k ω).vertexPath ω')} := by
  have hr : 0 < r := by linarith [hS.ι_pos, hS.ten_le]
  have hratio : (ι / r) * r = ι := by field_simp
  have hcircle (a : ℝ) : GMS3.vCircle (F.H k ω) z a =
      verticesMeeting (F.H k ω).cell (Metric.sphere z a) := by
    have hsphere : Metric.sphere z a = {u | ‖u - z‖ = a} := by
      ext u
      simp
    rw [GMS3.vCircle, hsphere]
  unfold HarmonicInfinity.hitDist
  congr 1
  ext ω'
  simp only [Set.mem_ofPred_eq]
  change (Markov.hitTime
      (GMS3.vCircle (F.H k ω) z ι ∪ GMS3.vCircle (F.H k ω) z r)
      ((F.G k ω).vertexPath ω') ≠ ⊤ ∧
      (F.G k ω).vertexPath ω'
        (Markov.hitTime
          (GMS3.vCircle (F.H k ω) z ι ∪ GMS3.vCircle (F.H k ω) z r)
          ((F.G k ω).vertexPath ω')).toNat ∈ GMS3.vCircle (F.H k ω) z ι) ↔
    Markov.hitTime
      (verticesMeeting (F.H k ω).cell (Metric.sphere z ((ι / r) * r)))
      ((F.G k ω).vertexPath ω') <
    Markov.hitTime (verticesMeeting (F.H k ω).cell (Metric.sphere z r))
      ((F.G k ω).vertexPath ω')
  rw [hratio, ← hcircle ι, ← hcircle r]
  exact hitTime_innerBefore_iff (GMS3.vCircle_disjoint hS)
    ((F.G k ω).vertexPath ω')

/-- The fixed representative's five tests control the corrected walk event at
every inner radius in its `5/4` block. The deterministic error is still
expressed at the representative radius. -/
theorem fiveInput_walkLaw_interval
    (F : CellFamily.RandomCellFamily) (k : ℕ) (ω : F.Ω)
    {z : ℂ} {s s' r R₁ w A α ρ₁ δ κ : ℝ}
    (hinput : ω ∈ fiveInputGood F k z (s * r) r R₁ w A α ρ₁ δ)
    (hr : 0 < r) (hs : 0 < s) (hss' : s ≤ s')
    (hs'5 : 4 * s' ≤ 5 * s) (hs10 : s ≤ 1 / 10)
    (hs'10 : s' ≤ 1 / 10)
    (hδ0 : 0 ≤ δ) (h6 : 6 * δ ≤ s * r) (hR₁ : r + δ < R₁)
    (hw : 0 < w) (hδw : δ ≤ w) (hA : 0 ≤ A)
    (hη : 0 ≤ CellFamily.mesh k ^ α) (hκ : 0 < κ)
    (hball : closedBall z R₁ ⊆ ball 0 ρ₁)
    {x : ℤ} (hx : x ∈ verticesMeeting (F.H k ω).cell (ball z (4 * s' * r))) :
    ENNReal.ofReal
      (1 - (6 * Real.sqrt (GMS3.lemma38K (s * r) w (2 * A) (CellFamily.mesh k ^ α)) *
        Real.sqrt (GMS3.lemma34Bound (s * r) r δ w (2 * A) (CellFamily.mesh k ^ α)) /
        (s * r) + 2 * κ)) ≤
      (F.G k ω).walkLaw x {ω' | CellFamily.HitsBefore (F.H k ω).cell z s' r
        ((F.G k ω).vertexPath ω')} := by
  have hι : 0 < s * r := mul_pos hs hr
  have hιι' : s * r ≤ s' * r := mul_le_mul_of_nonneg_right hss' hr.le
  have hι'5 : 4 * (s' * r) ≤ 5 * (s * r) := by
    nlinarith [mul_nonneg (show 0 ≤ 5 * s - 4 * s' by linarith) hr.le]
  have h10 : 10 * (s * r) ≤ r := by nlinarith
  have h10' : 10 * (s' * r) ≤ r := by nlinarith
  have hx' : x ∈ verticesMeeting (F.H k ω).cell (ball z (4 * (s' * r))) := by
    simpa only [show 4 * s' * r = 4 * (s' * r) by ring] using hx
  have hdist := fiveInput_hitDist_interval F k ω hinput hι hιι' hι'5 h10 h10'
    hδ0 h6 hR₁ hw hδw hA hη hκ hball hx'
  obtain ⟨h27, _, _⟩ := hinput
  have hdiam : ∀ y, ((F.H k ω).cell y ∩ closedBall z r).Nonempty →
      GMS3.cellDiam (F.H k ω) y ≤ δ := by
    intro y ⟨u, huy, huB⟩
    apply h27 y
    exact ⟨u, huy, hball (closedBall_subset_closedBall (by linarith) huB)⟩
  have hS' : GMS3.Lemma38Setup (F.H k ω) z (s' * r) r δ :=
    { ι_pos := lt_of_lt_of_le hι hιι', ten_le := h10', δ_nonneg := hδ0,
      six_le := le_trans h6 hιι', diam_le := hdiam }
  have heq := hitDist_eq_hitsBefore F k ω hS' x
  have hratio : (s' * r) / r = s' := by field_simp
  rw [hratio] at heq
  rw [← heq]
  exact ENNReal.ofReal_le_of_le_toReal hdist

end MatedCRTHarmonic.Lemma38Source
