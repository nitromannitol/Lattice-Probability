/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RPhysical at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RAllArc
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCEssentialLoop
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.LoopSep
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalScaleEventually
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGOsc
import LatticeProb.Bonanno.LQGMetric.Topo.Shortcut
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Glue
import Mathlib.Topology.Order.IntermediateValue
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRepeatLift
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet
import LatticeProb.Bonanno.LQGMetric.Topo.SectorRect
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalContinuousLimit
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAroundWitness
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalScaleWitness
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLargeKScale

 









set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise
universe u

theorem laneC1R_physical_resampling_le_around_of_lt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    {K n : ℕ} (hKn : K ≤ n) {s r : ℝ}
    (hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s)
    (hr : (2 : ℝ)⁻¹ ^ K + 2 * s ≤ r) (hr0 : 0 < r) (hsmall : 4 * r ≤ 1) :
    ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
      let c := T20.dyCenter K b
      let A : Set ℂ := {x | r < dist x c ∧ dist x c < 2 * r}
      ∀ γ : ℝ → ℂ,
      AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ γ →
      lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ ≠ ⊤ →
      ∀ m : ℝ, m ∈ Icc (0 : ℝ) 1 → dist (γ m) c < r →
      ∀ M : ℝ, 0 < M →
      (lfppContMetric ξ (fun x => psiMN Q W P 0 n x z.1)
        ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont z.1)).aroundDist A
          (sphere c r) (sphere c (2 * r)) < ENNReal.ofReal M →
      (rectLen ξ (fun x => psiMN Q W P 0 n x z.1 -
        T20B.blkKn Q W P K n b x z.1 + T20B.blkKn Q W P K n b x z.2) (rectAB 1 1)).toReal ≤
        (lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ).toReal + M := by
  filter_upwards [laneC_physical_boundary_resampling_le_of_continuous_arc
      hW Q ξ hKn hσ hr] with z hz
  intro b hb
  dsimp only
  intro γ hγ hγfin m hm hmid M hM haround
  let c := T20.dyCenter K b
  let A : Set ℂ := {x | r < dist x c ∧ dist x c < 2 * r}
  let D := lfppContMetric ξ (fun x => psiMN Q W P 0 n x z.1)
    ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont z.1)
  obtain ⟨a, d, ρ, had, hρcont, hρA, hsep, hρlen⟩ :=
    laneC_exists_around_witness_of_lt D A (sphere c r) (sphere c (2 * r)) haround
  obtain ⟨z₀, hz₀, z₁, hz₁, hpath, hγsq⟩ := hγ
  have h0 : γ 0 ∈ (rectAB 1 1).side₁ := by simpa only [hpath.source] using hz₀
  have h1 : γ 1 ∈ (rectAB 1 1).side₂ := by simpa only [hpath.target] using hz₁
  obtain ⟨α, t₀, t₁, hα, hαann, hαS, hcost, ht₀, ht₁, hle, hstart, hend⟩ :=
    laneC1R_detour_all (D := D) hsmall
      ⟨had, hρcont, hr0, (fun x hx => hρA ⟨x, hx, rfl⟩), hsep, hpath.continuousOn, hγsq,
        h0, h1, m, hm, hmid⟩
  exact hz b hb α γ hα hαann hαS ⟨z₀, hz₀, z₁, hz₁, hpath, hγsq⟩ hγfin M hM
    (lt_of_le_of_lt hcost hρlen) t₀ t₁ ht₀ ht₁ hle hstart hend

theorem laneC1R_physical_resampling_le_around
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    {K n : ℕ} (hKn : K ≤ n) {s r : ℝ}
    (hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s)
    (hr : (2 : ℝ)⁻¹ ^ K + 2 * s ≤ r) (hr0 : 0 < r) (hsmall : 4 * r ≤ 1) :
    ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
      let c := T20.dyCenter K b
      let A : Set ℂ := {x | r < dist x c ∧ dist x c < 2 * r}
      ∀ γ : ℝ → ℂ,
      AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ γ →
      lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ ≠ ⊤ →
      ∀ m : ℝ, m ∈ Icc (0 : ℝ) 1 → dist (γ m) c < r →
      let D := lfppContMetric ξ (fun x => psiMN Q W P 0 n x z.1)
        ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont z.1)
      D.aroundDist A (sphere c r) (sphere c (2 * r)) ≠ ⊤ →
      (rectLen ξ (fun x => psiMN Q W P 0 n x z.1 -
        T20B.blkKn Q W P K n b x z.1 + T20B.blkKn Q W P K n b x z.2) (rectAB 1 1)).toReal ≤
        (lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ).toReal +
          (D.aroundDist A (sphere c r) (sphere c (2 * r))).toReal := by
  filter_upwards [laneC1R_physical_resampling_le_around_of_lt
      hW Q ξ hKn hσ hr hr0 hsmall] with z hz
  intro b hb
  dsimp only
  intro γ hγ hγfin m hm hmid hfin
  let c := T20.dyCenter K b
  let A : Set ℂ := {x | r < dist x c ∧ dist x c < 2 * r}
  let D := lfppContMetric ξ (fun x => psiMN Q W P 0 n x z.1)
    ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont z.1)
  apply le_of_forall_pos_le_add
  intro η hη
  have hM : 0 < (D.aroundDist A (sphere c r) (sphere c (2 * r))).toReal + η :=
    add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hη
  have hlt : D.aroundDist A (sphere c r) (sphere c (2 * r)) <
      ENNReal.ofReal ((D.aroundDist A (sphere c r) (sphere c (2 * r))).toReal + η) :=
    (ENNReal.lt_ofReal_iff_toReal_lt hfin).2 (lt_add_of_pos_right _ hη)
  simpa only [add_assoc] using (hz b hb γ hγ hγfin m hm hmid _ hM hlt)

 

theorem laneC1R_largeK_resampling_le_source_around
    (Q : PsiParams) (hR : Q.r₀ ≤ (1 : ℝ) / 100) (hε : Q.ε₀ ≤ (1 : ℝ) / 100) (ξ : ℝ) :
    ∃ K₀ : ℕ, 8 ≤ K₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω]
      (P : Measure Ω) (W : WNSpace → Ω → ℝ),
      ∀ hW : IsWhiteNoise P W, ∀ n K m : ℕ,
      K₀ ≤ K → K ≤ n → m + 1 ≤ K →
      (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ Q.ε₀ →
      (K : ℝ) ^ Q.ε₀ ≤ (2 : ℝ) ^ m →
      ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
        ∀ γ : ℝ → ℂ,
        AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ γ →
        lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ ≠ ⊤ →
        ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        dist (γ t) (T20.dyCenter K b) < LaneCInputs.sourceRadius K m →
        let D := lfppContMetric ξ (fun x => psiMN Q W P 0 n x z.1)
          ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont z.1)
        D.aroundDist (LaneCInputs.sourceAround K m b) (LaneCInputs.sourceInner K m b)
          (LaneCInputs.sourceOuter K m b) ≠ ⊤ →
        (rectLen ξ (fun x => psiMN Q W P 0 n x z.1 -
          T20B.blkKn Q W P K n b x z.1 + T20B.blkKn Q W P K n b x z.2) (rectAB 1 1)).toReal ≤
          (lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ).toReal +
            (D.aroundDist (LaneCInputs.sourceAround K m b) (LaneCInputs.sourceInner K m b)
              (LaneCInputs.sourceOuter K m b)).toReal := by
  obtain ⟨Kσ, hKσ⟩ := laneC_eventual_physical_scale_witness Q hR hε
  refine ⟨max 8 Kσ, le_max_left _ _, ?_⟩
  intro Ω _ P W hW n K m hK hKn hmK hmLo hmHi
  obtain ⟨s, hσ, hr⟩ := hKσ K m n (le_trans (le_max_right _ _) hK) hKn hmK hmHi
  have hr0 : 0 < LaneCInputs.sourceRadius K m := by
    unfold LaneCInputs.sourceRadius
    positivity
  have hrSmall : 2 * LaneCInputs.sourceRadius K m < 1 / 8 :=
    laneC_source_outer_radius_lt_eighth ((le_max_left _ _).trans hK) hmK (by linarith) hmLo
  filter_upwards [laneC1R_physical_resampling_le_around hW Q ξ hKn hσ hr hr0
      (by linarith)] with z hz
  intro b hb γ hγ hγfin t ht hmid _D hfinite
  exact hz b hb γ hγ hγfin t ht hmid hfinite

end SupercriticalLQGUniqueness.B2.DG20Conc
