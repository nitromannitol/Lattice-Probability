/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RDefs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundShapes
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceIdx
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceRadius
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBScaleCutoff
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBCoarseIndexRange

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 
def laneSourceIdx (Q : PsiParams) (K : ℕ) : Finset (ℤ × ℤ) :=
  j1SourceIdx K (j1SourceRadius Q K)

 
def laneCHitBall (K m : ℕ) (b : ℤ × ℤ) : Set ℂ :=
  ball (T20.dyCenter K b) (LaneCInputs.sourceRadius K m)

 
def laneCHits {Ω : Type*} (γ : ℕ → ℕ → Ω → ℝ → ℂ) (j n K m : ℕ)
    (b : ℤ × ℤ) : Set Ω :=
  {ω | ∃ t ∈ Icc (0 : ℝ) 1, γ j n ω t ∈ laneCHitBall K m b}

 

def laneCEventualHit {Ω : Type*} (γ : ℕ → ℕ → Ω → ℝ → ℂ) (n K m : ℕ)
    (b : ℤ × ℤ) : Set Ω :=
  {ω | ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ω ∈ laneCHits γ j n K m b}

 
def laneA3Around {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    (n K : ℕ) (b : ℤ × ℤ) (ω : Ω) : ℝ≥0∞ :=
  (lfppContMetric ξ (fun z => psiMN Q W P 0 n z ω)
    ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
    (LaneCInputs.sourceAround K (laneBCoarseIndex Q K) b)
    (LaneCInputs.sourceInner K (laneBCoarseIndex Q K) b)
    (LaneCInputs.sourceOuter K (laneBCoarseIndex Q K) b)

 
def laneA3Across {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (Q : PsiParams) (ξ : ℝ)
    (n K : ℕ) (b : ℤ × ℤ) (ω : Ω) : ℝ≥0∞ :=
  crossLenIn ξ (fun z => psiMN Q W P 0 n z ω)
    (j1SourceCross K (laneBCoarseIndex Q K) b)
    (LaneCInputs.sourceInner K (laneBCoarseIndex Q K) b)
    (LaneCInputs.sourceOuter K (laneBCoarseIndex Q K) b)

 


def C1EventualHitResampling.{u} (Q : PsiParams) : Prop :=
  ∀ ξ : ℝ, ∃ K₀ : ℕ,
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (n K : ℕ),
    K₀ ≤ K → K ≤ n →
    ∀ γ : ℕ → ℕ → Ω → ℝ → ℂ,
      (∀ j : ℕ, T20.IsNearGeodSel ξ Q W P (((j : ℝ) + 1)⁻¹) (γ j)) →
    ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
      rectLen ξ (fun x => psiMN Q W P 0 n x z.1 -
          T20B.blkKn Q W P K n b x z.1 + T20B.blkKn Q W P K n b x z.2)
          (rectAB 1 1) ≤
        rectLen ξ (fun x => psiMN Q W P 0 n x z.1) (rectAB 1 1) +
        (laneCEventualHit γ n K (laneBCoarseIndex Q K) b).indicator
          (laneA3Around P W hW Q ξ n K b) z.1

end SupercriticalLQGUniqueness.B2.DG20Conc
