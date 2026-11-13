/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Iface.Statements at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.RescaledLFPP
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPNormalizer
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsWeakLQGMetric
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs
import Mathlib.Topology.Metrizable.Basic

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric (DistC DistOn restrictTo addFun IsGFFPlusCont IsGFFPlusBddCont)
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.Iface

 


def LscTop : Prop :=
  TopologicalSpace.MetrizableSpace LSCFun ∧
    TopologicalSpace.MetrizableSpace LSCMetric

 

def IsRationalCircle (O : Set ℂ) : Prop :=
  ∃ x y r : ℚ, 0 ≤ r ∧
    O = Metric.sphere (Complex.mk (x : ℝ) (y : ℝ)) (r : ℝ)

def IsRationalPoint (z : ℂ) : Prop :=
  ∃ x y : ℚ, z = Complex.mk (x : ℝ) (y : ℝ)

 

def setDistance (d : ℂ × ℂ → ℝ≥0∞) (A B : Set ℂ) : ℝ≥0∞ :=
  ⨅ u ∈ A, ⨅ v ∈ B, d (u, v)

 

def SubseqLimit (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusBddCont h P →
    ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
      (∀ δ, IsHeatSmoothing P h δ (X δ)) →
      (∀ᵐ ω ∂P,
        LSCTendsto (fun n => rescaledLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω))
          (D (h ω)).toLSCFun.1) ∧
      (∀ O O' : Set ℂ, IsRationalCircle O → IsRationalCircle O' →
        ∀ᵐ ω ∂P,
          Tendsto (fun n => ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
            setDistance (lfppDistance (ξ : ℝ) (X (ε n) ω)) O O') atTop
            (𝓝 (setDistance (D (h ω)).1 O O')))

 


def IsPfeWeakMetric (ξ : Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) : Prop :=
  Measurable D ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ᵐ ω ∂P, (D (h ω)).IsLengthSpace) ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ U : TopologicalSpace.Opens ℂ,
      ∃ F : DistOn U → (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞), Measurable F ∧
        ∀ᵐ ω ∂P, (D (h ω)).internal (U : Set ℂ) = F (restrictTo U (h ω))) ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P →
      ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ), weylScale (ξ : ℝ) f (D (h ω)) =
        (D (addFun (h ω) f)).1) ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (D (translateDist z (h ω))).1 (u, v) =
        (D (h ω)).1 (u + z, v + z)) ∧
  (∃ Λ : ℝ, 1 < Λ ∧
    (∀ δ : Set.Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ))) ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ a : Set.Ioi (0 : ℝ) → Ω → ℝ,
      (∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P, IsCircleAverage (h ω) r 0 (a r ω)) →
      ∀ A : EuclideanAnnulus,
        IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
          ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * a r ω))) *
            acrossDist (D (h ω)) (A.dilate r r.2)) ∧
        IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
          ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * a r ω))) *
            aroundDist (D (h ω)) (A.dilate r r.2)))

 


def DG20QuantileRatio : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ), ∃ p : Set.Ioo (0 : ℝ) (1 / 2),
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ,
          LambdaN ξ W P n (ENNReal.ofReal (p : ℝ)) ≤ C

 




def DG20PercEstimate' : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ),
    ∀ U : TopologicalSpace.Opens ℂ, ∀ K₁ K₂ : Set ℂ,
      IsCompact K₁ → IsCompact K₂ → IsConnected K₁ → IsConnected K₂ →
      K₁.Nontrivial → K₂.Nontrivial → K₁ ⊆ U → K₂ ⊆ U → Disjoint K₁ K₂ →
      IsConnected (U : Set ℂ) →
      ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
          ∀ n : ℕ, ∀ T : ℝ, 3 < T →
            P {ω | crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω)
                U K₁ K₂ < ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ≤
              ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) ∧
            P {ω | ENNReal.ofReal (T * lambdaN ξ W P n) <
                crossLenIn (ξ : ℝ) (fun z => phiMN W P 0 n z ω) U K₁ K₂} ≤
              ENNReal.ofReal (c₀ * Real.exp
                (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T)))

 


def DG20Section4 : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
    ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
          (∀ ε, IsHeatSmoothing P h ε (X ε)) →
          ∀ U : TopologicalSpace.Opens ℂ, IsConnected (U : Set ℂ) →
          ∀ z w : ℂ, z ∈ U → w ∈ U → z ≠ w →
            IsTwoSidedTight P (fun (ε : Set.Ioo (0 : ℝ) 1) ω =>
              ENNReal.ofReal ((m ⟨(ε : ℝ), Set.mem_Ioi.mpr ε.property.1⟩ : ℝ)⁻¹) *
                crossLenIn (ξ : ℝ) (X ⟨(ε : ℝ), Set.mem_Ioi.mpr ε.property.1⟩ ω) U {z} {w})) ∧
      (∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ, 0 < C ∧
        ∀ r : Set.Ioo (0 : ℝ) 1, ∀ ε : Set.Ioo (0 : ℝ) (r : ℝ),
          C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q + ζ) ≤
            (r : ℝ) * (m ⟨(ε : ℝ) / (r : ℝ), Set.mem_Ioi.mpr (div_pos ε.property.1 r.property.1)⟩ : ℝ) /
              (m ⟨(ε : ℝ), Set.mem_Ioi.mpr ε.property.1⟩ : ℝ) ∧
          (r : ℝ) * (m ⟨(ε : ℝ) / (r : ℝ), Set.mem_Ioi.mpr (div_pos ε.property.1 r.property.1)⟩ : ℝ) /
              (m ⟨(ε : ℝ), Set.mem_Ioi.mpr ε.property.1⟩ : ℝ) ≤
            C * (r : ℝ) ^ ((ξ : ℝ) * Q - ζ)) ∧
      (∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ, 0 < C ∧
        ∀ r : Set.Ioi (1 : ℝ), ∀ ε : Set.Ioo (0 : ℝ) 1,
          C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q - ζ) ≤
            (r : ℝ) * (m ⟨(ε : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos ε.property.1 (lt_trans one_pos r.property))⟩ : ℝ) /
              (m ⟨(ε : ℝ), Set.mem_Ioi.mpr ε.property.1⟩ : ℝ) ∧
          (r : ℝ) * (m ⟨(ε : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos ε.property.1 (lt_trans one_pos r.property))⟩ : ℝ) /
              (m ⟨(ε : ℝ), Set.mem_Ioi.mpr ε.property.1⟩ : ℝ) ≤
            C * (r : ℝ) ^ ((ξ : ℝ) * Q + ζ))

 



def DG20Limit : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
    ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ ε : ℕ → Set.Ioi (0 : ℝ),
        Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
            (∀ r : ℚ, ∀ hr : 0 < r,
              Tendsto (fun n => (r : ℝ) *
                (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
                  Set.mem_Ioi.mpr (div_pos (ε (φ n)).property
                    (Rat.cast_pos.mpr hr))⟩ : ℝ) /
                (m (ε (φ n)) : ℝ)) atTop
                (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) ∧
            ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
              ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
                (∀ δ, IsHeatSmoothing P h δ (X δ)) →
              ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
                (_ : IsProbabilityMeasure P') (h' : Ω' → DistC)
                (F : ℕ → Ω' → ℂ × ℂ → EReal) (L : Ω' → LSCMetric),
                Measurable L ∧ IsNormalizedWholePlaneGFF h' P' ∧
                (∀ n, P'.map (fun ω => (h' ω, F n ω)) =
                  P.map (fun ω => (h ω,
                    rescaledLFPP (ξ : ℝ) (m (ε (φ n))) (X (ε (φ n)) ω)))) ∧
                (∀ᵐ ω ∂P', LSCTendsto (fun n => F n ω) (L ω).toLSCFun.1) ∧
                (∀ᵐ ω ∂P', ∀ u v : ℂ, IsRationalPoint u → IsRationalPoint v →
                  Tendsto (fun n => F n ω (u, v)) atTop
                    (𝓝 ((L ω).toLSCFun.1 (u, v)))) ∧
                (∀ᵐ ω ∂P', (L ω).IsLengthSpace ∧
                  (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
                    ∀ v : ℂ, (L ω).1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
                  (∀ u v : ℂ, (L ω).1 (u, v) < ∞ →
                    ∃ (γ : ℝ → ℂ) (a b : ℝ),
                      (L ω).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
                        (L ω).len γ a b = (L ω).1 (u, v)))

 



def PfeThm17 : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ),
    ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ ε : ℕ → Set.Ioi (0 : ℝ),
        Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ D : DistC → LSCMetric,
            ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
              IsPfeWeakMetric ξ D c ∧ SubseqLimit ξ m (ε ∘ φ) D ∧
                (∀ r : ℚ, ∀ hr : 0 < r,
                  Tendsto (fun n => (r : ℝ) *
                    (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
                      Set.mem_Ioi.mpr (div_pos (ε (φ n)).property
                        (Rat.cast_pos.mpr hr))⟩ : ℝ) /
                    (m (ε (φ n)) : ℝ)) atTop
                    (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)))

 

def PLThm19 : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
    ∀ D : DistC → LSCMetric,
      ∀ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
        IsPfeWeakMetric ξ D c →
        (∃ C : ℝ, 0 < C ∧ ∀ r : Set.Ioi (0 : ℝ),
          C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q) ≤ c r ∧
          (c r : ℝ) ≤ C * (r : ℝ) ^ ((ξ : ℝ) * Q)) ∧
        IsWeakLQGMetric ξ Q D

 


def MedianPassage : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ),
    ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ ε ε' : ℕ → Set.Ioi (0 : ℝ),
        Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) → Tendsto (fun n => (ε' n : ℝ)) atTop (𝓝 0) →
        ∀ D D' : DistC → LSCMetric,
          SubseqLimit ξ m ε D → SubseqLimit ξ m ε' D' →
          ∀ c c' : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
            IsPfeWeakMetric ξ D c → IsPfeWeakMetric ξ D' c' →
          ∀ C : ℝ, 0 < C →
            (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (h : Ω → DistC), IsGFFPlusCont h P →
              ∀ᵐ ω ∂P, ∀ u v : ℂ,
                (D' (h ω)).1 (u, v) = ENNReal.ofReal C * (D (h ω)).1 (u, v)) →
            C = 1

 
def WeakToStrong : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, ∀ D : DistC → LSCMetric,
    IsLFPPExponent ξ Q → IsWeakLQGMetric ξ Q D → IsStrongLQGMetric ξ Q D

 
 







def DG20ExponentRelation : Prop :=
  ∀ ξ : Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
    ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n →
          C⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (k : ℝ)) *
              lambdaN (ξ : ℝ) W P (n - k) ≤ lambdaN (ξ : ℝ) W P n ∧
          lambdaN (ξ : ℝ) W P n ≤
            C * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (k : ℝ)) *
              lambdaN (ξ : ℝ) W P (n - k)

 



def DG20ExponentPositive : Prop :=
  ∀ ξ : Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q → 0 < Q

end SupercriticalLQGUniqueness.B2.Iface
