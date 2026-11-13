/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.HarmonicLawIngredients at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.Potentials
import LatticeProb.Bonanno.ReflectedGMS.Environment.RootDensities
import LatticeProb.Bonanno.ReflectedGMS.Environment.Laws

/-! Random-environment clauses used by the harmonic-coordinate statement.
No existence or convergence theorem is asserted here. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace ReflectedGMS.HarmonicLawIngredients
open Code StatementIngredients EnvironmentFields EnvironmentLaws RootDensities

/-- Exact FE assumption, with all boundary roots masked. -/
def FiniteEnergyMoment (ν : Measure Env) : Prop :=
  (∫⁻ e, rootedFiniteEnergyDensity (decode e) 0 ∂ν) < ∞

/-- The potential is zero at the original root wherever it is unmasked. -/
def RootNormalized (Φ : CellField) (e : Env) : Prop :=
  ∀ v, rootAt (decode e) 0 = some v → Φ.at e v = 0

/-- Finite expected specific gradient energy, including the factor one half. -/
def FiniteSpecificEnergy (ν : Measure Env) (Φ : CellField) : Prop :=
  (∫⁻ e, rootedSpecificEnergyDensity (decode e) (Φ.at e) 0 ∂ν) < ∞

/-- Gradient covariance is independent of the choice of normalized root. -/
def GradientCovariant (Φ : CellField) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env)
    (relabel : Vertex e.val ≃ Vertex e'.val),
    IsSimilarityRelabel s u hs e e' relabel → ∀ v w,
      Φ.gradient e' (relabel v) (relabel w) = s • Φ.gradient e v w

/-- Exact normalized covariance wherever the translated root is unmasked. -/
def NormalizedCovariant (Φ : CellField) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env)
    (relabel : Vertex e.val ≃ Vertex e'.val),
    IsSimilarityRelabel s u hs e e' relabel → ∀ r,
      rootAt (decode e) u = some r → ∀ v,
        Φ.at e' (relabel v) = s • (Φ.at e v - Φ.at e r)

/-- The bracket's deterministic mean. Finiteness/integrability is a separate
conclusion to preclude the Bochner integral's default zero on bad integrands. -/
noncomputable def meanCovariance (ν : Measure Env) (Φ : CellField) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => ∫ e, rootedGamma (decode e) (Φ.at e) 0 i j ∂ν

def IntegrableBracket (ν : Measure Env) (Φ : CellField) : Prop :=
  ∀ i j, Integrable (fun e => rootedGamma (decode e) (Φ.at e) 0 i j) ν

end ReflectedGMS.HarmonicLawIngredients
