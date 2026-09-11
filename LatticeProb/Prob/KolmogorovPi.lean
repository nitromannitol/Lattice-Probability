/-
Quantitative probability bounds for continuous processes on finite-dimensional boxes.
-/
import LatticeProb.Prob.ChentsovPiProcess
import LatticeProb.Prob.ChentsovPiLimit

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

def LatticeProb.boxClamp {k : ℕ} (a b : Fin k → ℝ) (hab : a ≤ b)
    (x : Fin k → ℝ) : Fin k → ℝ := fun i => Set.projIcc (a i) (b i) (hab i) (x i)

theorem LatticeProb.boxClamp_mem {k : ℕ} (a b : Fin k → ℝ) (hab : a ≤ b)
    (x : Fin k → ℝ) : boxClamp a b hab x ∈ Set.Icc a b := by
  unfold boxClamp
  rw [Set.mem_Icc]
  constructor
  · simp only [Pi.le_def]
    intro i
    exact (Set.projIcc (a i) (b i) (hab i) (x i)).property.1
  · simp only [Pi.le_def]
    intro i
    exact (Set.projIcc (a i) (b i) (hab i) (x i)).property.2
