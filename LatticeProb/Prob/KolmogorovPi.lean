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

theorem LatticeProb.boxClamp_eq {k : ℕ} {a b x : Fin k → ℝ} (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b) : boxClamp a b hab x = x := by
  funext i
  exact congrArg Subtype.val (Set.projIcc_of_mem (hab i) ⟨hx.1 i, hx.2 i⟩)

theorem LatticeProb.dist_boxClamp_le {k : ℕ} (a b : Fin k → ℝ) (hab : a ≤ b)
    (x y : Fin k → ℝ) : dist (boxClamp a b hab x) (boxClamp a b hab y) ≤ dist x y := by
  refine (dist_pi_le_iff dist_nonneg).mpr ?_
  intro i
  change |(Set.projIcc (a i) (b i) (hab i) (x i) : ℝ) - Set.projIcc (a i) (b i) (hab i) (y i)| ≤ dist x y
  exact (Set.abs_projIcc_sub_projIcc (hab i)).trans (dist_le_pi_dist x y i)
