/-
The localized odometer on the lattice: the one-step recursion for the value of
the optimal-stopping problem in which the scenery is summed only while the walk
has stayed inside a set `D`.

`zdKilledOdometer` is the localized odometer written in the scenery,
`w_{n+1}(x) = 1_D(x)(ζ(x) + P w_n(x))⁺`, and `zdKilledStopValues` is the set of
expected killed payoffs over stopping times bounded by `n`, in the integral
vocabulary of the dependent formalizations.  The two are related by
`LatticeProb.Graph.killedOdometer_isLUB` read on the lattice, through the
identification of the finite-horizon walk average with the integral.
-/
import LatticeProb.Graph.Killed
import LatticeProb.Graph.ZdRepresentation

open MeasureTheory LatticeProb

namespace LatticeProb.Graph.Zd

open scoped Classical

variable {d : ℕ}

/-- `S_n^D = ∑_{k<n} 1{X_0,…,X_k ∈ D} ζ(X_k)`, the scenery summed along the
trajectory only while it has stayed in `D`. -/
noncomputable def zdKilledPayoff (D : Set (Site d)) (ζ : Site d → ℝ) (n : ℕ)
    (X : ℕ → Site d) : ℝ :=
  ∑ k ∈ Finset.range n, Set.indicator {k : ℕ | ∀ i ≤ k, X i ∈ D} (fun k => ζ (X k)) k

/-- The localized odometer written in the scenery: `w_0 = 0` and
`w_{n+1}(x) = 1_D(x)(ζ(x) + P w_n(x))⁺`. -/
noncomputable def zdKilledOdometer (D : Set (Site d)) (ζ : Site d → ℝ) :
    ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x =>
      if x ∈ D then max 0 (ζ x + LatticeProb.walkOp (zdKilledOdometer D ζ n) x) else 0

/-- The set of expected killed payoffs over stopping times bounded by `n`. -/
noncomputable def zdKilledStopValues (D : Set (Site d)) (ζ : Site d → ℝ) (n : ℕ)
    (x : Site d) : Set ℝ :=
  {a | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
    a = ∫ X, zdKilledPayoff D ζ (τ X) X ∂(siteWalkLaw d x)}

theorem degree_pos_lattice (hd : 1 ≤ d) (v : Site d) : 0 < (lattice d).degree v := by
  rw [degree_eq]; omega

theorem killedPayoff_eq [NeZero d] (D : Set (Site d)) (ζ : Site d → ℝ) (n : ℕ)
    (X : ℕ → Site d) :
    LatticeProb.Graph.killedPayoff (lattice d)
        (LatticeProb.Graph.excess (config ζ)) D n X
      = zdKilledPayoff D ζ n X := by
  have hd : ((2 * d : ℕ) : ℝ) ≠ 0 := by
    have : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  rw [LatticeProb.Graph.killedPayoff, zdKilledPayoff]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : ∀ i ≤ k, X i ∈ D
  · rw [if_pos hk, Set.indicator_of_mem (show k ∈ {k : ℕ | ∀ i ≤ k, X i ∈ D} from hk)]
    rw [excess_config, degree_eq]
    field_simp
    push_cast
    ring
  · rw [if_neg hk, Set.indicator_of_notMem (show k ∉ {k : ℕ | ∀ i ≤ k, X i ∈ D} from hk)]

theorem killedPayoff_dependsUpTo [NeZero d] (D : Set (Site d)) (ζ : Site d → ℝ) (n : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : LatticeProb.Graph.IsStopping τ) (hle : ∀ X, τ X ≤ n) :
    ∀ X Y : ℕ → Site d, (∀ j ≤ n, X j = Y j) →
      LatticeProb.Graph.killedPayoff (lattice d)
          (LatticeProb.Graph.excess (config ζ)) D (τ X) X
        = LatticeProb.Graph.killedPayoff (lattice d)
          (LatticeProb.Graph.excess (config ζ)) D (τ Y) Y := by
  intro X Y hXY
  have hτXY : τ X = τ Y := (hτ (τ X) X Y (fun j hj => hXY j (le_trans hj (hle X))) rfl).symm
  rw [hτXY, LatticeProb.Graph.killedPayoff, LatticeProb.Graph.killedPayoff]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k < τ Y := Finset.mem_range.mp hk
  have hkle : ∀ i ≤ k, X i = Y i := fun i hi =>
    hXY i (le_trans (le_trans hi (le_of_lt hkn)) (hle Y))
  have hset : (∀ i ≤ k, X i ∈ D) ↔ (∀ i ≤ k, Y i ∈ D) := by
    constructor
    · intro h i hi; rw [← hkle i hi]; exact h i hi
    · intro h i hi; rw [hkle i hi]; exact h i hi
  by_cases h : ∀ i ≤ k, X i ∈ D
  · rw [if_pos h, if_pos (hset.mp h), hkle k le_rfl]
  · rw [if_neg h, if_neg (fun hc => h (hset.mpr hc))]

theorem walkExp_killedPayoff_eq_integral [NeZero d]
    (hW : LatticeProb.Graph.WalkAverageIsIntegral) (D : Set (Site d)) (ζ : Site d → ℝ)
    (n : ℕ) (x : Site d) {τ : (ℕ → Site d) → ℕ}
    (hτ : LatticeProb.Graph.IsStopping τ) (hle : ∀ X, τ X ≤ n) :
    LatticeProb.Graph.walkExp (lattice d) n x
        (fun X => LatticeProb.Graph.killedPayoff (lattice d)
          (LatticeProb.Graph.excess (config ζ)) D (τ X) X)
      = ∫ X, zdKilledPayoff D ζ (τ X) X ∂(siteWalkLaw d x) := by
  have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (NeZero.ne d)
  rw [hW d hd1 n x _ (killedPayoff_dependsUpTo D ζ n hτ hle)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun X => killedPayoff_eq D ζ (τ X) X)

theorem killedStopValues_eq [NeZero d] (hW : LatticeProb.Graph.WalkAverageIsIntegral)
    (D : Set (Site d)) (ζ : Site d → ℝ) (n : ℕ) (x : Site d) :
    LatticeProb.Graph.killedStopValues (lattice d)
        (LatticeProb.Graph.excess (config ζ)) D n x
      = zdKilledStopValues D ζ n x := by
  ext a
  constructor
  · rintro ⟨τ, hτ, hle, rfl⟩
    exact ⟨τ, hτ, hle, walkExp_killedPayoff_eq_integral hW D ζ n x hτ hle⟩
  · rintro ⟨τ, hτ, hle, rfl⟩
    exact ⟨τ, hτ, hle, (walkExp_killedPayoff_eq_integral hW D ζ n x hτ hle).symm⟩

theorem zdKilledOdometer_eq [NeZero d] (D : Set (Site d)) (ζ : Site d → ℝ) :
    ∀ (n : ℕ) (x : Site d),
      LatticeProb.Graph.killedOdometer (lattice d)
          (LatticeProb.Graph.excess (config ζ)) D n x
        = zdKilledOdometer D ζ n x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      have hfun : LatticeProb.Graph.killedOdometer (lattice d)
          (LatticeProb.Graph.excess (config ζ)) D n = zdKilledOdometer D ζ n := funext ih
      by_cases hx : x ∈ D
      · rw [LatticeProb.Graph.killedOdometer_succ_of_mem _ hx, hfun, walkOp_eq]
        show _ = (if x ∈ D then
          max 0 (ζ x + LatticeProb.walkOp (zdKilledOdometer D ζ n) x) else 0)
        rw [if_pos hx]
        congr 2
        rw [show LatticeProb.Graph.excess (config ζ) x / ((lattice d).degree x : ℝ)
            = LatticeProb.Graph.scenery (lattice d) (config ζ) x from rfl,
          scenery_config]
      · rw [LatticeProb.Graph.killedOdometer_of_notMem _ hx]
        show (0 : ℝ) = (if x ∈ D then
          max 0 (ζ x + LatticeProb.walkOp (zdKilledOdometer D ζ n) x) else 0)
        rw [if_neg hx]

/-- **The optimal-stopping representation of the localized odometer on the
lattice.** -/
theorem localizedStopping (hW : LatticeProb.Graph.WalkAverageIsIntegral)
    (d : ℕ) (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ) (n : ℕ) (x : Site d) :
    IsLUB (zdKilledStopValues D ζ n x) (zdKilledOdometer D ζ n x) := by
  haveI : NeZero d := ⟨by omega⟩
  rw [← killedStopValues_eq hW, ← zdKilledOdometer_eq]
  exact LatticeProb.Graph.isLUB_killedOdometer (degree_pos_lattice hd)
    (LatticeProb.Graph.excess (config ζ)) D n x

/-- The localized value is the supremum of the killed stopping values. -/
theorem localizedStopping' (d : ℕ) (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ)
    (n : ℕ) (x : Site d) :
    IsLUB (zdKilledStopValues D ζ n x) (zdKilledOdometer D ζ n x) :=
  localizedStopping LatticeProb.Graph.walkAverageIsIntegral d hd D ζ n x

/-- The supremum form: `sup_{τ ≤ n} E_x[S^D_τ]` is the localized odometer. -/
theorem sSup_zdKilledStopValues (d : ℕ) (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ)
    (n : ℕ) (x : Site d) :
    sSup (zdKilledStopValues D ζ n x) = zdKilledOdometer D ζ n x := by
  haveI : NeZero d := ⟨by omega⟩
  refine (localizedStopping' d hd D ζ n x).csSup_eq ⟨0, ?_⟩
  rw [← killedStopValues_eq LatticeProb.Graph.walkAverageIsIntegral]
  exact LatticeProb.Graph.zero_mem_killedStopValues _ D n x

/-- **The one-step recursion for the localized odometer.** -/
theorem zdKilledOdometer_succ_of_mem (D : Set (Site d)) (ζ : Site d → ℝ)
    {x : Site d} (hx : x ∈ D) (n : ℕ) :
    zdKilledOdometer D ζ (n + 1) x
      = max 0 (ζ x + LatticeProb.walkOp (zdKilledOdometer D ζ n) x) := by
  show (if x ∈ D then
    max 0 (ζ x + LatticeProb.walkOp (zdKilledOdometer D ζ n) x) else 0) = _
  rw [if_pos hx]

theorem zdKilledOdometer_of_notMem (D : Set (Site d)) (ζ : Site d → ℝ)
    {x : Site d} (hx : x ∉ D) (n : ℕ) : zdKilledOdometer D ζ n x = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
      show (if x ∈ D then
        max 0 (ζ x + LatticeProb.walkOp (zdKilledOdometer D ζ n) x) else 0) = 0
      rw [if_neg hx]

end LatticeProb.Graph.Zd
