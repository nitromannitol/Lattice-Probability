/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import Mathlib




 






set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent

 
def ann (w : ℂ) (a b : ℝ) : Set ℂ := {x | a < dist x w ∧ dist x w < b}

 
def cann (w : ℂ) (a b : ℝ) : Set ℂ := {x | a ≤ dist x w ∧ dist x w ≤ b}
def around (D : LSCMetric) (w : ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ⨅ (P : ℝ → ℂ), ⨅ (t : ℝ), ⨅ (u : ℝ), ⨅ (_ : D.IsCurve P t u),
    ⨅ (_ : P '' Icc t u ⊆ ann w a b),
    ⨅ (_ : LQGMetric.Disconnects (P '' Icc t u) (sphere w a) (sphere w b)),
    D.len P t u

 
def acr (D : LSCMetric) (w : ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ⨅ (P : ℝ → ℂ), ⨅ (t : ℝ), ⨅ (u : ℝ), ⨅ (_ : D.IsCurve P t u),
    ⨅ (_ : P '' Icc t u ⊆ cann w a b),
    ⨅ (_ : P t ∈ sphere w a), ⨅ (_ : P u ∈ sphere w b), D.len P t u

 
structure TubeData where
  r : ℝ
  rho : ℝ
  alpha : ℝ
  K : ℕ
  Kpos : 0 < K
  orientation : ℂ
  psiU : ℝ
  psiV : ℝ
  blockRadius : ℝ
  lambda : ℝ
  A_endpt : ℝ
  mollifier : LQGMetric.TestC
  bump : LQGMetric.TestC
  netRadius : ℝ
  netSites : Finset ℂ

 
structure Constants where
  ξ : ℝ
  Q : ℝ
  r : ℝ
  lamConst : ℝ
  ρ : ℝ
  A_loc : ℝ
  K_ann : ℝ
  A_across : ℝ
  A_around : ℝ
  c_reg : ℝ
  k0 : ℕ
  A_sp : ℝ
  A_nar : ℝ
  A_set : ℝ
  A_internal : ℝ
  A_max : ℝ
  A_sup : ℝ
  A_endpt : ℝ
  A_RN : ℝ
  rPos : 0 < r
  ξPos : 0 < ξ
  QPos : 0 < Q
  lamPos : 0 < lamConst
  rhoPos : 0 < ρ
  supPos : 0 < A_sup
  regPos : 0 < c_reg
  regLtOne : c_reg < 1
  k0Large : 48 ≤ k0
  acrossPos : 0 < A_across
  aroundGtOne : 1 < A_around
  spPos : 0 < A_sp
  spLtEp : A_sp < (2:ℝ) ^ (-(k0:ℝ))
  rhoLt : ρ < lamConst*A_sp
  narPos : 0 < A_nar
  narLe : A_nar ≤ lamConst*(1-K_ann)*A_endpt*ρ
  narLeQ : A_nar ≤ 20/21
   

  narrowQScale : (2 : ℝ) ^ ((8*Q+12)/3) ≤ lamConst/A_nar
  setPos : 0 < A_set
  setLtNar : A_set < A_nar
  internalPos : 0 < A_internal
  maxPos : 0 < A_max
  endptPos : 0 < A_endpt
  supLtSet : A_sup < A_set
  supLe : A_sup ≤ 1/64
  rnPos : 0 < A_RN

 

def normalizer (C : Constants) (g : LQGMetric.DistC) (s : ℝ) (w : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (s ^ (C.ξ * C.Q) * Real.exp (C.ξ * LQGMetric.circleAvg g s w))

 
def lam (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℝ))

 
def regK (k : ℕ) : ℕ := k / 12 - 1

 
def grid (a : ℝ) : Set ℂ :=
  {z | ∃ m n : ℤ, z = ((a * m : ℝ) : ℂ) + ((a * n : ℝ) : ℂ) * Complex.I}

 
def regSites (C : Constants) (k : ℕ) : Set ℂ :=
  {z | z ∈ grid (lam k * C.r / 4) ∧
    ball z (2 * 4 ^ (regK k) * lam k * C.r) ⊆ ann 0 C.r (4 * C.r)}

 
def regGood (C : Constants) (D : LSCMetric) (s : ℝ) (w : ℂ) : Prop :=
  0 < around D w s (2*s) ∧ around D w s (2*s) < ⊤ ∧
  0 < acr D w s (2*s) ∧ acr D w s (2*s) < ⊤ ∧
  around D w s (2*s) ≤ ENNReal.ofReal C.c_reg⁻¹ * acr D w s (2*s)

 
def S1 (C : Constants) (D : LSCMetric) (g : LQGMetric.DistC) : Prop :=
  ENNReal.ofReal C.A_across * normalizer C g C.r 0 ≤ acr D 0 C.r (1.5*C.r) ∧
  ENNReal.ofReal C.A_across * normalizer C g C.r 0 ≤ acr D 0 (2.5*C.r) (3*C.r)

 
def S3 (C : Constants) (D : LSCMetric) : Prop :=
  by
    classical
    exact ∀ k : ℕ, C.k0 ≤ k → ∀ z ∈ regSites C k,
      2 * ((Finset.Icc 1 (regK k)).filter
        (fun j => regGood C D (4 ^ j * lam k * C.r) z)).card ≥ regK k

 
def compareScale (k : ℕ) : ℝ := ((21 : ℝ) / 20) ^ (-(k : ℝ))

 
def compareSites (C : Constants) (k : ℕ) : Set ℂ :=
  let t := compareScale k
  {z | z ∈ grid (t*C.r/100) ∧
    Metric.infDist z (cann 0 (1.5*C.r) (3*C.r)) ≤ t*C.r/100}

 
def S5 (C : Constants) (D : LSCMetric) : Prop :=
  ∀ k : ℕ, compareScale k ≤ C.A_nar → ∀ z ∈ compareSites C k,
    let t := compareScale k
    let outer := around D z ((11/5)*t*C.r) ((14/5)*t*C.r)
    let inner := acr D z ((3/10)*t*C.r) ((9/20)*t*C.r)
    outer ≤ ENNReal.ofReal (t ^ (-(1:ℝ)/8)) * inner ∧ outer < ⊤ ∧
      0 < inner ∧ inner < ⊤

 
def zeta (C : Constants) : ℝ := C.ξ / (4*(1+C.ξ))

 
def narrowStart (C : Constants) : ℕ := Nat.floor (Real.logb 2 (C.lamConst/C.A_nar)) + 1

 
def narrowScale (C : Constants) (n : ℕ) : ℝ := (2:ℝ) ^ (-(n:ℝ)-1) * C.r

 
def narrowSites (C : Constants) (n : ℕ) : Set ℂ :=
  let a := (2:ℝ) ^ (-(n:ℝ)-4) * C.r
  {z | z ∈ grid a ∧ Metric.infDist z (cann 0 (1.5*C.r) (3*C.r)) ≤ a}

 
def S6 (C : Constants) (D : LSCMetric) (g : LQGMetric.DistC) : Prop :=
  ∀ n : ℕ, narrowStart C ≤ n → ∀ v ∈ narrowSites C n,
    ENNReal.ofReal ((2:ℝ) ^ (-(zeta C)*(n:ℝ))) *
        normalizer C g (narrowScale C n) v ≤
      acr D v (narrowScale C n / 4) (narrowScale C n) ∧
    |LQGMetric.circleAvg g (narrowScale C n) v - LQGMetric.circleAvg g C.r 0| ≤
      (2+zeta C)*(n:ℝ)*Real.log 2

 
end SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent
