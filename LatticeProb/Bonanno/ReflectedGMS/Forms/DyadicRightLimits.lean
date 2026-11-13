/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.DyadicRightLimits at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicPotentialCrossings
import LatticeProb.Bonanno.ReflectedGMS.Forms.UpcrossingSampling
import LatticeProb.Bonanno.ReflectedGMS.Forms.OneSidedAlternation
import Mathlib.Topology.Order.LiminfLimsup

-- Merged from `ReflectedGMS/Forms/UpcrossingWitnesses.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_UpcrossingWitnesses

/-! Finite alternating samples force the corresponding number of existing
mathlib upcrossings. Only the sampled finite prefix must be increasing. -/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS

variable {Ω : Type*} {a b : ℝ} {f : ℕ → Ω → ℝ}

theorem alternatingSamples_le_upcrossingsBefore (hab : a < b)
    (p : ℕ → ℕ) (ω : Ω) (n : ℕ)
    (hp : StrictMonoOn p (Iic (2 * n)))
    (hlow : ∀ i < n, f (p (2 * i)) ω < a)
    (hhigh : ∀ i < n, b < f (p (2 * i + 1)) ω) :
    n ≤ upcrossingsBefore a b f (p (2 * n)) ω := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hp' : StrictMonoOn p (Iic (2 * n)) := by
      apply hp.mono
      intro k hk
      change k ≤ 2 * (n + 1)
      change k ≤ 2 * n at hk
      omega
    have hi := ih hp' (fun i hi => hlow i (Nat.lt_succ_of_lt hi))
      (fun i hi => hhigh i (Nat.lt_succ_of_lt hi))
    have habidx : p (2 * n) ≤ p (2 * n + 1) :=
      (hp (by change 2 * n ≤ 2 * (n + 1); omega)
        (by change 2 * n + 1 ≤ 2 * (n + 1); omega) (by omega)).le
    have hnext := upcrossingsBefore_lt_of_exists_upcrossing hab
      (N := p (2 * n)) (N₁ := p (2 * n)) (N₂ := p (2 * n + 1))
      le_rfl (hlow n (Nat.lt_succ_self n)) habidx (hhigh n (Nat.lt_succ_self n))
    have hend : p (2 * n + 1) + 1 ≤ p (2 * (n + 1)) := by
      apply Nat.succ_le_of_lt
      exact hp (by change 2 * n + 1 ≤ 2 * (n + 1); omega)
        (by change 2 * (n + 1) ≤ 2 * (n + 1); rfl) (by omega)
    exact (Nat.succ_le_of_lt (hi.trans_lt hnext)).trans
      (upcrossingsBefore_mono hab hend ω)

end ReflectedGMS

end Merged_UpcrossingWitnesses

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS

/-- Dyadic times strictly before the horizon. -/
def dyadicSupport (T : ℝ≥0) : Set ℝ≥0 :=
  {s | ∃ n k : ℕ, k < 2 ^ n ∧ s = dyadicTime T n k}

theorem dyadicTime_refine_to (T : ℝ≥0) {n N k : ℕ} (hnN : n ≤ N) :
    dyadicTime T N (k * 2 ^ (N - n)) = dyadicTime T n k := by
  apply NNReal.eq
  simp only [dyadicTime, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hpow : (2 : ℝ) ^ N = 2 ^ (N - n) * 2 ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hnN]
  push_cast
  rw [hpow]
  field_simp

theorem dyadicTime_strictMono (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    StrictMono (dyadicTime T n) := by
  intro i j hij
  apply NNReal.coe_lt_coe.mp
  simp only [dyadicTime, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
  exact div_lt_div_of_pos_right
    (mul_lt_mul_of_pos_right (by exact_mod_cast hij) (NNReal.coe_pos.2 hT)) (by positivity)

/-- A finite ordered family of dyadic times, followed by the horizon, lies on
one common finer dyadic grid. -/
theorem exists_common_dyadic_grid (T : ℝ≥0) (hT : 0 < T)
    (p : ℕ → ℝ≥0) (m : ℕ) (hp : StrictMonoOn p (Iic (2 * m)))
    (hpT : p (2 * m) = T)
    (hmem : ∀ i < 2 * m, p i ∈ dyadicSupport T) :
    ∃ (N : ℕ) (q : ℕ → ℕ), q (2 * m) = 2 ^ N ∧
      StrictMonoOn q (Iic (2 * m)) ∧
      ∀ i ≤ 2 * m, p i = dyadicTime T N (q i) := by
  classical
  let rep : ∀ j : Fin (2 * m + 1), ∃ n k : ℕ,
      k ≤ 2 ^ n ∧ p j = dyadicTime T n k := fun j ↦ by
    by_cases hj : (j : ℕ) = 2 * m
    · exact ⟨0, 1, by simp, by simpa [hj, hpT, dyadicTime]⟩
    · obtain ⟨n, k, hk, heq⟩ := hmem j (by omega)
      exact ⟨n, k, hk.le, heq⟩
  choose level index hindex htime using rep
  let N := Finset.sup Finset.univ level
  let q : ℕ → ℕ := fun i ↦ if hi : i ≤ 2 * m then
    index ⟨i, by omega⟩ * 2 ^ (N - level ⟨i, by omega⟩) else 0
  have hlevel (i : Fin (2 * m + 1)) : level i ≤ N :=
    Finset.le_sup (f := level) (Finset.mem_univ i)
  have htime' (i : ℕ) (hi : i ≤ 2 * m) :
      p i = dyadicTime T N (q i) := by
    simp only [q, dif_pos hi]
    rw [dyadicTime_refine_to T (hlevel ⟨i, by omega⟩)]
    exact htime ⟨i, by omega⟩
  have hq : StrictMonoOn q (Iic (2 * m)) := by
    intro i hi j hj hij
    exact (dyadicTime_strictMono T hT N).lt_iff_lt.mp (by
      rw [← htime' i hi, ← htime' j hj]
      exact hp hi hj hij)
  have hqend : q (2 * m) = 2 ^ N := by
    apply (dyadicTime_strictMono T hT N).injective
    rw [← htime' (2 * m) le_rfl, hpT]
    simp [dyadicTime]
  exact ⟨N, q, hqend, hq, htime'⟩

/-- Uniformly finite upcrossing counts on all dyadic grids force a right
limit along the dyadic support at every time strictly before the horizon. -/
theorem exists_dyadic_right_limit_of_finite_upcrossings
    {Ω : Type*} (T : ℝ≥0) (hT : 0 < T) (f : ℝ≥0 → ℝ)
    (F : ℕ → ℕ → Ω → ℝ) (ω : Ω)
    (hF : ∀ n k, F n k ω = f (dyadicTime T n k))
    (hf : ∃ C : ℝ, ∀ s, |f s| ≤ C)
    (hcross : ∀ (a b : ℚ), a < b →
      (⨆ n, (upcrossingsBefore (a : ℝ) (b : ℝ)
        (F n) (2 ^ n) ω : ℝ≥0∞)) < ∞) :
    ∀ t < T, ∃ c : ℝ,
      Tendsto f (nhdsWithin t (dyadicSupport T ∩ Ioi t)) (𝓝 c) := by
  intro t htT
  rcases hf with ⟨C, hC⟩
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_
    (h := isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall fun s ↦ (le_abs_self (f s)).trans (hC s)))
    (h' := isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun s ↦ neg_le_of_abs_le (hC s)))
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab ⟨hlow, hhigh⟩
    have habq : a < b := Rat.cast_lt.mp hab
    let L : ℝ≥0∞ := ⨆ n, (upcrossingsBefore (a : ℝ) (b : ℝ)
      (F n) (2 ^ n) ω : ℝ≥0∞)
    have hL : L < ∞ := hcross a b habq
    obtain ⟨m, hLm⟩ := ENNReal.exists_nat_gt (ne_of_lt hL)
    have hm : 0 < m := by
      by_contra hm
      have : m = 0 := Nat.eq_zero_of_not_pos hm
      subst m
      have hbad := (show (0 : ℝ≥0∞) ≤ L from bot_le).trans_lt hLm
      simpa using hbad
    have hlowNear : ∀ r, t < r →
        ∃ x ∈ dyadicSupport T, t < x ∧ x < r ∧ f x < (a : ℝ) := by
      intro r htr
      rw [frequently_nhdsWithin_iff] at hlow
      obtain ⟨x, hxr, hfx, hxS, htx⟩ :=
        (frequently_iff.mp hlow) (Iio_mem_nhds htr)
      exact ⟨x, hxS, htx, hxr, hfx⟩
    have hhighNear : ∀ r, t < r →
        ∃ x ∈ dyadicSupport T, t < x ∧ x < r ∧ (b : ℝ) < f x := by
      intro r htr
      rw [frequently_nhdsWithin_iff] at hhigh
      obtain ⟨x, hxr, hfx, hxS, htx⟩ :=
        (frequently_iff.mp hhigh) (Iio_mem_nhds htr)
      exact ⟨x, hxS, htx, hxr, hfx⟩
    obtain ⟨p, hpT, hp, hpS, hpa, hpb⟩ :=
      exists_alternatingSamples_right htT hlowNear hhighNear m
    obtain ⟨N, q, hqT, hq, hgrid⟩ :=
      exists_common_dyadic_grid T hT p m hp hpT (fun i hi ↦ (hpS i hi).1)
    have hw := alternatingSamples_le_upcrossingsBefore
      (f := F N) hab q ω m hq
      (fun i hi ↦ by
        rw [hF, ← hgrid (2 * i) (by omega)]
        exact hpa i hi)
      (fun i hi ↦ by
        rw [hF, ← hgrid (2 * i + 1) (by omega)]
        exact hpb i hi)
    rw [hqT] at hw
    have hw' : (m : ℝ≥0∞) ≤ (upcrossingsBefore (a : ℝ) (b : ℝ)
        (F N) (2 ^ N) ω : ℝ≥0∞) := by
      exact_mod_cast hw
    have hcountL : (upcrossingsBefore (a : ℝ) (b : ℝ)
        (F N) (2 ^ N) ω : ℝ≥0∞) ≤ L := by
      exact le_iSup (fun n ↦ (upcrossingsBefore (a : ℝ) (b : ℝ)
        (F n) (2 ^ n) ω : ℝ≥0∞)) N
    exact (not_lt_of_ge (hw'.trans hcountL)) hLm

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-- The negative discounted vertex potential whose dyadic upcrossings are
controlled by `dyadicPotentialUpcrossings_ae_all_rat_nat`. -/
noncomputable def negativeDiscountedVertexPotential [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (PF : ReflectedWalk.ProcessFamily V) (alpha : ℝ) (y : V)
    (ω : PF.Ω) (s : ℝ≥0) : ℝ :=
  -(Real.exp (-alpha * (s : ℝ)) *
    (PF.X s ω).elim 0 (FullNetworkForm.vertexOccupationPotential G m alpha · y))

/-- On one full-probability event, the actual negative discounted vertex
potential has a dyadic right limit at every point before every positive
natural-number horizon. -/
theorem negativeDiscountedVertexPotential_ae_dyadic_right_limits [DecidableEq V]
    {G : ReflectedWalk.ConductanceGraph V} {m : V → ℝ}
    {hmin : G.EnergyMinimizer} {PF : ReflectedWalk.ProcessFamily V}
    (h : ReflectedWalk.IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {alpha : ℝ} (ha : 0 < alpha) (y z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ (T : ℕ), 0 < T → ∀ t < (T : ℝ≥0),
      ∃ c : ℝ, Tendsto (negativeDiscountedVertexPotential G m PF alpha y ω)
        (nhdsWithin t (dyadicSupport (T : ℝ≥0) ∩ Ioi t)) (𝓝 c) := by
  filter_upwards [dyadicPotentialUpcrossings_ae_all_rat_nat
    h hG hm hmsum ha y z] with ω hω
  intro T hT
  apply exists_dyadic_right_limit_of_finite_upcrossings (T : ℝ≥0)
    (by exact_mod_cast hT) (negativeDiscountedVertexPotential G m PF alpha y ω)
    (fun n k ω ↦ negativeDiscountedVertexPotential G m PF alpha y ω
      (dyadicTime (T : ℝ≥0) n k)) ω (by intros; rfl)
  · refine ⟨1 / alpha, fun s ↦ ?_⟩
    cases hx : PF.X s ω with
    | none => simp [negativeDiscountedVertexPotential, hx, le_of_lt ha]
    | some x =>
        rw [negativeDiscountedVertexPotential, hx, Option.elim_some, abs_neg,
          abs_of_nonneg]
        · calc
            Real.exp (-alpha * (s : ℝ)) *
                FullNetworkForm.vertexOccupationPotential G m alpha x y
              ≤ 1 * FullNetworkForm.vertexOccupationPotential G m alpha x y := by
                apply mul_le_mul_of_nonneg_right
                · exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
                    (neg_nonpos.mpr ha.le) s.2)
                · exact FullNetworkForm.vertexOccupationPotential_nonneg
                    G m hm ha x y
            _ ≤ 1 / alpha := by
              simpa using FullNetworkForm.vertexOccupationPotential_le_inv
                G m hm ha x y
        · exact mul_nonneg (Real.exp_nonneg _)
            (FullNetworkForm.vertexOccupationPotential_nonneg G m hm ha x y)
  · intro a b hab
    simpa only [dyadicPotentialUpcrossings, negativeDiscountedVertexPotential] using hω a b T hab

end ReflectedGMS
