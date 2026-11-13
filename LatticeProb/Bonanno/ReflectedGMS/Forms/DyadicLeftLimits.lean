/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.DyadicLeftLimits at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicRightLimits
import LatticeProb.Bonanno.ReflectedGMS.Forms.OneSidedAlternation

-- Merged from `ReflectedGMS/Forms/LeftAlternation.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_LeftAlternation

/-! The left-sided oscillation witness is obtained from the checked right-sided
construction by reversing the domain order, negating values, and reversing the
finite sample. -/

set_option autoImplicit false

open Set

namespace ReflectedGMS

variable {α : Type*} [LinearOrder α] {S : Set α} {f : α → ℝ}
  {L t : α} {a b : ℝ}

theorem exists_alternatingSamples_left
    (hL : L < t)
    (hlow : ∀ r, r < t → ∃ x ∈ S, r < x ∧ x < t ∧ f x < a)
    (hhigh : ∀ r, r < t → ∃ x ∈ S, r < x ∧ x < t ∧ b < f x)
    (n : ℕ) :
    ∃ q : ℕ → α, q (2 * n) = t ∧ StrictMonoOn q (Iic (2 * n)) ∧
      (∀ i < 2 * n, q i ∈ S ∧ L < q i ∧ q i < t) ∧
      (∀ i < n, f (q (2 * i)) < a) ∧
      (∀ i < n, b < f (q (2 * i + 1))) := by
  obtain ⟨p, hpL, hp, hmem, hpLo, hpHi⟩ :=
    exists_alternatingSamples_right (α := αᵒᵈ) (S := S)
      (f := fun x => -f x) (t := t) (R := L) (a := -b) (b := -a) hL
      (by
        intro r hr
        obtain ⟨x, hx, hrx, hxt, hfx⟩ := hhigh r hr
        exact ⟨x, hx, hxt, hrx, neg_lt_neg hfx⟩)
      (by
        intro r hr
        obtain ⟨x, hx, hrx, hxt, hfx⟩ := hlow r hr
        exact ⟨x, hx, hxt, hrx, neg_lt_neg hfx⟩) n
  let v : ℕ → α := p
  have hv : StrictAntiOn v (Iic (2 * n)) := hp
  have hvL : v (2 * n) = L := hpL
  have hvMem : ∀ i < 2 * n, v i ∈ S ∧ v i < t := hmem
  let q : ℕ → α := fun i => if i < 2 * n then v (2 * n - 1 - i) else t
  refine ⟨q, by simp [q], ?_, ?_, ?_, ?_⟩
  · apply strictMonoOn_Iic_of_lt_succ
    intro k hk
    have hk' : k < 2 * n := hk
    change q k < q (k + 1)
    by_cases hs : k + 1 < 2 * n
    · simp only [q, if_pos hk', if_pos hs]
      exact hv (by change 2 * n - 1 - (k + 1) ≤ 2 * n; omega)
        (by change 2 * n - 1 - k ≤ 2 * n; omega) (by omega)
    · simp only [q, if_pos hk', if_neg hs]
      exact (hvMem (2 * n - 1 - k) (by omega)).2
  · intro i hi
    simp only [q, if_pos hi]
    have hj : 2 * n - 1 - i < 2 * n := by omega
    refine ⟨(hvMem _ hj).1, ?_, (hvMem _ hj).2⟩
    rw [← hvL]
    exact hv (by exact hj.le) (by change 2 * n ≤ 2 * n; rfl) hj
  · intro i hi
    have he : 2 * i < 2 * n := by omega
    have hid : 2 * n - 1 - 2 * i = 2 * (n - 1 - i) + 1 := by omega
    simp only [q, if_pos he, hid]
    have hh := hpHi (n - 1 - i) (by omega)
    exact neg_lt_neg_iff.mp hh
  · intro i hi
    have he : 2 * i + 1 < 2 * n := by omega
    have hid : 2 * n - 1 - (2 * i + 1) = 2 * (n - 1 - i) := by omega
    simp only [q, if_pos he, hid]
    have hh := hpLo (n - 1 - i) (by omega)
    exact neg_lt_neg_iff.mp hh

end ReflectedGMS

end Merged_LeftAlternation

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS

/-- Uniformly finite upcrossing counts on all dyadic grids force a left
limit along the dyadic support at every positive time up to the horizon. -/
theorem exists_dyadic_left_limit_of_finite_upcrossings
    {Ω : Type*} (T : ℝ≥0) (hT : 0 < T) (f : ℝ≥0 → ℝ)
    (F : ℕ → ℕ → Ω → ℝ) (ω : Ω)
    (hF : ∀ n k, F n k ω = f (dyadicTime T n k))
    (hf : ∃ C : ℝ, ∀ s, |f s| ≤ C)
    (hcross : ∀ (a b : ℚ), a < b →
      (⨆ n, (upcrossingsBefore (a : ℝ) (b : ℝ)
        (F n) (2 ^ n) ω : ℝ≥0∞)) < ∞) :
    ∀ t, 0 < t → t ≤ T → ∃ c : ℝ,
      Tendsto f (nhdsWithin t (dyadicSupport T ∩ Iio t)) (𝓝 c) := by
  intro t h0t htT
  rcases hf with ⟨C, hC⟩
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_
    (h := isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall fun s ↦ (le_abs_self (f s)).trans (hC s)))
    (h' := isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun s ↦ neg_le_of_abs_le (hC s)))
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab ⟨hlow, hhigh⟩
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
  have hlowNear : ∀ r, r < t →
      ∃ x ∈ dyadicSupport T, r < x ∧ x < t ∧ f x < (a : ℝ) := by
    intro r hrt
    rw [frequently_nhdsWithin_iff] at hlow
    obtain ⟨x, hrx, hfx, hxS, hxt⟩ :=
      (frequently_iff.mp hlow) (Ioi_mem_nhds hrt)
    exact ⟨x, hxS, hrx, hxt, hfx⟩
  have hhighNear : ∀ r, r < t →
      ∃ x ∈ dyadicSupport T, r < x ∧ x < t ∧ (b : ℝ) < f x := by
    intro r hrt
    rw [frequently_nhdsWithin_iff] at hhigh
    obtain ⟨x, hrx, hfx, hxS, hxt⟩ :=
      (frequently_iff.mp hhigh) (Ioi_mem_nhds hrt)
    exact ⟨x, hxS, hrx, hxt, hfx⟩
  obtain ⟨q, hqt, hq, hqS, hqa, hqb⟩ :=
    exists_alternatingSamples_left h0t hlowNear hhighNear m
  let p : ℕ → ℝ≥0 := fun i ↦ if i < 2 * m then q i else T
  have hpT : p (2 * m) = T := by simp [p]
  have hp : StrictMonoOn p (Iic (2 * m)) := by
    apply strictMonoOn_Iic_of_lt_succ
    intro i hi
    have hi' : i < 2 * m := hi
    by_cases hs : i + 1 < 2 * m
    · change (if i < 2 * m then q i else T) <
          (if i + 1 < 2 * m then q (i + 1) else T)
      rw [if_pos hi', if_pos hs]
      exact hq hi'.le hs.le (Nat.lt_succ_self i)
    · change (if i < 2 * m then q i else T) <
          (if i + 1 < 2 * m then q (i + 1) else T)
      rw [if_pos hi', if_neg hs]
      exact (hqS i hi').2.2.trans_le htT
  have hpS : ∀ i < 2 * m, p i ∈ dyadicSupport T := by
    intro i hi
    simpa only [p, if_pos hi] using (hqS i hi).1
  obtain ⟨N, r, hrT, hr, hgrid⟩ :=
    exists_common_dyadic_grid T hT p m hp hpT hpS
  have hw := alternatingSamples_le_upcrossingsBefore
    (f := F N) hab r ω m hr
    (fun i hi ↦ by
      rw [hF, ← hgrid (2 * i) (by omega)]
      simpa only [p, if_pos (by omega : 2 * i < 2 * m)] using hqa i hi)
    (fun i hi ↦ by
      rw [hF, ← hgrid (2 * i + 1) (by omega)]
      simpa only [p, if_pos (by omega : 2 * i + 1 < 2 * m)] using hqb i hi)
  rw [hrT] at hw
  have hw' : (m : ℝ≥0∞) ≤ (upcrossingsBefore (a : ℝ) (b : ℝ)
      (F N) (2 ^ N) ω : ℝ≥0∞) := by exact_mod_cast hw
  have hcountL : (upcrossingsBefore (a : ℝ) (b : ℝ)
      (F N) (2 ^ N) ω : ℝ≥0∞) ≤ L := by
    exact le_iSup (fun n ↦ (upcrossingsBefore (a : ℝ) (b : ℝ)
      (F n) (2 ^ n) ω : ℝ≥0∞)) N
  exact (not_lt_of_ge (hw'.trans hcountL)) hLm

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-- The actual negative discounted potential has dyadic left limits on the
same full-probability event that controls all rational crossing levels and
natural-number horizons. -/
theorem negativeDiscountedVertexPotential_ae_dyadic_left_limits [DecidableEq V]
    {G : ReflectedWalk.ConductanceGraph V} {m : V → ℝ}
    {hmin : G.EnergyMinimizer} {PF : ReflectedWalk.ProcessFamily V}
    (h : ReflectedWalk.IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {alpha : ℝ} (ha : 0 < alpha) (y z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ (T : ℕ), 0 < T → ∀ (t : ℝ≥0), 0 < t → t ≤ (T : ℝ≥0) →
      ∃ c : ℝ, Tendsto (negativeDiscountedVertexPotential G m PF alpha y ω)
        (nhdsWithin t (dyadicSupport (T : ℝ≥0) ∩ Iio t)) (𝓝 c) := by
  filter_upwards [dyadicPotentialUpcrossings_ae_all_rat_nat
    h hG hm hmsum ha y z] with ω hω
  intro T hT
  apply exists_dyadic_left_limit_of_finite_upcrossings (T : ℝ≥0)
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
                · exact FullNetworkForm.vertexOccupationPotential_nonneg G m hm ha x y
            _ ≤ 1 / alpha := by
              simpa using FullNetworkForm.vertexOccupationPotential_le_inv G m hm ha x y
        · exact mul_nonneg (Real.exp_nonneg _)
            (FullNetworkForm.vertexOccupationPotential_nonneg G m hm ha x y)
  · intro a b hab
    simpa only [dyadicPotentialUpcrossings, negativeDiscountedVertexPotential] using hω a b T hab

end ReflectedGMS
