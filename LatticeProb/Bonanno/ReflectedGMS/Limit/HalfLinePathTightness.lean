/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.HalfLinePathTightness at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Tightness of path laws on the non-compact time half-line

`ReflectedGMS.MartingaleLimit.isTightMeasureSet_continuousMap_of_size_and_modulus`
proves tightness of laws on `C(K, E)` for a **compact** time domain `K`.  The
quenched invariance principle of `ReflectedGMS/InvarianceAssembly.lean` needs
tightness on `BouRabeeGwynne.BrownianPath 2 = C(ℝ≥0, Euc 2)`, whose time domain
is **not** compact, and no rescaling makes it compact.  This file closes that
gap: it produces tightness on `C(ℝ≥0, E)` out of a size tail and a
modulus-of-continuity tail on **each bounded time window** `[0, m]`, which is
exactly the form in which the martingale estimates of this development are
available.

The compactness step cannot reuse `BoundedContinuousFunction.arzela_ascoli`,
which is a statement about a compact domain.  It uses mathlib's
`ArzelaAscoli.isCompact_of_equicontinuous` instead: an equicontinuous set of
continuous maps whose image in the product topology is compact is compact in
the compact-open topology.  Compactness of that image is Tychonoff
(`isCompact_univ_pi`) together with closedness of the window conditions, and
the window modulus conditions are what force a product-space limit to be
continuous.

## Main results

* `isCompact_halfLineGood` — the set of paths obeying a size bound and a modulus
  bound on every window `[0, m]` is compact in `C(ℝ≥0, E)`.
* `isTightMeasureSet_halfLine_of_size_and_modulus` — per-window size and modulus
  tails give tightness of an arbitrary set of laws on `C(ℝ≥0, E)`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

section HalfLine

variable {E : Type*} [MetricSpace E] [ProperSpace E]

/-- Paths leaving the closed ball of radius `R` about `e₀` somewhere on the time
window `[0, m]`. -/
def halfLineSizeFailure (e₀ : E) (m : ℕ) (R : ℝ) : Set C(ℝ≥0, E) :=
  {f | ∃ t ≤ (m : ℝ≥0), R < dist (f t) e₀}

/-- Paths whose oscillation over a pair of times in the window `[0, m]` at
distance less than `d` exceeds `ε`. -/
def halfLineModulusFailure (m : ℕ) (ε d : ℝ) : Set C(ℝ≥0, E) :=
  {f | ∃ s ≤ (m : ℝ≥0), ∃ t ≤ (m : ℝ≥0), dist s t < d ∧ ε < dist (f s) (f t)}

/-- The raw-function description of the paths obeying the size bounds `R m` and
the moduli `δ m k` on every window. -/
def halfLineGoodProduct (e₀ : E) (R : ℕ → ℝ) (δ : ℕ → ℕ → ℝ) : Set (ℝ≥0 → E) :=
  (⋂ m : ℕ, ⋂ t : ℝ≥0, ⋂ _ : t ≤ (m : ℝ≥0), {g : ℝ≥0 → E | dist (g t) e₀ ≤ R m}) ∩
    ⋂ m : ℕ, ⋂ k : ℕ, ⋂ s : ℝ≥0, ⋂ _ : s ≤ (m : ℝ≥0), ⋂ t : ℝ≥0, ⋂ _ : t ≤ (m : ℝ≥0),
      ⋂ _ : dist s t < δ m k, {g : ℝ≥0 → E | dist (g s) (g t) ≤ 1 / (k + 1)}

/-- The same set inside the continuous-path space. -/
def halfLineGood (e₀ : E) (R : ℕ → ℝ) (δ : ℕ → ℕ → ℝ) : Set C(ℝ≥0, E) :=
  {f | ContinuousMap.toFun f ∈ halfLineGoodProduct e₀ R δ}

variable {e₀ : E} {R : ℕ → ℝ} {δ : ℕ → ℕ → ℝ}

theorem mem_halfLineGoodProduct {g : ℝ≥0 → E}
    (h1 : ∀ m : ℕ, ∀ t ≤ (m : ℝ≥0), dist (g t) e₀ ≤ R m)
    (h2 : ∀ m k : ℕ, ∀ s ≤ (m : ℝ≥0), ∀ t ≤ (m : ℝ≥0), dist s t < δ m k →
      dist (g s) (g t) ≤ 1 / (k + 1)) :
    g ∈ halfLineGoodProduct e₀ R δ := by
  constructor
  · simp only [Set.mem_iInter]
    exact fun m t ht => h1 m t ht
  · simp only [Set.mem_iInter]
    exact fun m k s hs t ht hst => h2 m k s hs t ht hst

theorem halfLineGoodProduct_size {g : ℝ≥0 → E} (hg : g ∈ halfLineGoodProduct e₀ R δ)
    (m : ℕ) {t : ℝ≥0} (ht : t ≤ (m : ℝ≥0)) : dist (g t) e₀ ≤ R m := by
  have h := hg.1
  simp only [Set.mem_iInter] at h
  exact h m t ht

theorem halfLineGoodProduct_modulus {g : ℝ≥0 → E} (hg : g ∈ halfLineGoodProduct e₀ R δ)
    (m k : ℕ) {s t : ℝ≥0} (hs : s ≤ (m : ℝ≥0)) (ht : t ≤ (m : ℝ≥0))
    (hst : dist s t < δ m k) : dist (g s) (g t) ≤ 1 / (k + 1) := by
  have h := hg.2
  simp only [Set.mem_iInter] at h
  exact h m k s hs t ht hst

theorem isClosed_halfLineGoodProduct (e₀ : E) (R : ℕ → ℝ) (δ : ℕ → ℕ → ℝ) :
    IsClosed (halfLineGoodProduct e₀ R δ) := by
  refine IsClosed.inter ?_ ?_
  · refine isClosed_iInter fun m => isClosed_iInter fun t => isClosed_iInter fun _ => ?_
    exact isClosed_le ((continuous_apply t).dist continuous_const) continuous_const
  · refine isClosed_iInter fun m => isClosed_iInter fun k => isClosed_iInter fun s =>
      isClosed_iInter fun _ => isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => ?_
    exact isClosed_le ((continuous_apply s).dist (continuous_apply t)) continuous_const

/-- A window modulus on every window forces continuity of a raw function. -/
theorem continuous_of_mem_halfLineGoodProduct (hδ : ∀ m k, 0 < δ m k)
    {g : ℝ≥0 → E} (hg : g ∈ halfLineGoodProduct e₀ R δ) : Continuous g := by
  rw [Metric.continuous_iff]
  intro x ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  refine ⟨min (δ (⌈(x : ℝ)⌉₊ + 1) k) 1, lt_min (hδ _ k) one_pos, ?_⟩
  intro y hy
  have hxr : (x : ℝ) ≤ (⌈(x : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hxm : x ≤ ((⌈(x : ℝ)⌉₊ + 1 : ℕ) : ℝ≥0) := by
    have : (x : ℝ) ≤ ((⌈(x : ℝ)⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hd : |(y : ℝ) - (x : ℝ)| < 1 := by
    have h := lt_of_lt_of_le hy (min_le_right _ _)
    rwa [NNReal.dist_eq] at h
  have hym : y ≤ ((⌈(x : ℝ)⌉₊ + 1 : ℕ) : ℝ≥0) := by
    have h := (abs_lt.mp hd).2
    have : (y : ℝ) ≤ ((⌈(x : ℝ)⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  exact lt_of_le_of_lt
    (halfLineGoodProduct_modulus hg (⌈(x : ℝ)⌉₊ + 1) k hym hxm
      (lt_of_lt_of_le hy (min_le_left _ _))) hk

theorem halfLineGoodProduct_subset_pi :
    halfLineGoodProduct e₀ R δ ⊆
      Set.univ.pi (fun t : ℝ≥0 => Metric.closedBall e₀ (R ⌈(t : ℝ)⌉₊)) := by
  intro g hg
  rw [Set.mem_univ_pi]
  intro t
  refine Metric.mem_closedBall.mpr (halfLineGoodProduct_size hg ⌈(t : ℝ)⌉₊ ?_)
  have : (t : ℝ) ≤ ((⌈(t : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  exact_mod_cast this

theorem isCompact_halfLineGoodProduct :
    IsCompact (halfLineGoodProduct e₀ R δ) :=
  IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun t : ℝ≥0 => isCompact_closedBall e₀ (R ⌈(t : ℝ)⌉₊))
    (isClosed_halfLineGoodProduct e₀ R δ) halfLineGoodProduct_subset_pi

theorem image_toFun_halfLineGood (hδ : ∀ m k, 0 < δ m k) :
    ContinuousMap.toFun '' halfLineGood e₀ R δ = halfLineGoodProduct e₀ R δ := by
  apply Set.Subset.antisymm
  · rintro g ⟨f, hf, rfl⟩
    exact hf
  · intro g hg
    exact ⟨⟨g, continuous_of_mem_halfLineGoodProduct hδ hg⟩, hg, rfl⟩

theorem equicontinuous_halfLineGood (hδ : ∀ m k, 0 < δ m k) :
    Equicontinuous ((↑) : halfLineGood e₀ R δ → ℝ≥0 → E) := by
  rw [Equicontinuous]
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  refine ⟨min (δ (⌈(x : ℝ)⌉₊ + 1) k) 1, lt_min (hδ _ k) one_pos, ?_⟩
  intro y hy f
  have hxr : (x : ℝ) ≤ (⌈(x : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hxm : x ≤ ((⌈(x : ℝ)⌉₊ + 1 : ℕ) : ℝ≥0) := by
    have : (x : ℝ) ≤ ((⌈(x : ℝ)⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hd : |(y : ℝ) - (x : ℝ)| < 1 := by
    have h := lt_of_lt_of_le hy (min_le_right _ _)
    rwa [NNReal.dist_eq] at h
  have hym : y ≤ ((⌈(x : ℝ)⌉₊ + 1 : ℕ) : ℝ≥0) := by
    have h := (abs_lt.mp hd).2
    have : (y : ℝ) ≤ ((⌈(x : ℝ)⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  refine lt_of_le_of_lt
    (halfLineGoodProduct_modulus f.2 (⌈(x : ℝ)⌉₊ + 1) k hxm hym ?_) hk
  rw [dist_comm]
  exact lt_of_lt_of_le hy (min_le_left _ _)

/-- **Compactness of the per-window size-and-modulus set of continuous paths on
the whole half-line.** -/
theorem isCompact_halfLineGood (hδ : ∀ m k, 0 < δ m k) :
    IsCompact (halfLineGood e₀ R δ) := by
  refine ArzelaAscoli.isCompact_of_equicontinuous _ ?_ (equicontinuous_halfLineGood hδ)
  rw [image_toFun_halfLineGood hδ]
  exact isCompact_halfLineGoodProduct

variable [MeasurableSpace E] [BorelSpace E]

/-- **Per-window size and modulus tails give tightness of path laws on the
non-compact half-line.**  No measurability of the failure sets is required:
only countable subadditivity of the measures is used. -/
theorem isTightMeasureSet_halfLine_of_size_and_modulus
    (e₀ : E) (𝒮 : Set (Measure C(ℝ≥0, E)))
    (hsize : ∀ (m : ℕ) (η : ℝ≥0∞), 0 < η → ∃ R : ℝ,
      ∀ ν ∈ 𝒮, ν (halfLineSizeFailure e₀ m R) ≤ η)
    (hmod : ∀ (m : ℕ) (ε : ℝ), 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ d : ℝ, 0 < d ∧
      ∀ ν ∈ 𝒮, ν (halfLineModulusFailure m ε d) ≤ η) :
    IsTightMeasureSet 𝒮 := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro η hη
  obtain ⟨budget, hbudget_pos, hbudget_sum⟩ :=
    ENNReal.exists_pos_sum_of_countable hη.ne' (ℕ ⊕ ℕ × ℕ)
  choose R hR using fun m : ℕ =>
    hsize m (budget (Sum.inl m)) (ENNReal.coe_pos.2 (hbudget_pos (Sum.inl m)))
  choose d hdpos hd using fun m k : ℕ =>
    hmod m (1 / (k + 1)) (by positivity) (budget (Sum.inr (m, k)))
      (ENNReal.coe_pos.2 (hbudget_pos (Sum.inr (m, k))))
  set failure : ℕ ⊕ ℕ × ℕ → Set C(ℝ≥0, E) :=
    Sum.elim (fun m => halfLineSizeFailure e₀ m (R m))
      (fun p => halfLineModulusFailure p.1 (1 / (p.2 + 1)) (d p.1 p.2)) with hfailure
  have hGsub : (⋂ j, (failure j)ᶜ) ⊆ halfLineGood e₀ R d := by
    intro f hf
    refine mem_halfLineGoodProduct ?_ ?_
    · intro m t ht
      have hj : f ∉ halfLineSizeFailure e₀ m (R m) := Set.mem_iInter.mp hf (Sum.inl m)
      by_contra hcon
      exact hj ⟨t, ht, lt_of_not_ge hcon⟩
    · intro m k s hs t ht hst
      have hj : f ∉ halfLineModulusFailure m (1 / (k + 1)) (d m k) :=
        Set.mem_iInter.mp hf (Sum.inr (m, k))
      by_contra hcon
      exact hj ⟨s, hs, t, ht, hst, lt_of_not_ge hcon⟩
  refine ⟨halfLineGood e₀ R d, isCompact_halfLineGood hdpos, ?_⟩
  intro ν hν
  have hcompl : (halfLineGood e₀ R d)ᶜ ⊆ ⋃ j, failure j := by
    intro f hf
    by_contra hcon
    exact hf (hGsub (Set.mem_iInter.mpr fun j hj => hcon (Set.mem_iUnion.mpr ⟨j, hj⟩)))
  calc ν (halfLineGood e₀ R d)ᶜ
      ≤ ν (⋃ j, failure j) := measure_mono hcompl
    _ ≤ ∑' j, ν (failure j) := measure_iUnion_le failure
    _ ≤ ∑' j, (budget j : ℝ≥0∞) := by
        refine ENNReal.tsum_le_tsum ?_
        rintro (m | ⟨m, k⟩)
        · exact hR m ν hν
        · exact hd m k ν hν
    _ ≤ η := hbudget_sum.le

end HalfLine

end ReflectedGMS.MartingaleLimit
