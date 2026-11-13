/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.HarmonicMeasure at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.Proposition13
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi

/-!
# Harmonic measure and the basic properties of `h_φ` (Gwynne–Sung, Definition 1.5, Section 2.2)

* `energyMin_le_max`, `min_le_energyMin` — **Lemma 2.3** (maximum principle): the values of
  `h_φ` lie between `min_A φ` and `max_A φ`.  As the paper stresses, this does not follow from
  harmonicity alone; the proof truncates `h_φ` at `M = max_A φ`, notes that truncation does not
  increase any edge gradient (`gradSq_min_le`), so the truncation is a competitor of no larger
  energy, and concludes by the *uniqueness* clause of Proposition 1.3 that the truncation is
  `h_φ` itself.
* `energyMin_restrict` — **Lemma 2.2** (consistency): `h_φ` is its own energy-minimizing
  extension from any larger finite set `B ⊇ A`; immediate from uniqueness.
* `indic`, `harmonicMeasure` — **Definition 1.5**: `hm^x_A(y) = h_{1_y}(x)`.
* `harmonicMeasure_nonneg`, `harmonicMeasure_le_one`, `sum_harmonicMeasure`,
  `energyMin_eq_sum_harmonicMeasure` — **Lemma 2.4**: `hm^x_A` is a probability measure on `A`
  and `h_φ(x) = ∑_{y ∈ A} φ(y) hm^x_A(y)` (2.8), from Lemma 2.3 and the linearity of `φ ↦ h_φ`.
-/

namespace ReflectedWalk

namespace ConductanceGraph

open Classical

variable {V : Type*} (G : ConductanceGraph V)

/-! ### Lemma 2.3: the maximum principle -/

/-- Truncating from above does not increase any edge gradient, (2.7):
`|min(a,M) − min(b,M)| ≤ |a − b|`. -/
lemma gradSq_min_le (h : V → ℝ) (M : ℝ) (p : V × V) :
    G.gradSq (fun v => min (h v) M) p ≤ G.gradSq h p := by
  simp only [gradSq]
  refine mul_le_mul_of_nonneg_left ?_ (G.c_nonneg _ _)
  rw [sq_le_sq]
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

/-- Truncating from below does not increase any edge gradient. -/
lemma gradSq_max_le (h : V → ℝ) (m : ℝ) (p : V × V) :
    G.gradSq (fun v => max (h v) m) p ≤ G.gradSq h p := by
  simp only [gradSq]
  refine mul_le_mul_of_nonneg_left ?_ (G.c_nonneg _ _)
  rw [sq_le_sq]
  exact abs_max_sub_max_le_abs _ _ _

/-- A function whose edge gradients are dominated by those of a finite-energy function has
finite energy and no larger energy. -/
lemma Energy_le_of_gradSq_le {f g : V → ℝ} (hg : G.HasFiniteEnergy g)
    (hle : ∀ p, G.gradSq f p ≤ G.gradSq g p) :
    G.HasFiniteEnergy f ∧ G.Energy f ≤ G.Energy g := by
  have hf : G.HasFiniteEnergy f := Summable.of_nonneg_of_le (fun p => G.gradSq_nonneg f p) hle hg
  refine ⟨hf, ?_⟩
  unfold Energy
  linarith [hf.tsum_le_tsum hle hg]

/-- **Lemma 2.3 (maximum principle)**: `h_φ ≤ max_A φ` everywhere.  The truncation
`min(h_φ, M)` agrees with `φ` on `A` and has no larger energy, so it is `h_φ` by uniqueness. -/
theorem energyMin_le_max (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    (φ : V → ℝ) (x : V) : G.energyMin hG A φ x ≤ A.sup' hA φ := by
  obtain ⟨hfin, hE⟩ := G.Energy_le_of_gradSq_le (G.energyMin_hasFiniteEnergy hG hA φ)
    (G.gradSq_min_le (G.energyMin hG A φ) (A.sup' hA φ))
  have hEq : Set.EqOn (fun v => min (G.energyMin hG A φ v) (A.sup' hA φ)) φ ↑A := by
    intro a ha
    show min (G.energyMin hG A φ a) (A.sup' hA φ) = φ a
    rw [G.energyMin_eqOn hG hA φ ha]
    exact min_eq_left (Finset.le_sup' φ (Finset.mem_coe.1 ha))
  have huniq := G.energyMin_unique hG hA φ hfin hEq
    fun g hg hgA => hE.trans (G.energyMin_le_energy hG hA φ hg hgA)
  exact min_eq_left_iff.1 (congrFun huniq x)

/-- **Lemma 2.3 (minimum principle)**: `min_A φ ≤ h_φ` everywhere. -/
theorem min_le_energyMin (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    (φ : V → ℝ) (x : V) : A.inf' hA φ ≤ G.energyMin hG A φ x := by
  obtain ⟨hfin, hE⟩ := G.Energy_le_of_gradSq_le (G.energyMin_hasFiniteEnergy hG hA φ)
    (G.gradSq_max_le (G.energyMin hG A φ) (A.inf' hA φ))
  have hEq : Set.EqOn (fun v => max (G.energyMin hG A φ v) (A.inf' hA φ)) φ ↑A := by
    intro a ha
    show max (G.energyMin hG A φ a) (A.inf' hA φ) = φ a
    rw [G.energyMin_eqOn hG hA φ ha]
    exact max_eq_left (Finset.inf'_le φ (Finset.mem_coe.1 ha))
  have huniq := G.energyMin_unique hG hA φ hfin hEq
    fun g hg hgA => hE.trans (G.energyMin_le_energy hG hA φ hg hgA)
  exact max_eq_left_iff.1 (congrFun huniq x)

/-! ### Lemma 2.2: consistency -/

/-- **Lemma 2.2 (consistency)**: for `A ⊆ B`, `h_φ` is the energy-minimizing function with
boundary values `h_φ|_B`.  Any competitor for `B` is a competitor for `A`, so uniqueness in
Proposition 1.3 applies. -/
theorem energyMin_restrict (hG : G.toSimpleGraph.Connected) {A B : Finset V} (hA : A.Nonempty)
    (hAB : A ⊆ B) (φ : V → ℝ) :
    G.energyMin hG B (G.energyMin hG A φ) = G.energyMin hG A φ := by
  refine (G.energyMin_unique hG (hA.mono hAB) _ (G.energyMin_hasFiniteEnergy hG hA φ)
    (fun _ _ => rfl) fun g hg hgB => ?_).symm
  refine G.energyMin_le_energy hG hA φ hg fun a ha => ?_
  rw [hgB (Finset.mem_coe.2 (hAB (Finset.mem_coe.1 ha)))]
  exact G.energyMin_eqOn hG hA φ ha

/-! ### Definition 1.5 and Lemma 2.4: harmonic measure -/

set_option linter.unusedVariables false in
/-- `1_y` of Definition 1.5.  `G` is carried as an (unused) explicit parameter so that the
contract's spelling `G.indic y` is available (hence the silenced linter). -/
noncomputable def indic (G : ConductanceGraph V) (y : V) : V → ℝ := fun v => if v = y then 1 else 0

/-- Definition 1.5: `hm^x_A(y) = h_{1_y}(x)`, the (energy-minimizing) harmonic measure on `A`
viewed from `x`. -/
noncomputable def harmonicMeasure (hG : G.toSimpleGraph.Connected) (A : Finset V)
    (x : V) (y : V) : ℝ := G.energyMin hG A (G.indic y) x

lemma indic_nonneg (y v : V) : 0 ≤ G.indic y v := by
  unfold indic; split_ifs <;> norm_num

lemma indic_le_one (y v : V) : G.indic y v ≤ 1 := by
  unfold indic; split_ifs <;> norm_num

/-- Lemma 2.4: `hm^x_A(y) ≥ 0`, from the minimum principle. -/
theorem harmonicMeasure_nonneg (hG : G.toSimpleGraph.Connected) {A : Finset V}
    (hA : A.Nonempty) (x : V) (y : V) : 0 ≤ G.harmonicMeasure hG A x y :=
  (Finset.le_inf' hA _ fun a _ => G.indic_nonneg y a).trans (G.min_le_energyMin hG hA _ x)

/-- Lemma 2.4: `hm^x_A(y) ≤ 1`, from the maximum principle. -/
theorem harmonicMeasure_le_one (hG : G.toSimpleGraph.Connected) {A : Finset V}
    (hA : A.Nonempty) (x : V) (y : V) : G.harmonicMeasure hG A x y ≤ 1 :=
  (G.energyMin_le_max hG hA _ x).trans (Finset.sup'_le hA _ fun a _ => G.indic_le_one y a)

/-- The linearity clause of Proposition 1.3, packaged: `φ ↦ h_φ` as a linear map. -/
noncomputable def energyMinₗ (hG : G.toSimpleGraph.Connected) {A : Finset V}
    (hA : A.Nonempty) : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun := G.energyMin hG A
  map_add' := G.energyMin_add hG hA
  map_smul' := G.energyMin_smul hG hA

@[simp] lemma energyMinₗ_apply (hG : G.toSimpleGraph.Connected) {A : Finset V}
    (hA : A.Nonempty) (φ : V → ℝ) : G.energyMinₗ hG hA φ = G.energyMin hG A φ := rfl

/-- `∑_{y ∈ A} 1_y ≡ 1` on `A`. -/
lemma sum_indic_eqOn (A : Finset V) :
    Set.EqOn (∑ y ∈ A, G.indic y) (Function.const V 1) ↑A := by
  intro v hv
  simp [Finset.sum_apply, indic, Finset.mem_coe.1 hv]

/-- **Lemma 2.4 (total mass)**: `hm^x_A` is a probability measure on `A`, by linearity applied
to `∑_{y ∈ A} 1_y ≡ 1` on `A` and `energyMin_const`. -/
theorem sum_harmonicMeasure (hG : G.toSimpleGraph.Connected) {A : Finset V}
    (hA : A.Nonempty) (x : V) : ∑ y ∈ A, G.harmonicMeasure hG A x y = 1 := by
  have h1 : ∑ y ∈ A, G.harmonicMeasure hG A x y =
      G.energyMinₗ hG hA (∑ y ∈ A, G.indic y) x := by
    rw [map_sum, Finset.sum_apply]; rfl
  rw [h1, energyMinₗ_apply, G.energyMin_congr hG hA (G.sum_indic_eqOn A),
    G.energyMin_const hG hA 1]
  rfl

/-- `φ = ∑_{y ∈ A} φ(y) 1_y` on `A`. -/
lemma eqOn_sum_smul_indic (A : Finset V) (φ : V → ℝ) :
    Set.EqOn φ (∑ y ∈ A, φ y • G.indic y) ↑A := by
  intro v hv
  simp [Finset.sum_apply, indic, Finset.mem_coe.1 hv]

/-- **Lemma 2.4, equation (2.8)**: `h_φ(x) = ∑_{y ∈ A} φ(y) hm^x_A(y)`, by linearity. -/
theorem energyMin_eq_sum_harmonicMeasure (hG : G.toSimpleGraph.Connected) {A : Finset V}
    (hA : A.Nonempty) (φ : V → ℝ) (x : V) :
    G.energyMin hG A φ x = ∑ y ∈ A, φ y * G.harmonicMeasure hG A x y := by
  rw [G.energyMin_congr hG hA (G.eqOn_sum_smul_indic A φ), ← G.energyMinₗ_apply hG hA, map_sum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_smul]
  rfl

end ConductanceGraph

end ReflectedWalk
