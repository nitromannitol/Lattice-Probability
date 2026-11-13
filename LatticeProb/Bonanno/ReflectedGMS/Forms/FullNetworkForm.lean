/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FullNetworkForm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Analysis.WeightedGradient

/-!
# Closed graph of the full network energy domain

We use the standard weighted-sequence realization of atomic speed `L²`: a function
`f` is represented by `v ↦ sqrt (m v) * f v` in mathlib's `lp 2`. The energy coordinate
is the already normalized `weightedGradient`, over all ordered pairs.

The compatibility equations define a closed linear subspace of the product of these
two complete spaces. The inherited product norm is the **maximum** of the value and
gradient norms; it is an equivalent complete graph norm, not the Hilbert sum norm.
The exact domain characterization below includes every function of finite energy;
no finite-support closure, connectivity, or positive lower bound on speeds is used.
-/

set_option autoImplicit false

open scoped ENNReal

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

abbrev ValueSpace (V : Type*) := lp (fun _ : V => ℝ) 2
abbrev GradientSpace (V : Type*) := lp (fun _ : V × V => ℝ) 2

/-- Recover a vertex function from its weighted `L²` coordinates. -/
noncomputable def unweight (m : V → ℝ) (u : ValueSpace V) : V → ℝ :=
  fun v => u v / Real.sqrt (m v)

/-- The full weighted `L²` condition, stated with the existing `Memℓp` predicate. -/
def HasSpeedL2 (m : V → ℝ) (f : V → ℝ) : Prop :=
  Memℓp (fun v => Real.sqrt (m v) * f v) 2

/-- A finite-speed-`L²` function as a genuine `lp 2` vector. -/
noncomputable def weightedValue (m : V → ℝ) (f : V → ℝ) (hf : HasSpeedL2 m f) :
    ValueSpace V := ⟨_, hf⟩

@[simp] theorem weightedValue_apply (m : V → ℝ) (f : V → ℝ)
    (hf : HasSpeedL2 m f) (v : V) :
    weightedValue m f hf v = Real.sqrt (m v) * f v := rfl

/-- Strict positivity of each atom makes weighted coordinates lossless. -/
theorem unweight_weightedValue (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (f : V → ℝ) (hf : HasSpeedL2 m f) :
    unweight m (weightedValue m f hf) = f := by
  funext v
  simp only [unweight, weightedValue_apply]
  exact mul_div_cancel_left₀ (f v) (Real.sqrt_pos.2 (hm v)).ne'

/-- The weighted coordinate norm has precisely the atomic speed normalization. -/
theorem weightedValue_norm_sq (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (f : V → ℝ) (hf : HasSpeedL2 m f) :
    ‖weightedValue m f hf‖ ^ 2 = ∑' v, m v * (f v) ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (E := fun _ : V => ℝ)
    (p := 2) (by norm_num) (weightedValue m f hf)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    weightedValue_apply, mul_pow, Real.sq_sqrt (hm _).le] using h

variable (G : ReflectedWalk.ConductanceGraph V)

/-- The weighted-gradient condition is equivalent to full finite energy. -/
theorem weightedGradientCoord_mem_iff (f : V → ℝ) :
    Memℓp (weightedGradientCoord G f) 2 ↔ G.HasFiniteEnergy f := by
  constructor
  · intro hf
    have hs := hf.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      weightedGradientCoord_sq] at hs
    have ht := hs.mul_left 2
    exact ht.congr fun p => by ring
  · exact weightedGradientCoord_memℓp G

/-- Compatibility graph of the full gradient operator on weighted `L²`. -/
noncomputable def graphSubmodule (m : V → ℝ) :
    Submodule ℝ (ValueSpace V × GradientSpace V) where
  carrier := {z | ∀ p, z.2 p = weightedGradientCoord G (unweight m z.1) p}
  zero_mem' := by
    intro p
    simp [weightedGradientCoord, unweight]
  add_mem' := by
    intro z z' hz hz' p
    change z.2 p + z'.2 p = _
    rw [hz p, hz' p]
    simp only [weightedGradientCoord, unweight, Prod.fst_add, lp.coeFn_add,
      Pi.add_apply]
    ring
  smul_mem' := by
    intro a z hz p
    change a * z.2 p = _
    rw [hz p]
    simp only [weightedGradientCoord, unweight, Prod.smul_fst, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul]
    ring

@[simp] theorem mem_graphSubmodule (m : V → ℝ) (z : ValueSpace V × GradientSpace V) :
    z ∈ graphSubmodule G m ↔
      ∀ p, z.2 p = weightedGradientCoord G (unweight m z.1) p := Iff.rfl

/-- Each graph condition is a closed equality of continuous coordinate maps. -/
theorem isClosed_graphSubmodule (m : V → ℝ) :
    IsClosed (graphSubmodule G m : Set (ValueSpace V × GradientSpace V)) := by
  have h : (graphSubmodule G m : Set (ValueSpace V × GradientSpace V)) =
      ⋂ p, {z | z.2 p = weightedGradientCoord G (unweight m z.1) p} := by
    ext z
    simp only [SetLike.mem_coe, mem_graphSubmodule, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [h]
  apply isClosed_iInter
  intro p
  have hv (v : V) : Continuous (fun z : ValueSpace V × GradientSpace V =>
      unweight m z.1 v) :=
    ((lp.evalCLM ℝ (fun _ : V => ℝ) 2 v).continuous.comp continuous_fst).div_const _
  exact isClosed_eq
    ((lp.evalCLM ℝ (fun _ : V × V => ℝ) 2 p).continuous.comp continuous_snd)
    (continuous_const.mul ((hv p.2).sub (hv p.1)))

/-- No smaller energy domain is introduced by the closed graph representation. -/
theorem exists_gradient_iff (m : V → ℝ) (u : ValueSpace V) :
    (∃ g : GradientSpace V, (u, g) ∈ graphSubmodule G m) ↔
      G.HasFiniteEnergy (unweight m u) := by
  constructor
  · rintro ⟨g, hg⟩
    apply (weightedGradientCoord_mem_iff G _).1
    have heq : (g : V × V → ℝ) = weightedGradientCoord G (unweight m u) :=
      funext hg
    rw [← heq]
    exact g.property
  · intro hf
    exact ⟨weightedGradient G (unweight m u) hf, fun _ => rfl⟩

/-- Every full finite-energy function in speed `L²` belongs to the closed graph. -/
theorem weightedPair_mem (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (f : V → ℝ) (hL2 : HasSpeedL2 m f) (hE : G.HasFiniteEnergy f) :
    (weightedValue m f hL2, weightedGradient G f hE) ∈ graphSubmodule G m := by
  rw [mem_graphSubmodule, unweight_weightedValue m hm]
  intro p
  rfl

end ReflectedGMS.FullNetworkForm
