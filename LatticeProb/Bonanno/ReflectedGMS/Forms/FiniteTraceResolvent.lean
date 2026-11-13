/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FiniteTraceResolvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTargetL2
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceEnergy
import LatticeProb.Bonanno.ReflectedGMS.Forms.ParameterizedResolventMarkov

/-!
# Finite-trace resolvents and their full-network harmonic extensions

The forcing and speed are restricted to a nonempty finite target, the genuine
parameterized resolvent is taken on the resulting trace conductance graph, and
its boundary values are extended by the full-network energy minimizer.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Classical
open scoped ENNReal

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

/-- Restriction of weighted forcing coordinates to a finite target. -/
noncomputable def finiteTraceForcing (A : Finset V) (f : ValueSpace V) :
    ValueSpace {x // x ∈ A} :=
  ⟨fun x => f x.1, Memℓp.all _⟩

private theorem weightedValue_sub_norm_sq
    (m : V → ℝ) (hm : ∀ v, 0 < m v) (f g : V → ℝ)
    (hf : HasSpeedL2 m f) (hg : HasSpeedL2 m g) :
    ‖weightedValue m f hf - weightedValue m g hg‖ ^ 2 =
      ∑' v, m v * (f v - g v) ^ 2 := by
  have hn := lp.norm_rpow_eq_tsum (E := fun _ : V => ℝ)
    (p := 2) (by norm_num)
    (weightedValue m f hf - weightedValue m g hg)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
  exact hn.trans (congrArg tsum (funext fun v => by
    simp only [Real.norm_eq_abs, sq_abs, lp.coeFn_sub, Pi.sub_apply,
      weightedValue_apply]
    ring_nf
    rw [Real.sq_sqrt (hm v).le]
    ring))

private theorem finiteTrace_weighted_error_norm_sq
    (A : Finset V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (f : ValueSpace V) (g : {x // x ∈ A} → ℝ)
    (hg : HasSpeedL2 (fun x : {v // v ∈ A} => m x.1) g) :
    ‖weightedValue (fun x : {v // v ∈ A} => m x.1) g hg -
        finiteTraceForcing A f‖ ^ 2 =
      ∑' x : {v // v ∈ A}, m x.1 * (g x - unweight m f x.1) ^ 2 := by
  have hn := lp.norm_rpow_eq_tsum (E := fun _ : {v // v ∈ A} => ℝ)
    (p := 2) (by norm_num)
    (weightedValue (fun x : {v // v ∈ A} => m x.1) g hg - finiteTraceForcing A f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
  exact hn.trans (congrArg tsum (funext fun x => by
    have hfx : f x.1 = Real.sqrt (m x.1) * unweight m f x.1 := by
      simpa only [weightedValue_apply] using congrArg (fun z : ValueSpace V => z x.1)
        (weightedValue_unweight m hm f).symm
    simp only [Real.norm_eq_abs, sq_abs, lp.coeFn_sub, Pi.sub_apply,
      weightedValue_apply, finiteTraceForcing]
    rw [hfx]
    ring_nf
    rw [Real.sq_sqrt (hm x.1).le]
    ring))

/-- The decoded genuine parameterized resolvent on the finite trace graph. -/
noncomputable def finiteTraceResolventFunction
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (h : ℝ)
    (f : ValueSpace V) : {x // x ∈ A} → ℝ :=
  parameterizedResolventFunction (finiteTargetGraph G hG A hA)
    (fun x => m x.1) h (finiteTraceForcing A f)

/-- Boundary data on the original vertex type supplied by the finite trace resolvent. -/
noncomputable def finiteTraceResolventBoundary
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (h : ℝ)
    (f : ValueSpace V) : V → ℝ :=
  fun v => if hv : v ∈ A then
    finiteTraceResolventFunction G hG A hA m h f ⟨v, hv⟩ else 0

/-- The actual full-network harmonic extension of the finite trace resolvent. -/
noncomputable def finiteTraceResolventExtension
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (h : ℝ)
    (f : ValueSpace V) : V → ℝ :=
  G.energyMin hG A (finiteTraceResolventBoundary G hG A hA m h f)

@[simp] theorem unweight_finiteTraceForcing
    (A : Finset V) (m : V → ℝ) (f : ValueSpace V) (x : {v // v ∈ A}) :
    unweight (fun y : {v // v ∈ A} => m y.1) (finiteTraceForcing A f) x =
      unweight m f x.1 := rfl

@[simp] theorem finiteTraceResolventExtension_eqOn
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (h : ℝ)
    (f : ValueSpace V) {v : V} (hv : v ∈ A) :
    finiteTraceResolventExtension G hG A hA m h f v =
      finiteTraceResolventFunction G hG A hA m h f ⟨v, hv⟩ := by
  rw [finiteTraceResolventExtension, G.energyMin_eqOn hG hA _ hv]
  simp [finiteTraceResolventBoundary, hv]

theorem finiteTraceResolventFunction_mem_Icc
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {h : ℝ} (hh : 0 < h) (f : ValueSpace V)
    (hf : ∀ v, unweight m f v ∈ Set.Icc (0 : ℝ) 1)
    (x : {v // v ∈ A}) :
    finiteTraceResolventFunction G hG A hA m h f x ∈ Set.Icc (0 : ℝ) 1 := by
  apply parameterizedResolventFunction_mem_Icc
    (finiteTargetGraph G hG A hA) (fun y => m y.1) (fun y => hm y.1) hh
  intro y
  simpa using hf y.1

theorem finiteTraceResolventExtension_mem_Icc
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {h : ℝ} (hh : 0 < h) (f : ValueSpace V)
    (hf : ∀ v, unweight m f v ∈ Set.Icc (0 : ℝ) 1) (v : V) :
    finiteTraceResolventExtension G hG A hA m h f v ∈ Set.Icc (0 : ℝ) 1 := by
  let b := finiteTraceResolventBoundary G hG A hA m h f
  have hb (x : V) (hx : x ∈ A) : b x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [b, finiteTraceResolventBoundary, hx] using
      finiteTraceResolventFunction_mem_Icc G hG A hA m hm hh f hf ⟨x, hx⟩
  constructor
  · exact (Finset.le_inf' hA b (fun x hx => (hb x hx).1)).trans
      (G.min_le_energyMin hG hA b v)
  · exact (G.energyMin_le_max hG hA b v).trans
      (Finset.sup'_le hA b fun x hx => (hb x hx).2)

theorem finiteTraceResolventExtension_hasFiniteEnergy
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (h : ℝ)
    (f : ValueSpace V) :
    G.HasFiniteEnergy (finiteTraceResolventExtension G hG A hA m h f) :=
  G.energyMin_hasFiniteEnergy hG hA _

theorem finiteTraceResolventExtension_hasSpeedL2
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {h : ℝ} (hh : 0 < h) (f : ValueSpace V)
    (hf : ∀ v, unweight m f v ∈ Set.Icc (0 : ℝ) 1) :
    HasSpeedL2 m (finiteTraceResolventExtension G hG A hA m h f) := by
  apply hasSpeedL2_of_abs_le hm hmsum (C := 1)
  intro v
  have hv := finiteTraceResolventExtension_mem_Icc G hG A hA m hm hh f hf v
  rw [abs_of_nonneg hv.1]
  exact hv.2

theorem finiteTraceResolventExtension_sub_resolvent_hasSpeedL2
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {h : ℝ} (hh : 0 < h) (f : ValueSpace V)
    (hf : ∀ v, unweight m f v ∈ Set.Icc (0 : ℝ) 1) :
    HasSpeedL2 m (finiteTraceResolventExtension G hG A hA m h f -
      parameterizedResolventFunction G m h f) := by
  apply hasSpeedL2_of_abs_le hm hmsum (C := 1)
  intro v
  have he := finiteTraceResolventExtension_mem_Icc G hG A hA m hm hh f hf v
  have hu := parameterizedResolventFunction_mem_Icc G m hm hh f hf v
  rcases he with ⟨he0, he1⟩
  rcases hu with ⟨hu0, hu1⟩
  rw [abs_le]
  constructor <;> dsimp <;> linarith

/-- The genuine finite-trace resolvent minimizes the finite trace objective. -/
theorem finiteTraceResolvent_objective_le
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {h : ℝ} (hh : 0 < h) (f : ValueSpace V)
    (g : {x // x ∈ A} → ℝ)
    (hgL2 : HasSpeedL2 (fun x : {v // v ∈ A} => m x.1) g)
    (hgE : (finiteTargetGraph G hG A hA).HasFiniteEnergy g) :
    ‖weightedValue (fun x : {v // v ∈ A} => m x.1)
        (finiteTraceResolventFunction G hG A hA m h f)
        (parameterizedResolventFunction_hasSpeedL2
          (finiteTargetGraph G hG A hA) (fun x : {v // v ∈ A} => m x.1)
          (fun x => hm x.1) h (finiteTraceForcing A f)) - finiteTraceForcing A f‖ ^ 2 +
      h * (finiteTargetGraph G hG A hA).Energy
        (finiteTraceResolventFunction G hG A hA m h f) ≤
    ‖weightedValue (fun x : {v // v ∈ A} => m x.1) g hgL2 -
        finiteTraceForcing A f‖ ^ 2 +
      h * (finiteTargetGraph G hG A hA).Energy g := by
  let T := finiteTargetGraph G hG A hA
  let mA : {x // x ∈ A} → ℝ := fun x => m x.1
  let fA := finiteTraceForcing A f
  let u := parameterizedResolventFunction T mA h fA
  have huL2 := parameterizedResolventFunction_hasSpeedL2 T mA (fun x => hm x.1) h fA
  have huE := parameterizedResolventFunction_hasFiniteEnergy T mA h fA
  let q := inHilbertDomain T mA (fun x => hm x.1) u huL2 huE
  let w := inHilbertDomain T mA (fun x => hm x.1) g hgL2 hgE
  have hs := parameterizedResolventObjective_eq_min_add_squares
    T mA (fun x => hm x.1) hh fA w
  have hnonneg :
      0 ≤ ‖valueInclusion T mA (w - q)‖ ^ 2 +
        h * ‖gradientInclusion T mA (w - q)‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (mul_nonneg hh.le (sq_nonneg _))
  have hmin : parameterizedResolventObjective T mA h fA q ≤
      parameterizedResolventObjective T mA h fA w := by
    change parameterizedResolventObjective T mA h fA w =
        parameterizedResolventObjective T mA h fA q +
          ‖valueInclusion T mA (w - q)‖ ^ 2 +
            h * ‖gradientInclusion T mA (w - q)‖ ^ 2 at hs
    linarith
  dsimp [q, w] at hmin
  rw [parameterizedResolventObjective_inHilbertDomain,
    parameterizedResolventObjective_inHilbertDomain] at hmin
  exact hmin

/-- The finite trace objective, after harmonic extension, is no larger than the
full resolvent objective.  The only later loss comes from weighted error outside
the target. -/
theorem finiteTraceResolvent_extension_core_objective_le
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {h : ℝ} (hh : 0 < h) (f : ValueSpace V) :
    ‖weightedValue (fun x : {v // v ∈ A} => m x.1)
        (finiteTraceResolventFunction G hG A hA m h f)
        (parameterizedResolventFunction_hasSpeedL2
          (finiteTargetGraph G hG A hA) (fun x : {v // v ∈ A} => m x.1)
          (fun x => hm x.1) h (finiteTraceForcing A f)) - finiteTraceForcing A f‖ ^ 2 +
      h * G.Energy (finiteTraceResolventExtension G hG A hA m h f) ≤
    ‖parameterizedResolvent G m h f - f‖ ^ 2 +
      h * G.Energy (parameterizedResolventFunction G m h f) := by
  let T := finiteTargetGraph G hG A hA
  let u := parameterizedResolventFunction G m h f
  let uA := finiteTraceResolventFunction G hG A hA m h f
  let gA : {x // x ∈ A} → ℝ := fun x => u x.1
  have hgAL2 : HasSpeedL2 (fun x : {v // v ∈ A} => m x.1) gA := Memℓp.all _
  have hgAE : T.HasFiniteEnergy gA :=
    T.hasFiniteEnergy_of_support_subset Finset.univ (by simp)
  have hmin := finiteTraceResolvent_objective_le G hG A hA m hm hh f gA hgAL2 hgAE
  have hleftE : T.Energy uA =
      G.Energy (finiteTraceResolventExtension G hG A hA m h f) := by
    have he := finiteTargetGraph_energy G hG A hA
      (finiteTraceResolventBoundary G hG A hA m h f)
    change T.Energy uA =
      G.Energy (G.energyMin hG A (finiteTraceResolventBoundary G hG A hA m h f))
    rw [← he]
    congr 1
    funext x
    simp [uA, finiteTraceResolventBoundary]
  have hrightE : T.Energy gA ≤ G.Energy u := by
    have he := finiteTargetGraph_energy G hG A hA u
    have hp := energyMin_energy_pythagorean G hG hA u
      (parameterizedResolventFunction_hasFiniteEnergy G m h f)
    rw [he]
    linarith [G.Energy_nonneg (u - G.energyMin hG A u)]
  have huL2 := parameterizedResolventFunction_hasSpeedL2 G m hm h f
  have hnormFull :
      ‖weightedValue m u huL2 - weightedValue m (unweight m f)
          (hasSpeedL2_unweight m hm f)‖ ^ 2 =
        ‖parameterizedResolvent G m h f - f‖ ^ 2 := by
    have huweight := weightedValue_unweight m hm (parameterizedResolvent G m h f)
    change weightedValue m u huL2 = parameterizedResolvent G m h f at huweight
    rw [huweight, weightedValue_unweight m hm f]
  have hsummable : Summable
      (fun v => m v * (u v - unweight m f v) ^ 2) := by
    have hs := (lp.memℓp (weightedValue m u huL2 -
      weightedValue m (unweight m f) (hasSpeedL2_unweight m hm f)))
    have hs' := hs.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, lp.coeFn_sub, Pi.sub_apply,
      weightedValue_apply, Real.norm_eq_abs, sq_abs] at hs'
    exact hs'.congr (fun v => by
      rw [← mul_sub, mul_pow, Real.sq_sqrt (hm v).le])
  have hrightNorm :
      ‖weightedValue (fun x : {v // v ∈ A} => m x.1) gA hgAL2 -
          finiteTraceForcing A f‖ ^ 2 ≤
        ‖parameterizedResolvent G m h f - f‖ ^ 2 := by
    rw [finiteTrace_weighted_error_norm_sq A m hm f gA hgAL2]
    rw [← hnormFull, weightedValue_sub_norm_sq m hm u (unweight m f) huL2
      (hasSpeedL2_unweight m hm f)]
    rw [tsum_fintype]
    have hatt :
        (∑ x : {v // v ∈ A}, m x.1 * (gA x - unweight m f x.1) ^ 2) =
          ∑ v ∈ A, m v * (u v - unweight m f v) ^ 2 := by
      change (∑ x ∈ A.attach, m x.1 * (u x.1 - unweight m f x.1) ^ 2) = _
      exact Finset.sum_attach A (fun v => m v * (u v - unweight m f v) ^ 2)
    rw [hatt]
    exact hsummable.sum_le_tsum A (fun v _ => mul_nonneg (hm v).le (sq_nonneg _))
  rw [hleftE] at hmin
  exact hmin.trans (add_le_add hrightNorm (mul_le_mul_of_nonneg_left hrightE hh.le))

/-- The full weighted forcing error of the harmonic extension costs at most its
finite-target error plus the speed mass outside the target. -/
theorem finiteTraceResolventExtension_weighted_error_le_tail
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {h : ℝ} (hh : 0 < h) (f : ValueSpace V)
    (hf : ∀ v, unweight m f v ∈ Set.Icc (0 : ℝ) 1) :
    ‖weightedValue m (finiteTraceResolventExtension G hG A hA m h f)
        (finiteTraceResolventExtension_hasSpeedL2 G hG A hA m hm hmsum hh f hf) - f‖ ^ 2 ≤
      ‖weightedValue (fun x : {v // v ∈ A} => m x.1)
          (finiteTraceResolventFunction G hG A hA m h f)
          (parameterizedResolventFunction_hasSpeedL2
            (finiteTargetGraph G hG A hA) (fun x : {v // v ∈ A} => m x.1)
            (fun x => hm x.1) h (finiteTraceForcing A f)) - finiteTraceForcing A f‖ ^ 2 +
        ∑' v : {v // v ∉ A}, m v.1 := by
  let e := finiteTraceResolventExtension G hG A hA m h f
  let eA := finiteTraceResolventFunction G hG A hA m h f
  let g := unweight m f
  have heL2 := finiteTraceResolventExtension_hasSpeedL2 G hG A hA m hm hmsum hh f hf
  have hgL2 := hasSpeedL2_unweight m hm f
  have hnorm : ‖weightedValue m e heL2 - f‖ ^ 2 =
      ∑' v, m v * (e v - g v) ^ 2 := by
    rw [← weightedValue_unweight m hm f]
    exact weightedValue_sub_norm_sq m hm e g heL2 hgL2
  have hfinite :
      ‖weightedValue (fun x : {v // v ∈ A} => m x.1) eA
          (parameterizedResolventFunction_hasSpeedL2
            (finiteTargetGraph G hG A hA) (fun x : {v // v ∈ A} => m x.1)
            (fun x => hm x.1) h (finiteTraceForcing A f)) - finiteTraceForcing A f‖ ^ 2 =
        ∑ v ∈ A, m v * (e v - g v) ^ 2 := by
    have hbase := finiteTrace_weighted_error_norm_sq A m hm f
      (parameterizedResolventFunction (finiteTargetGraph G hG A hA)
        (fun x : {v // v ∈ A} => m x.1) h (finiteTraceForcing A f))
      (parameterizedResolventFunction_hasSpeedL2
        (finiteTargetGraph G hG A hA) (fun x : {v // v ∈ A} => m x.1)
        (fun x => hm x.1) h (finiteTraceForcing A f))
    change ‖weightedValue (fun x : {v // v ∈ A} => m x.1)
        (finiteTraceResolventFunction G hG A hA m h f) _ -
          finiteTraceForcing A f‖ ^ 2 =
      ∑' x : {v // v ∈ A}, m x.1 * (eA x - g x.1) ^ 2 at hbase
    rw [hbase]
    rw [tsum_fintype]
    change (∑ x ∈ A.attach, m x.1 * (eA x - g x.1) ^ 2) = _
    calc
      (∑ x ∈ A.attach, m x.1 * (eA x - g x.1) ^ 2) =
          ∑ x ∈ A.attach, m x.1 * (e x.1 - g x.1) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxval := finiteTraceResolventExtension_eqOn G hG A hA m h f x.2
        change e x.1 = eA x at hxval
        rw [← hxval]
      _ = ∑ v ∈ A, m v * (e v - g v) ^ 2 :=
        Finset.sum_attach A (fun v => m v * (e v - g v) ^ 2)
  have herrSummable : Summable (fun v => m v * (e v - g v) ^ 2) := by
    have hs := lp.memℓp (weightedValue m e heL2 - weightedValue m g hgL2)
    have hs' := hs.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, lp.coeFn_sub, Pi.sub_apply,
      weightedValue_apply, Real.norm_eq_abs, sq_abs] at hs'
    exact hs'.congr (fun v => by
      rw [← mul_sub, mul_pow, Real.sq_sqrt (hm v).le])
  have hsplit := herrSummable.sum_add_tsum_subtype_compl A
  have houtside : (∑' v : {v // v ∉ A}, m v.1 * (e v.1 - g v.1) ^ 2) ≤
      ∑' v : {v // v ∉ A}, m v.1 := by
    have hmcomp : Summable (fun v : {v // v ∉ A} => m v.1) := hmsum.subtype _
    apply (herrSummable.subtype _).tsum_le_tsum
    · intro v
      have he := finiteTraceResolventExtension_mem_Icc G hG A hA m hm hh f hf v.1
      have hgv := hf v.1
      rcases he with ⟨he0, he1⟩
      rcases hgv with ⟨hg0, hg1⟩
      have hsquare : (e v.1 - g v.1) ^ 2 ≤ 1 := by nlinarith
      change m v.1 * (e v.1 - g v.1) ^ 2 ≤ m v.1
      simpa using mul_le_mul_of_nonneg_left hsquare (hm v.1).le
    · exact hmcomp
  rw [hnorm, hfinite]
  rw [← hsplit]
  exact add_le_add_right houtside _

/-- Quantitative comparison of the actual finite trace resolvent extension with
the actual full resolvent. -/
theorem finiteTraceResolventExtension_error_le_tail
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {h : ℝ} (hh : 0 < h) (f : ValueSpace V)
    (hf : ∀ v, unweight m f v ∈ Set.Icc (0 : ℝ) 1) :
    ‖weightedValue m
        (finiteTraceResolventExtension G hG A hA m h f -
          parameterizedResolventFunction G m h f)
        (finiteTraceResolventExtension_sub_resolvent_hasSpeedL2
          G hG A hA m hm hmsum hh f hf)‖ ^ 2 +
      h * G.Energy (finiteTraceResolventExtension G hG A hA m h f -
        parameterizedResolventFunction G m h f) ≤
      ∑' v : {v // v ∉ A}, m v.1 := by
  let e := finiteTraceResolventExtension G hG A hA m h f
  let u := parameterizedResolventFunction G m h f
  have heL2 := finiteTraceResolventExtension_hasSpeedL2 G hG A hA m hm hmsum hh f hf
  have heE := finiteTraceResolventExtension_hasFiniteEnergy G hG A hA m h f
  have huL2 := parameterizedResolventFunction_hasSpeedL2 G m hm h f
  have huE := parameterizedResolventFunction_hasFiniteEnergy G m h f
  let w := inHilbertDomain G m hm e heL2 heE
  let q := inHilbertDomain G m hm u huL2 huE
  have hcore := finiteTraceResolvent_extension_core_objective_le G hG A hA m hm hh f
  have htail := finiteTraceResolventExtension_weighted_error_le_tail
    G hG A hA m hm hmsum hh f hf
  have huweight := weightedValue_unweight m hm (parameterizedResolvent G m h f)
  change weightedValue m u huL2 = parameterizedResolvent G m h f at huweight
  have hobj : parameterizedResolventObjective G m h f w ≤
      parameterizedResolventObjective G m h f q + ∑' v : {v // v ∉ A}, m v.1 := by
    rw [parameterizedResolventObjective_inHilbertDomain,
      parameterizedResolventObjective_inHilbertDomain]
    calc
      ‖weightedValue m e heL2 - f‖ ^ 2 + h * G.Energy e ≤
          (‖weightedValue (fun x : {v // v ∈ A} => m x.1)
              (finiteTraceResolventFunction G hG A hA m h f)
              (parameterizedResolventFunction_hasSpeedL2
                (finiteTargetGraph G hG A hA) (fun x : {v // v ∈ A} => m x.1)
                (fun x => hm x.1) h (finiteTraceForcing A f)) -
              finiteTraceForcing A f‖ ^ 2 +
            ∑' v : {v // v ∉ A}, m v.1) + h * G.Energy e :=
        by linarith [htail]
      _ = (‖weightedValue (fun x : {v // v ∈ A} => m x.1)
              (finiteTraceResolventFunction G hG A hA m h f)
              (parameterizedResolventFunction_hasSpeedL2
                (finiteTargetGraph G hG A hA) (fun x : {v // v ∈ A} => m x.1)
                (fun x => hm x.1) h (finiteTraceForcing A f)) -
              finiteTraceForcing A f‖ ^ 2 + h * G.Energy e) +
            ∑' v : {v // v ∉ A}, m v.1 := by ring
      _ ≤ (‖weightedValue m u huL2 - f‖ ^ 2 + h * G.Energy u) +
            ∑' v : {v // v ∉ A}, m v.1 := by
        rw [huweight]
        linarith [hcore]
  have hs := parameterizedResolventObjective_eq_min_add_squares G m hm hh f w
  change parameterizedResolventObjective G m h f w =
      parameterizedResolventObjective G m h f q +
        ‖valueInclusion G m (w - q)‖ ^ 2 +
          h * ‖gradientInclusion G m (w - q)‖ ^ 2 at hs
  have hv : valueInclusion G m (w - q) =
      weightedValue m (e - u)
        (finiteTraceResolventExtension_sub_resolvent_hasSpeedL2
          G hG A hA m hm hmsum hh f hf) := by
    ext v
    simp [w, q, e, u, weightedValue_apply]
    ring
  have hg : ‖gradientInclusion G m (w - q)‖ ^ 2 = G.Energy (e - u) := by
    rw [map_sub]
    change ‖weightedGradient G e heE - weightedGradient G u huE‖ ^ 2 = _
    have heq : weightedGradient G e heE - weightedGradient G u huE =
        weightedGradient G (e - u) (heE.sub huE) := by
      ext p
      simp [weightedGradient_apply]
      ring
    rw [heq, weightedGradient_norm_sq]
  rw [hv, hg] at hs
  linarith

end ReflectedGMS.FullNetworkForm
