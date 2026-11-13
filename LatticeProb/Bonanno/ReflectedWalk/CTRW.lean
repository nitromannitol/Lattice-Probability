/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.CTRW at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.ApproximatingChain
import LatticeProb.Bonanno.ReflectedWalk.Theorem16Statement
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The Markov property of a continuous-time random walk
(Gwynne–Sung, arXiv:2506.18827, Section 3.4, proof of property (iv), p. 25)

The paper's verification of property (iv) of Theorem 1.6 for the constructed process `X`
starts from "each `Xⁿ` is a continuous time random walk, so the Markov property of continuous
time random walk implies that … on the event `{Xⁿ_t = x}`, the `P_z`-conditional law of
`{Xⁿ_{s+t}}_{s ≥ 0}` given `{Xⁿ_s}_{s ≤ t}` is the same as the `P_x`-law of `{Xⁿ_s}_{s ≥ 0}`".
Mathlib has no continuous-time Markov chains and no memorylessness for the exponential law, so
this file proves that statement from scratch, for the *generic* continuous-time random walk of
(3.15):

* the skeleton `Y : ℕ → V` is a Markov chain with one-step kernel `κ`
  (`MarkovChain.chainLaw κ z`), and the unit holding times `e : ℕ → ℝ` are an independent
  i.i.d. `Exponential(1)` sequence (`unitTimes`);
* the clock is `S_k := ∑_{i<k} e_i / w(Y_i)` (`clock`) and the walk is `X_t := Y_k` for
  `t ∈ [S_k, S_{k+1})` (`ctrw`), exactly the shape of `PathProperties.Xn`.

The proof is the textbook one, made explicit because nothing in mathlib supplies it:
on `{X_t = x}` the walk is in its `j`-th holding interval for a unique `j`; the past
`{X_s}_{s ≤ t}` is a function of `(Y_0, …, Y_j, e_0, …, e_{j-1})`; the future is the walk built
from the shifted skeleton `(Y_{j+k})_k` and the holding times `(e_j − c, e_{j+1}, e_{j+2}, …)`,
where `c = (t − S_j)·w(x)` is the elapsed unit time; **memorylessness** of `Exponential(1)`
(`expMeasure_one_restrict_map_sub`) makes `e_j − c` again `Exponential(1)` given `e_j > c`, and
the **Markov property of the skeleton at the deterministic time `j`**
(`lintegral_mul_walkShift`, from the restart identity of `ApproximatingChain.lean`) makes the
shifted skeleton a fresh chain from `x`.  Summing over `j` gives property (iv)
(`markovProperty`), in the joint-law form of `Theorem16Statement.lean`.

`MarkovProperty.lean` transfers this to the processes `Xⁿ` of (3.15) under the paper's `P_z`
and passes to the limit `n → ∞` (Lemma 3.8).
-/

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal NNReal

universe u

namespace ReflectedWalk

namespace CTRW

/-- `Exponential(1)` is a probability measure (also declared in `RateFunction.lean`, which
this file does not import). -/
instance instIsProbabilityMeasureExpMeasureOne' : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-! ### Memorylessness of `Exponential(1)` -/

/-- **Memorylessness** of the exponential law (the input of the Markov property of a
continuous-time random walk): the image of `Exponential(1)` restricted to `(c, ∞)` under
`r ↦ r − c` is `e^{−c} · Exponential(1)`, i.e. conditionally on `{E > c}` the residual `E − c`
is again `Exponential(1)`. -/
lemma expMeasure_one_restrict_map_sub {c : ℝ} (hc : 0 ≤ c) :
    ((expMeasure 1).restrict (Set.Ioi c)).map (fun r => r - c) =
      ENNReal.ofReal (Real.exp (-c)) • expMeasure 1 := by
  have hm : Measurable fun r : ℝ => r - c := measurable_id.sub_const c
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [Measure.map_apply hm measurableSet_Iic, Measure.restrict_apply (hm measurableSet_Iic),
    Measure.smul_apply, smul_eq_mul]
  have hcdf : ∀ x : ℝ, expMeasure 1 (Set.Iic x) =
      ENNReal.ofReal (if 0 ≤ x then 1 - Real.exp (-x) else 0) := by
    intro x
    rw [← ofReal_cdf, cdf_expMeasure_eq one_pos, one_mul]
  have e : (fun r : ℝ => r - c) ⁻¹' Set.Iic a ∩ Set.Ioi c = Set.Iic (a + c) \ Set.Iic c := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioi, Set.mem_diff,
      not_le]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, h2⟩
  by_cases ha : 0 ≤ a
  · rw [e, measure_diff (Set.Iic_subset_Iic.mpr (by linarith)) measurableSet_Iic.nullMeasurableSet
      (measure_ne_top _ _), hcdf, hcdf, hcdf, ite_eq_left ha, ite_eq_left (by linarith), ite_eq_left hc]
    have h1 : 0 ≤ 1 - Real.exp (-c) := by
      rw [sub_nonneg]
      exact Real.exp_le_one_iff.mpr (by linarith)
    rw [← ENNReal.ofReal_sub _ h1, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [neg_add, Real.exp_add]
    ring
  · have e' : (fun r : ℝ => r - c) ⁻¹' Set.Iic a ∩ Set.Ioi c = ∅ := by
      rw [e, Set.diff_eq_empty]
      exact Set.Iic_subset_Iic.mpr (by linarith)
    rw [e', measure_empty, hcdf, ite_eq_right ha, ENNReal.ofReal_zero, mul_zero]

/-- Memorylessness in integral form: `∫ 1_{r > c} g(r − c) dExp(1)(r) = e^{−c} ∫ g dExp(1)`. -/
lemma lintegral_expMeasure_one_indicator_sub {c : ℝ} (hc : 0 ≤ c) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ r, (Set.Ioi c).indicator (fun r => g (r - c)) r ∂expMeasure 1 =
      ENNReal.ofReal (Real.exp (-c)) * ∫⁻ r, g r ∂expMeasure 1 := by
  have hm : Measurable fun r : ℝ => r - c := measurable_id.sub_const c
  rw [lintegral_indicator measurableSet_Ioi, ← lintegral_map hg hm,
    expMeasure_one_restrict_map_sub hc, lintegral_smul_measure, smul_eq_mul]

/-! ### The i.i.d. `Exponential(1)` unit holding times along one level -/

/-- The law of the unit holding times `(e_i)_{i ≥ 0}` of one level: an i.i.d. `Exponential(1)`
sequence (Section 3.3, "conditionally independent … `T_ξ ~ Exponential(w(Y_ξ))`", before the
scaling by `w`). -/
noncomputable def unitTimes : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => expMeasure 1

instance unitTimes_isProbabilityMeasure : IsProbabilityMeasure unitTimes := by
  unfold unitTimes
  infer_instance

/-- Re-indexing an i.i.d. family along an injective map gives an i.i.d. family with the same
marginal. -/
lemma infinitePi_map_comp_injective {ι κ X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {f : ι → κ} (hf : Function.Injective f) :
    (Measure.infinitePi fun _ : κ => μ).map (fun e => e ∘ f) =
      Measure.infinitePi fun _ : ι => μ := by
  classical
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  have hm : Measurable fun e : κ → X => e ∘ f :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (f i)
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have e : (fun e : κ → X => e ∘ f) ⁻¹' Set.pi (↑s) t =
      Set.pi (↑(s.map ⟨f, hf⟩)) (Function.extend f t fun _ => Set.univ) := by
    ext e
    constructor
    · intro he
      refine Set.mem_pi.mpr fun j hj => ?_
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hj)
      show e (f i) ∈ Function.extend f t (fun _ => Set.univ) (f i)
      rw [hf.extend_apply]
      exact Set.mem_pi.mp he i (Finset.mem_coe.mpr hi)
    · intro he
      refine Set.mem_pi.mpr fun i hi => ?_
      have := Set.mem_pi.mp he (f i)
        (Finset.mem_coe.mpr (Finset.mem_map_of_mem (⟨f, hf⟩ : ι ↪ κ) (Finset.mem_coe.mp hi)))
      rwa [hf.extend_apply] at this
  rw [e, Measure.infinitePi_pi, Finset.prod_map]
  · refine Finset.prod_congr rfl fun i _ => ?_
    show μ (Function.extend f t (fun _ => Set.univ) (f i)) = μ (t i)
    rw [hf.extend_apply]
  · intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hj
    show MeasurableSet (Function.extend f t (fun _ => Set.univ) (f i))
    rw [hf.extend_apply]
    exact ht i

/-- The shift `(e_{k+i})_i` of the i.i.d. sequence is again i.i.d. `Exponential(1)`. -/
lemma unitTimes_map_walkShift (k : ℕ) : unitTimes.map (MarkovChain.walkShift k) = unitTimes :=
  infinitePi_map_comp_injective (expMeasure 1) (add_right_injective k)

/-- The coordinates of `unitTimes` are independent. -/
lemma iIndepFun_eval_unitTimes : iIndepFun (fun (i : ℕ) (e : ℕ → ℝ) => e i) unitTimes := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map fun i => measurable_pi_apply i]
  simp only [unitTimes, Measure.infinitePi_map_eval]
  exact Measure.map_id

set_option warn.classDefReducibility false in
/-- The σ-algebra generated by the coordinates with index in `S`. -/
def blockSigma (S : Set ℕ) : MeasurableSpace (ℕ → ℝ) :=
  ⨆ i ∈ S, MeasurableSpace.comap (fun e : ℕ → ℝ => e i) inferInstance

lemma measurable_eval_blockSigma {S : Set ℕ} {i : ℕ} (hi : i ∈ S) :
    Measurable[blockSigma S] fun e : ℕ → ℝ => e i :=
  Measurable.mono (measurable_iff_comap_le.mpr le_rfl)
    (le_iSup_of_le i (le_iSup_of_le hi le_rfl)) le_rfl

/-- Functions of disjoint blocks of coordinates are independent under `unitTimes`. -/
lemma indepFun_of_disjoint {S T : Set ℕ} (hST : Disjoint S T) {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {f : (ℕ → ℝ) → α} {g : (ℕ → ℝ) → β}
    (hf : Measurable[blockSigma S] f) (hg : Measurable[blockSigma T] g) :
    IndepFun f g unitTimes := by
  have hind : iIndep (fun i : ℕ => MeasurableSpace.comap (fun e : ℕ → ℝ => e i) inferInstance)
      unitTimes := iIndepFun_eval_unitTimes.iIndep
  have hle : ∀ i : ℕ, MeasurableSpace.comap (fun e : ℕ → ℝ => e i) inferInstance ≤
      (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
    fun i => measurable_iff_comap_le.mp (measurable_pi_apply i)
  have h := indep_iSup_of_disjoint hle hind hST
  change Indep (MeasurableSpace.comap _ _) (MeasurableSpace.comap _ _) unitTimes
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left h (measurable_iff_comap_le.mp hf))
    (measurable_iff_comap_le.mp hg)

/-- The coordinates `< j` of a sequence, the others set to `0`. -/
def trunc (j : ℕ) (e : ℕ → ℝ) : ℕ → ℝ := fun i => if i < j then e i else 0

/-- The coordinates `≥ j` of a sequence, the others set to `0`. -/
def tail (j : ℕ) (e : ℕ → ℝ) : ℕ → ℝ := fun i => if j ≤ i then e i else 0

/-- Reassembling a sequence from its coordinates `< j`, its coordinate `j` and its
coordinates `> j` (the latter shifted down by `j + 1`). -/
def glue (j : ℕ) (a : ℕ → ℝ) (r : ℝ) (e : ℕ → ℝ) : ℕ → ℝ :=
  fun i => if i < j then a i else if i = j then r else e (i - (j + 1))

lemma trunc_apply_of_lt {j i : ℕ} (hi : i < j) (e : ℕ → ℝ) : trunc j e i = e i := ite_eq_left hi

lemma glue_apply_of_lt {j i : ℕ} (hi : i < j) (a : ℕ → ℝ) (r : ℝ) (e : ℕ → ℝ) :
    glue j a r e i = a i := ite_eq_left hi

lemma glue_apply_self (j : ℕ) (a : ℕ → ℝ) (r : ℝ) (e : ℕ → ℝ) : glue j a r e j = r := by
  simp [glue]

lemma walkShift_succ_glue (j : ℕ) (a : ℕ → ℝ) (r : ℝ) (e : ℕ → ℝ) :
    MarkovChain.walkShift (j + 1) (glue j a r e) = e := by
  funext i
  simp only [MarkovChain.walkShift_apply, glue]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  congr 1
  omega

lemma glue_trunc (j : ℕ) (a : ℕ → ℝ) (r : ℝ) (e : ℕ → ℝ) :
    glue j (trunc j a) r e = glue j a r e := by
  funext i
  simp only [glue, trunc]
  split_ifs <;> rfl

lemma glue_trunc_self (j : ℕ) (e : ℕ → ℝ) :
    glue j (trunc j e) (e j) (MarkovChain.walkShift (j + 1) e) = e := by
  funext i
  simp only [glue, trunc, MarkovChain.walkShift_apply]
  by_cases h1 : i < j
  · rw [ite_eq_left h1, ite_eq_left h1]
  · rw [ite_eq_right h1]
    by_cases h2 : i = j
    · rw [ite_eq_left h2, h2]
    · rw [ite_eq_right h2]
      congr 1
      omega

lemma measurable_trunc (j : ℕ) : Measurable (trunc j) := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases hi : i < j
  · simp only [trunc, ite_eq_left hi]
    exact measurable_pi_apply i
  · simp only [trunc, ite_eq_right hi]
    exact measurable_const

lemma measurable_glue (j : ℕ) :
    Measurable fun p : (ℕ → ℝ) × ℝ × (ℕ → ℝ) => glue j p.1 p.2.1 p.2.2 := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h1 : i < j
  · simp only [glue, ite_eq_left h1]
    exact (measurable_pi_apply i).comp measurable_fst
  · by_cases h2 : i = j
    · simp only [glue, ite_eq_right h1, ite_eq_left h2]
      exact measurable_fst.comp measurable_snd
    · simp only [glue, ite_eq_right h1, ite_eq_right h2]
      exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)

lemma measurable_trunc_blockSigma (j : ℕ) : Measurable[blockSigma (Set.Iio j)] (trunc j) := by
  refine (@measurable_pi_iff (ℕ → ℝ) ℕ (fun _ => ℝ) (blockSigma (Set.Iio j)) _ _).mpr
    fun i => ?_
  by_cases hi : i < j
  · have e : (fun e : ℕ → ℝ => trunc j e i) = fun e => e i := funext fun e => ite_eq_left hi
    rw [e]
    exact measurable_eval_blockSigma (Set.mem_Iio.mpr hi)
  · have e : (fun e : ℕ → ℝ => trunc j e i) = fun _ => 0 := funext fun e => ite_eq_right hi
    rw [e]
    exact measurable_const

lemma measurable_tail_blockSigma (j : ℕ) : Measurable[blockSigma (Set.Ici j)] (tail j) := by
  refine (@measurable_pi_iff (ℕ → ℝ) ℕ (fun _ => ℝ) (blockSigma (Set.Ici j)) _ _).mpr
    fun i => ?_
  by_cases hi : j ≤ i
  · have e : (fun e : ℕ → ℝ => tail j e i) = fun e => e i := funext fun e => ite_eq_left hi
    rw [e]
    exact measurable_eval_blockSigma (Set.mem_Ici.mpr hi)
  · have e : (fun e : ℕ → ℝ => tail j e i) = fun _ => 0 := funext fun e => ite_eq_right hi
    rw [e]
    exact measurable_const

lemma measurable_walkShift_blockSigma (k : ℕ) :
    Measurable[blockSigma (Set.Ici k)] (MarkovChain.walkShift (S := ℝ) k) :=
  (@measurable_pi_iff (ℕ → ℝ) ℕ (fun _ => ℝ) (blockSigma (Set.Ici k)) _ _).mpr
    fun i => measurable_eval_blockSigma (Set.mem_Ici.mpr (Nat.le_add_right k i))

/-- The coordinate `e_j` and the shifted sequence `(e_{j+1+i})_i` are independent, with laws
`Exponential(1)` and `unitTimes`. -/
lemma unitTimes_map_eval_walkShift (j : ℕ) :
    unitTimes.map (fun e => (e j, MarkovChain.walkShift (j + 1) e)) =
      (expMeasure 1).prod unitTimes := by
  have hind : IndepFun (fun e : ℕ → ℝ => e j) (MarkovChain.walkShift (j + 1)) unitTimes :=
    indepFun_of_disjoint (S := {j}) (T := Set.Ici (j + 1))
      (Set.disjoint_singleton_left.mpr (by simp))
      (measurable_eval_blockSigma (Set.mem_singleton j)) (measurable_walkShift_blockSigma (j + 1))
  rw [hind.map_prod_eq_prod_map_map (measurable_pi_apply j).aemeasurable
    (MarkovChain.measurable_walkShift (j + 1)).aemeasurable, unitTimes_map_walkShift]
  congr 1
  exact Measure.infinitePi_map_eval _ _

lemma measurable_consPath_uncurry :
    Measurable fun q : ℝ × (ℕ → ℝ) => MarkovChain.consPath q.1 q.2 := by
  refine measurable_pi_iff.mpr fun k => ?_
  cases k with
  | zero => exact measurable_fst
  | succ k => exact (measurable_pi_apply k).comp measurable_snd

lemma measurable_consPath_left (r : ℝ) :
    Measurable fun e : ℕ → ℝ => MarkovChain.consPath r e := by
  refine measurable_pi_iff.mpr fun k => ?_
  cases k with
  | zero => exact measurable_const
  | succ k => exact measurable_pi_apply k

/-- `unitTimes` is the law of `(r, e_0, e_1, …)` for `r ~ Exponential(1)` independent of
`e ~ unitTimes`. -/
lemma unitTimes_eq_map_consPath :
    unitTimes = ((expMeasure 1).prod unitTimes).map
      (fun q : ℝ × (ℕ → ℝ) => MarkovChain.consPath q.1 q.2) := by
  have h := unitTimes_map_eval_walkShift 0
  simp only [Nat.zero_add] at h
  rw [← h, Measure.map_map measurable_consPath_uncurry
    ((measurable_pi_apply 0).prodMk (MarkovChain.measurable_walkShift 1))]
  symm
  convert Measure.map_id using 2
  funext e
  exact MarkovChain.consPath_walkShift e

/-- The integral form of `unitTimes_eq_map_consPath`. -/
lemma lintegral_unitTimes_consPath {G : (ℕ → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ r, ∫⁻ e, G (MarkovChain.consPath r e) ∂unitTimes ∂expMeasure 1 =
      ∫⁻ e, G e ∂unitTimes := by
  conv_rhs => rw [unitTimes_eq_map_consPath, lintegral_map hG measurable_consPath_uncurry,
    lintegral_prod (fun q : ℝ × (ℕ → ℝ) => G (MarkovChain.consPath q.1 q.2))
      (hG.comp measurable_consPath_uncurry).aemeasurable]

/-- **The decomposition of the i.i.d. sequence at index `j`**: `unitTimes` is the law of
`glue j a r e` for independent `a ~ unitTimes` (only its coordinates `< j` are used),
`r ~ Exponential(1)` and `e ~ unitTimes`. -/
lemma unitTimes_eq_map_glue (j : ℕ) :
    unitTimes = (unitTimes.prod ((expMeasure 1).prod unitTimes)).map
      (fun p : (ℕ → ℝ) × ℝ × (ℕ → ℝ) => glue j p.1 p.2.1 p.2.2) := by
  have hF : Measurable fun e : ℕ → ℝ => (e j, MarkovChain.walkShift (j + 1) e) :=
    (measurable_pi_apply j).prodMk (MarkovChain.measurable_walkShift (j + 1))
  have hind : IndepFun (trunc j) (tail j) unitTimes :=
    indepFun_of_disjoint (S := Set.Iio j) (T := Set.Ici j)
      (Set.disjoint_left.mpr fun i (hi : i < j) (hi' : j ≤ i) => absurd hi' (not_le.mpr hi))
      (measurable_trunc_blockSigma j) (measurable_tail_blockSigma j)
  have hpair : (fun e : ℕ → ℝ => (e j, MarkovChain.walkShift (j + 1) e)) =
      (fun e : ℕ → ℝ => (e j, MarkovChain.walkShift (j + 1) e)) ∘ tail j := by
    funext e
    refine Prod.ext ?_ ?_
    · show e j = tail j e j
      simp [tail]
    · funext i
      show e (j + 1 + i) = tail j e (j + 1 + i)
      simp only [tail]
      rw [ite_eq_left (by omega)]
  have hind' : IndepFun (trunc j) (fun e : ℕ → ℝ => (e j, MarkovChain.walkShift (j + 1) e))
      unitTimes := by
    rw [hpair]
    exact hind.comp measurable_id hF
  have h1 : unitTimes.map (fun e => (trunc j e, (e j, MarkovChain.walkShift (j + 1) e))) =
      (unitTimes.map (trunc j)).prod ((expMeasure 1).prod unitTimes) := by
    rw [hind'.map_prod_eq_prod_map_map (measurable_trunc j).aemeasurable hF.aemeasurable,
      unitTimes_map_eval_walkShift]
  have h2 : unitTimes = unitTimes.map
      ((fun p : (ℕ → ℝ) × ℝ × (ℕ → ℝ) => glue j p.1 p.2.1 p.2.2) ∘
        (fun e => (trunc j e, (e j, MarkovChain.walkShift (j + 1) e)))) := by
    conv_lhs => rw [← Measure.map_id (μ := unitTimes)]
    congr 1
    funext e
    exact (glue_trunc_self j e).symm
  have h3 : (unitTimes.map (trunc j)).prod ((expMeasure 1).prod unitTimes) =
      (unitTimes.prod ((expMeasure 1).prod unitTimes)).map (Prod.map (trunc j) id) := by
    rw [← Measure.map_prod_map _ _ (measurable_trunc j) measurable_id, Measure.map_id]
  conv_lhs => rw [h2]
  rw [← Measure.map_map (measurable_glue j) ((measurable_trunc j).prodMk hF), h1, h3,
    Measure.map_map (measurable_glue j) ((measurable_trunc j).prodMap measurable_id)]
  congr 1
  funext p
  exact glue_trunc j p.1 p.2.1 p.2.2

/-- The integral form of `unitTimes_eq_map_glue`. -/
lemma lintegral_unitTimes_glue (j : ℕ) {F : (ℕ → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ e, F e ∂unitTimes =
      ∫⁻ a, ∫⁻ r, ∫⁻ e, F (glue j a r e) ∂unitTimes ∂expMeasure 1 ∂unitTimes := by
  conv_lhs => rw [unitTimes_eq_map_glue j]
  rw [lintegral_map hF (measurable_glue j),
    lintegral_prod (fun p : (ℕ → ℝ) × ℝ × (ℕ → ℝ) => F (glue j p.1 p.2.1 p.2.2))
      (hF.comp (measurable_glue j)).aemeasurable]
  refine lintegral_congr fun a => ?_
  rw [lintegral_prod (fun q : ℝ × (ℕ → ℝ) => F (glue j a q.1 q.2))
    ((hF.comp (measurable_glue j)).comp measurable_prodMk_left).aemeasurable]

/-! ### The Markov property of the skeleton at a deterministic time, integral form -/

section skeleton

variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] (κ : Kernel S S)
  [IsMarkovKernel κ]

/-- A path extending a finite history `h` of length `j`: `h` up to time `j`, constant
afterwards. -/
def extendPath (j : ℕ) (h : Finset.Iic j → S) : ℕ → S :=
  fun i => if hi : i ≤ j then h ⟨i, Finset.mem_Iic.mpr hi⟩ else h ⟨j, Finset.mem_Iic.mpr le_rfl⟩

lemma frestrictLe_extendPath (j : ℕ) (h : Finset.Iic j → S) :
    frestrictLe j (extendPath j h) = h := by
  funext ⟨i, hi⟩
  simp [extendPath, frestrictLe_apply, Finset.mem_Iic.mp hi]

lemma measurable_extendPath (j : ℕ) : Measurable (extendPath (S := S) j) := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases hi : i ≤ j
  · simp only [extendPath, hi, dite_true]
    exact measurable_pi_apply _
  · simp only [extendPath, hi, dite_false]
    exact measurable_pi_apply _

/-- **The Markov property of the chain at the deterministic time `j`, integral form**: for
`f` depending only on `Y_0, …, Y_j` and any `g ≥ 0`,
`E_z[f(Y) g(θ_j Y)] = E_z[f(Y) · E_{Y_j}[g]]`.  From the restart identity
`MarkovChain.chainLaw_eq_traj_comp_prefix` and `MarkovChain.continuation_walkShift_law`. -/
lemma lintegral_mul_walkShift (z : S) (j : ℕ) {f : (ℕ → S) → ℝ≥0∞} (hf : Measurable f)
    (hf' : ∀ Y Y', frestrictLe j Y = frestrictLe j Y' → f Y = f Y')
    {g : (ℕ → S) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ Y, f Y * g (MarkovChain.walkShift j Y) ∂MarkovChain.chainLaw κ z =
      ∫⁻ Y, f Y * ∫⁻ Y', g Y' ∂MarkovChain.chainLaw κ (Y j) ∂MarkovChain.chainLaw κ z := by
  have hGm : Measurable fun x : S => ∫⁻ Y', g Y' ∂MarkovChain.chainLaw κ x := by
    have e : (fun x : S => ∫⁻ Y', g Y' ∂MarkovChain.chainLaw κ x) =
        fun x => ∫⁻ Y', (fun q : S × (ℕ → S) => g q.2) (x, Y') ∂MarkovChain.pathKernel κ x := by
      funext x
      rw [MarkovChain.pathKernel_apply]
    rw [e]
    exact Measurable.lintegral_kernel_prod_right' (hg.comp measurable_snd)
  have key : ∀ h : Finset.Iic j → S,
      ∫⁻ Y, f Y * g (MarkovChain.walkShift j Y)
          ∂(Kernel.traj (X := fun _ => S) (MarkovChain.histKernel κ) j h) =
        f (extendPath j h) * ∫⁻ Y', g Y' ∂MarkovChain.chainLaw κ (MarkovChain.lastCoord j h) := by
    intro h
    have hae : ∀ᵐ Y ∂(Kernel.traj (X := fun _ => S) (MarkovChain.histKernel κ) j h),
        frestrictLe j Y = h := by
      rw [ae_iff]
      have e : {Y : ℕ → S | ¬ frestrictLe j Y = h} =
          (frestrictLe j ⁻¹' ({h} : Set (Finset.Iic j → S)))ᶜ := by
        ext Y
        simp
      rw [e]
      exact MarkovChain.traj_fiber_compl κ j h
    calc ∫⁻ Y, f Y * g (MarkovChain.walkShift j Y)
            ∂(Kernel.traj (X := fun _ => S) (MarkovChain.histKernel κ) j h)
        = ∫⁻ Y, f (extendPath j h) * g (MarkovChain.walkShift j Y)
            ∂(Kernel.traj (X := fun _ => S) (MarkovChain.histKernel κ) j h) := by
          refine lintegral_congr_ae (hae.mono fun Y hY => ?_)
          show f Y * g (MarkovChain.walkShift j Y) =
            f (extendPath j h) * g (MarkovChain.walkShift j Y)
          rw [hf' Y (extendPath j h) (by rw [hY, frestrictLe_extendPath])]
      _ = f (extendPath j h) * ∫⁻ Y, g (MarkovChain.walkShift j Y)
            ∂(Kernel.traj (X := fun _ => S) (MarkovChain.histKernel κ) j h) :=
          lintegral_const_mul _ (hg.comp (MarkovChain.measurable_walkShift j))
      _ = f (extendPath j h) * ∫⁻ Y', g Y' ∂MarkovChain.chainLaw κ (MarkovChain.lastCoord j h) := by
          rw [← lintegral_map hg (MarkovChain.measurable_walkShift j),
            MarkovChain.continuation_walkShift_law]
  conv_lhs => rw [MarkovChain.chainLaw_eq_traj_comp_prefix κ z j]
  rw [Measure.lintegral_bind (f := fun Y => f Y * g (MarkovChain.walkShift j Y))
    (Kernel.measurable _).aemeasurable
    (hf.mul (hg.comp (MarkovChain.measurable_walkShift j))).aemeasurable]
  simp_rw [key]
  rw [lintegral_map (f := fun h : Finset.Iic j → S =>
    f (extendPath j h) * ∫⁻ Y', g Y' ∂MarkovChain.chainLaw κ (MarkovChain.lastCoord j h))
    ((hf.comp (measurable_extendPath j)).mul
      (hGm.comp (MarkovChain.measurable_lastCoord j))) (measurable_frestrictLe j)]
  refine lintegral_congr fun Y => ?_
  rw [hf' (extendPath j (frestrictLe j Y)) Y (frestrictLe_extendPath j _)]
  rfl

end skeleton

/-! ### The continuous-time random walk (3.15) with a given skeleton and unit holding times -/

section ctrw

variable {V : Type u} (w : V → ℝ)

/-- The clock of (3.15): `S_k := ∑_{i<k} e_i / w(Y_i)`, the time of the `k`-th jump of the walk
with skeleton `Y` and unit holding times `e`. -/
noncomputable def clock (Y : ℕ → V) (e : ℕ → ℝ) (k : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range k, ENNReal.ofReal (e i / w (Y i))

section deterministic

variable (Y : ℕ → V) (e : ℕ → ℝ)

@[simp] lemma clock_zero : clock w Y e 0 = 0 := Finset.sum_range_zero _

lemma clock_succ (k : ℕ) :
    clock w Y e (k + 1) = clock w Y e k + ENNReal.ofReal (e k / w (Y k)) :=
  Finset.sum_range_succ _ _

lemma clock_mono : Monotone (clock w Y e) := by
  refine monotone_nat_of_le_succ fun k => ?_
  rw [clock_succ]
  exact le_self_add

lemma clock_ne_top (k : ℕ) : clock w Y e k ≠ ⊤ :=
  (ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top).ne

/-- The clock up to `k` depends only on the first `k` states and unit holding times. -/
lemma clock_congr {Y' : ℕ → V} {e' : ℕ → ℝ} {k : ℕ} (hY : ∀ i < k, Y i = Y' i)
    (he : ∀ i < k, e i = e' i) : clock w Y e k = clock w Y' e' k :=
  Finset.sum_congr rfl fun i hi => by
    rw [hY i (Finset.mem_range.mp hi), he i (Finset.mem_range.mp hi)]

/-- `t ∈ [S_k, S_{k+1})`: the walk is in its `k`-th holding interval at time `t`. -/
def InHold (k : ℕ) (t : ℝ≥0) : Prop :=
  clock w Y e k ≤ t ∧ (t : ℝ≥0∞) < clock w Y e (k + 1)

lemma inHold_unique {k k' : ℕ} {t : ℝ≥0} (h1 : InHold w Y e k t) (h2 : InHold w Y e k' t) :
    k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd (lt_of_lt_of_le h1.2 (le_trans (clock_mono w Y e hlt) h2.1)) (lt_irrefl _)
  · exact absurd (lt_of_lt_of_le h2.2 (le_trans (clock_mono w Y e hlt) h1.1)) (lt_irrefl _)

lemma inHold_congr {Y' : ℕ → V} {e' : ℕ → ℝ} {k : ℕ} {t : ℝ≥0} (hY : ∀ i ≤ k, Y i = Y' i)
    (he : ∀ i ≤ k, e i = e' i) : InHold w Y e k t ↔ InHold w Y' e' k t := by
  show (clock w Y e k ≤ t ∧ (t : ℝ≥0∞) < clock w Y e (k + 1)) ↔ _
  rw [clock_congr w Y e (fun i hi => hY i hi.le) (fun i hi => he i hi.le),
    clock_congr w Y e (k := k + 1) (fun i hi => hY i (Nat.lt_succ_iff.mp hi))
      (fun i hi => he i (Nat.lt_succ_iff.mp hi))]
  exact Iff.rfl

open Classical in
/-- **(3.15)**: the continuous-time random walk with skeleton `Y` and unit holding times `e`:
`X_t := Y_k` for `t ∈ [S_k, S_{k+1})`, and `∞` (`none`) if `t` lies in no holding interval. -/
noncomputable def ctrw (t : ℝ≥0) : Option V :=
  if h : ∃ k, InHold w Y e k t then some (Y (Classical.choose h)) else none

lemma ctrw_eq_of_inHold {k : ℕ} {t : ℝ≥0} (hk : InHold w Y e k t) :
    ctrw w Y e t = some (Y k) := by
  unfold ctrw
  rw [dite_eq_left ⟨k, hk⟩]
  exact congrArg (fun k => some (Y k))
    (inHold_unique w Y e (Classical.choose_spec (⟨k, hk⟩ : ∃ k, InHold w Y e k t)) hk)

lemma ctrw_eq_none_iff (t : ℝ≥0) : ctrw w Y e t = none ↔ ¬ ∃ k, InHold w Y e k t := by
  unfold ctrw
  split_ifs with hx <;> simp [hx]

lemma ctrw_eq_some_iff (t : ℝ≥0) (x : V) :
    ctrw w Y e t = some x ↔ ∃ k, InHold w Y e k t ∧ Y k = x := by
  constructor
  · intro ht
    obtain ⟨k, hk⟩ : ∃ k, InHold w Y e k t := by
      by_contra hn
      rw [(ctrw_eq_none_iff w Y e t).mpr hn] at ht
      exact absurd ht (by simp)
    rw [ctrw_eq_of_inHold w Y e hk] at ht
    exact ⟨k, hk, Option.some_injective V ht⟩
  · rintro ⟨k, hk, rfl⟩
    exact ctrw_eq_of_inHold w Y e hk

/-- Two walks agree at given times as soon as their holding-interval descriptions agree. -/
lemma ctrw_congr {Y' : ℕ → V} {e' : ℕ → ℝ} {t t' : ℝ≥0}
    (h : ∀ x, (∃ k, InHold w Y e k t ∧ Y k = x) ↔ ∃ k, InHold w Y' e' k t' ∧ Y' k = x) :
    ctrw w Y e t = ctrw w Y' e' t' := by
  rcases hc : ctrw w Y' e' t' with _ | x
  · rw [ctrw_eq_none_iff] at hc ⊢
    rintro ⟨k, hk⟩
    obtain ⟨k', hk', -⟩ := (h (Y k)).mp ⟨k, hk, rfl⟩
    exact hc ⟨k', hk'⟩
  · rw [ctrw_eq_some_iff] at hc ⊢
    exact (h x).mpr hc

/-- The elapsed unit time at the current state `x` at time `t` in the `j`-th holding interval:
`c := (t − S_j)·w(x)`. -/
noncomputable def elapsed (t : ℝ≥0) (x : V) (j : ℕ) : ℝ :=
  ((t : ℝ) - (clock w Y e j).toReal) * w x

/-- The unit holding times of the future after time `t` in the `j`-th holding interval: the
residual `e_j − c` of the current one, then `e_{j+1}, e_{j+2}, …`. -/
noncomputable def futureTimes (t : ℝ≥0) (x : V) (j : ℕ) : ℕ → ℝ :=
  MarkovChain.consPath (e j - elapsed w Y e t x j) (MarkovChain.walkShift (j + 1) e)

/-- `S_j ≤ t` in real terms. -/
lemma toReal_le_of_clock_le {t : ℝ≥0} {j : ℕ} (hj : clock w Y e j ≤ t) :
    (clock w Y e j).toReal ≤ t := by
  have := (ENNReal.toReal_le_toReal (clock_ne_top w Y e j) ENNReal.coe_ne_top).mpr hj
  rwa [ENNReal.coe_toReal] at this

/-- On `{S_j ≤ t, Y_j = x}`, the condition `t < S_{j+1}` reads `c < e_j` with `c` the elapsed
unit time. -/
lemma lt_clock_succ_iff {t : ℝ≥0} {x : V} {j : ℕ} (hx : Y j = x) (hw : 0 < w x)
    (hj : clock w Y e j ≤ t) :
    (t : ℝ≥0∞) < clock w Y e (j + 1) ↔ elapsed w Y e t x j < e j := by
  have hτ : clock w Y e j = ENNReal.ofReal (clock w Y e j).toReal :=
    (ENNReal.ofReal_toReal (clock_ne_top w Y e j)).symm
  have hτT : (clock w Y e j).toReal ≤ t := toReal_le_of_clock_le w Y e hj
  rw [clock_succ, hx, elapsed, ← lt_div_iff₀ hw, sub_lt_iff_lt_add']
  conv_lhs => rw [hτ, ← ENNReal.ofReal_coe_nnreal]
  by_cases hq : e j / w x ≤ 0
  · rw [ENNReal.ofReal_eq_zero.mpr hq, add_zero,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (NNReal.coe_nonneg t)]
    constructor
    · intro h
      exact absurd (lt_of_le_of_lt hτT h) (lt_irrefl _)
    · intro h
      exact absurd (lt_of_le_of_lt hτT (lt_of_lt_of_le h (by linarith))) (lt_irrefl _)
  · rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg (not_le.mp hq).le,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (NNReal.coe_nonneg t)]

/-- The clock of the future walk: `S'_{k+1} = S_{j+1+k} − t`. -/
lemma clock_futureTimes_succ {t : ℝ≥0} {x : V} {j : ℕ} (hx : Y j = x) (hw : 0 < w x)
    (hj : clock w Y e j ≤ t) (hlt : (t : ℝ≥0∞) < clock w Y e (j + 1)) (k : ℕ) :
    clock w (MarkovChain.walkShift j Y) (futureTimes w Y e t x j) (k + 1) =
      clock w Y e (j + 1 + k) - t := by
  induction k with
  | zero =>
    rw [clock_succ, clock_zero, zero_add, Nat.add_zero]
    simp only [futureTimes, MarkovChain.consPath_zero, MarkovChain.walkShift_apply, Nat.add_zero,
      hx]
    rw [clock_succ, hx]
    have hc : elapsed w Y e t x j < e j := (lt_clock_succ_iff w Y e hx hw hj).mp hlt
    have hτT : (clock w Y e j).toReal ≤ t := toReal_le_of_clock_le w Y e hj
    have hc0 : 0 ≤ elapsed w Y e t x j := mul_nonneg (by linarith) hw.le
    have hq : 0 < e j / w x := div_pos (by linarith) hw
    have hτ : clock w Y e j = ENNReal.ofReal (clock w Y e j).toReal :=
      (ENNReal.ofReal_toReal (clock_ne_top w Y e j)).symm
    have hT : (t : ℝ≥0∞) = ENNReal.ofReal (t : ℝ) := ENNReal.ofReal_coe_nnreal.symm
    rw [hτ, hT, ← ENNReal.ofReal_add ENNReal.toReal_nonneg hq.le,
      ← ENNReal.ofReal_sub _ (NNReal.coe_nonneg t)]
    congr 1
    simp only [elapsed]
    field_simp
    ring
  | succ k ih =>
    have hle : (t : ℝ≥0∞) ≤ clock w Y e (j + 1 + k) :=
      hlt.le.trans (clock_mono w Y e (Nat.le_add_right _ _))
    rw [clock_succ, ih, show j + 1 + (k + 1) = (j + 1 + k) + 1 from rfl, clock_succ,
      ENNReal.sub_add_eq_add_sub hle ENNReal.coe_ne_top]
    have hAB : futureTimes w Y e t x j (k + 1) / w (MarkovChain.walkShift j Y (k + 1)) =
        e (j + 1 + k) / w (Y (j + 1 + k)) := by
      simp only [futureTimes, MarkovChain.consPath_succ, MarkovChain.walkShift_apply]
      rw [show j + (k + 1) = j + 1 + k by omega]
    rw [hAB]

/-- **The future after time `t` in the `j`-th holding interval** is the walk with the shifted
skeleton `(Y_{j+k})_k` and the unit holding times `futureTimes` (residual first). -/
lemma ctrw_add_eq {t : ℝ≥0} {x : V} {j : ℕ} (hx : Y j = x) (hw : 0 < w x)
    (hj : clock w Y e j ≤ t) (hlt : (t : ℝ≥0∞) < clock w Y e (j + 1)) (s : ℝ≥0) :
    ctrw w Y e (s + t) = ctrw w (MarkovChain.walkShift j Y) (futureTimes w Y e t x j) s := by
  have hcl := clock_futureTimes_succ w Y e hx hw hj hlt
  have hst : ((s + t : ℝ≥0) : ℝ≥0∞) = (s : ℝ≥0∞) + t := ENNReal.coe_add s t
  refine ctrw_congr w Y e fun y => ⟨?_, ?_⟩
  · rintro ⟨k, ⟨hk1, hk2⟩, hky⟩
    rw [hst] at hk1 hk2
    have hjk : j ≤ k := by
      by_contra hc
      have : clock w Y e (k + 1) ≤ clock w Y e j := clock_mono w Y e (by omega)
      exact absurd (lt_of_lt_of_le hk2 (this.trans (hj.trans le_add_self))) (lt_irrefl _)
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hjk
    cases k' with
    | zero =>
      refine ⟨0, ⟨by rw [clock_zero]; exact zero_le, ?_⟩, ?_⟩
      · rw [hcl 0, Nat.add_zero, lt_tsub_iff_right]
        rwa [Nat.add_zero] at hk2
      · rwa [MarkovChain.walkShift_apply]
    | succ k'' =>
      refine ⟨k'' + 1, ⟨?_, ?_⟩, ?_⟩
      · rw [hcl k'', tsub_le_iff_right]
        rwa [show j + (k'' + 1) = j + 1 + k'' by omega] at hk1
      · rw [hcl (k'' + 1), lt_tsub_iff_right]
        rwa [show j + (k'' + 1) + 1 = j + 1 + (k'' + 1) by omega] at hk2
      · rwa [MarkovChain.walkShift_apply]
  · rintro ⟨k', ⟨hk1, hk2⟩, hky⟩
    cases k' with
    | zero =>
      refine ⟨j, ⟨?_, ?_⟩, ?_⟩
      · rw [hst]
        exact hj.trans le_add_self
      · rw [hst]
        rw [hcl 0, Nat.add_zero, lt_tsub_iff_right] at hk2
        exact hk2
      · rwa [MarkovChain.walkShift_apply, Nat.add_zero] at hky
    | succ k'' =>
      refine ⟨j + 1 + k'', ⟨?_, ?_⟩, ?_⟩
      · rw [hst]
        rw [hcl k'', tsub_le_iff_right] at hk1
        exact hk1
      · rw [hst]
        rw [hcl (k'' + 1), lt_tsub_iff_right] at hk2
        exact hk2
      · rwa [MarkovChain.walkShift_apply, show j + (k'' + 1) = j + 1 + k'' by omega] at hky

end deterministic

/-- The past up to time `t` in the `j`-th holding interval, as a function of the data before
the `j`-th jump: `X_s` for `s < S_j`, and `Y_j` afterwards. -/
noncomputable def pastj (t : ℝ≥0) (j : ℕ) (p : (ℕ → V) × (ℕ → ℝ)) : Set.Iic t → Option V :=
  fun s => if ((s : ℝ≥0) : ℝ≥0∞) < clock w p.1 p.2 j then ctrw w p.1 p.2 s else some (p.1 j)

/-- On `{S_j ≤ t < S_{j+1}}` the past `{X_s}_{s ≤ t}` is `pastj`. -/
lemma pastPath_eq_pastj {Y : ℕ → V} {e : ℕ → ℝ} {t : ℝ≥0} {j : ℕ} (hj : clock w Y e j ≤ t)
    (hlt : (t : ℝ≥0∞) < clock w Y e (j + 1)) :
    Theorem16.pastPath (fun (t : ℝ≥0) (p : (ℕ → V) × (ℕ → ℝ)) => ctrw w p.1 p.2 t) t (Y, e) =
      pastj w t j (Y, e) := by
  funext ⟨s, hs⟩
  simp only [Theorem16.pastPath, pastj]
  split_ifs with h
  · rfl
  · exact ctrw_eq_of_inHold w Y e ⟨not_lt.mp h, lt_of_le_of_lt (ENNReal.coe_le_coe.mpr hs) hlt⟩

/-- `pastj` depends only on `Y_0, …, Y_j` and `e_0, …, e_{j-1}`. -/
lemma pastj_congr {Y Y' : ℕ → V} {e e' : ℕ → ℝ} {t : ℝ≥0} {j : ℕ}
    (hY : ∀ i ≤ j, Y i = Y' i) (he : ∀ i < j, e i = e' i) :
    pastj w t j (Y, e) = pastj w t j (Y', e') := by
  have hcl : clock w Y e j = clock w Y' e' j := clock_congr w Y e (fun i hi => hY i hi.le) he
  funext s
  simp only [pastj]
  rw [hcl, hY j le_rfl]
  split_ifs with h
  · refine ctrw_congr w Y e fun y => ?_
    have key : ∀ {Z : ℕ → V} {f : ℕ → ℝ} k, clock w Z f j = clock w Y' e' j →
        InHold w Z f k s → k < j := fun k hk hin => by
      by_contra hc
      rw [← hk] at h
      exact absurd (lt_of_le_of_lt (le_trans (clock_mono w _ _ (not_lt.mp hc)) hin.1) h)
        (lt_irrefl _)
    constructor
    · rintro ⟨k, hk, hky⟩
      have hkj := key k hcl hk
      refine ⟨k, (inHold_congr w Y e (fun i hi => hY i (by omega)) (fun i hi => he i (by omega))).mp hk, ?_⟩
      rw [← hY k hkj.le]
      exact hky
    · rintro ⟨k, hk, hky⟩
      have hkj := key k rfl hk
      refine ⟨k, (inHold_congr w Y e (fun i hi => hY i (by omega)) (fun i hi => he i (by omega))).mpr hk, ?_⟩
      rw [hY k hkj.le]
      exact hky
  · rfl

section measurability

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

lemma measurable_clock (k : ℕ) :
    Measurable fun p : (ℕ → V) × (ℕ → ℝ) => clock w p.1 p.2 k :=
  Finset.measurable_sum _ fun i _ => ENNReal.measurable_ofReal.comp
    (((measurable_pi_apply i).comp measurable_snd).div
      ((measurable_of_countable w).comp ((measurable_pi_apply i).comp measurable_fst)))

lemma measurableSet_inHold (k : ℕ) (t : ℝ≥0) :
    MeasurableSet {p : (ℕ → V) × (ℕ → ℝ) | InHold w p.1 p.2 k t} :=
  (measurableSet_le (measurable_clock w k) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_clock w (k + 1)))

omit [Countable V] in
lemma measurableSet_fst_eq (k : ℕ) (x : V) :
    MeasurableSet {p : (ℕ → V) × (ℕ → ℝ) | p.1 k = x} := by
  have h : Measurable fun p : (ℕ → V) × (ℕ → ℝ) => p.1 k :=
    (measurable_pi_apply k).comp measurable_fst
  exact h (measurableSet_singleton x)

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
/-- The fibre of `∞`, as the complement of the fibres of the vertices. -/
lemma preimage_none_eq_compl_iUnion {α : Type*} (F : α → Option V) :
    F ⁻¹' {none} = (⋃ x, F ⁻¹' {some x})ᶜ := by
  ext a
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
    not_exists]
  generalize F a = o
  cases o <;> simp

/-- `X_t` is a random variable on `(ℕ → V) × (ℕ → ℝ)`. -/
lemma measurable_ctrw (t : ℝ≥0) :
    Measurable fun p : (ℕ → V) × (ℕ → ℝ) => ctrw w p.1 p.2 t := by
  have hsome : ∀ x : V,
      MeasurableSet ((fun p : (ℕ → V) × (ℕ → ℝ) => ctrw w p.1 p.2 t) ⁻¹' {some x}) := by
    intro x
    have e : (fun p : (ℕ → V) × (ℕ → ℝ) => ctrw w p.1 p.2 t) ⁻¹' {some x} =
        ⋃ k, {p : (ℕ → V) × (ℕ → ℝ) | InHold w p.1 p.2 k t} ∩ {p | p.1 k = x} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, ctrw_eq_some_iff, Set.mem_iUnion,
        Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [e]
    exact MeasurableSet.iUnion fun k => (measurableSet_inHold w k t).inter
      (measurableSet_fst_eq k x)
  refine measurable_to_countable' fun o => ?_
  cases o with
  | none =>
    rw [preimage_none_eq_compl_iUnion]
    exact (MeasurableSet.iUnion hsome).compl
  | some x => exact hsome x

lemma measurable_pastj (t : ℝ≥0) (j : ℕ) : Measurable (pastj w t j) := by
  refine measurable_pi_iff.mpr fun s => ?_
  refine Measurable.ite (measurableSet_lt measurable_const (measurable_clock w j))
    (measurable_ctrw w s) ?_
  exact (measurable_of_countable (fun v : V => (some v : Option V))).comp
    ((measurable_pi_apply j).comp measurable_fst)

lemma measurable_elapsed (t : ℝ≥0) (x : V) (j : ℕ) :
    Measurable fun p : (ℕ → V) × (ℕ → ℝ) => elapsed w p.1 p.2 t x j :=
  (measurable_const.sub (ENNReal.measurable_toReal.comp (measurable_clock w j))).mul
    measurable_const

lemma measurable_futureTimes (t : ℝ≥0) (x : V) (j : ℕ) :
    Measurable fun p : (ℕ → V) × (ℕ → ℝ) => futureTimes w p.1 p.2 t x j :=
  measurable_consPath_uncurry.comp
    ((((measurable_pi_apply j).comp measurable_snd).sub (measurable_elapsed w t x j)).prodMk
      ((MarkovChain.measurable_walkShift (j + 1)).comp measurable_snd))

end measurability

end ctrw

/-! ### The Markov property of the continuous-time random walk -/

section markov

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  (w : V → ℝ) (κ : Kernel V V) [IsMarkovKernel κ]

/-- The law of (skeleton, unit holding times) started at `z`: the chain law `P_z` of the
skeleton tensored with the i.i.d. `Exponential(1)` unit holding times. -/
noncomputable def law (z : V) : Measure ((ℕ → V) × (ℕ → ℝ)) :=
  (MarkovChain.chainLaw κ z).prod unitTimes

instance law_isProbabilityMeasure (z : V) : IsProbabilityMeasure (law κ z) := by
  unfold law
  infer_instance

/-- The walk (3.15) as a stochastic process on `(ℕ → V) × (ℕ → ℝ)`. -/
noncomputable def proc (t : ℝ≥0) (p : (ℕ → V) × (ℕ → ℝ)) : Option V := ctrw w p.1 p.2 t

lemma measurable_proc (t : ℝ≥0) : Measurable (proc w t) := measurable_ctrw w t

/-- The trajectory `{X_s}_{s ≥ 0}` of the walk with data `p`. -/
noncomputable def traj (p : (ℕ → V) × (ℕ → ℝ)) : Trajectory V := fun s => proc w s p

lemma measurable_traj : Measurable (traj w) := measurable_pi_iff.mpr fun s => measurable_ctrw w s

/-- The law of the trajectory `{X_s}_{s ≥ 0}` of the walk started at `x`. -/
noncomputable def trajLaw (x : V) : Measure (Trajectory V) := (law κ x).map (traj w)

instance trajLaw_isProbabilityMeasure (x : V) : IsProbabilityMeasure (trajLaw w κ x) :=
  ⟨by rw [trajLaw, Measure.map_apply (measurable_traj w) MeasurableSet.univ, Set.preimage_univ,
    measure_univ]⟩

/-- The law of the trajectory from `x`, evaluated on `B`, as an integral over the skeleton. -/
lemma trajLaw_apply (x : V) {B : Set (Trajectory V)} (hB : MeasurableSet B) :
    trajLaw w κ x B =
      ∫⁻ Y', ∫⁻ e, B.indicator 1 (traj w (Y', e)) ∂unitTimes ∂MarkovChain.chainLaw κ x := by
  have hm : MeasurableSet (traj w ⁻¹' B) := (measurable_traj w) hB
  rw [trajLaw, Measure.map_apply (measurable_traj w) hB, ← lintegral_indicator_one hm, law,
    lintegral_prod (fun p => (traj w ⁻¹' B).indicator 1 p) (measurable_one.indicator hm).aemeasurable]
  refine lintegral_congr fun Y' => lintegral_congr fun e => ?_
  by_cases h : traj w (Y', e) ∈ B
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_preimage.mpr h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (Set.mem_preimage.mp h'))]

/-- The event `{S_j ≤ t < S_{j+1}, Y_j = x}`: at time `t` the walk is in its `j`-th holding
interval, at the state `x`. -/
def slice (t : ℝ≥0) (x : V) (j : ℕ) : Set ((ℕ → V) × (ℕ → ℝ)) :=
  {p | InHold w p.1 p.2 j t ∧ p.1 j = x}

lemma measurableSet_slice (t : ℝ≥0) (x : V) (j : ℕ) : MeasurableSet (slice w t x j) :=
  (measurableSet_inHold w j t).inter (measurableSet_fst_eq j x)

lemma slice_disjoint (t : ℝ≥0) (x : V) :
    Pairwise fun i j => Disjoint (slice w t x i) (slice w t x j) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun p hi hj => hij ?_
  exact inHold_unique w p.1 p.2 hi.1 hj.1

/-- `{X_t = x}` is the disjoint union of the slices. -/
lemma setOf_proc_eq_some (t : ℝ≥0) (x : V) :
    {p | proc w t p = some x} = ⋃ j, slice w t x j := by
  ext p
  simp only [Set.mem_ofPred_eq, proc, ctrw_eq_some_iff, Set.mem_iUnion, slice]

/-- **Memorylessness at the current jump**: for a fixed future skeleton `Y'`, integrating the
residual unit holding time `r − c` over `{r > c}` against `Exponential(1)` and then the later
unit holding times gives `e^{−c}` times the law of the walk from `Y'`. -/
lemma lintegral_residual (Y' : ℕ → V) {c : ℝ} (hc : 0 ≤ c) {B : Set (Trajectory V)}
    (hB : MeasurableSet B) :
    ∫⁻ r, ∫⁻ e, (Set.Ioi c).indicator 1 r *
        B.indicator 1 (traj w (Y', MarkovChain.consPath (r - c) e)) ∂unitTimes ∂expMeasure 1 =
      ENNReal.ofReal (Real.exp (-c)) * ∫⁻ e, B.indicator 1 (traj w (Y', e)) ∂unitTimes := by
  have hG : Measurable fun q : ℝ × (ℕ → ℝ) =>
      B.indicator (1 : Trajectory V → ℝ≥0∞) (traj w (Y', MarkovChain.consPath q.1 q.2)) :=
    (measurable_one.indicator hB).comp
      ((measurable_traj w).comp (measurable_const.prodMk measurable_consPath_uncurry))
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ≥0∞,
      g = fun r => ∫⁻ e, B.indicator 1 (traj w (Y', MarkovChain.consPath r e)) ∂unitTimes :=
    ⟨_, rfl⟩
  have hgm : Measurable g := by
    rw [hg]
    exact hG.lintegral_prod_right'
  have h1 : ∀ r, ∫⁻ e, (Set.Ioi c).indicator 1 r *
      B.indicator 1 (traj w (Y', MarkovChain.consPath (r - c) e)) ∂unitTimes =
        (Set.Ioi c).indicator (fun r => g (r - c)) r := by
    intro r
    have hmeas : Measurable fun e : ℕ → ℝ =>
        B.indicator (1 : Trajectory V → ℝ≥0∞) (traj w (Y', MarkovChain.consPath (r - c) e)) :=
      (measurable_one.indicator hB).comp ((measurable_traj w).comp
        (measurable_const.prodMk (measurable_consPath_left (r - c))))
    rw [lintegral_const_mul _ hmeas]
    by_cases hr : r ∈ Set.Ioi c
    · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, Pi.one_apply, one_mul, hg]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr, zero_mul]
  simp_rw [h1]
  rw [lintegral_expMeasure_one_indicator_sub hc hgm, hg]
  congr 1
  have hG' : Measurable fun e : ℕ → ℝ => B.indicator (1 : Trajectory V → ℝ≥0∞) (traj w (Y', e)) :=
    (measurable_one.indicator hB).comp ((measurable_traj w).comp
      (measurable_const.prodMk measurable_id))
  exact lintegral_unitTimes_consPath hG'

/-- **The core computation of the Markov property** on the `j`-th slice: for `ψ ≥ 0` depending
only on `(Y_0, …, Y_j, e_0, …, e_{j-1})` and vanishing off `{Y_j = x}`, and an elapsed time
`c ≥ 0` of the same kind,
`E_z[ψ · 1_{e_j > c} · 1_B(walk from (θ_j Y, (e_j − c, θ_{j+1} e)))] = μ_x(B) · E_z[ψ · e^{−c}]`.
Memorylessness handles the residual `e_j − c`, the Markov property of the skeleton at time `j`
(`lintegral_mul_walkShift`) handles `θ_j Y`. -/
lemma lintegral_core (z x : V) (j : ℕ) {ψ : (ℕ → V) × (ℕ → ℝ) → ℝ≥0∞} (hψ : Measurable ψ)
    (hψ' : ∀ Y Y' e e', (∀ i ≤ j, Y i = Y' i) → (∀ i < j, e i = e' i) → ψ (Y, e) = ψ (Y', e'))
    (hψx : ∀ p, ψ p ≠ 0 → p.1 j = x)
    {c : (ℕ → V) × (ℕ → ℝ) → ℝ} (hc : Measurable c)
    (hc' : ∀ Y Y' e e', (∀ i ≤ j, Y i = Y' i) → (∀ i < j, e i = e' i) → c (Y, e) = c (Y', e'))
    (hc0 : ∀ p, ψ p ≠ 0 → 0 ≤ c p) {B : Set (Trajectory V)} (hB : MeasurableSet B) :
    ∫⁻ p, ψ p * ({p : (ℕ → V) × (ℕ → ℝ) | c p < p.2 j}.indicator 1 p *
        B.indicator 1 (traj w (MarkovChain.walkShift j p.1,
          MarkovChain.consPath (p.2 j - c p) (MarkovChain.walkShift (j + 1) p.2)))) ∂law κ z =
      trajLaw w κ x B * ∫⁻ p, ψ p * ENNReal.ofReal (Real.exp (-(c p))) ∂law κ z := by
  -- measurability of the pieces
  have hfd : Measurable fun p : (ℕ → V) × (ℕ → ℝ) => (MarkovChain.walkShift j p.1,
      MarkovChain.consPath (p.2 j - c p) (MarkovChain.walkShift (j + 1) p.2)) :=
    ((MarkovChain.measurable_walkShift j).comp measurable_fst).prodMk
      (measurable_consPath_uncurry.comp
        ((((measurable_pi_apply j).comp measurable_snd).sub hc).prodMk
          ((MarkovChain.measurable_walkShift (j + 1)).comp measurable_snd)))
  have hind : Measurable fun p : (ℕ → V) × (ℕ → ℝ) =>
      {p : (ℕ → V) × (ℕ → ℝ) | c p < p.2 j}.indicator (1 : (ℕ → V) × (ℕ → ℝ) → ℝ≥0∞) p :=
    measurable_one.indicator (measurableSet_lt hc ((measurable_pi_apply j).comp measurable_snd))
  have hΦ : Measurable fun p : (ℕ → V) × (ℕ → ℝ) => ψ p *
      ({p : (ℕ → V) × (ℕ → ℝ) | c p < p.2 j}.indicator 1 p *
        B.indicator 1 (traj w (MarkovChain.walkShift j p.1,
          MarkovChain.consPath (p.2 j - c p) (MarkovChain.walkShift (j + 1) p.2)))) :=
    hψ.mul (hind.mul ((measurable_one.indicator hB).comp ((measurable_traj w).comp hfd)))
  have hexp : Measurable fun p : (ℕ → V) × (ℕ → ℝ) => ψ p * ENNReal.ofReal (Real.exp (-(c p))) :=
    hψ.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc.neg))
  -- the glue substitutions
  have hglue_ψ : ∀ Y a r e'', ψ (Y, glue j a r e'') = ψ (Y, a) := fun Y a r e'' =>
    hψ' _ _ _ _ (fun _ _ => rfl) (fun i hi => glue_apply_of_lt hi a r e'')
  have hglue_c : ∀ Y a r e'', c (Y, glue j a r e'') = c (Y, a) := fun Y a r e'' =>
    hc' _ _ _ _ (fun _ _ => rfl) (fun i hi => glue_apply_of_lt hi a r e'')
  -- the future law from a fixed skeleton
  obtain ⟨φ, hφ⟩ : ∃ φ : (ℕ → V) → ℝ≥0∞,
      φ = fun Y' => ∫⁻ e, B.indicator 1 (traj w (Y', e)) ∂unitTimes := ⟨_, rfl⟩
  have hφm : Measurable φ := by
    rw [hφ]
    exact Measurable.lintegral_prod_right' ((measurable_one.indicator hB).comp (measurable_traj w))
  -- the prefix function
  obtain ⟨f, hf⟩ : ∃ f : (ℕ → V) → ℝ≥0∞,
      f = fun Y => ∫⁻ a, ψ (Y, a) * ENNReal.ofReal (Real.exp (-(c (Y, a)))) ∂unitTimes :=
    ⟨_, rfl⟩
  have hfm : Measurable f := by
    rw [hf]
    exact hexp.lintegral_prod_right'
  have hf' : ∀ Y Y', frestrictLe j Y = frestrictLe j Y' → f Y = f Y' := by
    intro Y Y' h
    have hY : ∀ i ≤ j, Y i = Y' i := fun i hi => congrFun h ⟨i, Finset.mem_Iic.mpr hi⟩
    rw [hf]
    refine lintegral_congr fun a => ?_
    rw [hψ' Y Y' a a hY (fun _ _ => rfl), hc' Y Y' a a hY (fun _ _ => rfl)]
  -- the inner integral over the unit holding times
  have hinner : ∀ Y, ∫⁻ e, ψ (Y, e) * ({p : (ℕ → V) × (ℕ → ℝ) | c p < p.2 j}.indicator 1 (Y, e) *
      B.indicator 1 (traj w (MarkovChain.walkShift j Y,
        MarkovChain.consPath (e j - c (Y, e)) (MarkovChain.walkShift (j + 1) e)))) ∂unitTimes
      = f Y * φ (MarkovChain.walkShift j Y) := by
    intro Y
    have hΦY : Measurable fun e : ℕ → ℝ => ψ (Y, e) *
        ({p : (ℕ → V) × (ℕ → ℝ) | c p < p.2 j}.indicator 1 (Y, e) *
          B.indicator 1 (traj w (MarkovChain.walkShift j Y,
            MarkovChain.consPath (e j - c (Y, e)) (MarkovChain.walkShift (j + 1) e)))) :=
      hΦ.comp measurable_prodMk_left
    have hexpY : Measurable fun a : ℕ → ℝ => ψ (Y, a) * ENNReal.ofReal (Real.exp (-(c (Y, a)))) :=
      hexp.comp measurable_prodMk_left
    rw [lintegral_unitTimes_glue j hΦY, hf, ← lintegral_mul_const _ hexpY]
    refine lintegral_congr fun a => ?_
    have hI : ∀ r e'', {p : (ℕ → V) × (ℕ → ℝ) | c p < p.2 j}.indicator
        (1 : (ℕ → V) × (ℕ → ℝ) → ℝ≥0∞) (Y, glue j a r e'') =
          (Set.Ioi (c (Y, a))).indicator 1 r := by
      intro r e''
      by_cases hr : r ∈ Set.Ioi (c (Y, a))
      · have hmem : (Y, glue j a r e'') ∈ {p : (ℕ → V) × (ℕ → ℝ) | c p < p.2 j} := by
          show c (Y, glue j a r e'') < glue j a r e'' j
          rw [hglue_c, glue_apply_self]
          exact hr
        rw [Set.indicator_of_mem hr, Set.indicator_of_mem hmem]
        rfl
      · have hmem : (Y, glue j a r e'') ∉ {p : (ℕ → V) × (ℕ → ℝ) | c p < p.2 j} := by
          intro h
          apply hr
          have h' : c (Y, glue j a r e'') < glue j a r e'' j := h
          rw [hglue_c, glue_apply_self] at h'
          exact h'
        rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hmem]
    simp only [hglue_ψ, hglue_c, glue_apply_self, walkShift_succ_glue, hI]
    by_cases hψ0 : ψ (Y, a) = 0
    · simp only [hψ0, zero_mul, lintegral_zero]
    · have hc0' : 0 ≤ c (Y, a) := hc0 _ hψ0
      have hF : Measurable fun q : ℝ × (ℕ → ℝ) =>
          (Set.Ioi (c (Y, a))).indicator (1 : ℝ → ℝ≥0∞) q.1 *
            B.indicator 1 (traj w (MarkovChain.walkShift j Y,
              MarkovChain.consPath (q.1 - c (Y, a)) q.2)) :=
        ((measurable_one.indicator measurableSet_Ioi).comp measurable_fst).mul
          ((measurable_one.indicator hB).comp ((measurable_traj w).comp (measurable_const.prodMk
            (measurable_consPath_uncurry.comp
              ((measurable_fst.sub measurable_const).prodMk measurable_snd)))))
      calc ∫⁻ r, ∫⁻ e'', ψ (Y, a) * ((Set.Ioi (c (Y, a))).indicator 1 r *
              B.indicator 1 (traj w (MarkovChain.walkShift j Y,
                MarkovChain.consPath (r - c (Y, a)) e''))) ∂unitTimes ∂expMeasure 1
          = ∫⁻ r, ψ (Y, a) * ∫⁻ e'', (Set.Ioi (c (Y, a))).indicator 1 r *
              B.indicator 1 (traj w (MarkovChain.walkShift j Y,
                MarkovChain.consPath (r - c (Y, a)) e'')) ∂unitTimes ∂expMeasure 1 :=
            lintegral_congr fun r => lintegral_const_mul _ (hF.comp measurable_prodMk_left)
        _ = ψ (Y, a) * ∫⁻ r, ∫⁻ e'', (Set.Ioi (c (Y, a))).indicator 1 r *
              B.indicator 1 (traj w (MarkovChain.walkShift j Y,
                MarkovChain.consPath (r - c (Y, a)) e'')) ∂unitTimes ∂expMeasure 1 :=
            lintegral_const_mul _ hF.lintegral_prod_right'
        _ = ψ (Y, a) * ENNReal.ofReal (Real.exp (-(c (Y, a)))) * φ (MarkovChain.walkShift j Y) := by
            rw [lintegral_residual w _ hc0' hB, hφ, mul_assoc]
  -- the outer integral over the skeleton
  rw [law, lintegral_prod _ hΦ.aemeasurable, lintegral_congr hinner,
    lintegral_mul_walkShift κ z j hfm hf' hφm]
  have hG : ∀ Y, f Y * ∫⁻ Y', φ Y' ∂MarkovChain.chainLaw κ (Y j) = f Y * trajLaw w κ x B := by
    intro Y
    by_cases hY : Y j = x
    · rw [hY, trajLaw_apply w κ x hB, hφ]
    · have h0 : ∀ a, ψ (Y, a) = 0 := fun a => by
        by_contra h
        exact hY (hψx _ h)
      rw [hf]
      simp only [h0, zero_mul, lintegral_zero]
  rw [lintegral_congr hG, lintegral_mul_const _ hfm, mul_comm _ (trajLaw w κ x B), hf,
    lintegral_prod _ hexp.aemeasurable]

/-- The weight `1_{S_j ≤ t, Y_j = x, pastj ∈ A}` of the `j`-th slice, a function of
`(Y_0, …, Y_j, e_0, …, e_{j-1})`. -/
noncomputable def pastWeight (t : ℝ≥0) (x : V) (j : ℕ) (A : Set (Set.Iic t → Option V))
    (p : (ℕ → V) × (ℕ → ℝ)) : ℝ≥0∞ :=
  {p : (ℕ → V) × (ℕ → ℝ) | clock w p.1 p.2 j ≤ t ∧ p.1 j = x ∧ pastj w t j p ∈ A}.indicator 1 p

/-- The elapsed unit time, as a function on the sample space. -/
noncomputable def elapsedAt (t : ℝ≥0) (x : V) (j : ℕ) (p : (ℕ → V) × (ℕ → ℝ)) : ℝ :=
  elapsed w p.1 p.2 t x j

lemma pastWeight_ne_zero {t : ℝ≥0} {x : V} {j : ℕ} {A : Set (Set.Iic t → Option V)}
    {p : (ℕ → V) × (ℕ → ℝ)} (h : pastWeight w t x j A p ≠ 0) :
    clock w p.1 p.2 j ≤ t ∧ p.1 j = x ∧ pastj w t j p ∈ A := by
  by_contra h'
  have hnot : p ∉ {p : (ℕ → V) × (ℕ → ℝ) |
      clock w p.1 p.2 j ≤ t ∧ p.1 j = x ∧ pastj w t j p ∈ A} := h'
  apply h
  unfold pastWeight
  exact Set.indicator_of_notMem hnot _

lemma pastWeight_congr (t : ℝ≥0) (x : V) (j : ℕ) (A : Set (Set.Iic t → Option V))
    {Y Y' : ℕ → V} {e e' : ℕ → ℝ} (hY : ∀ i ≤ j, Y i = Y' i) (he : ∀ i < j, e i = e' i) :
    pastWeight w t x j A (Y, e) = pastWeight w t x j A (Y', e') := by
  have hS : (Y, e) ∈ {p : (ℕ → V) × (ℕ → ℝ) |
        clock w p.1 p.2 j ≤ t ∧ p.1 j = x ∧ pastj w t j p ∈ A} ↔
      (Y', e') ∈ {p : (ℕ → V) × (ℕ → ℝ) |
        clock w p.1 p.2 j ≤ t ∧ p.1 j = x ∧ pastj w t j p ∈ A} := by
    show (clock w Y e j ≤ t ∧ Y j = x ∧ pastj w t j (Y, e) ∈ A) ↔
      (clock w Y' e' j ≤ t ∧ Y' j = x ∧ pastj w t j (Y', e') ∈ A)
    rw [clock_congr w Y e (fun i hi => hY i hi.le) he, hY j le_rfl, pastj_congr w hY he]
  unfold pastWeight
  by_cases h : (Y, e) ∈ {p : (ℕ → V) × (ℕ → ℝ) |
      clock w p.1 p.2 j ≤ t ∧ p.1 j = x ∧ pastj w t j p ∈ A}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hS.mp h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hS.mpr h'))]

lemma measurable_pastWeight (t : ℝ≥0) (x : V) (j : ℕ) {A : Set (Set.Iic t → Option V)}
    (hA : MeasurableSet A) : Measurable (pastWeight w t x j A) :=
  measurable_one.indicator ((measurableSet_le (measurable_clock w j) measurable_const).inter
    ((measurableSet_fst_eq j x).inter ((measurable_pastj w t j) hA)))

lemma measurable_elapsedAt (t : ℝ≥0) (x : V) (j : ℕ) : Measurable (elapsedAt w t x j) :=
  measurable_elapsed w t x j

lemma elapsedAt_congr (t : ℝ≥0) (x : V) (j : ℕ) {Y Y' : ℕ → V} {e e' : ℕ → ℝ}
    (hY : ∀ i ≤ j, Y i = Y' i) (he : ∀ i < j, e i = e' i) :
    elapsedAt w t x j (Y, e) = elapsedAt w t x j (Y', e') := by
  simp only [elapsedAt, elapsed, clock_congr w Y e (fun i hi => hY i hi.le) he]

/-- **Property (iv) on the `j`-th slice**: on `{S_j ≤ t < S_{j+1}, Y_j = x}` the joint law of
`({X_s}_{s ≤ t}, {X_{s+t}}_{s ≥ 0})` is the product of the law of the past and the law of the
walk from `x`. -/
lemma markov_slice (hw : ∀ x, 0 < w x) (z : V) (t : ℝ≥0) (x : V) (j : ℕ) :
    ((law κ z).restrict (slice w t x j)).map
        (fun p => (Theorem16.pastPath (proc w) t p, Theorem16.shiftedPath (proc w) t p)) =
      (((law κ z).restrict (slice w t x j)).map (Theorem16.pastPath (proc w) t)).prod
        (trajLaw w κ x) := by
  have hpast : Measurable (Theorem16.pastPath (proc w) t) :=
    measurable_pi_iff.mpr fun s => measurable_ctrw w s
  have hfut : Measurable (Theorem16.shiftedPath (proc w) t) :=
    measurable_pi_iff.mpr fun s => measurable_ctrw w (s + t)
  have hpair : Measurable fun p =>
      (Theorem16.pastPath (proc w) t p, Theorem16.shiftedPath (proc w) t p) :=
    hpast.prodMk hfut
  symm
  refine Measure.prod_eq fun A B hA hB => ?_
  rw [Measure.map_apply hpair (hA.prod hB), Measure.map_apply hpast hA,
    Measure.restrict_apply (hpair (hA.prod hB)), Measure.restrict_apply (hpast hA)]
  have hψ' : ∀ Y Y' e e', (∀ i ≤ j, Y i = Y' i) → (∀ i < j, e i = e' i) →
      pastWeight w t x j A (Y, e) = pastWeight w t x j A (Y', e') :=
    fun Y Y' e e' hY he => pastWeight_congr w t x j A hY he
  have hψx : ∀ p, pastWeight w t x j A p ≠ 0 → p.1 j = x :=
    fun p hp => (pastWeight_ne_zero w hp).2.1
  have hc' : ∀ Y Y' e e', (∀ i ≤ j, Y i = Y' i) → (∀ i < j, e i = e' i) →
      elapsedAt w t x j (Y, e) = elapsedAt w t x j (Y', e') :=
    fun Y Y' e e' hY he => elapsedAt_congr w t x j hY he
  have hc0 : ∀ p, pastWeight w t x j A p ≠ 0 → 0 ≤ elapsedAt w t x j p := fun p hp =>
    mul_nonneg (sub_nonneg.mpr (toReal_le_of_clock_le w p.1 p.2 (pastWeight_ne_zero w hp).1))
      (hw x).le
  -- the rectangle identity, for every `B`
  have hL : ∀ B : Set (Trajectory V), MeasurableSet B →
      law κ z ((fun p => (Theorem16.pastPath (proc w) t p, Theorem16.shiftedPath (proc w) t p))
          ⁻¹' (A ×ˢ B) ∩ slice w t x j) =
        trajLaw w κ x B *
          ∫⁻ p, pastWeight w t x j A p * ENNReal.ofReal (Real.exp (-(elapsedAt w t x j p)))
            ∂law κ z := by
    intro B hB
    have hident : ∀ p, ((fun p => (Theorem16.pastPath (proc w) t p,
        Theorem16.shiftedPath (proc w) t p)) ⁻¹' (A ×ˢ B) ∩ slice w t x j).indicator
          (1 : (ℕ → V) × (ℕ → ℝ) → ℝ≥0∞) p =
        pastWeight w t x j A p * ({p : (ℕ → V) × (ℕ → ℝ) | elapsedAt w t x j p < p.2 j}.indicator
          1 p * B.indicator 1 (traj w (MarkovChain.walkShift j p.1,
            MarkovChain.consPath (p.2 j - elapsedAt w t x j p)
              (MarkovChain.walkShift (j + 1) p.2)))) := by
      intro p
      by_cases hp : p ∈ slice w t x j
      · obtain ⟨⟨hj, hlt⟩, hx⟩ := hp
        have hc_lt : elapsedAt w t x j p < p.2 j :=
          (lt_clock_succ_iff w p.1 p.2 hx (hw x) hj).mp hlt
        have hpast_eq : Theorem16.pastPath (proc w) t p = pastj w t j p :=
          pastPath_eq_pastj w hj hlt
        have hfut_eq : Theorem16.shiftedPath (proc w) t p =
            traj w (MarkovChain.walkShift j p.1,
              MarkovChain.consPath (p.2 j - elapsedAt w t x j p)
                (MarkovChain.walkShift (j + 1) p.2)) :=
          funext fun s => ctrw_add_eq w p.1 p.2 hx (hw x) hj hlt s
        have hmemc : p ∈ {p : (ℕ → V) × (ℕ → ℝ) | elapsedAt w t x j p < p.2 j} := hc_lt
        rw [Set.indicator_of_mem hmemc, Pi.one_apply, one_mul]
        by_cases hA' : pastj w t j p ∈ A
        · have hmemψ : p ∈ {p : (ℕ → V) × (ℕ → ℝ) |
              clock w p.1 p.2 j ≤ t ∧ p.1 j = x ∧ pastj w t j p ∈ A} := ⟨hj, hx, hA'⟩
          rw [pastWeight, Set.indicator_of_mem hmemψ, Pi.one_apply, one_mul]
          by_cases hB' : traj w (MarkovChain.walkShift j p.1,
              MarkovChain.consPath (p.2 j - elapsedAt w t x j p)
                (MarkovChain.walkShift (j + 1) p.2)) ∈ B
          · have hmem_pair : p ∈ (fun p => (Theorem16.pastPath (proc w) t p,
                Theorem16.shiftedPath (proc w) t p)) ⁻¹' (A ×ˢ B) := by
              show Theorem16.pastPath (proc w) t p ∈ A ∧ Theorem16.shiftedPath (proc w) t p ∈ B
              rw [hpast_eq, hfut_eq]
              exact ⟨hA', hB'⟩
            have hmem2 : p ∈ (fun p => (Theorem16.pastPath (proc w) t p,
                Theorem16.shiftedPath (proc w) t p)) ⁻¹' (A ×ˢ B) ∩ slice w t x j :=
              ⟨hmem_pair, ⟨⟨hj, hlt⟩, hx⟩⟩
            rw [Set.indicator_of_mem hB', Set.indicator_of_mem hmem2]
            rfl
          · rw [Set.indicator_of_notMem hB', Set.indicator_of_notMem]
            intro h
            have h2 : Theorem16.shiftedPath (proc w) t p ∈ B := h.1.2
            rw [hfut_eq] at h2
            exact hB' h2
        · have hnψ : p ∉ {p : (ℕ → V) × (ℕ → ℝ) |
              clock w p.1 p.2 j ≤ t ∧ p.1 j = x ∧ pastj w t j p ∈ A} := fun h => hA' h.2.2
          rw [pastWeight, Set.indicator_of_notMem hnψ, zero_mul, Set.indicator_of_notMem]
          intro h
          have h1 : Theorem16.pastPath (proc w) t p ∈ A := h.1.1
          rw [hpast_eq] at h1
          exact hA' h1
      · rw [Set.indicator_of_notMem (fun h => hp h.2)]
        by_cases hψ0 : pastWeight w t x j A p = 0
        · rw [hψ0, zero_mul]
        · have hmem := pastWeight_ne_zero w hψ0
          have hnot : p ∉ {p : (ℕ → V) × (ℕ → ℝ) | elapsedAt w t x j p < p.2 j} := fun h =>
            hp ⟨⟨hmem.1, (lt_clock_succ_iff w p.1 p.2 hmem.2.1 (hw x) hmem.1).mpr h⟩, hmem.2.1⟩
          rw [Set.indicator_of_notMem hnot, zero_mul, mul_zero]
    rw [← lintegral_indicator_one ((hpair (hA.prod hB)).inter (measurableSet_slice w t x j)),
      lintegral_congr hident, lintegral_core w κ z x j (measurable_pastWeight w t x j hA) hψ' hψx
        (measurable_elapsedAt w t x j) hc' hc0 hB]
  have hpre : (fun p => (Theorem16.pastPath (proc w) t p, Theorem16.shiftedPath (proc w) t p))
      ⁻¹' (A ×ˢ Set.univ) = Theorem16.pastPath (proc w) t ⁻¹' A := by
    ext p
    simp
  rw [hL B hB, ← hpre, hL Set.univ MeasurableSet.univ, measure_univ, one_mul, mul_comm]

/-- **The Markov property of the continuous-time random walk (3.15)** (p. 25, "the Markov
property of continuous time random walk"), in the joint-law form of property (iv): for every
`t ≥ 0` and `x ∈ V`, on `{X_t = x}` the joint law of `({X_s}_{s ≤ t}, {X_{s+t}}_{s ≥ 0})` under
`P_z ⊗ unitTimes` is the product of the law of the past and the law of the walk started at `x`.
Summing `markov_slice` over the holding intervals. -/
theorem markovProperty (hw : ∀ x, 0 < w x) (z : V) :
    Theorem16.MarkovProperty (fun x => trajLaw w κ x) (law κ z) (proc w) := by
  intro t x
  have hpast : Measurable (Theorem16.pastPath (proc w) t) :=
    measurable_pi_iff.mpr fun s => measurable_ctrw w s
  have hfut : Measurable (Theorem16.shiftedPath (proc w) t) :=
    measurable_pi_iff.mpr fun s => measurable_ctrw w (s + t)
  have hpair : Measurable fun p =>
      (Theorem16.pastPath (proc w) t p, Theorem16.shiftedPath (proc w) t p) :=
    hpast.prodMk hfut
  rw [setOf_proc_eq_some w t x, Measure.restrict_iUnion (slice_disjoint w t x)
    (measurableSet_slice w t x), Measure.map_sum hpair.aemeasurable,
    Measure.map_sum hpast.aemeasurable, Measure.prod_sum_left]
  congr 1
  funext j
  exact markov_slice w κ hw z t x j

end markov

end CTRW

end ReflectedWalk
