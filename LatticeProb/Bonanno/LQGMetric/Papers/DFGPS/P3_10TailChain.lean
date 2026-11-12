/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_10TailChain at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_10TailGeom

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
proof of Proposition 3.10, Step 2 (T:1895–1904): "each point of `X_S` can be joined to `X_{S'}` by
a path in `S` of `D_h`-length at most …"; "since the metric `D_h` is a continuous function …
`sup_{w ∈ S_{N}(z)} D_h(z, w; 𝕣𝕊) ≤ Σ_{n ≥ N} …`".

`internalDiam_le_of_crossings`: if every dyadic square of `𝕣𝕊` at level `n` has the crossings of
`P3_10TailGeom` with `D`-lengths `≤ B θⁿ` (`θ < 1`), then the internal diameter of `𝕣𝕊` is at most
`10 B / (1 - θ)`. We use the crossings at all levels `n ≥ 0` (the root square is `𝕣𝕊`), so the
paper's Step 3 (triangle inequality over the squares of level `N_C`) is not needed (proposed
DEVIATIONS entry). Continuity of `D(·,·;𝕣𝕊)` (`continuousOn_internal`) needs `D` to be a length
metric (Axiom I).
-/

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint MetricGeometry

variable {D : ContMetric} {Y : Set ℂ}

lemma internal_comm' (D : ContMetric) (Y : Set ℂ) (u v : ℂ) :
    D.internal Y u v = D.internal Y v u :=
  internalEDist_comm _ _ _

lemma isOpen_rS (𝕣 : ℝ) (h𝕣 : 0 < 𝕣) : IsOpen (rS 𝕣) := by
  have : rS 𝕣 = {z : ℂ | 0 < z.re} ∩ {z | z.re < 𝕣} ∩ {z | 0 < z.im} ∩ {z | z.im < 𝕣} := by
    ext z; rw [mem_rS_iff h𝕣]; simp only [mem_inter_iff, mem_setOf_eq]; tauto
  rw [this]
  refine (((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)).inter
    (isOpen_lt continuous_const Complex.continuous_im)).inter
    (isOpen_lt Complex.continuous_im continuous_const)

/-- **One step of the chain** (T:1897–1899): from `X_S` to `X_{S'}` for a dyadic child `S'`. -/
lemma chain_step {s : ℝ} (hs : 0 < s) {w : ℂ} {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1)
    {e₀ e₁ : ℝ} (he₀ : 0 ≤ e₀ ∧ e₀ ≤ 1 / 2) (he₁ : 0 ≤ e₁ ∧ e₁ ≤ 1 / 2)
    {H0 Hb V0 V' H' : ℝ → ℂ} {L L' : ℝ}
    (hH0 : HCr D Y s w e₀ H0 L) (hHb : HCr D Y s w ((b : ℝ) / 2) Hb L) (hV0 : VCr D Y s w V0 L)
    (hV' : VCr D Y (s / 2) (w + ⟨s / 2 * a, s / 2 * b⟩) V' L')
    (hH' : HCr D Y (s / 2) (w + ⟨s / 2 * a, s / 2 * b⟩) e₁ H' L') :
    D.internal Y (H0 0) (H' 0) ≤ 3 * ENNReal.ofReal L + 2 * ENNReal.ofReal L' := by
  have ha' : (a : ℝ) ≤ 1 := by exact_mod_cast ha
  have hb' : (b : ℝ) ≤ 1 := by exact_mod_cast hb
  obtain ⟨t1, ht1, t1', ht1', e1⟩ := meet_in hs he₀.1 he₀.2 hH0 hV0
  obtain ⟨t2, ht2, t2', ht2', e2⟩ := meet_in hs (by positivity) (by linarith) hHb hV0
  obtain ⟨t3, ht3, t3', ht3', e3⟩ := meet_child hs (Nat.cast_nonneg a) ha' (Nat.cast_nonneg b)
    hb' hHb hV'
  obtain ⟨t4, ht4, t4', ht4', e4⟩ := meet_in (half_pos hs) he₁.1 he₁.2 hH' hV'
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have l1 := (internal_le_len_of_path D hH0.1 hH0.2.2.2.2.1 h0 ht1).trans hH0.2.2.2.2.2
  have l2 := (internal_le_len_of_path D hV0.1 hV0.2.2.2.2.1 ht1' ht2').trans hV0.2.2.2.2.2
  have l3 := (internal_le_len_of_path D hHb.1 hHb.2.2.2.2.1 ht2 ht3).trans hHb.2.2.2.2.2
  have l4 := (internal_le_len_of_path D hV'.1 hV'.2.2.2.2.1 ht3' ht4').trans hV'.2.2.2.2.2
  have l5 := (internal_le_len_of_path D hH'.1 hH'.2.2.2.2.1 ht4 h0).trans hH'.2.2.2.2.2
  rw [← e1, ← e2] at l2
  rw [← e3, ← e4] at l4
  calc D.internal Y (H0 0) (H' 0)
      ≤ D.internal Y (H0 0) (H0 t1) + (D.internal Y (H0 t1) (Hb t2) +
          (D.internal Y (Hb t2) (Hb t3) + (D.internal Y (Hb t3) (H' t4) +
            D.internal Y (H' t4) (H' 0)))) := by
        refine (internal_triangle D Y _ (H0 t1) _).trans (add_le_add le_rfl ?_)
        refine (internal_triangle D Y _ (Hb t2) _).trans (add_le_add le_rfl ?_)
        refine (internal_triangle D Y _ (Hb t3) _).trans (add_le_add le_rfl ?_)
        exact internal_triangle D Y _ (H' t4) _
    _ ≤ ENNReal.ofReal L + (ENNReal.ofReal L + (ENNReal.ofReal L + (ENNReal.ofReal L' +
          ENNReal.ofReal L'))) := by gcongr
    _ = _ := by ring

/-- **Multiscale chaining** (T:1895–1904). -/
theorem internalDiam_le_of_crossings (hDl : D.IsLength) {𝕣 B θ : ℝ} (h𝕣 : 0 < 𝕣) (hB : 0 ≤ B)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hH : ∀ n j k : ℕ, j < 2 ^ n → k < 2 ^ n → ∀ b : ℕ, b ≤ 1 → ∃ P,
      HCr D (rS 𝕣) (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k) ((b : ℝ) / 2) P (B * θ ^ n))
    (hV : ∀ n j k : ℕ, j < 2 ^ n → k < 2 ^ n → ∃ P,
      VCr D (rS 𝕣) (𝕣 / 2 ^ n) (dyCorner 𝕣 n j k) P (B * θ ^ n)) :
    internalDiam D (rS 𝕣) (rS 𝕣) ≤ ENNReal.ofReal (2 * (5 * B / (1 - θ))) := by
  choose! Hf hHf using hH
  choose! Vf hVf using hV
  set Y := rS 𝕣
  set c := 5 * B / (1 - θ) with hc
  have hc0 : 0 ≤ c := div_nonneg (by positivity) (by linarith)
  have hroot : ∀ z ∈ Y, D.internal Y z (Hf 0 0 0 0 0) ≤ ENNReal.ofReal c := by
    intro z hz
    obtain ⟨hre0, hre1, him0, him1⟩ := (mem_rS_iff h𝕣).1 hz
    set J : ℕ → ℕ := fun n => dyIdx 𝕣 n z.re
    set K : ℕ → ℕ := fun n => dyIdx 𝕣 n z.im
    have hJ : ∀ n, J n < 2 ^ n := fun n => dyIdx_lt h𝕣 n hre0.le hre1
    have hK : ∀ n, K n < 2 ^ n := fun n => dyIdx_lt h𝕣 n him0.le him1
    set xs : ℕ → ℂ := fun n => Hf n (J n) (K n) 0 0
    have hHx : ∀ n, HCr D Y (𝕣 / 2 ^ n) (dyCorner 𝕣 n (J n) (K n)) (((0 : ℕ) : ℝ) / 2)
        (Hf n (J n) (K n) 0) (B * θ ^ n) := fun n => hHf n _ _ (hJ n) (hK n) 0 (Nat.zero_le _)
    have hxY : ∀ n, xs n ∈ Y := fun n => (hHx n).2.2.2.2.1 (left_mem_Icc.2 zero_le_one)
    have hx0 : xs 0 = Hf 0 0 0 0 0 := by
      have h1 : J 0 = 0 := Nat.lt_one_iff.1 (by simpa using hJ 0)
      have h2 : K 0 = 0 := Nat.lt_one_iff.1 (by simpa using hK 0)
      simp only [xs, h1, h2]
    -- one step
    have hstep : ∀ n, D.internal Y (xs n) (xs (n + 1)) ≤ ENNReal.ofReal (5 * (B * θ ^ n)) := by
      intro n
      obtain ⟨a, ha, hJa⟩ := dyIdx_succ h𝕣 n hre0.le
      obtain ⟨b, hb, hKb⟩ := dyIdx_succ h𝕣 n him0.le
      have hs : 𝕣 / 2 ^ (n + 1) = 𝕣 / 2 ^ n / 2 := by rw [pow_succ]; ring
      have h4 := hVf (n + 1) (J (n + 1)) (K (n + 1)) (hJ _) (hK _)
      have h5 := hHx (n + 1)
      simp only [J, K] at h4 h5
      rw [hJa, hKb, dyCorner_succ, hs] at h4 h5
      have key := chain_step (D := D) (Y := Y) (by positivity : 0 < 𝕣 / 2 ^ n) ha hb
        (by norm_num) (by norm_num) (hHx n) (hHf n _ _ (hJ n) (hK n) b hb)
        (hVf n _ _ (hJ n) (hK n)) h4 h5
      have e : xs (n + 1) = Hf (n + 1) (2 * dyIdx 𝕣 n z.re + a) (2 * dyIdx 𝕣 n z.im + b) 0 0 := by
        simp only [xs, J, K, hJa, hKb]
      rw [e]
      refine key.trans ?_
      have hθn : B * θ ^ (n + 1) ≤ B * θ ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hθ0 hθ1.le n.le_succ) hB
      calc 3 * ENNReal.ofReal (B * θ ^ n) + 2 * ENNReal.ofReal (B * θ ^ (n + 1))
          ≤ 3 * ENNReal.ofReal (B * θ ^ n) + 2 * ENNReal.ofReal (B * θ ^ n) := by
            have := ENNReal.ofReal_le_ofReal hθn
            gcongr
        _ = ENNReal.ofReal (5 * (B * θ ^ n)) := by
            rw [← add_mul, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
            norm_num
    -- partial sums
    have hsum : ∀ m, D.internal Y (xs 0) (xs m) ≤
        ENNReal.ofReal (∑ n ∈ Finset.range m, 5 * (B * θ ^ n)) := by
      intro m
      induction m with
      | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, ENNReal.ofReal_zero, nonpos_iff_eq_zero]
        exact internalEDist_self (mem_image_of_mem _ (hxY 0))
      | succ m ih =>
        rw [Finset.sum_range_succ, ENNReal.ofReal_add (Finset.sum_nonneg fun n _ => by positivity)
          (by positivity)]
        exact (internal_triangle D Y _ (xs m) _).trans (add_le_add ih (hstep m))
    have hgeom : ∀ m, ∑ n ∈ Finset.range m, 5 * (B * θ ^ n) ≤ c := by
      intro m
      rw [← Finset.mul_sum, ← Finset.mul_sum, hc, mul_div_assoc, div_eq_mul_one_div B]
      gcongr
      calc _ = ∑ i ∈ Finset.Ico 0 m, θ ^ i := by rw [Finset.range_eq_Ico]
        _ ≤ θ ^ 0 / (1 - θ) := geom_sum_Ico_le_of_lt_one hθ0 hθ1
        _ = 1 / (1 - θ) := by rw [pow_zero]
    -- convergence `xs m → z`
    have hnorm : ∀ m, ‖xs m - z‖ ≤ 2 * (𝕣 * (1 / 2) ^ m) := by
      intro m
      obtain ⟨-, hre, -, him, -, -⟩ := hHx m
      have him0' := him 0 (left_mem_Icc.2 zero_le_one)
      have bJ := dyIdx_bounds h𝕣 m hre0.le
      have bK := dyIdx_bounds h𝕣 m him0.le
      have hsm : 𝕣 / 2 ^ m = 𝕣 * (1 / 2) ^ m := by rw [one_div, inv_pow]; ring
      simp only [dyCorner, Nat.cast_zero, zero_div, add_zero, mem_Icc] at hre him0'
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.sub_re, Complex.sub_im]
      rw [← hsm]
      have hs0 : 0 < 𝕣 / 2 ^ m := by positivity
      have a1 : |(xs m).re - z.re| ≤ 𝕣 / 2 ^ m := by
        rw [abs_le]; simp only [xs] at hre ⊢; constructor <;> nlinarith
      have a2 : |(xs m).im - z.im| ≤ 𝕣 / 2 ^ m := by
        rw [abs_le]; simp only [xs] at him0' ⊢; constructor <;> nlinarith
      linarith
    have hxt : Tendsto xs atTop (𝓝 z) := by
      rw [← tendsto_sub_nhds_zero_iff]
      refine squeeze_zero_norm hnorm ?_
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 𝕣).const_mul 2
      simpa using this
    have hcont := ContMetric.continuousOn_internal D hDl (isOpen_rS 𝕣 h𝕣)
    have ht : Tendsto (fun m => D.internal Y z (xs m)) atTop (𝓝 (D.internal Y z z)) :=
      ((hcont (z, z) ⟨hz, hz⟩).tendsto).comp (tendsto_nhdsWithin_iff.2
        ⟨tendsto_const_nhds.prodMk_nhds hxt, Eventually.of_forall fun m => ⟨hz, hxY m⟩⟩)
    have hzz : D.internal Y z z = 0 := internalEDist_self (mem_image_of_mem _ hz)
    rw [hzz] at ht
    have hlim := ht.add (tendsto_const_nhds (x := ENNReal.ofReal c))
    rw [zero_add] at hlim
    refine ge_of_tendsto hlim (Eventually.of_forall fun m => ?_)
    rw [← hx0]
    refine (internal_triangle D Y z (xs m) (xs 0)).trans (add_le_add le_rfl ?_)
    rw [internal_comm']
    exact (hsum m).trans (ENNReal.ofReal_le_ofReal (hgeom m))
  unfold internalDiam
  refine iSup₂_le fun u hu => iSup₂_le fun v hv => ?_
  refine (internal_triangle D Y u (Hf 0 0 0 0 0) v).trans ?_
  rw [internal_comm' D Y _ v, two_mul, ENNReal.ofReal_add hc0 hc0]
  exact add_le_add (hroot u hu) (hroot v hv)

end LQGMetric.DFGPS
