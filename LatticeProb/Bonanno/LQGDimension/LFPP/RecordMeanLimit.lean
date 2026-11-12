/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordMeanLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordMeanLimitAux1
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordMeanLimitAux4
import LatticeProb.Bonanno.LQGDimension.LFPP.Lemma33
import LatticeProb.Bonanno.LQGDimension.LFPP.CircCovDominated
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordMeanTransfer
import LatticeProb.Bonanno.LQGDimension.LFPP.ExpectedSupLimit

/-!
# Node `M46` (`Draft.RecordMeanLimit`, the limiting mean bound (4.6))

We prove `Blueprint.Draft.RecordMeanLimit` from `ConstrainedCovLimit` (`L32c`) and
`ExpectedSupLimit` (`ESL`) (`recordMeanLimit_of`); Lemma 3.3 (`L33`), the PSD property of the log
kernel (`L31d`) and of `zCov` are already proved.  Since `ESL` is proved
(`expectedSupLimit`), `recordMeanLimit_of_constrainedCovLimit` takes only `L32c`.

## Proof

Fix `n ≥ 1`, `k`, `θ > 0`, and put `M = 16 ^ n`.

1. **Parametrization** (`RecordMeanLimitAux2`, `Aux4`).  Parameters are vectors
   `p : Fin (M + 4) → ℝ` (node values of the profile, and the two endpoint offsets).  For small
   `δ`, every `c ∈ smallFamily M δ k` has exactly `M` edges, all but the last pointing forwards,
   and `c = constrCfg M δ (fOf n p) (p0Of p) (p1Of p)` for `p = prm M δ c`, with `|p i| ≤ B`
   (`B = 2M(k+1) + 1`) and offsets of norm at most `cellRad M = 4/M²`.  By (3.3) (part of
   `L32c`), `E(fOf n p) ≤ δ⁻² log(len/R) + 1 < k + 2`.  So `p` lies in the compact set
   `K = Kset n k B (cellRad M)`.
2. **Convergence** (`L32c`, `ESL`).  On `K`, `Cδ p q = δ⁻¹ logCov` of the constrained
   configurations converges uniformly to `C p q = zDiffCov (fOf p) g_p (fOf q) g_q`, with a
   uniform Hölder-`1/2` modulus.  `ESL` (with drift `0`) gives a finite `G ⊆ K` with
   `E max_{F.image prm} ≤ E max_G + θ`.
3. **Lemma 3.3** bounds `E max_G` after reindexing along `p ↦ (fOf p, Im p₀, Im p₁)`; the drift
   `-k` is restored by `gEM_const`.  If `G = ∅`, the bound is trivial since the right side is
   at least `-k`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension

open Blueprint.Draft

namespace RML

open LFPPRecords

/-- The test combination of the constrained configuration of a parameter vector. -/
def ccomb (n : ℕ) (δ : ℝ) (p : Fin (16 ^ n + 4) → ℝ) : SegComb :=
  cfgComb (constrCfg (16 ^ n) δ (fOf n p) (p0Of (16 ^ n) p) (p1Of (16 ^ n) p))

/-- The normalized covariance kernel on parameters (cut off at `δ > 1`, where it is not
needed, to keep it positive semidefinite for all `δ > 0`). -/
def Cdel (n : ℕ) (δ : ℝ) (p q : Fin (16 ^ n + 4) → ℝ) : ℝ :=
  if δ ≤ 1 then δ⁻¹ * (ccomb n δ p).logCov (ccomb n δ q) else 0

/-- The limiting covariance kernel on parameters. -/
def Clim (n : ℕ) (p q : Fin (16 ^ n + 4) → ℝ) : ℝ :=
  zDiffCov (fOf n p) (affineFn (p0Of (16 ^ n) p).im (p1Of (16 ^ n) p).im)
    (fOf n q) (affineFn (p0Of (16 ^ n) q).im (p1Of (16 ^ n) q).im)

/-- The Lemma 3.3 kernel on triples `(f, t₀, t₁)`. -/
def Ker33 (q q' : (ℝ → ℝ) × ℝ × ℝ) : ℝ :=
  zDiffCov q.1 (affineFn q.2.1 q.2.2) q'.1 (affineFn q'.2.1 q'.2.2)

/-- The Lemma 3.3 parameters of a parameter vector. -/
def psi33 (n : ℕ) (p : Fin (16 ^ n + 4) → ℝ) : (ℝ → ℝ) × ℝ × ℝ :=
  (fOf n p, (p0Of (16 ^ n) p).im, (p1Of (16 ^ n) p).im)

lemma ccomb_mass_nondeg {n : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {p : Fin (16 ^ n + 4) → ℝ} (hp0 : ‖p0Of (16 ^ n) p‖ ≤ 1 / 64)
    (hp1 : ‖p1Of (16 ^ n) p‖ ≤ 1 / 64) :
    (ccomb n δ p).mass = 0 ∧ (ccomb n δ p).Nondeg := by
  set a := (δ : ℂ) * p0Of (16 ^ n) p
  set b := 1 + (δ : ℂ) * p1Of (16 ^ n) p
  have hn1 : ‖(δ : ℂ) * p0Of (16 ^ n) p‖ ≤ 1 / 64 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
    nlinarith [norm_nonneg (p0Of (16 ^ n) p)]
  have hn2 : ‖(δ : ℂ) * p1Of (16 ^ n) p‖ ≤ 1 / 64 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
    nlinarith [norm_nonneg (p1Of (16 ^ n) p)]
  have hR : 0 < ‖b - a‖ := by
    have e : (1 : ℂ) = (b - a) - (δ : ℂ) * p1Of (16 ^ n) p + a := by simp only [a, b]; ring
    have h1 : ‖(1 : ℂ)‖ ≤ ‖b - a‖ + ‖(δ : ℂ) * p1Of (16 ^ n) p‖ + ‖a‖ := by
      calc ‖(1 : ℂ)‖ = ‖(b - a) - (δ : ℂ) * p1Of (16 ^ n) p + a‖ := by rw [← e]
        _ ≤ ‖(b - a) - (δ : ℂ) * p1Of (16 ^ n) p‖ + ‖a‖ := norm_add_le _ _
        _ ≤ ‖b - a‖ + ‖(δ : ℂ) * p1Of (16 ^ n) p‖ + ‖a‖ := by gcongr; exact norm_sub_le _ _
    rw [norm_one] at h1
    linarith
  apply MeanTransfer.cfgComb_mass_nondeg
  constructor
  · show 0 < polyLen [a, b]
    rw [polyLen_pair]
    exact hR
  · show 0 < polyLen (constrPoly (16 ^ n) δ a b (fOf n p))
    exact hR.trans_le (polyLen_constrPoly_ge (by positivity) δ a b (fOf_zero n p))

lemma smallFamily_log_lt {M : ℕ} {δ : ℝ} {k : ℕ} {c : Config} (hc : c ∈ smallFamily M δ k) :
    Real.log (polyLen c.2 / polyLen c.1) < ((k : ℝ) + 1) * δ ^ 2 := by
  obtain ⟨x, y, z, rfl, -, -, -, -, -, -, -, -, -, h, -⟩ := hc
  show Real.log (polyLen z / polyLen [x, y]) < _
  rw [polyLen_pair]
  exact h

lemma cellRad_eq (n : ℕ) : cellRad (16 ^ n) = 4 / (16 : ℝ) ^ (2 * n) := by
  unfold cellRad
  rw [show (16 : ℝ) ^ (2 * n) = ((16 : ℝ) ^ n) ^ 2 by rw [← pow_mul, mul_comm]]
  push_cast
  ring

end RML

open RML in
/-- **Node `M46` ((4.6))**, from `ConstrainedCovLimit` and `ExpectedSupLimit`. -/
theorem recordMeanLimit_of (hL32c : Blueprint.Draft.ConstrainedCovLimit)
    (hESL : Blueprint.Draft.ExpectedSupLimit) : Blueprint.Draft.RecordMeanLimit := by
  classical
  obtain ⟨C₃, hC₃⟩ := lemma33 4
  refine ⟨max C₃ 0, 1, fun n hn k θ hθ => ?_⟩
  have hM16 : 16 ≤ 16 ^ n := Nat.le_self_pow (by omega) 16
  have hMr : (16 : ℝ) ≤ ((16 ^ n : ℕ) : ℝ) := by exact_mod_cast hM16
  set B : ℝ := 2 * ((16 ^ n : ℕ) : ℝ) * ((k : ℝ) + 1) + 1 with hB
  have hB0 : 0 ≤ B := by positivity
  set ρ : ℝ := cellRad (16 ^ n) with hρ
  have hρ64 : ρ ≤ 1 / 64 := cellRad_le hM16
  obtain ⟨Lmod, hL⟩ := hL32c n B ρ
  have hKc : IsCompact (Kset n k B ρ) := isCompact_Kset n k hB0 ρ
  have hKmem : ∀ p ∈ Kset n k B ρ, fOf n p ∈ V n ∧ (∀ x, |fOf n p x| ≤ B) ∧
      ‖p0Of (16 ^ n) p‖ ≤ ρ ∧ ‖p1Of (16 ^ n) p‖ ≤ ρ ∧ energy (fOf n p) ≤ k + 2 := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    exact ⟨fOf_mem n p, abs_fOf_le n h1 hB0, h3, h4, h2⟩
  -- (a) positive semidefiniteness of the prelimit kernels
  have ha : ∀ δ > 0, ∀ F : Finset (Fin (16 ^ n + 4) → ℝ), ↑F ⊆ Kset n k B ρ →
      PSDOn F (Cdel n δ) := by
    intro δ hδ F hF
    by_cases h1 : δ ≤ 1
    · have hpsd := CircDom.logCov_psdOn F (ccomb n δ) fun p hp => by
        obtain ⟨-, -, h3, h4, -⟩ := hKmem p (hF hp)
        exact ccomb_mass_nondeg hδ h1 (h3.trans hρ64) (h4.trans hρ64)
      refine psdOn_congr F (psdOn_smul F hpsd (inv_nonneg.2 hδ.le)) fun p _ q _ => ?_
      simp only [Cdel, if_pos h1]
    · refine psdOn_congr F (psdOn_zero F) fun p _ q _ => ?_
      simp only [Cdel, if_neg h1]
  -- (b) positive semidefiniteness of the limit kernel
  have hb : ∀ F : Finset (Fin (16 ^ n + 4) → ℝ), ↑F ⊆ Kset n k B ρ → PSDOn F (Clim n) :=
    fun F _ => psdOn_zDiffCov F (fun p => fOf n p)
      (fun p => affineFn (p0Of (16 ^ n) p).im (p1Of (16 ^ n) p).im)
      (fun p _ => Subadd.V_continuous (fOf_mem n p)) (fun p _ => L33.affineFn_continuous _ _)
  -- (c) uniform convergence
  have hc : ∀ θ' > 0, ∀ᶠ δ in 𝓝[>] 0, ∀ p ∈ Kset n k B ρ, ∀ q ∈ Kset n k B ρ,
      |Cdel n δ p q - Clim n p q| ≤ θ' ∧
        |(fun (_ : ℝ) (_ : Fin (16 ^ n + 4) → ℝ) => (0 : ℝ)) δ p -
          (fun (_ : Fin (16 ^ n + 4) → ℝ) => (0 : ℝ)) p| ≤ θ' := by
    intro θ' hθ'
    filter_upwards [hL θ' hθ', Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ hδ1
    intro p hp q hq
    obtain ⟨m1, b1, r1, s1, -⟩ := hKmem p hp
    obtain ⟨m2, b2, r2, s2, -⟩ := hKmem q hq
    refine ⟨?_, by simp only [sub_self, abs_zero]; exact hθ'.le⟩
    simp only [Cdel, if_pos hδ1.2.le, Clim, ccomb]
    exact (hδ _ m1 _ m2 _ _ _ _ b1 b2 r1 s1 r2 s2).1
  -- (d) uniform modulus
  set L : ℝ := 5 * max Lmod 0 with hLdef
  have hd : ∀ᶠ δ in 𝓝[>] 0, ∀ p ∈ Kset n k B ρ, ∀ q ∈ Kset n k B ρ,
      Cdel n δ p p - 2 * Cdel n δ p q + Cdel n δ q q ≤ L * ‖p - q‖ := by
    filter_upwards [hL 1 one_pos, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ hδ1
    intro p hp q hq
    obtain ⟨m1, b1, r1, s1, -⟩ := hKmem p hp
    obtain ⟨m2, b2, r2, s2, -⟩ := hKmem q hq
    have hmod := (hδ _ m1 _ m2 _ _ _ _ b1 b2 r1 s1 r2 s2).2.2
    have hmn1 := ccomb_mass_nondeg (n := n) hδ1.1 hδ1.2.le (r1.trans hρ64) (s1.trans hρ64)
    have hmn2 := ccomb_mass_nondeg (n := n) hδ1.1 hδ1.2.le (r2.trans hρ64) (s2.trans hρ64)
    have hcomm : (ccomb n δ q).logCov (ccomb n δ p) = (ccomb n δ p).logCov (ccomb n δ q) :=
      CircDom.logCov_comm hmn2.1 hmn2.2 hmn1.1 hmn1.2
    have hexp := MeanTransfer.logCov_sub_sub (ccomb n δ p) (ccomb n δ q)
    have lhs : Cdel n δ p p - 2 * Cdel n δ p q + Cdel n δ q q =
        δ⁻¹ * ((ccomb n δ p).sub (ccomb n δ q)).logCov ((ccomb n δ p).sub (ccomb n δ q)) := by
      simp only [Cdel, if_pos hδ1.2.le]
      rw [hexp, hcomm]
      ring
    rw [lhs]
    refine hmod.trans ?_
    have hsup : (⨆ x ∈ Icc (0 : ℝ) 1, |fOf n p x - fOf n q x|) ≤ ‖p - q‖ :=
      Real.iSup_le (fun x => Real.iSup_le (fun _ => abs_fOf_sub_le n p q x) (norm_nonneg _))
        (norm_nonneg _)
    have hsup0 : 0 ≤ ⨆ x ∈ Icc (0 : ℝ) 1, |fOf n p x - fOf n q x| :=
      Real.iSup_nonneg fun x => Real.iSup_nonneg fun _ => abs_nonneg _
    have hX : (⨆ x ∈ Icc (0 : ℝ) 1, |fOf n p x - fOf n q x|) +
        ‖p0Of (16 ^ n) p - p0Of (16 ^ n) q‖ + ‖p1Of (16 ^ n) p - p1Of (16 ^ n) q‖ ≤
          5 * ‖p - q‖ := by
      linarith [norm_p0Of_sub_le p q, norm_p1Of_sub_le p q]
    have hX0 : 0 ≤ (⨆ x ∈ Icc (0 : ℝ) 1, |fOf n p x - fOf n q x|) +
        ‖p0Of (16 ^ n) p - p0Of (16 ^ n) q‖ + ‖p1Of (16 ^ n) p - p1Of (16 ^ n) q‖ := by
      positivity
    calc Lmod * ((⨆ x ∈ Icc (0 : ℝ) 1, |fOf n p x - fOf n q x|) +
          ‖p0Of (16 ^ n) p - p0Of (16 ^ n) q‖ + ‖p1Of (16 ^ n) p - p1Of (16 ^ n) q‖)
        ≤ max Lmod 0 * ((⨆ x ∈ Icc (0 : ℝ) 1, |fOf n p x - fOf n q x|) +
          ‖p0Of (16 ^ n) p - p0Of (16 ^ n) q‖ + ‖p1Of (16 ^ n) p - p1Of (16 ^ n) q‖) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
      _ ≤ max Lmod 0 * (5 * ‖p - q‖) := mul_le_mul_of_nonneg_left hX (le_max_right _ _)
      _ = L * ‖p - q‖ := by rw [hLdef]; ring
  -- apply `ExpectedSupLimit`
  have hE := hESL (16 ^ n + 4) (Kset n k B ρ) hKc (Cdel n) (Clim n)
    (fun _ _ => 0) (fun _ => 0) L ha hb hc hd continuousOn_const θ hθ
  -- the small-`δ` conditions
  set δ₀ : ℝ := 1 / (8 * ((16 ^ n : ℕ) : ℝ) * ((k : ℝ) + 1)) with hδ₀def
  have hδ₀ : 0 < δ₀ := by positivity
  filter_upwards [hE, hL 1 one_pos, Ioo_mem_nhdsGT hδ₀,
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hEδ h33 hδ hδ1
  intro F hFne hFsub
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkδ : ((k : ℝ) + 1) * δ < 1 / (8 * ((16 ^ n : ℕ) : ℝ)) := by
    calc ((k : ℝ) + 1) * δ < ((k : ℝ) + 1) * δ₀ := mul_lt_mul_of_pos_left hδ.2 hk0
      _ = 1 / (8 * ((16 ^ n : ℕ) : ℝ)) := by rw [hδ₀def]; field_simp
  have hkδ2 : ((k : ℝ) + 1) * δ ^ 2 < 1 / (8 * ((16 ^ n : ℕ) : ℝ)) := by
    calc ((k : ℝ) + 1) * δ ^ 2 = (((k : ℝ) + 1) * δ) * δ := by ring
      _ ≤ ((k : ℝ) + 1) * δ := by
          have := mul_pos hk0 hδ.1
          nlinarith [hδ1.2]
      _ < _ := hkδ
  have hk1 : ((k : ℝ) + 1) * δ ^ 2 ≤ 1 := by
    have : 1 / (8 * ((16 ^ n : ℕ) : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith
  have hk2 : 2 * (((k : ℝ) + 1) * δ ^ 2) < 1 / (2 * ((16 ^ n : ℕ) : ℝ)) := by
    have e : 2 * (1 / (8 * ((16 ^ n : ℕ) : ℝ))) < 1 / (2 * ((16 ^ n : ℕ) : ℝ)) := by
      rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hspec := fun c (hc : c ∈ F) => prm_spec hn hδ.1 hδ1.2 hk1 hk2 (hFsub hc)
  -- the parameters lie in `K`
  have hπK : ∀ c ∈ F, prm (16 ^ n) δ c ∈ Kset n k B ρ := by
    intro c hc
    obtain ⟨hbox, hp0, hp1, heq⟩ := hspec c hc
    refine ⟨hbox, ?_, hp0, hp1⟩
    have hbf := abs_fOf_le n hbox hB0
    have h := (h33 _ (fOf_mem n (prm (16 ^ n) δ c)) _ (fOf_mem n (prm (16 ^ n) δ c)) _ _ _ _
      hbf hbf hp0 hp1 hp0 hp1).2.1
    have e1 : ‖(1 + (δ : ℂ) * p1Of (16 ^ n) (prm (16 ^ n) δ c)) -
        (δ : ℂ) * p0Of (16 ^ n) (prm (16 ^ n) δ c)‖ =
        polyLen (constrCfg (16 ^ n) δ (fOf n (prm (16 ^ n) δ c))
          (p0Of (16 ^ n) (prm (16 ^ n) δ c)) (p1Of (16 ^ n) (prm (16 ^ n) δ c))).1 :=
      (LFPPRecords.polyLen_pair _ _).symm
    rw [e1, heq] at h
    have hlog := smallFamily_log_lt (hFsub hc)
    have hz : δ ^ (-2 : ℤ) = (δ ^ 2)⁻¹ := by rw [zpow_neg, zpow_two, sq]
    have hd2 : δ ^ (-2 : ℤ) * Real.log (polyLen c.2 / polyLen c.1) < (k : ℝ) + 1 := by
      rw [hz, inv_mul_lt_iff₀ (pow_pos hδ.1 2)]
      linarith
    have := (abs_le.1 h).1
    linarith
  -- the covariances are the parameter kernels
  have hcov : ∀ c ∈ F, ∀ c' ∈ F, δ⁻¹ * (cfgComb c).logCov (cfgComb c') =
      Cdel n δ (prm (16 ^ n) δ c) (prm (16 ^ n) δ c') := by
    intro c hc c' hc'
    simp only [Cdel, if_pos hδ1.2.le, ccomb, (hspec c hc).2.2.2, (hspec c' hc').2.2.2]
  have hFK : ↑(F.image (prm (16 ^ n) δ)) ⊆ Kset n k B ρ := by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
    exact hπK c hc
  have hPSD' : PSDOn (F.image (prm (16 ^ n) δ)) (Cdel n δ) := ha δ hδ.1 _ hFK
  have step1 : gaussianExpectedMax F (fun c c' => δ⁻¹ * (cfgComb c).logCov (cfgComb c'))
      (fun _ => -(k : ℝ)) =
      gaussianExpectedMax (F.image (prm (16 ^ n) δ)) (Cdel n δ) (fun _ => -(k : ℝ)) := by
    rw [← gEM_comp_image F (prm (16 ^ n) δ) (Cdel n δ) (fun _ => -(k : ℝ)) hPSD']
    exact Subadd.gEM_congr F (fun c hc c' hc' => hcov c hc c' hc') (fun _ _ => rfl)
  have step2 := gEM_const (F.image (prm (16 ^ n) δ)) (hFne.image _) (Cdel n δ) hPSD' (-(k : ℝ))
  obtain ⟨G, hGK, hFG⟩ := hEδ (F.image (prm (16 ^ n) δ)) hFK
  rw [step1, step2]
  -- nonnegativity facts for the right side
  have han : 0 ≤ a n := EReal.toReal_nonneg (Bounds.aE_nonneg n)
  have hC0 : 0 ≤ max C₃ 0 := le_max_right _ _
  have hn34 : 0 ≤ (n : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hk14 : 0 ≤ ((k : ℝ) + 1) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hk0.le _
  rcases G.eq_empty_or_nonempty with hG | hG
  · rw [hG, gEM_empty] at hFG
    have h1 : -(k : ℝ) ≤ min (a n + max C₃ 0)
        (max C₃ 0 * (n : ℝ) ^ (3 / 4 : ℝ) * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k + max C₃ 0) := by
      refine le_min (by linarith [Nat.cast_nonneg (α := ℝ) k]) ?_
      have := mul_nonneg (mul_nonneg hC0 hn34) hk14
      linarith
    linarith
  · have hPSDG0 := psdOn_zDiffCov (G.image (psi33 n)) (fun q => q.1)
      (fun q => affineFn q.2.1 q.2.2)
      (fun q hq => by
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hq
        exact Subadd.V_continuous (fOf_mem n p))
      (fun q _ => L33.affineFn_continuous _ _)
    have hPSDG : PSDOn (G.image (psi33 n)) Ker33 :=
      psdOn_congr _ hPSDG0 fun _ _ _ _ => rfl
    have step3 : gaussianExpectedMax G (Clim n) (fun _ => 0) =
        gaussianExpectedMax (G.image (psi33 n)) Ker33 (fun _ => 0) := by
      rw [← gEM_comp_image G (psi33 n) Ker33 (fun _ => 0) hPSDG]
      exact Subadd.gEM_congr G (fun _ _ _ _ => rfl) (fun _ _ => rfl)
    have step4 := gEM_const (G.image (psi33 n)) (hG.image _) Ker33 hPSDG (-(k : ℝ))
    have step5 : gaussianExpectedMax (G.image (psi33 n)) Ker33 (fun _ => -(k : ℝ)) ≤
        min (a n + C₃) (C₃ * (n : ℝ) ^ (3 / 4 : ℝ) * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k + C₃) := by
      refine hC₃ n hn k (G.image (psi33 n)) (hG.image _) fun q hq => ?_
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨-, -, h3, h4, h5⟩ := hKmem p (hGK hp)
      rw [← cellRad_eq n]
      exact ⟨fOf_mem n p, h5, (Complex.abs_im_le_norm _).trans h3,
        (Complex.abs_im_le_norm _).trans h4⟩
    have step6 : min (a n + C₃) (C₃ * (n : ℝ) ^ (3 / 4 : ℝ) * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k + C₃)
        ≤ min (a n + max C₃ 0)
          (max C₃ 0 * (n : ℝ) ^ (3 / 4 : ℝ) * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) - k + max C₃ 0) := by
      have hle := le_max_left C₃ 0
      have hX : C₃ * (n : ℝ) ^ (3 / 4 : ℝ) * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) ≤
          max C₃ 0 * (n : ℝ) ^ (3 / 4 : ℝ) * ((k : ℝ) + 1) ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hn34) hk14
      exact min_le_min (by linarith) (by linarith)
    linarith

/-- **Node `M46` ((4.6))**, from `ConstrainedCovLimit` alone (`ExpectedSupLimit` is proved). -/
theorem recordMeanLimit_of_constrainedCovLimit (hL32c : Blueprint.Draft.ConstrainedCovLimit) :
    Blueprint.Draft.RecordMeanLimit :=
  recordMeanLimit_of hL32c expectedSupLimit

end LQGDimension
