/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L35B2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35B1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L34
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L212
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6

/-!
# CONF Lemma 2.12 (1) as printed (`CONFLem2_12aP`), from LM Lemma 3.1 (task P2-CONF35b)

Source: Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381,
`confluence-final.tex` C:785–795 (Lemma 2.12 (1): events `E_{r_k} ∈ σ((h − h_{r_k}(0))|_{𝔸_{S₁r_k,
S₂r_k}(0)})`, `r_{k+1}/r_k ≥ S₂`); Gwynne–Miller, *Local metrics of the GFF*, arXiv:1905.00379,
Lemma 3.1 (`Blueprint.LMLem3_1a`, proved as `LM.lmLem3_1a`); D47's mod-constant form
`CONF.CONFLem2_12a` (`confLem2_12a_of_LM`, radii reversal).

CONF proves L2.12 by "the exact same argument" as LM L3.1 outward, or via inversion (C:798–800).
We instead reduce it to D47's mod-constant form (own elementary argument, proposed DV-CONF-212P):

1. **Measurability** (`ae_eventMod`): the circle average `h_{r}(0)` is determined by `h` near
   `∂B_r(0)`, so an event of `σ((h − h_r(0))|_{𝔸_{S₁r,S₂r}})` is a.s. equal to an event of
   `σ(h|_{𝔸_{r/2,S₂r}})` modulo additive constants (normalize by a unit bump `ψ₀` in the annulus,
   `GM.gm_fieldSigma_eq_fieldSigma0On`), hence measurable for `σ((h − h_ρ(0))|_{𝔸_{r/2,S₂r}})`
   for every `ρ`.
2. **Sparse subsequences**: the annuli `𝔸_{r_k/2, S₂r_k} = 𝔸_{2r'_k, 4S₂r'_k}` (`r'_k = r_k/4`)
   overlap; along each residue class `k = mi + j` (`S₂^m ≥ 4S₂`) they satisfy D47's hypotheses
   with `S₁' = 2`, `S₂' = 4S₂`, and `#{k ≤ K : E_k} < bK` forces `#{i ≤ K' : E_{mi+j}} < b'K'`
   for some `j < m` (`b' = (1+b)/2`, `K' = ⌊K/m⌋ − 1`, `K` large); a union bound over `j` and
   `a' = am` give the rate `e^{−aK}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

theorem measurable_restrictTo_addConst' {Ω : Type} {M : MeasurableSpace Ω} (O : Opens ℂ)
    {Ψ : Ω → DistC} {x : Ω → ℝ} (hΨ : Measurable[M] fun ω => restrictTo O (Ψ ω))
    (hx : Measurable[M] x) : Measurable[M] fun ω => restrictTo O (addConst (Ψ ω) (x ω)) := by
  refine (measurable_distOn_iff (α := Ω)).2 fun φ => ?_
  have e : ∀ ω, restrictTo O (addConst (Ψ ω) (x ω)) φ = restrictTo O (Ψ ω) φ +
      (∫ y, (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤) φ) y) * x ω :=
    fun ω => GFFInv.addConst_apply _ _ _
  simp_rw [e]
  exact ((measurable_distOn_apply φ).comp hΨ).add (hx.const_mul _)

/-- **measurability transfer**: an event of `σ((h − h_r(0))|_{𝔸_{S₁r,S₂r}(0)})` is a.s. equal to
an event measurable for `σ((h + c)|_{𝔸_{r/2,S₂r}(0)})` for every random constant `c`. -/
theorem ae_eventMod {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {r S₁ S₂ : ℝ} (hr : 0 < r) (hS₁ : 1 < S₁)
    (h12 : S₁ < S₂) {E : Set Ω}
    (hE : MeasurableSet[fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) r 0))
      (annulus 0 (S₁ * r) (S₂ * r))] E) :
    ∃ E' : Set Ω, E =ᵐ[P] E' ∧ ∀ c : Ω → ℝ,
      MeasurableSet[fieldSigma (fun ω => addConst (h ω) (c ω)) (annulus 0 (r / 2) (S₂ * r))] E' := by
  set A := annulus 0 (S₁ * r) (S₂ * r)
  set A' := annulus 0 (r / 2) (S₂ * r)
  have hAA' : A ≤ A' := fun x hx => ⟨by have := hx.1; nlinarith, hx.2⟩
  have hsph : sphere (0 : ℂ) r ⊆ (A' : Set ℂ) := fun x hx => by
    rw [mem_sphere, dist_zero_right] at hx
    refine ⟨?_, ?_⟩ <;> simp only [sub_zero, hx] <;> nlinarith
  have hne : (A' : Set ℂ).Nonempty := by
    refine ⟨(r : ℂ), hsph ?_⟩
    rw [mem_sphere, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  obtain ⟨ψ₀, hψA, hψ1⟩ := HarmLoc.exists_unit_test A'.isOpen hne
  set h'' := normIn h ψ₀
  set X : Ω → ℝ := fun ω => circleAvg (h'' ω) r 0
  have hX : Measurable[fieldSigma h'' A'] X :=
    measurable_circleAvg_of_sphere_subset h'' A'.isOpen hr hsph
  have hres : Measurable[fieldSigma h'' A'] fun ω => restrictTo A (h'' ω) :=
    (comap_measurable (fun ω => restrictTo A (h'' ω))).mono (GM.fieldSigma_mono h'' hAA') le_rfl
  set f'' : Ω → DistOn A := fun ω => restrictTo A (addConst (h'' ω) (-X ω))
  have hf'' : Measurable[fieldSigma h'' A'] f'' :=
    measurable_restrictTo_addConst' A hres hX.neg
  obtain ⟨s, hs, rfl⟩ := hE
  refine ⟨f'' ⁻¹' s, ?_, fun c => ?_⟩
  · filter_upwards [CircleAvg.ae_circleAvg_addConst hh 0 hr] with ω hω
    have key : addConst (h'' ω) (-X ω) = addConst (h ω) (-circleAvg (h ω) r 0) := by
      simp only [X, h'', normIn]
      rw [hω, GFFLaw.addConst_addConst]
      congr 1
      ring
    change ((fun ω => restrictTo A (addConst (h ω) (-circleAvg (h ω) r 0))) ω ∈ s) = (f'' ω ∈ s)
    simp only [f'', key]
  · have hle : fieldSigma h'' A' ≤ fieldSigma (fun ω => addConst (h ω) (c ω)) A' := by
      rw [GM.gm_fieldSigma_eq_fieldSigma0On (V := A') hψ1 (normIn_apply_psi h hψ1) hψA,
        fieldSigma0On_normIn, ← fieldSigma0On_addConst h c]
      exact fieldSigma0On_le_fieldSigma _ A'.isOpen
    exact hle _ (hf'' hs)

/-- `r_{k+n} ≥ S^n r_k` -/
theorem rad_pow_le {r : ℕ → ℝ} {S : ℝ} (hS : 0 ≤ S) (hr : ∀ k, 0 < r k)
    (hrat : ∀ k, S ≤ r (k + 1) / r k) (k n : ℕ) : S ^ n * r k ≤ r (k + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : S * r (k + n) ≤ r (k + n + 1) := by
      have := hrat (k + n)
      rwa [le_div_iff₀ (hr _)] at this
    calc S ^ (n + 1) * r k = S * (S ^ n * r k) := by ring
      _ ≤ S * r (k + n) := mul_le_mul_of_nonneg_left ih hS
      _ ≤ r (k + (n + 1)) := h1

open Classical in
/-- the residue classes `k = m i + j`, `1 ≤ i ≤ K'`, `j < m`, inject into `[1, K]` -/
theorem sum_countOcc_le {Ω : Type} (E : ℕ → Set Ω) {m K' K : ℕ} (hm : 1 ≤ m)
    (hK : ∀ i, 1 ≤ i → i ≤ K' → m * i + m ≤ K + 1) (ω : Ω) :
    (∑ j ∈ Finset.range m, countOcc (fun i => E (m * i + j)) K' ω) ≤ countOcc E K ω := by
  unfold countOcc
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn (fun p => m * p.2 + p.1) ?_ ?_
  · intro p hp
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_range,
      Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    obtain ⟨hj, ⟨hi1, hiK⟩, hE⟩ := hp
    refine ⟨⟨?_, ?_⟩, hE⟩
    · nlinarith
    · have := hK _ hi1 hiK
      omega
  · intro p hp q hq hpq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_range] at hp hq
    have hpq' : m * p.2 + p.1 = m * q.2 + q.1 := hpq
    have h1 : p.1 = q.1 := by
      have := congrArg (· % m) hpq'
      simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hp.1, Nat.mod_eq_of_lt hq.1] at this
      exact this
    have h2 : p.2 = q.2 := by
      rw [h1] at hpq'
      have := Nat.add_right_cancel hpq'
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    exact Sigma.ext h1 (heq_of_eq h2)

end LQGMetric.CONF
