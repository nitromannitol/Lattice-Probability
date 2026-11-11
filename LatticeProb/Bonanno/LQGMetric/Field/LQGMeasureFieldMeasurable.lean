import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueOpenExist
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.GMCInterfaces

/-!
# Measurable versions of the γ-LQG area measure

For a family of random measures `ν n : Ω → Measure ℂ` whose integrals against continuous compactly supported
functions are measurable, the vague limit is a measurable function of `ω` on the event where it exists
(`LatticeProb.VagueWholePlane.exists_measurable_vagueLimit`). The construction uses a countable dense family of test
functions (`exists_denseTestFamilyC`), the Riesz–Markov–Kakutani existence of vague limits on `ℂ`
(`QuantumZipper.VagueOpen.exists_isVagueLimitOn_of_tendsto_open`), and the continuous cutoffs of open sets.

Applied to the approximations `ε^{γ²/2} e^{γ h_ε(z)} dz`, `ε = 2^{-k}`, of the γ-LQG area measure of a whole-plane
Gaussian free field with jointly measurable, locally continuous circle averages `h_ε(z)` (Duplantier–Sheffield 2011,
Proposition 1.1), the area measure agrees almost surely with a measurable function of the field
(`LatticeProb.exists_measurable_version_of_lqgArea`).
-/

noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LatticeProb
namespace VagueWholePlane

/-- A continuous compactly supported function on `ℂ`. -/
def IsTestC (f : ℂ → ℝ) : Prop := Continuous f ∧ HasCompactSupport f

theorem IsTestC.integrable {μ : Measure ℂ} {f : ℂ → ℝ} (hf : IsTestC f) (hμ : μ (tsupport f) < ∞) :
    Integrable f μ :=
  QuantumZipper.VagueOpen.integrable_of_testFun hf.1 hf.2 hμ

/-- A countable family of test functions, uniformly dense with support control, and with dominating bumps. -/
def IsDenseTestFamilyC (F : Set (ℂ → ℝ)) : Prop :=
  (∀ f ∈ F, IsTestC f) ∧ ∀ f, IsTestC f → ∃ K, IsCompact K ∧ tsupport f ⊆ K ∧
    (∃ φ ∈ F, (∀ z, 0 ≤ φ z) ∧ ∀ z ∈ K, 1 ≤ φ z) ∧
    ∀ η > 0, ∃ g ∈ F, tsupport g ⊆ K ∧ ∀ z, |f z - g z| ≤ η

theorem tendsto_of_denseTestFamilyC {μs : ℕ → Measure ℂ}
    (hfin : ∀ K, IsCompact K → ∀ᶠ k in atTop, μs k K < ∞) {F : Set (ℂ → ℝ)}
    (hF : IsDenseTestFamilyC F)
    (hconv : ∀ f ∈ F, ∃ l, Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 l))
    (f : ℂ → ℝ) (hf : IsTestC f) :
    ∃ l, Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 l) := by
  obtain ⟨K, hK, hfK, ⟨φ, hφF, hφ0, hφ1⟩, happrox⟩ := hF.2 f hf
  have hφ := hF.1 φ hφF
  obtain ⟨lφ, hlφ⟩ := hconv φ hφF
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
  set B := |lφ| + 1 with hB
  have hB0 : 0 < B := by positivity
  set η := ε / (4 * B) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨g, hgF, hgK, hfg⟩ := happrox η hη0
  have hg := hF.1 g hgF
  obtain ⟨lg, hlg⟩ := hconv g hgF
  obtain ⟨N1, hN1⟩ := Metric.cauchySeq_iff.1 hlg.cauchySeq (ε / 2) (by positivity)
  have hev : ∀ᶠ k in atTop, |∫ z, f z ∂(μs k) - ∫ z, g z ∂(μs k)| ≤ ε / 4 := by
    have hbφ : ∀ᶠ k in atTop, ∫ z, φ z ∂(μs k) < B :=
      hlφ.eventually (gt_mem_nhds (by rw [hB]; linarith [le_abs_self lφ]))
    filter_upwards [hfin K hK, hfin _ hφ.2.isCompact, hbφ] with k hkK hkφ hkb
    have hif : Integrable f (μs k) := hf.integrable ((measure_mono hfK).trans_lt hkK)
    have hig : Integrable g (μs k) := hg.integrable ((measure_mono hgK).trans_lt hkK)
    have hiφ : Integrable φ (μs k) := hφ.integrable hkφ
    have hpt : ∀ z, |f z - g z| ≤ η * φ z := by
      intro z
      by_cases hz : z ∈ K
      · calc |f z - g z| ≤ η := hfg z
          _ = η * 1 := (mul_one η).symm
          _ ≤ η * φ z := mul_le_mul_of_nonneg_left (hφ1 z hz) hη0.le
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hfK h)),
          image_eq_zero_of_notMem_tsupport (fun h => hz (hgK h)), sub_zero, abs_zero]
        exact mul_nonneg hη0.le (hφ0 z)
    calc |∫ z, f z ∂(μs k) - ∫ z, g z ∂(μs k)| = |∫ z, (f z - g z) ∂(μs k)| := by
          rw [integral_sub hif hig]
      _ ≤ ∫ z, |f z - g z| ∂(μs k) := abs_integral_le_integral_abs
      _ ≤ ∫ z, η * φ z ∂(μs k) :=
          integral_mono (hif.sub hig).abs (hiφ.const_mul η) hpt
      _ = η * ∫ z, φ z ∂(μs k) := integral_const_mul _ _
      _ ≤ η * B := mul_le_mul_of_nonneg_left hkb.le hη0.le
      _ = ε / 4 := by rw [hη]; field_simp
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 hev
  refine ⟨max N1 N2, fun m hm n hn => ?_⟩
  have h1 := hN2 m (le_of_max_le_right hm)
  have h2 := hN2 n (le_of_max_le_right hn)
  have h3 := hN1 m (le_of_max_le_left hm) n (le_of_max_le_left hn)
  rw [Real.dist_eq] at h3 ⊢
  calc |∫ z, f z ∂(μs m) - ∫ z, f z ∂(μs n)|
      ≤ |∫ z, f z ∂(μs m) - ∫ z, g z ∂(μs m)| + |∫ z, g z ∂(μs m) - ∫ z, g z ∂(μs n)| +
        |∫ z, g z ∂(μs n) - ∫ z, f z ∂(μs n)| := by
        have := abs_sub_le (∫ z, f z ∂(μs m)) (∫ z, g z ∂(μs m)) (∫ z, f z ∂(μs n))
        have := abs_sub_le (∫ z, g z ∂(μs m)) (∫ z, g z ∂(μs n)) (∫ z, f z ∂(μs n))
        linarith
    _ < ε / 4 + ε / 2 + ε / 4 := by
        rw [abs_sub_comm (∫ z, g z ∂(μs n))]
        linarith
    _ = ε := by ring

/-- A bump `φ_n ≥ 0`, `φ_n = 1` on `closedBall 0 n`, compactly supported. -/
theorem exists_bump_closedBall (n : ℕ) :
    ∃ φ : ℂ → ℝ, IsTestC φ ∧ (∀ z, 0 ≤ φ z) ∧ ∀ z ∈ closedBall (0 : ℂ) n, 1 ≤ φ z := by
  obtain ⟨φ, hφ1, -, hφc, hφr⟩ := exists_continuous_one_zero_of_isCompact (X := ℂ)
    (isCompact_closedBall (0 : ℂ) n) (isOpen_ball (x := (0 : ℂ)) (ε := (n : ℝ) + 1)).isClosed_compl
    (Set.disjoint_left.2 fun z hz hzt => hzt (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz) (by linarith))))
  exact ⟨φ, ⟨φ.continuous, hφc⟩, fun z => (hφr z).1, fun z hz => by rw [hφ1 hz]; rfl⟩

/-- For each `n`, a countable family of test functions supported in `closedBall 0 n`, uniformly dense among the test
functions supported there. -/
theorem exists_dense_closedBall (n : ℕ) :
    ∃ D : Set (ℂ → ℝ), D.Countable ∧ (∀ g ∈ D, IsTestC g ∧ tsupport g ⊆ closedBall (0 : ℂ) n) ∧
      ∀ f, IsTestC f → tsupport f ⊆ closedBall (0 : ℂ) n → ∀ η > 0, ∃ g ∈ D, ∀ z, |f z - g z| ≤ η := by
  classical
  have : CompactSpace (closedBall (0 : ℂ) n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let T : Set C(closedBall (0 : ℂ) n, ℝ) :=
    {F | ∃ f : ℂ → ℝ, (IsTestC f ∧ tsupport f ⊆ closedBall (0 : ℂ) n) ∧ ∀ x : closedBall (0 : ℂ) n, F x = f x}
  obtain ⟨c, hcT, hcc, hTc⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace T).exists_countable_dense_subset
  let w : C(closedBall (0 : ℂ) n, ℝ) → (ℂ → ℝ) := fun F => if h : F ∈ T then h.choose else 0
  have hw : ∀ F ∈ T, (IsTestC (w F) ∧ tsupport (w F) ⊆ closedBall (0 : ℂ) n) ∧
      ∀ x : closedBall (0 : ℂ) n, F x = w F x := by
    intro F hF
    simp only [w, hF, ↓reduceDIte]
    exact hF.choose_spec
  refine ⟨w '' c, hcc.image w, ?_, ?_⟩
  · rintro g ⟨F, hF, rfl⟩
    exact (hw F (hcT hF)).1
  · intro f hf hfK η hη
    let F : C(closedBall (0 : ℂ) n, ℝ) := ⟨fun x => f x, hf.1.comp continuous_subtype_val⟩
    have hFT : F ∈ T := ⟨f, ⟨hf, hfK⟩, fun x => rfl⟩
    obtain ⟨G, hGc, hFG⟩ := Metric.mem_closure_iff.1 (hTc hFT) η hη
    obtain ⟨⟨hgt, hgK⟩, hGw⟩ := hw G (hcT hGc)
    refine ⟨w G, ⟨G, hGc, rfl⟩, fun z => ?_⟩
    by_cases hz : z ∈ closedBall (0 : ℂ) n
    · have h1 := ContinuousMap.dist_apply_le_dist (f := F) (g := G) ⟨z, hz⟩
      rw [Real.dist_eq] at h1
      have e1 : F ⟨z, hz⟩ = f z := rfl
      rw [e1, hGw ⟨z, hz⟩] at h1
      exact h1.trans hFG.le
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hfK h)),
        image_eq_zero_of_notMem_tsupport (fun h => hz (hgK h)), sub_zero, abs_zero]
      exact hη.le

/-- **A countable dense test family on `ℂ` exists.** -/
theorem exists_denseTestFamilyC : ∃ F : Set (ℂ → ℝ), F.Countable ∧ IsDenseTestFamilyC F := by
  choose D hDc hDt hDa using exists_dense_closedBall
  choose φ hφt hφ0 hφ1 using exists_bump_closedBall
  refine ⟨⋃ n, (D n ∪ {φ n}), countable_iUnion fun n => (hDc n).union (countable_singleton _), ?_, ?_⟩
  · intro f hf
    obtain ⟨n, hn⟩ := mem_iUnion.1 hf
    rcases hn with hn | hn
    · exact (hDt n f hn).1
    · rw [mem_singleton_iff.1 hn]
      exact hφt n
  · intro f hf
    obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hf.2.isCompact.isBounded
    obtain ⟨n, hn⟩ := exists_nat_ge r
    have hfn : tsupport f ⊆ closedBall (0 : ℂ) n := hr.trans (closedBall_subset_closedBall hn)
    refine ⟨closedBall (0 : ℂ) n, isCompact_closedBall _ _, hfn,
      ⟨φ n, mem_iUnion.2 ⟨n, Or.inr rfl⟩, hφ0 n, hφ1 n⟩, fun η hη => ?_⟩
    obtain ⟨g, hgD, hg⟩ := hDa n f hf hfn η hη
    exact ⟨g, mem_iUnion.2 ⟨n, Or.inl hgD⟩, (hDt n g hgD).2, hg⟩

/-- **Vague limit on `ℂ` from a dense countable family.** -/
theorem exists_isVagueLimitOn_univ_of_family {μs : ℕ → Measure ℂ}
    (hfin : ∀ K, IsCompact K → ∀ᶠ k in atTop, μs k K < ∞) {F : Set (ℂ → ℝ)} (hF : IsDenseTestFamilyC F)
    (hconv : ∀ f ∈ F, ∃ l, Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 l)) :
    ∃ μ, QuantumZipper.IsVagueLimitOn univ μs μ :=
  QuantumZipper.VagueOpen.exists_isVagueLimitOn_of_tendsto_open isOpen_univ (fun K hK _ => hfin K hK)
    fun f hf hfc _ => tendsto_of_denseTestFamilyC hfin hF hconv f ⟨hf, hfc⟩

end VagueWholePlane
namespace VagueWholePlane

/-! ### Continuous cutoffs of open sets -/

/-- `cut U j x = min 1 (j · dist(x, Uᶜ ∪ (B_j)ᶜ))`, continuous, supported in `closedBall 0 j`, increasing to `𝟙_U`. -/
def cut (U : Set ℂ) (j : ℕ) (x : ℂ) : ℝ := min 1 ((j : ℝ) * infDist x (Uᶜ ∪ (ball 0 j)ᶜ))

lemma continuous_cut (U : Set ℂ) (j : ℕ) : Continuous (cut U j) :=
  continuous_const.min (continuous_const.mul (continuous_infDist_pt _))

lemma cut_nonneg (U : Set ℂ) (j : ℕ) (x : ℂ) : 0 ≤ cut U j x :=
  le_min zero_le_one (mul_nonneg (Nat.cast_nonneg j) infDist_nonneg)

lemma cut_le_one (U : Set ℂ) (j : ℕ) (x : ℂ) : cut U j x ≤ 1 := min_le_left _ _

lemma cut_eq_zero {U : Set ℂ} {j : ℕ} {x : ℂ} (hx : x ∈ Uᶜ ∪ (ball 0 j)ᶜ) : cut U j x = 0 := by
  rw [cut, infDist_zero_of_mem hx, mul_zero, min_eq_right zero_le_one]

lemma hasCompactSupport_cut (U : Set ℂ) (j : ℕ) : HasCompactSupport (cut U j) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) j) fun _ hx =>
    cut_eq_zero (Or.inr fun h => hx (ball_subset_closedBall h))

lemma cut_mono (U : Set ℂ) (x : ℂ) : Monotone fun j => cut U j x := by
  intro j j' hjj'
  refine min_le_min le_rfl (mul_le_mul (Nat.cast_le.2 hjj') ?_ infDist_nonneg (Nat.cast_nonneg _))
  refine infDist_le_infDist_of_subset ?_ ?_
  · exact union_subset_union le_rfl (compl_subset_compl.2 (ball_subset_ball (Nat.cast_le.2 hjj')))
  · obtain ⟨y, hy⟩ : ((ball (0 : ℂ) j')ᶜ).Nonempty := by
      refine ⟨(j' : ℂ) + 1, fun h => ?_⟩
      rw [mem_ball, dist_zero_right] at h
      have : ‖((j' : ℂ) + 1)‖ = (j' : ℝ) + 1 := by
        rw [show ((j' : ℂ) + 1) = (((j' : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      linarith
    exact ⟨y, Or.inr hy⟩

lemma iSup_ofReal_cut (U : Set ℂ) (hU : IsOpen U) (x : ℂ) :
    ⨆ j : ℕ, ENNReal.ofReal (cut U j x) = U.indicator 1 x := by
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx, Pi.one_apply]
    refine le_antisymm (iSup_le fun j => ?_) ?_
    · rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (cut_le_one U j x)
    · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
      obtain ⟨j, hj⟩ := exists_nat_gt (max (‖x‖ + δ) (1 / δ))
      have hjx : ‖x‖ + δ < j := lt_of_le_of_lt (le_max_left _ _) hj
      have hjδ : 1 / δ < j := lt_of_le_of_lt (le_max_right _ _) hj
      have hinf : δ ≤ infDist x (Uᶜ ∪ (ball 0 j)ᶜ) := by
        refine (le_infDist ?_).2 fun y hy => ?_
        · exact ⟨(j : ℂ) + (j : ℂ) + 1, Or.inr fun h => by
            rw [mem_ball, dist_zero_right] at h
            have : ‖(j : ℂ) + (j : ℂ) + 1‖ = (j : ℝ) + j + 1 := by
              rw [show (j : ℂ) + (j : ℂ) + 1 = (((j : ℝ) + j + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
                Real.norm_of_nonneg (by positivity)]
            linarith⟩
        · by_contra hlt
          rw [not_le] at hlt
          have hyb : y ∈ ball x δ := by rw [mem_ball, dist_comm]; exact hlt
          rcases hy with hy | hy
          · exact hy (hball hyb)
          · apply hy
            rw [mem_ball, dist_zero_right]
            have := norm_le_norm_add_norm_sub' y x
            rw [mem_ball, dist_eq_norm] at hyb
            linarith
      have h1 : 1 ≤ (j : ℝ) * infDist x (Uᶜ ∪ (ball 0 j)ᶜ) := by
        have : 1 ≤ (j : ℝ) * δ := by
          rw [div_lt_iff₀ hδ] at hjδ
          linarith
        exact this.trans (mul_le_mul_of_nonneg_left hinf (Nat.cast_nonneg j))
      have hcut : cut U j x = 1 := min_eq_left h1
      calc (1 : ℝ≥0∞) = ENNReal.ofReal (cut U j x) := by rw [hcut, ENNReal.ofReal_one]
        _ ≤ ⨆ j : ℕ, ENNReal.ofReal (cut U j x) := le_iSup (fun j : ℕ => ENNReal.ofReal (cut U j x)) j
  · rw [indicator_of_notMem hx]
    refine le_antisymm (iSup_le fun j => ?_) (by simp)
    rw [cut_eq_zero (Or.inl hx), ENNReal.ofReal_zero]

/-- The mass of an open set is the supremum of the integrals of the cutoffs. -/
lemma measure_eq_iSup_integral_cut {m : Measure ℂ} (hm : ∀ K, IsCompact K → m K < ∞) {U : Set ℂ}
    (hU : IsOpen U) : m U = ⨆ j : ℕ, ENNReal.ofReal (∫ x, cut U j x ∂m) := by
  have hint : ∀ j, ENNReal.ofReal (∫ x, cut U j x ∂m) = ∫⁻ x, ENNReal.ofReal (cut U j x) ∂m := fun j =>
    ofReal_integral_eq_lintegral_ofReal
      (IsTestC.integrable (f := cut U j) ⟨continuous_cut U j, hasCompactSupport_cut U j⟩
        (hm _ (hasCompactSupport_cut U j).isCompact))
      (Eventually.of_forall (cut_nonneg U j))
  simp_rw [hint]
  rw [← lintegral_iSup (fun j => (continuous_cut U j).measurable.ennreal_ofReal)
    (fun j j' h x => ENNReal.ofReal_le_ofReal (cut_mono U x h))]
  simp_rw [iSup_ofReal_cut U hU]
  rw [lintegral_indicator hU.measurableSet]
  simp only [Pi.one_apply, setLIntegral_one]

/-! ### The measurable vague limit -/

open Classical in
/-- A chosen vague limit on `ℂ` (or `0`). -/
def vagueLimit (νs : ℕ → Measure ℂ) : Measure ℂ :=
  if h : ∃ μ, QuantumZipper.IsVagueLimitOn univ νs μ then h.choose else 0

lemma vagueLimit_eq {νs : ℕ → Measure ℂ} {μ : Measure ℂ} (h : QuantumZipper.IsVagueLimitOn univ νs μ) :
    vagueLimit νs = μ := by
  have hex : ∃ μ, QuantumZipper.IsVagueLimitOn univ νs μ := ⟨μ, h⟩
  unfold vagueLimit
  split
  · rename_i h'
    exact QuantumZipper.isVagueLimitOn_unique isOpen_univ h'.choose_spec h
  · exact absurd hex ‹_›

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **A measurable choice of vague limits.** -/
theorem exists_measurable_vagueLimit (ν : ℕ → Ω → Measure ℂ) (hν : ∀ n, Measurable (ν n))
    (hint : ∀ n (f : ℂ → ℝ), Continuous f → HasCompactSupport f → Measurable fun ω => ∫ z, f z ∂(ν n ω)) :
    ∃ μ' : Ω → Measure ℂ, Measurable μ' ∧ ∀ ω μ, (∀ K, IsCompact K → ∀ᶠ n in atTop, ν n ω K < ∞) →
      QuantumZipper.IsVagueLimitOn univ (fun n => ν n ω) μ → μ' ω = μ := by
  classical
  obtain ⟨F, hFc, hF⟩ := exists_denseTestFamilyC
  have : Countable F := hFc.to_subtype
  let G : Set Ω := {ω | (∀ f : F, ∃ l, Tendsto (fun n => ∫ z, (f : ℂ → ℝ) z ∂(ν n ω)) atTop (𝓝 l)) ∧
    ∀ j : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ν n ω (closedBall 0 j) < ∞}
  have hG : MeasurableSet G := by
    refine measurableSet_setOfPred.2 (Measurable.and (Measurable.forall fun f => measurableSet_setOfPred.1
      (measurableSet_exists_tendsto fun n => hint n f (hF.1 f f.2).1 (hF.1 f f.2).2))
      (Measurable.forall fun j => Measurable.exists fun N =>
        Measurable.forall fun n => measurable_const.imp (measurableSet_setOfPred.1 ?_)))
    exact measurableSet_lt ((Measure.measurable_coe measurableSet_closedBall).comp (hν n)) measurable_const
  have hfinG : ∀ ω ∈ G, ∀ K, IsCompact K → ∀ᶠ n in atTop, ν n ω K < ∞ := by
    intro ω hω K hK
    obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hK.isBounded
    obtain ⟨j, hj⟩ := exists_nat_ge r
    obtain ⟨N, hN⟩ := hω.2 j
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (measure_mono (hr.trans (closedBall_subset_closedBall hj))).trans_lt (hN n hn)
  have hexG : ∀ ω ∈ G, QuantumZipper.IsVagueLimitOn univ (fun n => ν n ω) (vagueLimit fun n => ν n ω) := by
    intro ω hω
    obtain ⟨μ, hμ⟩ := exists_isVagueLimitOn_univ_of_family (hfinG ω hω) hF fun f hf => hω.1 ⟨f, hf⟩
    rw [vagueLimit_eq hμ]
    exact hμ
  let μ' : Ω → Measure ℂ := fun ω => if ω ∈ G then vagueLimit (fun n => ν n ω) else 0
  have hloc : ∀ ω K, IsCompact K → μ' ω K < ∞ := by
    intro ω K hK
    by_cases hω : ω ∈ G
    · simp only [μ', hω, ↓reduceIte]
      exact (hexG ω hω).2.1 K hK (subset_univ _)
    · simp only [μ', hω, ↓reduceIte,Measure.coe_zero, Pi.zero_apply]
      exact ENNReal.zero_lt_top
  -- the masses of open sets
  have hopen : ∀ U : Set ℂ, IsOpen U → Measurable fun ω => μ' ω U := by
    intro U hU
    have e : (fun ω => μ' ω U) = G.indicator fun ω =>
        ⨆ j : ℕ, ENNReal.ofReal (limsup (fun n => ∫ x, cut U j x ∂(ν n ω)) atTop) := by
      funext ω
      by_cases hω : ω ∈ G
      · rw [indicator_of_mem hω]
        simp only [μ', hω, ↓reduceIte]
        rw [measure_eq_iSup_integral_cut (fun K hK => (hexG ω hω).2.1 K hK (subset_univ _)) hU]
        congr 1
        funext j
        rw [((hexG ω hω).2.2 (cut U j) (continuous_cut U j) (hasCompactSupport_cut U j)
          (subset_univ _)).limsup_eq]
      · rw [indicator_of_notMem hω]
        simp only [μ', hω, ↓reduceIte,Measure.coe_zero, Pi.zero_apply]
    rw [e]
    exact (Measurable.iSup fun j => ENNReal.measurable_ofReal.comp
      (Measurable.limsup fun n => hint n _ (continuous_cut U j) (hasCompactSupport_cut U j))).indicator hG
  -- the restrictions to balls
  have hball : ∀ j : ℕ, Measurable fun ω => (μ' ω).restrict (ball (0 : ℂ) j) := by
    intro j
    have : ∀ ω, IsFiniteMeasure ((μ' ω).restrict (ball (0 : ℂ) j)) := fun ω =>
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (measure_mono ball_subset_closedBall).trans_lt (hloc ω _ (isCompact_closedBall _ _))⟩
    refine Measurable.measure_of_isPiSystem (S := {s | IsOpen s}) BorelSpace.measurable_eq isPiSystem_isOpen
      (fun s hs => ?_) ?_
    · have hs' : IsOpen s := hs
      simp_rw [Measure.restrict_apply hs'.measurableSet]
      exact hopen _ (hs'.inter isOpen_ball)
    · simp_rw [Measure.restrict_apply_univ]
      exact hopen _ isOpen_ball
  refine ⟨μ', Measure.measurable_of_measurable_coe _ fun s hs => ?_, fun ω μ hfin hμ => ?_⟩
  · have e : (fun ω => μ' ω s) = fun ω => ⨆ j : ℕ, (μ' ω).restrict (ball (0 : ℂ) j) s := by
      funext ω
      simp_rw [Measure.restrict_apply hs]
      rw [← Monotone.measure_iUnion fun j j' h => inter_subset_inter_right _ (ball_subset_ball (Nat.cast_le.2 h)),
        ← inter_iUnion, iUnion_ball_nat, inter_univ]
    rw [e]
    exact Measurable.iSup fun j => (Measure.measurable_coe hs).comp (hball j)
  · have hω : ω ∈ G := by
      refine ⟨fun f => ⟨_, hμ.2.2 f (hF.1 f f.2).1 (hF.1 f f.2).2 (subset_univ _)⟩, fun j => ?_⟩
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hfin _ (isCompact_closedBall (0 : ℂ) j))
      exact ⟨N, hN⟩
    simp only [μ', hω, ↓reduceIte]
    exact vagueLimit_eq hμ

end VagueWholePlane

/-! ### Measurable densities and integrals -/

section Density

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma measurable_withDensity_ofReal_uncurry {d : Ω → ℂ → ℝ} (hd : Measurable (Function.uncurry d)) :
    Measurable fun ω => (volume : Measure ℂ).withDensity fun z => ENNReal.ofReal (d ω z) :=
  measurable_withDensity (ENNReal.measurable_ofReal.comp hd)

lemma measurable_integral_withDensity_ofReal_uncurry {d : Ω → ℂ → ℝ} (hd : Measurable (Function.uncurry d))
    (hd0 : ∀ ω z, 0 ≤ d ω z) {f : ℂ → ℝ} (hf : Measurable f) :
    Measurable fun ω => ∫ z, f z ∂((volume : Measure ℂ).withDensity fun z => ENNReal.ofReal (d ω z)) := by
  have e : ∀ ω, ∫ z, f z ∂((volume : Measure ℂ).withDensity fun z => ENNReal.ofReal (d ω z)) =
      ∫ z, d ω z * f z := by
    intro ω
    have hm : Measurable fun z => Real.toNNReal (d ω z) := (hd.comp measurable_prodMk_left).real_toNNReal
    rw [show (fun z => ENNReal.ofReal (d ω z)) = fun z => ((Real.toNNReal (d ω z) : ℝ≥0) : ℝ≥0∞) from rfl,
      integral_withDensity_eq_integral_smul hm]
    congr 1
    funext z
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hd0 ω z), smul_eq_mul]
  simp_rw [e]
  exact (hd.mul (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

lemma withDensity_ofReal_lt_top_of_continuous {g : ℂ → ℝ} (hg : Continuous g) {K : Set ℂ} (hK : IsCompact K) :
    ((volume : Measure ℂ).withDensity fun z => ENNReal.ofReal (g z)) K < ∞ := by
  rw [withDensity_apply _ hK.measurableSet]
  exact (hg.continuousOn.integrableOn_compact hK).lintegral_lt_top

end Density

open MatedCRTHarmonic.GMSLemma27

/-- **Measurable version of the γ-LQG area measure.** Let `H ε z ω` be circle averages of a whole-plane
Gaussian free field on `Ω` with respect to `P`, jointly measurable in `(ω, z)` for the sub-σ-algebra `m` at each
dyadic radius `ε = 2^{-k}`, and continuous in `z` for almost every `ω`. If `μ` is the γ-LQG area measure of `H`
(`IsLQGAreaOf`: the almost sure vague limit of the approximations `ε^{γ²/2} e^{γ h_ε(z)} dz`), then `μ` agrees
almost surely with an `m`-measurable random measure. In applications `m` is the σ-algebra generated by the field
(Duplantier–Sheffield 2011, Proposition 1.1; the measurable choice of vague limits is `VagueWholePlane.exists_measurable_vagueLimit`). -/
theorem exists_measurable_version_of_lqgArea {Ω : Type*} [MeasurableSpace Ω] (m : MeasurableSpace Ω)
    (P : Measure Ω) (γ : ℝ) (H : ℝ → ℂ → Ω → ℝ) (μ : Ω → Measure ℂ)
    (hH : ∀ k : ℕ, Measurable[m.prod (inferInstance : MeasurableSpace ℂ)]
      (Function.uncurry fun ω z => H (dyadicRadius k) z ω))
    (hHc : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous fun z => H (dyadicRadius k) z ω)
    (hμ : IsLQGAreaOf γ H μ P) :
    ∃ μ' : Ω → Measure ℂ, Measurable[m] μ' ∧ ∀ᵐ ω ∂P, μ' ω = μ ω := by
  have hd : ∀ k : ℕ, Measurable[m.prod (inferInstance : MeasurableSpace ℂ)]
      (Function.uncurry fun ω z => dyadicRadius k ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicRadius k) z ω)) :=
    fun k => measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul (hH k)))
  have hd0 : ∀ k : ℕ, ∀ ω z, 0 ≤ dyadicRadius k ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicRadius k) z ω) :=
    fun k ω z => mul_nonneg (Real.rpow_nonneg (by unfold dyadicRadius; positivity) _) (Real.exp_pos _).le
  have hν : ∀ k : ℕ, Measurable[m] fun ω => lqgApprox γ H k ω := fun k =>
    measurable_withDensity_ofReal_uncurry (mΩ := m) (hd k)
  have hint : ∀ (k : ℕ) (f : ℂ → ℝ), Continuous f → HasCompactSupport f →
      Measurable[m] fun ω => ∫ z, f z ∂(lqgApprox γ H k ω) := fun k f hf _ =>
    measurable_integral_withDensity_ofReal_uncurry (mΩ := m) (hd k) (hd0 k) hf.measurable
  obtain ⟨μ', hμ'm, hμ'⟩ := VagueWholePlane.exists_measurable_vagueLimit (mΩ := m)
    (fun k ω => lqgApprox γ H k ω) hν hint
  refine ⟨μ', hμ'm, ?_⟩
  filter_upwards [hHc, hμ] with ω hc hω
  obtain ⟨hloc, hconv⟩ := hω
  have := hloc
  refine hμ' ω (μ ω) (fun K hK => Eventually.of_forall fun k => ?_) ⟨by simp, fun K hK _ => hK.measure_lt_top,
    fun f hf hfc _ => hconv f hf hfc⟩
  exact withDensity_ofReal_lt_top_of_continuous
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hc k)))) hK

end LatticeProb
