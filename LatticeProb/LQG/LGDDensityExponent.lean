import LatticeProb.LQG.LGDDensitySandwichAE
import LatticeProb.LQG.LGDWalledUpperRate
import LatticeProb.LQG.LGDRandomSandwichExponent
import LatticeProb.Bonanno.LQGMetric.Assembly.MainFinal
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53W1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5InputsW1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5ChiB2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D123
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61C

/-!
# The Liouville graph distance exponent of a measure with a continuous LQG density

Let `W` be a white noise, `0 < γ < 2`, and let `μ` be a random measure that almost surely coincides,
on an open set `V` inside the unit square, with `e^{γ Y} M_γ`, where `M_γ` is the `γ`-LQG measure of
the white-noise field of the unit square and `Y(·, ω)` is continuous. Then for `u ≠ v` joined by a
segment inside `V`, almost surely `log D_δ(μ)(u, v) / log δ⁻¹ → χ_γ` as `δ ↓ 0`, where `χ_γ` is
the Ding-Zeitouni-Zhang exponent (`LQGMetric.chiDZZ`).

The proof is that of Ding-Zeitouni-Zhang (arXiv:1807.00422, Theorem 1.1 and Proposition 5.1): the
distance `D_δ(μ)(u, v)` is squeezed, with random constants in the scale, between the minimal walled
distance of the Wick-normalized measure from `u` to the boundary of a small box around `u` (lower
rate, DZZ Proposition 5.1 lower half) and its walled distance from `u` to `v` with a wall around the
segment (upper rate); the rates hold for the exponent of DZZ Lemma 5.3, which is `χ_γ`.

* `LatticeProb.LQG.ae_tendsto_lgdRatio_of_restrict_eq_withDensity`: the statement above.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric

open DZZ WhiteNoise QuantumZipper

/-- **The Liouville graph distance exponent through a continuous density.** If almost surely
`μ = e^{γ Y} M_γ` on the open set `V ⊆ (0,1)²`, with `M_γ` the `γ`-LQG measure of the white-noise
field of the unit square and `Y(·, ω)` continuous, then for `u ≠ v` whose segment lies in `V`,
almost surely `log D_δ(μ)(u, v) / log δ⁻¹ → χ_γ` as `δ ↓ 0`. -/
theorem _root_.LatticeProb.LQG.ae_tendsto_lgdRatio_of_restrict_eq_withDensity {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} {Y : ℂ → Ω → ℝ}
    (hY : ∀ ω, Continuous fun z => Y z ω) {V : Set ℂ} (hV : IsOpen V) (hVsq : V ⊆ openSquare)
    (hμ : ∀ᵐ ω ∂P, (μ ω).restrict V =
      ((qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare).restrict V).withDensity
        fun z => ENNReal.ofReal (Real.exp (γ * Y z ω)))
    {u v : ℂ} (huv : u ≠ v) (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → u + (t : ℂ) * (v - u) ∈ V) :
    ∀ᵐ ω ∂P, Tendsto (fun δ : ℝ => Real.log (lgdDZZ (μ ω) δ u v).toNat / Real.log δ⁻¹)
      (𝓝[>] 0) (𝓝 (chiDZZ γ)) := by
  -- the exponent of DZZ Lemma 5.3 is `χ_γ`
  obtain ⟨χ, hL⟩ := dzzLem53ExpAll_of_hbadB l53HbadBAll_proved P W hW γ hγ hγ2
  have hw := dzzProp317WallsAll_holds P W hW γ hγ hγ2
  have hχ := dzzChiIdentW P W hW γ hγ hγ2 χ hL hw
  have hc : chiDZZ γ = χ := DZZInW.chiDZZ_eq_of_ident hχ.1 (@And.right _ _ hχ)
  rw [hc]
  have hu : u ∈ V := by simpa using hseg 0 le_rfl zero_le_one
  -- the wall `K'` around the segment
  set S : Set ℂ := (fun t : ℝ => u + (t : ℂ) * (v - u)) '' Icc 0 1 with hSdef
  have hS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hSV : S ⊆ V := by
    rintro _ ⟨t, ⟨h0, h1⟩, rfl⟩
    exact hseg t h0 h1
  obtain ⟨m', hm', hm'V⟩ := hS.exists_cthickening_subset_open hV hSV
  have hKseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℂ, ‖z - (u + (t : ℂ) * (v - u))‖ ≤ m' →
      z ∈ cthickening m' S := fun t h0 h1 z hz =>
    mem_cthickening_of_dist_le z _ m' S ⟨t, ⟨h0, h1⟩, rfl⟩ (by rwa [dist_eq_norm])
  -- the box `U` around `u` and its wall `K`
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV u hu
  have hd : 0 < ‖v - u‖ := norm_pos_iff.2 (sub_ne_zero.2 huv.symm)
  set lam : ℝ := min (min (ε / 4) (1 / 20)) (‖v - u‖ / 2) with hlamdef
  have hlam : 0 < lam := lt_min (lt_min (by positivity) (by norm_num)) (by positivity)
  have hlam1 : lam ≤ 1 / 20 := (min_le_left _ _).trans (min_le_right _ _)
  have hlamε : lam ≤ ε / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hlamd : lam ≤ ‖v - u‖ / 2 := min_le_right _ _
  have hnorm : ∀ z : ℂ, ‖z‖ ≤ |z.re| + |z.im| := fun z => Complex.norm_le_abs_re_add_abs_im z
  set U : Set ℂ := Ioo (u.re - lam / 2) (u.re + lam / 2) ×ℂ Ioo (u.im - lam / 2) (u.im + lam / 2)
    with hUdef
  have hUo : IsOpen U := isOpen_Ioo.reProdIm isOpen_Ioo
  have huU : u ∈ U := by
    rw [hUdef, Complex.mem_reProdIm]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hUsq : U ⊆ sqBox u lam := by
    intro z hz
    rw [hUdef, Complex.mem_reProdIm] at hz
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩
  have hvU : v ∉ U := by
    intro hv
    rw [hUdef, Complex.mem_reProdIm] at hv
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hv
    have h5 := hnorm (v - u)
    rw [Complex.sub_re, Complex.sub_im] at h5
    have h6 : |v.re - u.re| ≤ lam / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have h7 : |v.im - u.im| ≤ lam / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hC : IsCompact (closure U) :=
    (isCompact_sqBox u hlam.le).of_isClosed_subset isClosed_closure
      (closure_minimal hUsq (isClosed_sqBox u lam))
  have hK : IsCompact (sqBox u (2 * lam)) := isCompact_sqBox u (by positivity)
  have hKV : sqBox u (2 * lam) ⊆ V := by
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    refine hεV (mem_ball.2 ?_)
    rw [dist_eq_norm]
    have h5 := hnorm (z - u)
    rw [Complex.sub_re, Complex.sub_im] at h5
    linarith
  have hCK : ∀ p ∈ closure U, ∀ z ∉ sqBox u (2 * lam), 4 * (lam / 8) ≤ dist p z := by
    intro p hp z hz
    obtain ⟨hp1, hp2⟩ := closure_minimal hUsq (isClosed_sqBox u lam) hp
    by_contra hlt
    rw [not_le] at hlt
    have hre : |p.re - z.re| < lam / 2 := by
      have := Complex.abs_re_le_norm (p - z)
      rw [Complex.sub_re, ← dist_eq_norm] at this
      linarith
    have him : |p.im - z.im| < lam / 2 := by
      have := Complex.abs_im_le_norm (p - z)
      rw [Complex.sub_im, ← dist_eq_norm] at this
      linarith
    refine hz ⟨abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩⟩ <;>
      linarith [abs_le.1 hp1, abs_le.1 hp2, abs_lt.1 hre, abs_lt.1 him]
  have hs := LatticeProb.LQG.ae_lgd_sandwich_of_restrict_eq_withDensity hW hγ hγ2 hY hVsq hμ
    hUo hC hK hKV (hS.cthickening) hm'V (r := lam / 8) (by positivity) hCK
  rw [frontier_openBox_eq u hlam] at hs
  refine LatticeProb.LQG.ae_tendsto_lgdRatio_of_random_sandwich
    (g := fun ω δ => lgdDZZ (μ ω) δ u v)
    (lo := fun ω δ => lgdMinSet (dzzWall (sqBox u (2 * lam)) (dzzMuIn γ W ω)) δ {u}
      (frontier (sqBox u lam)))
    (up := fun ω δ => lgdDZZ (dzzWall (cthickening m' S) (dzzMuIn γ W ω)) δ u v)
    (fun ω δ δ' hδ hδδ' => lgdDZZ_antitone _ hδ.le hδδ' u v)
    (fun ω δ δ' hδ hδδ' => LatticeProb.LQG.lgdMinSet_antitone _ hδ.le hδδ' _ _)
    (fun ω δ δ' hδ hδδ' => lgdDZZ_antitone _ hδ.le hδδ' u v)
    (fun ω δ => one_le_lgdDZZ _ _ _ _)
    (fun ι hι => LatticeProb.LQG.hasRate_dzzWall_upper_interior hW hγ hγ2 hL hw (hVsq hu)
      (hVsq (by simpa using hseg 1 zero_le_one le_rfl)) huv hm' hKseg hι)
    (fun ι hι => hasRate_dzzMuIn_lower_box hW hγ hγ2 hL hw (hVsq hu) hlam hlam1
      (hKV.trans hVsq) hι) ?_
  filter_upwards [hs] with ω ⟨a, b, δ₀, hδ₀, h⟩
  exact ⟨Real.exp (b / 2), Real.exp (-a / 2), δ₀, Real.exp_pos _, Real.exp_pos _, hδ₀,
    fun δ hδ hδδ₀ => h δ hδ hδδ₀ u huU v hvU⟩

end LQGMetric
