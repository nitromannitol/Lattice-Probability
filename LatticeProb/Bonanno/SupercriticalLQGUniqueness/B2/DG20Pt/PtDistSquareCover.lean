/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistSquareCover at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistNet
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGradShift

 


set_option autoImplicit false
noncomputable section

open Set Metric
open LQGMetric.SupTail

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem exists_pt_dist_square_cover (V : Set ℂ)
    (hV : Bornology.IsBounded V) :
    ∃ F : Finset ℂ, ∀ z ∈ V, ∃ c ∈ F, z - c ∈ ferniqueBox 0 1 := by
  obtain ⟨C, hC, hnet⟩ := exists_pt_dist_net V hV
  obtain ⟨F₀, hcard, hcover⟩ := hnet 0
  let shift : ℂ → ℂ := fun x => x - ⟨1 / 2, 1 / 2⟩
  let F : Finset ℂ := F₀.image shift
  refine ⟨F, ?_⟩
  intro z hz
  obtain ⟨x, hx, hzx⟩ := hcover z hz
  refine ⟨shift x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
  have hnorm : ‖z - x‖ < 1 / 4 := by
    norm_num at hzx
    simpa [dist_eq_norm] using hzx
  have hre := abs_le.mp ((Complex.abs_re_le_norm (z - x)).trans hnorm.le)
  have him := abs_le.mp ((Complex.abs_im_le_norm (z - x)).trans hnorm.le)
  simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc,
    Complex.zero_re, Complex.zero_im, zero_add,
    Complex.sub_re, Complex.sub_im, shift]
  constructor <;> constructor <;> norm_num at * <;> linarith

end SupercriticalLQGUniqueness.B2.DG20Pt
