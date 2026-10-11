import SharpSwitchGap.WeightedSlice
import OAI.Probability.SwitchChain.SliceReindexedComparison

namespace SharpSwitchGap.WeightedSlice

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 SliceNormalized
variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

theorem reindexed_centered {q : ℕ} (e : Ω ≃ State V q) (hq : q ≤ Fintype.card V)
    (f : EuclideanSpace ℝ Ω) (hf : ∑ ω, f ω = 0) :
    SliceMoments.equalMean (Finset.univ : Finset V) q *
      ((1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ reindexedRaw e i j).starProjection f‖ ^ 2) +
      ‖f‖ ^ 2 ≤ (1/8 : ℝ) * ∑ i, ∑ j, ∑ ω : Ω,
        (f ω - f (e.symm (SliceEuclideanGenerator.swapState q i j (e ω)))) ^ 2 := by
  let g : Space V q := (pullback e).symm f
  have hfg : pullback e g = f := (pullback e).apply_symm_apply f
  have hg : ∑ S, g S = 0 := by
    rw [← e.sum_comp (fun S => g S)]
    change (∑ ω, pullback e g ω) = 0
    rw [hfg, hf]
  have h := weighted_centered q hq g hg
  dsimp only at h
  rw [raw_projection_frame_energy q hq g, SliceEuclideanGenerator.generator_energy] at h
  have hp (i j : V) : ‖(ℝ ∙ reindexedRaw e i j).starProjection f‖ ^ 2 =
      ‖(ℝ ∙ raw q i j).starProjection g‖ ^ 2 := by
    rw [← hfg]
    exact congrArg (fun t : ℝ => t ^ 2) (norm_projection_pullback e (raw q i j) g)
  have hm (i j : V) : (∑ ω : Ω,
      (f ω - f (e.symm (SliceEuclideanGenerator.swapState q i j (e ω)))) ^ 2) =
      ‖g - SliceEuclideanGenerator.moveOperator q i j g‖ ^ 2 := by
    calc
      _ = ‖f - reindexedMove e i j f‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        rfl
      _ = _ := by rw [← hfg, ← pullback_move, ← map_sub, (pullback e).norm_map]
  simp_rw [hp, hm]
  rw [← hfg, (pullback e).norm_map]
  exact h

end
end SharpSwitchGap.WeightedSlice
