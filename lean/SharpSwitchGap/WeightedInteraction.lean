import OAI.Probability.SwitchChain.RankOneInteraction
import SharpSwitchGap.WeightedScalars

/- Weighted adaptation of openai-math#131's RankOneInteraction argument
(pin adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0).
This proves the abstract plane estimate. WeightedCell.lean transports it to the
actual graph cells, using the probability identities in GraphCellWeights.lean. -/

namespace SharpSwitchGap.WeightedInteraction

open scoped RealInnerProductSpace
open OAI.Problem315.RankOneInteraction

theorem rank_one_disjoint_interaction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q G R S : E →ₗ[ℝ] E)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (u v : E) (c α β : ℝ) (hc : c ^ 2 < 1) (hc0 : c ≤ 0)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hfactor : α * β = c ^ 2)
    (huu : inner ℝ u u = 1) (hvv : inner ℝ v v = 1) (huv : inner ℝ u v = c)
    (hPu : P u = u) (hPv : P v = c • u)
    (hQu : Q u = c • v) (hQv : Q v = v)
    (hPQ : ∀ z, P (Q z) = (c * inner ℝ z v) • u)
    (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (hRline : R (v - c • u) = v - c • u)
    (hSline : S (u - c • v) = u - c • v)
    (f : E) :
    2 * ‖G f‖ ^ 2 - α * ‖R f‖ ^ 2 - β * ‖S f‖ ^ 2 ≤
      2 * inner ℝ (f - P f) (f - Q f) := by
  obtain ⟨x, y, hfu, hfv⟩ := exists_plane_coefficients
    (inner ℝ f u) (inner ℝ f v) c (by linarith)
  let j := f - P f - Q f + (c * y) • u + (c * x) • v
  let a := y • (v - c • u)
  let b := x • (u - c • v)
  have hid : inner ℝ (f - P f) (f - Q f) = ‖j‖ ^ 2 + inner ℝ a b :=
    projection_interaction_identity P Q hPs hQs hPi hQi u v c huu hvv huv
      hPu hPv hQu hQv hPQ f x y hfu hfv
  have hGu : G u = 0 := by rw [← hPu, hGP]
  have hGv : G v = 0 := by rw [← hQv, hGQ]
  have hGj : G j = G f := by
    simp only [j, map_add, map_sub, map_smul, hGP, hGQ, hGu, hGv,
      smul_zero, sub_zero, add_zero]
  have hg : ‖G f‖ ^ 2 ≤ ‖j‖ ^ 2 := by
    rw [← hGj]
    exact projection_norm_sq_le G hGs hGi j
  have hfa : inner ℝ f a = inner ℝ a a := by
    apply error_inner_self f u v c y huu hvv huv
    rw [hfu, hfv]
    ring
  have hfb : inner ℝ f b = inner ℝ b b := by
    apply error_inner_self f v u c x hvv huu
      (by rw [real_inner_comm, huv])
    rw [hfu, hfv]
    ring
  have hra : ‖a‖ ^ 2 ≤ ‖R f‖ ^ 2 :=
    error_norm_sq_le R hRs f a (by simp only [a, map_smul, hRline]) hfa
  have hsb : ‖b‖ ^ 2 ≤ ‖S f‖ ^ 2 :=
    error_norm_sq_le S hSs f b (by simp only [b, map_smul, hSline]) hfb
  have hvu : inner ℝ v u = c := by rw [real_inner_comm, huv]
  have han : ‖a‖ ^ 2 = y ^ 2 * (1 - c ^ 2) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [a, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      RCLike.conj_to_real, huu, hvv, huv, hvu]
    ring
  have hbn : ‖b‖ ^ 2 = x ^ 2 * (1 - c ^ 2) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [b, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      RCLike.conj_to_real, huu, hvv, huv, hvu]
    ring
  have hab : inner ℝ a b = -c * x * y * (1 - c ^ 2) := by
    simp only [a, b, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      RCLike.conj_to_real, huu, hvv, huv, hvu]
    ring
  have hs := WeightedScalars.weighted_square α β (-c) x y hα hβ
    (by linarith) (by simpa using hfactor)
  have hplane : -α * ‖a‖ ^ 2 - β * ‖b‖ ^ 2 ≤ 2 * inner ℝ a b := by
    rw [han, hbn, hab]
    nlinarith [mul_nonneg (show 0 ≤ 1 - c ^ 2 by linarith) hs]
  have hra' := mul_le_mul_of_nonneg_left hra hα
  have hsb' := mul_le_mul_of_nonneg_left hsb hβ
  linarith

end SharpSwitchGap.WeightedInteraction

#print axioms SharpSwitchGap.WeightedInteraction.rank_one_disjoint_interaction
