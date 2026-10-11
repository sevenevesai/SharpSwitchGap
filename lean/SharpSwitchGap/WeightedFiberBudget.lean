import SharpSwitchGap.WeightedSliceTransport
import SharpSwitchGap.WeightedError
import OAI.Probability.SwitchChain.PairEqualityBudgetUnordered

namespace SharpSwitchGap.WeightedFiberBudget

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 PairResampling PairFiber PairEquality
open GraphCellWeights WeightedError
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem restriction_weighted (G : GraphState n d) (i j k l : Fin n) (hij : i ≠ j)
    (f : StateSpace n d) :
    assignmentRestriction G i j hij (weightedProjection i j k l f) =
      Real.sqrt (fiberWeight i j G) • assignmentRestriction G i j hij (projection i j k l f) := by
  ext T
  let H := (stateFiberEquiv G i j hij).symm T
  have hfiber : SameFiber {i,j} H.val.val G.val :=
    (sameFiber_iff_key_eq i j hij H.val.val G.val).mpr H.property
  change Real.sqrt (fiberWeight i j H.val) * projection i j k l f H.val =
    Real.sqrt (fiberWeight i j G) * projection i j k l f H.val
  rw [fiberWeight_constant i j hij hfiber]

theorem restriction_weighted_norm_sq (G : GraphState n d) (i j k l : Fin n) (hij : i ≠ j)
    (f : StateSpace n d) :
    ‖assignmentRestriction G i j hij (weightedProjection i j k l f)‖ ^ 2 =
      fiberWeight i j G * ‖assignmentRestriction G i j hij (projection i j k l f)‖ ^ 2 := by
  rw [restriction_weighted, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (fiberWeight_nonneg i j G)]

theorem orderedGain_fluctuation (i j k l : Fin n) (f : StateSpace n d) :
    orderedGain i j k l (fluctuation n d {i,j} f) = orderedGain i j k l f := by
  rw [orderedGain_eq_gain, fluctuation_eq_sub, map_sub, CrossToggle.gain_expectation_left, sub_zero]

theorem restriction_centered (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (f : StateSpace n d) :
    (∑ T, assignmentRestriction G i j hij (fluctuation n d {i,j} f) T) = 0 := by
  have hz : expectation n d {i,j} (fluctuation n d {i,j} f) = 0 := by
    rw [fluctuation_eq_sub, map_sub, expectation_idempotent, sub_self]
  have he := expectation_eq_assignment_average G i j hij (fluctuation n d {i,j} f)
  rw [hz] at he
  change 0 = (∑ T, assignmentRestriction G i j hij (fluctuation n d {i,j} f) T) / _ at he
  apply (div_eq_zero_iff.mp he.symm).resolve_right
  exact_mod_cast (Nat.choose_pos (Finset.card_le_card (leftSet_subset_singletonSet G.val i j))).ne'

theorem assignment_budget (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (f : StateSpace n d) :
    (1/2 : ℝ) * (∑ k, ∑ l, if k = l then 0 else
      ‖assignmentRestriction G i j hij (weightedProjection i j k l f)‖ ^ 2) +
      ‖assignmentRestriction G i j hij (fluctuation n d {i,j} f)‖ ^ 2 ≤
      (1/2 : ℝ) * ∑ k, ∑ l, ‖assignmentRestriction G i j hij (orderedGain i j k l f)‖ ^ 2 := by
  have hq : (leftSet G.val i j).card ≤ Fintype.card (singletonSet G.val i j) := by
    rw [Fintype.card_coe]
    exact Finset.card_le_card (leftSet_subset_singletonSet G.val i j)
  let g := fluctuation n d {i,j} f
  have h := WeightedSlice.reindexed_centered (assignmentNormalizedEquiv G i j) hq
    (assignmentRestriction G i j hij g) (restriction_centered G i j hij f)
  have hswap (x y : singletonSet G.val i j) (T : Assignment G.val i j) :
      (assignmentNormalizedEquiv G i j).symm
        (SliceEuclideanGenerator.swapState (leftSet G.val i j).card x y
          (assignmentNormalizedEquiv G i j T)) =
        assignmentRelabel G.val i j (Equiv.swap x y) T :=
    SliceNormalized.conjugated_swap_cardSlice (assignmentSliceEquiv G.val i j) x y T
  simp_rw [← restriction_projection_energy_eq_raw G i j hij, hswap, assignmentRestriction_apply] at h
  have hgproj (k l : Fin n) : projection i j k l g = projection i j k l f :=
    projection_fluctuation i j k l f
  have hggain (k l : Fin n) : orderedGain i j k l g = orderedGain i j k l f :=
    orderedGain_fluctuation i j k l f
  have hgain : (1/8 : ℝ) * ∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
      ∑ T : Assignment G.val i j,
        (g ((stateFiberEquiv G i j hij).symm T).val -
          g ((stateFiberEquiv G i j hij).symm (assignmentRelabel G.val i j (Equiv.swap x y) T)).val)^2 =
      (1/2 : ℝ) * ∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
        ‖assignmentRestriction G i j hij (orderedGain i j x.val y.val f)‖ ^ 2 := by
    simp_rw [← hggain, assignment_orderedGain_norm_sq G i j hij]
    simp only [← Finset.mul_sum]
    ring
  rw [hgain] at h
  simp_rw [hgproj] at h
  have hproj : (∑ k : Fin n, ∑ l : Fin n, if k = l then 0 else
      ‖assignmentRestriction G i j hij (weightedProjection i j k l f)‖ ^ 2) =
      fiberWeight i j G * (∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
        if x = y then 0 else ‖assignmentRestriction G i j hij (projection i j x.val y.val f)‖ ^ 2) := by
    have hterm (k l : Fin n) : (if k = l then 0 else
        ‖assignmentRestriction G i j hij (weightedProjection i j k l f)‖ ^ 2) =
        fiberWeight i j G * (if k = l then 0 else
          ‖assignmentRestriction G i j hij (projection i j k l f)‖ ^ 2) := by
      by_cases hkl : k = l
      · simp [hkl]
      · simp only [hkl, ite_false]
        exact restriction_weighted_norm_sq G i j k l hij f
    simp_rw [hterm]
    simp_rw [← Finset.mul_sum]
    rw [assignment_projection_sum_eq_singletons G i j hij f]
  rw [hproj]
  have hle := sum_array_subtype_le (singletonSet G.val i j)
    (fun k l => ‖assignmentRestriction G i j hij (orderedGain i j k l f)‖ ^ 2)
    (fun _ _ => sq_nonneg _)
  change fiberWeight i j G * _ + _ ≤ _ at h
  nlinarith

end
end SharpSwitchGap.WeightedFiberBudget
