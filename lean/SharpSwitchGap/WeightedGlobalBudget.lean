import SharpSwitchGap.WeightedFiberBudget

namespace SharpSwitchGap.WeightedFiberBudget

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 PairResampling PairFiber PairEquality
open GraphCellWeights WeightedError
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem ordered_budget (i j : Fin n) (hij : i ≠ j) (f : StateSpace n d) :
    (1/2 : ℝ) * (∑ k, ∑ l, if k = l then 0 else ‖weightedProjection i j k l f‖ ^ 2) +
      ‖fluctuation n d {i,j} f‖ ^ 2 ≤
      (1/2 : ℝ) * ∑ k, ∑ l, ‖orderedGain i j k l f‖ ^ 2 := by
  let F : Fin n × Fin n → StateSpace n d :=
    fun p => if p.1 = p.2 then 0 else weightedProjection i j p.1 p.2 f
  let H : Fin n × Fin n → StateSpace n d := fun p => orderedGain i j p.1 p.2 f
  have hF (G : GraphState n d) (k l : Fin n) :
      ‖assignmentRestriction G i j hij (F (k,l))‖ ^ 2 =
        if k = l then 0 else ‖assignmentRestriction G i j hij (weightedProjection i j k l f)‖ ^ 2 := by
    by_cases hkl : k = l <;> simp [F,hkl]
  have hl (G : GraphState n d) :
      (1/2 : ℝ) * (∑ a, ‖assignmentRestriction G i j hij (F a)‖ ^ 2) +
        ‖assignmentRestriction G i j hij (fluctuation n d {i,j} f)‖ ^ 2 ≤
        (1/2 : ℝ) * ∑ b, ‖assignmentRestriction G i j hij (H b)‖ ^ 2 := by
    simpa only [Fintype.sum_prod_type, hF, H] using assignment_budget G i j hij f
  have h := Finset.sum_le_sum (s := Finset.univ) (fun G _ =>
    div_le_div_of_nonneg_right (hl G)
      (Nat.cast_nonneg (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card)))
  simp only [add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_assignmentRestriction_family_norm_sq i j hij,
    sum_assignmentRestriction_norm_sq i j hij] at h
  have hFg (k l : Fin n) : ‖F (k,l)‖ ^ 2 =
      if k = l then 0 else ‖weightedProjection i j k l f‖ ^ 2 := by
    by_cases hkl : k = l <;> simp [F,hkl]
  simpa only [Fintype.sum_prod_type, hFg, H] using h

def weightedRightPair (i j : Fin n) (b : Finset (Fin n)) (f : StateSpace n d) : StateSpace n d :=
  WithLp.toLp 2 (fun G => Real.sqrt (fiberWeight i j G) * pairProjection {i,j} b f G)

theorem weightedRightPair_pair (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (f : StateSpace n d) : weightedRightPair i j {k,l} f = weightedProjection i j k l f := by
  unfold weightedRightPair weightedProjection
  rw [pairProjection_pair i j k l hij hkl]

theorem weightedRightPair_zero (i j : Fin n) (b : Finset (Fin n))
    (h : ¬ Disjoint ({i,j} : Finset (Fin n)) b) (f : StateSpace n d) :
    weightedRightPair i j b f = 0 := by
  unfold weightedRightPair
  rw [pairProjection_eq_zero_of_not_disjoint _ _ h]
  ext G
  simp

theorem rightPair_sum (i j : Fin n) (hij : i ≠ j) (f : StateSpace n d) :
    (∑ b ∈ pairs n, ‖weightedRightPair i j b f‖ ^ 2) =
      (1/2 : ℝ) * ∑ k, ∑ l, if k = l then 0 else ‖weightedProjection i j k l f‖ ^ 2 := by
  have h := UnorderedPairSums.sum_ordered_eq_two_mul
    (fun b => ‖weightedRightPair i j b f‖ ^ 2)
  have he (k l : Fin n) : (if k ≠ l then ‖weightedRightPair i j {k,l} f‖ ^ 2 else 0) =
      if k = l then 0 else ‖weightedProjection i j k l f‖ ^ 2 := by
    by_cases hkl : k = l
    · simp [hkl]
    · simp only [hkl, ne_eq, not_false_eq_true, ite_true, ite_false,
        weightedRightPair_pair i j k l hij hkl]
  simp_rw [he] at h
  change (∑ b ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
    ‖weightedRightPair i j b f‖ ^ 2) = _
  linarith

theorem pair_budget_named (i j : Fin n) (hij : i ≠ j) (f : StateSpace n d) :
    (∑ b ∈ pairs n, ‖weightedRightPair i j b f‖ ^ 2) + ‖fluctuation n d {i,j} f‖ ^ 2 ≤
      ∑ b ∈ pairs n, ‖CrossToggle.gain {i,j} b f‖ ^ 2 := by
  rw [rightPair_sum i j hij f, sum_gain_eq_half_ordered]
  exact ordered_budget i j hij f

end
end SharpSwitchGap.WeightedFiberBudget
