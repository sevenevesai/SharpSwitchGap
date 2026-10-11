import SharpSwitchGap.GraphCellPlane
import SharpSwitchGap.WeightedError

namespace SharpSwitchGap.WeightedCell

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 PairResampling DisjointEncoding DisjointMarginal
open GraphCellCompression GraphCellPlane GraphCellWeights WeightedError
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem cell_bound (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (p : SwitchProposal n) (hpa : SwitchPairFiber.Crosses p {e 0,e 1})
    (hpb : SwitchPairFiber.Crosses p {e 2,e 3}) (f : StateSpace n d) :
    2 * ‖crossCellRestriction e G (SwitchFlip.projection p f)‖ ^ 2 -
      ‖crossCellRestriction e G (weightedProjection (e 0) (e 1) (e 2) (e 3) f)‖ ^ 2 -
      ‖crossCellRestriction e G (weightedProjection (e 2) (e 3) (e 0) (e 1) f)‖ ^ 2 ≤
      2 * ⟪crossCellRestriction e G (fluctuation n d {e 0,e 1} f),
        crossCellRestriction e G (fluctuation n d {e 2,e 3} f)⟫ := by
  let s := CrossBlock.total (crossCode e G.val)
  let r := fun x : LeftData e G.val => x.val.1
  let c := fun x : RightData e G.val => x.val.1
  have hindep (hcase : s ≠ 2 ∨
      CrossCellMoments.average s r c (fun x _ => CrossCellMoments.offCenter r x) = 0 ∨
      CrossCellMoments.average s r c (fun _ x => CrossCellMoments.offCenter c x) = 0) :
      2 * ‖crossCellRestriction e G (SwitchFlip.projection p f)‖ ^ 2 -
        ‖crossCellRestriction e G (weightedProjection (e 0) (e 1) (e 2) (e 3) f)‖ ^ 2 -
        ‖crossCellRestriction e G (weightedProjection (e 2) (e 3) (e 0) (e 1) f)‖ ^ 2 ≤
        2 * ⟪crossCellRestriction e G (fluctuation n d {e 0,e 1} f),
          crossCellRestriction e G (fluctuation n d {e 2,e 3} f)⟫ := by
    have h := independent_cell_bound e G hcase p hpa hpb f
    nlinarith [sq_nonneg ‖crossCellRestriction e G (weightedProjection (e 0) (e 1) (e 2) (e 3) f)‖,
      sq_nonneg ‖crossCellRestriction e G (weightedProjection (e 2) (e 3) (e 0) (e 1) f)‖]
  by_cases hs : s = 2
  · by_cases hr : ∃ z : CrossCell e G, r z.val.2.1 ≠ 1
    · by_cases hc : ∃ z : CrossCell e G, c z.val.2.2 ≠ 1
      · rw [cell_norm_sq e G _ _ _ _ f (CellWeights.weight r)
          (fun H => left_weight_on_projection e G hs H f),
          cell_norm_sq e G _ _ _ _ f (CellWeights.weight c)
          (fun H => right_weight_on_projection e G hs H f)]
        exact nondegenerate_cell_bound e G hs hr hc p hpa hpb f
      · apply hindep (Or.inr (Or.inr ?_))
        unfold CrossCellMoments.average
        apply (div_eq_zero_iff).mpr
        left
        apply Finset.sum_eq_zero
        intro z _
        have hz : c z.val.2.2 = 1 := by by_contra h; exact hc ⟨z,h⟩
        simp [CrossCellMoments.offCenter,hz]
    · apply hindep (Or.inr (Or.inl ?_))
      unfold CrossCellMoments.average
      apply (div_eq_zero_iff).mpr
      left
      apply Finset.sum_eq_zero
      intro z _
      have hz : r z.val.2.1 = 1 := by by_contra h; exact hr ⟨z,h⟩
      simp [CrossCellMoments.offCenter,hz]
  · exact hindep (Or.inl hs)

theorem actual_switch_interaction (e : Fin 4 ↪ Fin n)
    (p : SwitchProposal n) (hpa : SwitchPairFiber.Crosses p {e 0,e 1})
    (hpb : SwitchPairFiber.Crosses p {e 2,e 3}) (f : StateSpace n d) :
    2 * ‖SwitchFlip.projection p f‖ ^ 2 -
      ‖weightedProjection (e 0) (e 1) (e 2) (e 3) f‖ ^ 2 -
      ‖weightedProjection (e 2) (e 3) (e 0) (e 1) f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {e 0,e 1} f, fluctuation n d {e 2,e 3} f⟫ := by
  apply interaction_bound_of_cell_bounds e (SwitchFlip.projection p)
    (weightedProjection (e 0) (e 1) (e 2) (e 3))
    (weightedProjection (e 2) (e 3) (e 0) (e 1)) f
    (fun c => SwitchFlip.projection_restrictCell_of_crosses p _ hpa _ (cellInvariant_left e c) f)
    (fun c => restrictCell_commute _ _ _ _ _ (cellInvariant_left e c) f)
    (fun c => restrictCell_commute _ _ _ _ _ (cellInvariant_right e c) f)
  intro c
  induction c using Quotient.inductionOn with
  | h G =>
    have h := cell_bound e G p hpa hpb f
    rw [norm_restrict_mask, norm_restrict_mask, norm_restrict_mask, inner_restrict_mask] at h
    rw [← SwitchFlip.projection_restrictCell_of_crosses p _ hpa _ (invariant_left e G),
      ← restrictCell_commute _ _ _ _ _ (invariant_left e G),
      ← restrictCell_commute _ _ _ _ _ (invariant_right e G),
      ← fluctuation_restrictCell _ _ (invariant_left e G),
      ← fluctuation_restrictCell _ _ (invariant_right e G)] at h
    have hC : cell e G = (fun H => cellIndex e H = cellIndex e G) := by
      funext H
      apply propext
      rw [cellIndex_eq_iff]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    simpa only [hC, cellIndex] using h

theorem actual_named_interaction (i j k l : Fin n) (h : FourDistinct i j k l)
    (f : StateSpace n d) :
    2 * ‖SwitchFlip.projection (CrossToggle.crossProposal i j k l h) f‖ ^ 2 -
      (∑ G, fiberWeight i j G * (PairEquality.projection i j k l f G) ^ 2) -
      (∑ G, fiberWeight k l G * (PairEquality.projection k l i j f G) ^ 2) ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫ := by
  let e : Fin 4 ↪ Fin n :=
    ⟨![i,j,k,l], by
      rcases h with ⟨hij,hik,hil,hjk,hjl,hkl⟩
      intro x y hxy
      fin_cases x <;> fin_cases y <;>
        simp_all [Ne.symm hij, Ne.symm hik, Ne.symm hil,
          Ne.symm hjk, Ne.symm hjl, Ne.symm hkl]⟩
  have hh := actual_switch_interaction e (CrossToggle.crossProposal i j k l h)
    (CrossToggle.crossProposal_left i j k l h) (CrossToggle.crossProposal_right i j k l h) f
  change 2 * ‖SwitchFlip.projection (CrossToggle.crossProposal i j k l h) f‖ ^ 2 -
    ‖weightedProjection i j k l f‖ ^ 2 - ‖weightedProjection k l i j f‖ ^ 2 ≤
    2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫ at hh
  simpa only [norm_sq] using hh

end
end SharpSwitchGap.WeightedCell
