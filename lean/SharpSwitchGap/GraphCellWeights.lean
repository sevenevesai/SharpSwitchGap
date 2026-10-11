import SharpSwitchGap.CellWeights
import OAI.Probability.SwitchChain.DisjointGraphAffine
import OAI.Probability.SwitchChain.PairFiberEqualityTransport

namespace SharpSwitchGap.GraphCellWeights

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 PairResampling PairFiber DisjointEncoding DisjointMarginal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def fiberWeight (i j : Fin n) (G : GraphState n d) : ℝ :=
  SliceMoments.equalMean (Finset.univ : Finset (singletonSet G.val i j))
    (leftSet G.val i j).card

theorem fiberWeight_nonneg (i j : Fin n) (G : GraphState n d) : 0 ≤ fiberWeight i j G := by
  have hn (m : ℕ) : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) := by
    cases m with
    | zero => norm_num
    | succ m => push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hq : (leftSet G.val i j).card ≤ (singletonSet G.val i j).card :=
    Finset.card_le_card (leftSet_subset_singletonSet G.val i j)
  unfold fiberWeight SliceMoments.equalMean
  simp only [Finset.card_univ, Fintype.card_coe]
  rw [← Nat.cast_sub hq]
  exact div_nonneg (add_nonneg (hn _) (hn _)) (hn _)

theorem fiberWeight_constant (i j : Fin n) (hij : i ≠ j)
    {G H : GraphState n d} (h : SameFiber {i,j} G.val H.val) :
    fiberWeight i j G = fiberWeight i j H := by
  have hk := (sameFiber_iff_key_eq i j hij G.val H.val).mp h
  have hq := (leftSet_card_eq_iff_degree_eq hij hk).mpr ((G.property i).trans (H.property i).symm)
  unfold fiberWeight SliceMoments.equalMean
  simp only [Finset.card_univ, Fintype.card_coe]
  rw [singletonSet_eq_of_key_eq hk, hq]

theorem restriction_left_observable (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    crossCellRestriction e G (PairEquality.observable (e 0) (e 2) (e 3)) =
      WithLp.toLp 2 (fun z : CrossCell e G =>
        CrossCellMoments.offCenter (fun x : LeftData e G.val => x.val.1) z.val.2.1) := by
  ext z
  obtain ⟨H,rfl⟩ := (stateCellCrossEquiv e G).surjective z
  rw [crossCellRestriction_apply_equiv]
  exact (stateLeftFlag_eq_observable e G H).symm

theorem active_column_center (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) (ha : PairEquality.active (e 0) (e 1) (e 2) (e 3) H.val) :
    (stateRightData e G H).val.1 = 1 := by
  apply Fin.ext
  rw [stateRightData_margin]
  change CrossBlock.col (crossCode e H.val.val) 0 = 1
  simp only [CrossBlock.col, Fin.sum_univ_two, CrossBlock.entry, crossCode,
    decide_eq_true_eq]
  change (if H.val.val.Adj (e 0) (e 2) then 1 else 0) +
    (if H.val.val.Adj (e 1) (e 2) then 1 else 0) = 1
  rcases (mem_singletonSet H.val.val (e 0) (e 1) (e 2)).mp ha.1 with ⟨_, h⟩
  rcases h with ⟨h0,h1⟩ | ⟨h0,h1⟩ <;> simp [h0,h1]

theorem left_weight_on_active_cell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (hs : CrossBlock.total (crossCode e G.val) = 2) (H : StateCell e G)
    (ha : PairEquality.active (e 0) (e 1) (e 2) (e 3) H.val) :
    fiberWeight (e 0) (e 1) H.val =
      CellWeights.weight (fun x : LeftData e G.val => x.val.1) := by
  have he (a b : Fin 4) (hab : a ≠ b) : e a ≠ e b :=
    fun h => hab (e.injective h)
  have hm := expectation_eq_equalMean_of_fiber H.val (e 0) (e 1) (he 0 1 (by decide))
    ⟨e 2,ha.1⟩ ⟨e 3,ha.2⟩ (by intro h; exact he 2 3 (by decide) (congrArg Subtype.val h))
    (PairEquality.observable (e 0) (e 2) (e 3)) (fun _ => rfl)
  change expectation n d {e 0,e 1} (PairEquality.observable (e 0) (e 2) (e 3)) H.val =
    fiberWeight (e 0) (e 1) H.val at hm
  rw [← hm, left_expectation_eq_crossCell, restriction_left_observable]
  change PairFibers.expectation
    (CrossCellMoments.secondPartition (CrossBlock.total (crossCode e G.val))
      (fun x : LeftData e G.val => x.val.1) (fun y : RightData e G.val => y.val.1))
    _ (stateCellCrossEquiv e G H) = _
  rw [CrossCellMoments.expectation_second_left_apply]
  have hflag : CrossCellMoments.offCenter (fun y : RightData e G.val => y.val.1)
      (stateCellCrossEquiv e G H).val.2.2 = 0 := by
    simp [CrossCellMoments.offCenter, active_column_center e G H ha]
  rw [CellWeights.flag_conditionalLeft_of_two _ hs, hflag]
  ring

theorem left_weight_on_projection (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (hs : CrossBlock.total (crossCode e G.val) = 2) (H : StateCell e G)
    (f : StateSpace n d) :
    fiberWeight (e 0) (e 1) H.val * PairEquality.projection (e 0) (e 1) (e 2) (e 3) f H.val =
      CellWeights.weight (fun x : LeftData e G.val => x.val.1) *
        PairEquality.projection (e 0) (e 1) (e 2) (e 3) f H.val := by
  by_cases ha : PairEquality.active (e 0) (e 1) (e 2) (e 3) H.val
  · rw [left_weight_on_active_cell e G hs H ha]
  · have hp := (PairEquality.equalitySpace (d := d) (e 0) (e 1) (e 2) (e 3)).starProjection_apply_mem f
    obtain ⟨c,hc⟩ := hp H.val
    have hz := hc H.val (SameFiber.refl _ _)
    simp only [ha, ite_false, mul_zero] at hz
    change PairEquality.projection (e 0) (e 1) (e 2) (e 3) f H.val = 0 at hz
    rw [hz, mul_zero, mul_zero]

theorem left_weight_eq_ratio (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (hs : CrossBlock.total (crossCode e G.val) = 2) (H : StateCell e G)
    (ha : PairEquality.active (e 0) (e 1) (e 2) (e 3) H.val) :
    fiberWeight (e 0) (e 1) H.val =
      CellWeights.rowProbability (fun x : LeftData e G.val => x.val.1)
        (fun y : RightData e G.val => y.val.1) /
      (1 - CellWeights.colProbability (fun x : LeftData e G.val => x.val.1)
        (fun y : RightData e G.val => y.val.1)) := by
  rw [left_weight_on_active_cell e G hs H ha]
  let z : CrossCellMoments.Cell 2 (fun x : LeftData e G.val => x.val.1)
      (fun y : RightData e G.val => y.val.1) :=
    ⟨(stateCellCrossEquiv e G H).val, by
      have hp := (stateCellCrossEquiv e G H).property
      exact ⟨hp.1.trans hs, hp.2⟩⟩
  exact CellWeights.weight_eq_probability_ratio _ _ z (active_column_center e G H ha)

theorem restriction_right_observable (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    crossCellRestriction e G (PairEquality.observable (e 2) (e 0) (e 1)) =
      WithLp.toLp 2 (fun z : CrossCell e G =>
        CrossCellMoments.offCenter (fun y : RightData e G.val => y.val.1) z.val.2.2) := by
  ext z
  obtain ⟨H,rfl⟩ := (stateCellCrossEquiv e G).surjective z
  rw [crossCellRestriction_apply_equiv]
  exact (stateRightFlag_eq_observable e G H).symm

theorem active_row_center (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) (ha : PairEquality.active (e 2) (e 3) (e 0) (e 1) H.val) :
    (stateLeftData e G H).val.1 = 1 := by
  apply Fin.ext
  rw [stateLeftData_margin]
  change CrossBlock.row (crossCode e H.val.val) 0 = 1
  simp only [CrossBlock.row, Fin.sum_univ_two, CrossBlock.entry, crossCode,
    decide_eq_true_eq]
  change (if H.val.val.Adj (e 0) (e 2) then 1 else 0) +
    (if H.val.val.Adj (e 0) (e 3) then 1 else 0) = 1
  rw [H.val.val.adj_comm (e 0) (e 2), H.val.val.adj_comm (e 0) (e 3)]
  rcases (mem_singletonSet H.val.val (e 2) (e 3) (e 0)).mp ha.1 with ⟨_, h⟩
  rcases h with ⟨h0,h1⟩ | ⟨h0,h1⟩ <;> simp [h0,h1]

theorem right_weight_on_active_cell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (hs : CrossBlock.total (crossCode e G.val) = 2) (H : StateCell e G)
    (ha : PairEquality.active (e 2) (e 3) (e 0) (e 1) H.val) :
    fiberWeight (e 2) (e 3) H.val =
      CellWeights.weight (fun y : RightData e G.val => y.val.1) := by
  have he (a b : Fin 4) (hab : a ≠ b) : e a ≠ e b :=
    fun h => hab (e.injective h)
  have hm := expectation_eq_equalMean_of_fiber H.val (e 2) (e 3) (he 2 3 (by decide))
    ⟨e 0,ha.1⟩ ⟨e 1,ha.2⟩ (by intro h; exact he 0 1 (by decide) (congrArg Subtype.val h))
    (PairEquality.observable (e 2) (e 0) (e 1)) (fun _ => rfl)
  change expectation n d {e 2,e 3} (PairEquality.observable (e 2) (e 0) (e 1)) H.val =
    fiberWeight (e 2) (e 3) H.val at hm
  rw [← hm, right_expectation_eq_crossCell, restriction_right_observable]
  change PairFibers.expectation
    (CrossCellMoments.firstPartition (CrossBlock.total (crossCode e G.val))
      (fun x : LeftData e G.val => x.val.1) (fun y : RightData e G.val => y.val.1))
    _ (stateCellCrossEquiv e G H) = _
  rw [CrossCellMoments.expectation_first_right_apply]
  have hflag : CrossCellMoments.offCenter (fun x : LeftData e G.val => x.val.1)
      (stateCellCrossEquiv e G H).val.2.1 = 0 := by
    simp [CrossCellMoments.offCenter, active_row_center e G H ha]
  rw [CellWeights.flag_conditionalRight_of_two _ hs, hflag]
  ring

theorem right_weight_on_projection (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (hs : CrossBlock.total (crossCode e G.val) = 2) (H : StateCell e G)
    (f : StateSpace n d) :
    fiberWeight (e 2) (e 3) H.val * PairEquality.projection (e 2) (e 3) (e 0) (e 1) f H.val =
      CellWeights.weight (fun y : RightData e G.val => y.val.1) *
        PairEquality.projection (e 2) (e 3) (e 0) (e 1) f H.val := by
  by_cases ha : PairEquality.active (e 2) (e 3) (e 0) (e 1) H.val
  · rw [right_weight_on_active_cell e G hs H ha]
  · have hp := (PairEquality.equalitySpace (d := d) (e 2) (e 3) (e 0) (e 1)).starProjection_apply_mem f
    obtain ⟨c,hc⟩ := hp H.val
    have hz := hc H.val (SameFiber.refl _ _)
    simp only [ha, ite_false, mul_zero] at hz
    change PairEquality.projection (e 2) (e 3) (e 0) (e 1) f H.val = 0 at hz
    rw [hz, mul_zero, mul_zero]

theorem right_weight_eq_ratio (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (hs : CrossBlock.total (crossCode e G.val) = 2) (H : StateCell e G)
    (ha : PairEquality.active (e 2) (e 3) (e 0) (e 1) H.val) :
    fiberWeight (e 2) (e 3) H.val =
      CellWeights.colProbability (fun x : LeftData e G.val => x.val.1)
        (fun y : RightData e G.val => y.val.1) /
      (1 - CellWeights.rowProbability (fun x : LeftData e G.val => x.val.1)
        (fun y : RightData e G.val => y.val.1)) := by
  rw [right_weight_on_active_cell e G hs H ha]
  let z : CrossCellMoments.Cell 2 (fun x : LeftData e G.val => x.val.1)
      (fun y : RightData e G.val => y.val.1) :=
    ⟨(stateCellCrossEquiv e G H).val, by
      have hp := (stateCellCrossEquiv e G H).property
      exact ⟨hp.1.trans hs, hp.2⟩⟩
  exact CellWeights.right_weight_eq_probability_ratio _ _ z (active_row_center e G H ha)

end
end SharpSwitchGap.GraphCellWeights
