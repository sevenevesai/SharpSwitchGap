import SharpSwitchGap.EventPlane
import SharpSwitchGap.CellWeights
import OAI.Probability.SwitchChain.CrossCellAffineComposition
import OAI.Probability.SwitchChain.CrossCellProjectionIndependence

namespace SharpSwitchGap.CrossCellPlane

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 CrossCellMoments FiniteEventVectors
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [Fintype β]

def rowEvent (r : α → Fin 3) (c : β → Fin 3) : Finset (Cell 2 r c) :=
  Finset.univ.filter (fun z => r z.val.2.1 ≠ 1)

def colEvent (r : α → Fin 3) (c : β → Fin 3) : Finset (Cell 2 r c) :=
  Finset.univ.filter (fun z => c z.val.2.2 ≠ 1)

@[simp] theorem raw_row (r : α → Fin 3) (c : β → Fin 3) (z : Cell 2 r c) :
    rawIndicator (rowEvent r c) z = offCenter r z.val.2.1 := by
  by_cases h : r z.val.2.1 = 1 <;> simp [rawIndicator, rowEvent, offCenter, h]

@[simp] theorem raw_col (r : α → Fin 3) (c : β → Fin 3) (z : Cell 2 r c) :
    rawIndicator (colEvent r c) z = offCenter c z.val.2.2 := by
  by_cases h : c z.val.2.2 = 1 <;> simp [rawIndicator, colEvent, offCenter, h]

theorem row_probability (r : α → Fin 3) (c : β → Fin 3) :
    probability (rowEvent r c) = CellWeights.rowProbability r c := by
  unfold probability CellWeights.rowProbability average rowEvent
  congr 1
  have he : (∑ z : Cell 2 r c, offCenter r z.val.2.1) =
      ∑ z ∈ Finset.univ.filter (fun z : Cell 2 r c => r z.val.2.1 ≠ 1), (1 : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : r z.val.2.1 = 1 <;> simp [offCenter,hz]
  rw [he]
  simp

theorem col_probability (r : α → Fin 3) (c : β → Fin 3) :
    probability (colEvent r c) = CellWeights.colProbability r c := by
  unfold probability CellWeights.colProbability average colEvent
  congr 1
  have he : (∑ z : Cell 2 r c, offCenter c z.val.2.2) =
      ∑ z ∈ Finset.univ.filter (fun z : Cell 2 r c => c z.val.2.2 ≠ 1), (1 : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : c z.val.2.2 = 1 <;> simp [offCenter,hz]
  rw [he]
  simp

theorem weighted_interaction_two (r : α → Fin 3) (c : β → Fin 3)
    (hr : ∃ z : Cell 2 r c, r z.val.2.1 ≠ 1)
    (hc : ∃ z : Cell 2 r c, c z.val.2.2 ≠ 1)
    (G R S : EuclideanSpace ℝ (Cell 2 r c) →ₗ[ℝ] EuclideanSpace ℝ (Cell 2 r c))
    (hGs : G.IsSymmetric) (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hGi : ∀ f, G (G f) = G f)
    (hRconst : R constantVector = 0) (hSconst : S constantVector = 0)
    (hGfirst : ∀ f, G (PairFibers.expectation (firstPartition 2 r c) f) = 0)
    (hGsecond : ∀ f, G (PairFibers.expectation (secondPartition 2 r c) f) = 0)
    (hRrange : ∀ z,
      let P := PairFibers.expectation (secondPartition 2 r c)
      let Q := PairFibers.expectation (firstPartition 2 r c)
      R (Q (P z) - P (Q (P z))) = Q (P z) - P (Q (P z)))
    (hSrange : ∀ z,
      let P := PairFibers.expectation (secondPartition 2 r c)
      let Q := PairFibers.expectation (firstPartition 2 r c)
      S (P (Q z) - Q (P (Q z))) = P (Q z) - Q (P (Q z)))
    (f : EuclideanSpace ℝ (Cell 2 r c)) :
    2 * ‖G f‖ ^ 2 - CellWeights.weight r * ‖R f‖ ^ 2 -
      CellWeights.weight c * ‖S f‖ ^ 2 ≤
      2 * ⟪f - PairFibers.expectation (secondPartition 2 r c) f,
        f - PairFibers.expectation (firstPartition 2 r c) f⟫ := by
  obtain ⟨w,hw⟩ := exists_center_of_both_offCenter r c hr hc
  let : Nonempty (Cell 2 r c) := ⟨w⟩
  have hcenter : ∃ z : Cell 2 r c, z ∉ colEvent r c ∧ z ∉ rowEvent r c :=
    ⟨w, by simp [colEvent, rowEvent, hw.1, hw.2]⟩
  have hs : (colEvent r c).Nonempty := by
    obtain ⟨z,hz⟩ := hc
    exact ⟨z, by simp [colEvent,hz]⟩
  have ht : (rowEvent r c).Nonempty := by
    obtain ⟨z,hz⟩ := hr
    exact ⟨z, by simp [rowEvent,hz]⟩
  have hd : Disjoint (colEvent r c) (rowEvent r c) := by
    apply Finset.disjoint_left.mpr
    intro z hz hzr
    have hrz : r z.val.2.1 ≠ 1 := (Finset.mem_filter.mp hzr).2
    exact (Finset.mem_filter.mp hz).2 (offCenter_disjoint r c z hrz)
  rw [CellWeights.weight_eq_probability_ratio r c w hw.2,
    CellWeights.right_weight_eq_probability_ratio r c w hw.1,
    ← row_probability, ← col_probability]
  apply EventPlane.weighted_interaction
    (PairFibers.expectation (secondPartition 2 r c)).toLinearMap
    (PairFibers.expectation (firstPartition 2 r c)).toLinearMap G R S
    (PairFibers.expectation_symmetric _) (PairFibers.expectation_symmetric _)
    hGs hRs hSs (PairFibers.expectation_idempotent _) (PairFibers.expectation_idempotent _)
    hGi (colEvent r c) (rowEvent r c) hs ht hd hcenter
    (IndependentCell.expectation_constantVector _) (IndependentCell.expectation_constantVector _)
    ?_ ?_ ?_ ?_ hRconst hSconst hGsecond hGfirst hRrange hSrange f
  · rw [eventVector, map_smul]
    congr 1
    apply (PairFibers.expectation_eq_self_iff _ _).mpr
    intro x y hxy
    simpa only [raw_col] using congrArg (offCenter c) hxy
  · rw [eventVector, map_smul]
    congr 1
    apply (PairFibers.expectation_eq_self_iff _ _).mpr
    intro x y hxy
    simpa only [raw_row] using congrArg (offCenter r) hxy
  · intro z
    obtain ⟨a,b,_,hab⟩ := expectation_second_first_affine 2 r c z
    refine ⟨a,b,?_⟩
    intro x
    change PairFibers.expectation _ (PairFibers.expectation _ z) x = _
    rw [raw_col]
    exact hab x
  · intro z
    obtain ⟨a,b,_,hab⟩ := expectation_first_second_affine 2 r c z
    refine ⟨a,b,?_⟩
    intro x
    change PairFibers.expectation _ (PairFibers.expectation _ z) x = _
    rw [raw_row]
    exact hab x

theorem weighted_interaction_of_two (s : ℕ) (hs : s = 2) (r : α → Fin 3) (c : β → Fin 3)
    (hr : ∃ z : Cell s r c, r z.val.2.1 ≠ 1) (hc : ∃ z : Cell s r c, c z.val.2.2 ≠ 1)
    (G R S : EuclideanSpace ℝ (Cell s r c) →ₗ[ℝ] EuclideanSpace ℝ (Cell s r c))
    (hGs : G.IsSymmetric) (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hGi : ∀ f, G (G f) = G f)
    (hRconst : R constantVector = 0) (hSconst : S constantVector = 0)
    (hGfirst : ∀ f, G (PairFibers.expectation (firstPartition s r c) f) = 0)
    (hGsecond : ∀ f, G (PairFibers.expectation (secondPartition s r c) f) = 0)
    (hRrange : ∀ z,
      let P := PairFibers.expectation (secondPartition s r c)
      let Q := PairFibers.expectation (firstPartition s r c)
      R (Q (P z) - P (Q (P z))) = Q (P z) - P (Q (P z)))
    (hSrange : ∀ z,
      let P := PairFibers.expectation (secondPartition s r c)
      let Q := PairFibers.expectation (firstPartition s r c)
      S (P (Q z) - Q (P (Q z))) = P (Q z) - Q (P (Q z)))
    (f : EuclideanSpace ℝ (Cell s r c)) :
    2 * ‖G f‖ ^ 2 - CellWeights.weight r * ‖R f‖ ^ 2 - CellWeights.weight c * ‖S f‖ ^ 2 ≤
      2 * ⟪f - PairFibers.expectation (secondPartition s r c) f,
        f - PairFibers.expectation (firstPartition s r c) f⟫ := by
  subst s
  exact weighted_interaction_two r c hr hc G R S hGs hRs hSs hGi hRconst hSconst
    hGfirst hGsecond hRrange hSrange f

end
end SharpSwitchGap.CrossCellPlane
