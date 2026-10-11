import SharpSwitchGap.GraphCellCompression
import SharpSwitchGap.CrossCellPlane

namespace SharpSwitchGap.GraphCellPlane

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 PairResampling DisjointEncoding DisjointMarginal
open GraphCellCompression
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem nondegenerate_cell_bound (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (hs : CrossBlock.total (crossCode e G.val) = 2)
    (hr : ∃ z : CrossCell e G, z.val.2.1.val.1 ≠ 1)
    (hc : ∃ z : CrossCell e G, z.val.2.2.val.1 ≠ 1)
    (p : SwitchProposal n) (hpa : SwitchPairFiber.Crosses p {e 0,e 1})
    (hpb : SwitchPairFiber.Crosses p {e 2,e 3}) (f : StateSpace n d) :
    2 * ‖crossCellRestriction e G (SwitchFlip.projection p f)‖ ^ 2 -
      CellWeights.weight (fun x : LeftData e G.val => x.val.1) *
        ‖crossCellRestriction e G (PairEquality.projection (e 0) (e 1) (e 2) (e 3) f)‖ ^ 2 -
      CellWeights.weight (fun x : RightData e G.val => x.val.1) *
        ‖crossCellRestriction e G (PairEquality.projection (e 2) (e 3) (e 0) (e 1) f)‖ ^ 2 ≤
      2 * ⟪crossCellRestriction e G (fluctuation n d {e 0,e 1} f),
        crossCellRestriction e G (fluctuation n d {e 2,e 3} f)⟫ := by
  let C := compression e G
  let P := (expectation n d {e 0,e 1}).toLinearMap
  let Q := (expectation n d {e 2,e 3}).toLinearMap
  let T := (SwitchFlip.projection (d := d) p).toLinearMap
  let R := (PairEquality.projection (d := d) (e 0) (e 1) (e 2) (e 3)).toLinearMap
  let S := (PairEquality.projection (d := d) (e 2) (e 3) (e 0) (e 1)).toLinearMap
  have hP : C.Commutes P := commutes_left e G
  have hQ : C.Commutes Q := commutes_right e G
  have hR : C.Commutes R := commutes_left_error e G
  have hS : C.Commutes S := commutes_right_error e G
  have hT : C.Commutes T := commutes_gain e G p hpa
  have heP := left_expectation e G
  have heQ := right_expectation e G
  have hGP z : C.compress T (PairFibers.expectation
      (Setoid.ker (fun z : CrossCell e G => z.val.2.2)) z) = 0 := by
    change C.compress T ((PairFibers.expectation _).toLinearMap z) = 0
    rw [← heP]
    exact C.kills T P hP (SwitchFlip.projection_expectation p _ hpa) z
  have hGQ z : C.compress T (PairFibers.expectation
      (Setoid.ker (fun z : CrossCell e G => z.val.2.1)) z) = 0 := by
    change C.compress T ((PairFibers.expectation _).toLinearMap z) = 0
    rw [← heQ]
    exact C.kills T Q hQ (SwitchFlip.projection_expectation p _ hpb) z
  have hRc : C.compress R FiniteEventVectors.constantVector = 0 := by
    rw [← IndependentCell.expectation_constantVector
      (Setoid.ker (fun z : CrossCell e G => z.val.2.2))]
    change C.compress R ((PairFibers.expectation _).toLinearMap _) = 0
    rw [← heP]
    exact C.kills R P hP (PairEquality.projection_expectation _ _ _ _) _
  have hSc : C.compress S FiniteEventVectors.constantVector = 0 := by
    rw [← IndependentCell.expectation_constantVector
      (Setoid.ker (fun z : CrossCell e G => z.val.2.1))]
    change C.compress S ((PairFibers.expectation _).toLinearMap _) = 0
    rw [← heQ]
    exact C.kills S Q hQ (PairEquality.projection_expectation _ _ _ _) _
  have hRrange z := C.error_range P Q R hP hQ hR (left_error_range e) z
  have hSrange z := C.error_range Q P S hQ hP hS (right_error_range e) z
  rw [show C.compress P = _ from heP, show C.compress Q = _ from heQ] at hRrange hSrange
  have h := CrossCellPlane.weighted_interaction_of_two _ hs
    (fun x : LeftData e G.val => x.val.1) (fun x : RightData e G.val => x.val.1) hr hc
    (C.compress T) (C.compress R) (C.compress S)
    (C.symmetric T (SwitchFlip.projection_symmetric p))
    (C.symmetric R (PairEquality.projection_isSymmetric _ _ _ _))
    (C.symmetric S (PairEquality.projection_isSymmetric _ _ _ _))
    (C.idempotent T hT (SwitchFlip.projection_idempotent p))
    (by simpa only [FiniteEventVectors.constantVector, FiniteEventVectors.eventVector,
      FiniteEventVectors.rawIndicator, Finset.mem_univ, ite_true] using hRc)
    (by simpa only [FiniteEventVectors.constantVector, FiniteEventVectors.eventVector,
      FiniteEventVectors.rawIndicator, Finset.mem_univ, ite_true] using hSc) hGQ hGP
    hRrange hSrange (C.restrict f)
  have hresP : PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
      (C.restrict f) = C.restrict (P f) := by
    change (PairFibers.expectation _).toLinearMap (C.restrict f) = _
    rw [← heP]
    exact C.intertwine P hP f
  have hresQ : PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
      (C.restrict f) = C.restrict (Q f) := by
    change (PairFibers.expectation _).toLinearMap (C.restrict f) = _
    rw [← heQ]
    exact C.intertwine Q hQ f
  simp only [CrossCellMoments.firstPartition, CrossCellMoments.secondPartition,
    C.intertwine T hT, C.intertwine R hR, C.intertwine S hS, hresP, hresQ,
    ← map_sub] at h
  simpa only [fluctuation_eq_sub, C, P, Q, T, R, S, ContinuousLinearMap.coe_coe,
    restrict_eq] using h

theorem independent_cell_bound (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (hcase : CrossBlock.total (crossCode e G.val) ≠ 2 ∨
      CrossCellMoments.average (CrossBlock.total (crossCode e G.val))
        (fun x : LeftData e G.val => x.val.1) (fun x : RightData e G.val => x.val.1)
        (fun x _ => CrossCellMoments.offCenter (fun x : LeftData e G.val => x.val.1) x) = 0 ∨
      CrossCellMoments.average (CrossBlock.total (crossCode e G.val))
        (fun x : LeftData e G.val => x.val.1) (fun x : RightData e G.val => x.val.1)
        (fun _ x => CrossCellMoments.offCenter (fun x : RightData e G.val => x.val.1) x) = 0)
    (p : SwitchProposal n) (hpa : SwitchPairFiber.Crosses p {e 0,e 1})
    (hpb : SwitchPairFiber.Crosses p {e 2,e 3}) (f : StateSpace n d) :
    ‖crossCellRestriction e G (SwitchFlip.projection p f)‖ ^ 2 ≤
      ⟪crossCellRestriction e G (fluctuation n d {e 0,e 1} f),
        crossCellRestriction e G (fluctuation n d {e 2,e 3} f)⟫ := by
  let C := compression e G
  let T := (SwitchFlip.projection (d := d) p).toLinearMap
  have hT : C.Commutes T := commutes_gain e G p hpa
  let : Nonempty (CrossCell e G) := ⟨stateCellCrossEquiv e G ⟨G,SameCell.refl e G.val⟩⟩
  have hGsecond z : C.compress T (PairFibers.expectation
      (Setoid.ker (fun z : CrossCell e G => z.val.2.2)) z) = 0 := by
    change C.compress T ((PairFibers.expectation _).toLinearMap z) = 0
    rw [← left_expectation]
    exact C.kills T _ (commutes_left e G) (SwitchFlip.projection_expectation p _ hpa) z
  have hGfirst z : C.compress T (PairFibers.expectation
      (Setoid.ker (fun z : CrossCell e G => z.val.2.1)) z) = 0 := by
    change C.compress T ((PairFibers.expectation _).toLinearMap z) = 0
    rw [← right_expectation]
    exact C.kills T _ (commutes_right e G) (SwitchFlip.projection_expectation p _ hpb) z
  have h := CrossCellMoments.independent_projection_interaction _
    (fun x : LeftData e G.val => x.val.1) (fun x : RightData e G.val => x.val.1)
    (hcase.imp_right (Or.imp_right Or.inl)) (C.compress T)
    (C.symmetric T (SwitchFlip.projection_symmetric p))
    (C.idempotent T hT (SwitchFlip.projection_idempotent p)) hGfirst hGsecond (C.restrict f)
  rw [C.intertwine T hT] at h
  change ‖crossCellRestriction e G (SwitchFlip.projection p f)‖ ^ 2 ≤
    ⟪crossCellRestriction e G f - _, crossCellRestriction e G f - _⟫ at h
  simp only [C, restrict_eq] at h
  rw [← crossCellRestriction_left_expectation, ← crossCellRestriction_right_expectation] at h
  have hsub (x y : StateSpace n d) : crossCellRestriction e G x - crossCellRestriction e G y =
      crossCellRestriction e G (x-y) := ((compression e G).restrict.map_sub x y).symm
  rw [hsub, hsub] at h
  rw [fluctuation_eq_sub, fluctuation_eq_sub]
  rw [real_inner_comm] at h
  exact h

end
end SharpSwitchGap.GraphCellPlane
