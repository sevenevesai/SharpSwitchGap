import SharpSwitchGap.Compression
import SharpSwitchGap.GraphCellWeights
import OAI.Probability.SwitchChain.PairActualAffine
import OAI.Probability.SwitchChain.PairEqualityCell
import OAI.Probability.SwitchChain.PairEqualityProjectionFacts
import OAI.Probability.SwitchChain.CrossToggleCells

namespace SharpSwitchGap.GraphCellCompression

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 PairResampling DisjointEncoding DisjointMarginal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def cell (e : Fin 4 ↪ Fin n) (G : GraphState n d) : GraphState n d → Prop :=
  fun H => SameCell e G.val H.val

def compression (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    Compression (StateSpace n d) (EuclideanSpace ℝ (CrossCell e G)) :=
  Compression.ofEquiv (cell e G) (stateCellCrossEquiv e G)

@[simp] theorem restrict_eq (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : StateSpace n d) :
    (compression e G).restrict f = crossCellRestriction e G f := rfl

@[simp] theorem mask_eq (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : StateSpace n d) :
    (compression e G).extend ((compression e G).restrict f) = restrictCell (cell e G) f := by
  ext H
  by_cases h : cell e G H
  · change (if hh : cell e G H then
        CellProjectionTransport.pull (stateCellCrossEquiv e G)
          (crossCellRestriction e G f) ⟨H,hh⟩ else 0) = if cell e G H then f H else 0
    simp only [h, dite_true, ite_true, CellProjectionTransport.pull_apply,
      crossCellRestriction_apply_equiv]
  · change (if hh : cell e G H then _ else 0) = if cell e G H then f H else 0
    simp [h]

theorem invariant_left (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    CellInvariant {e 0,e 1} (cell e G) := by
  intro H K h
  have hc := sameCell_of_sameFiber_left e H.val K.val h
  exact ⟨fun hH => hH.trans hc, fun hK => hK.trans hc.symm⟩

theorem inner_restrict_mask (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f g : StateSpace n d) :
    ⟪crossCellRestriction e G f,crossCellRestriction e G g⟫ =
      ⟪restrictCell (cell e G) f,restrictCell (cell e G) g⟫ := by
  have h := (compression e G).extend_inner ((compression e G).restrict f)
    ((compression e G).restrict g)
  rw [mask_eq, mask_eq] at h
  exact h.symm

theorem norm_restrict_mask (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : StateSpace n d) :
    ‖crossCellRestriction e G f‖ ^ 2 = ‖restrictCell (cell e G) f‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using inner_restrict_mask e G f f

theorem invariant_right (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    CellInvariant {e 2,e 3} (cell e G) := by
  intro H K h
  have hc := sameCell_of_sameFiber_right e H.val K.val h
  exact ⟨fun hH => hH.trans hc, fun hK => hK.trans hc.symm⟩

theorem commutes_left (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    (compression e G).Commutes (expectation n d {e 0,e 1}).toLinearMap := by
  intro f
  simp only [mask_eq, ContinuousLinearMap.coe_coe]
  exact expectation_restrictCell _ _ (invariant_left e G) f

theorem commutes_right (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    (compression e G).Commutes (expectation n d {e 2,e 3}).toLinearMap := by
  intro f
  simp only [mask_eq, ContinuousLinearMap.coe_coe]
  exact expectation_restrictCell _ _ (invariant_right e G) f

theorem left_expectation (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    (compression e G).compress (expectation n d {e 0,e 1}).toLinearMap =
      (PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.2))).toLinearMap := by
  ext f z
  have h := crossCellRestriction_left_expectation e G ((compression e G).extend f)
  change (compression e G).restrict (expectation n d {e 0,e 1} ((compression e G).extend f)) =
    PairFibers.expectation _ ((compression e G).restrict ((compression e G).extend f)) at h
  rw [(compression e G).restrict_extend] at h
  exact congrArg (fun w => w z) h

theorem right_expectation (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    (compression e G).compress (expectation n d {e 2,e 3}).toLinearMap =
      (PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.1))).toLinearMap := by
  ext f z
  have h := crossCellRestriction_right_expectation e G ((compression e G).extend f)
  change (compression e G).restrict (expectation n d {e 2,e 3} ((compression e G).extend f)) =
    PairFibers.expectation _ ((compression e G).restrict ((compression e G).extend f)) at h
  rw [(compression e G).restrict_extend] at h
  exact congrArg (fun w => w z) h

theorem commutes_left_error (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    (compression e G).Commutes
      (PairEquality.projection (e 0) (e 1) (e 2) (e 3)).toLinearMap := by
  intro f
  simp only [mask_eq, ContinuousLinearMap.coe_coe]
  exact PairEquality.projection_restrictCell _ _ _ _ _ (invariant_left e G) f

theorem commutes_right_error (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    (compression e G).Commutes
      (PairEquality.projection (e 2) (e 3) (e 0) (e 1)).toLinearMap := by
  intro f
  simp only [mask_eq, ContinuousLinearMap.coe_coe]
  exact PairEquality.projection_restrictCell _ _ _ _ _ (invariant_right e G) f

theorem commutes_gain (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (p : SwitchProposal n) (hp : SwitchPairFiber.Crosses p {e 0,e 1}) :
    (compression e G).Commutes (SwitchFlip.projection p).toLinearMap := by
  intro f
  simp only [mask_eq, ContinuousLinearMap.coe_coe]
  exact SwitchFlip.projection_restrictCell_of_crosses p _ hp _ (invariant_left e G) f

theorem left_error_range (e : Fin 4 ↪ Fin n) (z : StateSpace n d) :
    let P := expectation n d {e 0,e 1}
    let Q := expectation n d {e 2,e 3}
    PairEquality.projection (e 0) (e 1) (e 2) (e 3) (Q (P z) - P (Q (P z))) =
      Q (P z) - P (Q (P z)) := by
  have he (a b : Fin 4) (hab : a ≠ b) : e a ≠ e b := fun h => hab (e.injective h)
  have h := PairEquality.projection_fixes_fluctuation_of_affineFlagImage
    (e 0) (e 1) (e 2) (e 3) (he 0 1 (by decide))
    ⟨he 2 0 (by decide), he 2 1 (by decide)⟩
    ⟨he 3 0 (by decide), he 3 1 (by decide)⟩
    (expectation n d {e 2,e 3} (expectation n d {e 0,e 1} z))
    (PairEquality.right_left_expectation_affine e z)
  simpa only [fluctuation_eq_sub] using h

theorem right_error_range (e : Fin 4 ↪ Fin n) (z : StateSpace n d) :
    let P := expectation n d {e 0,e 1}
    let Q := expectation n d {e 2,e 3}
    PairEquality.projection (e 2) (e 3) (e 0) (e 1) (P (Q z) - Q (P (Q z))) =
      P (Q z) - Q (P (Q z)) := by
  have he (a b : Fin 4) (hab : a ≠ b) : e a ≠ e b := fun h => hab (e.injective h)
  have h := PairEquality.projection_fixes_fluctuation_of_affineFlagImage
    (e 2) (e 3) (e 0) (e 1) (he 2 3 (by decide))
    ⟨he 0 2 (by decide), he 0 3 (by decide)⟩
    ⟨he 1 2 (by decide), he 1 3 (by decide)⟩
    (expectation n d {e 0,e 1} (expectation n d {e 2,e 3} z))
    (PairEquality.left_right_expectation_affine e z)
  simpa only [fluctuation_eq_sub] using h

end
end SharpSwitchGap.GraphCellCompression
