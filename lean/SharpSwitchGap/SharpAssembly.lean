import SharpSwitchGap.WeightedPairs
import SharpSwitchGap.LocalToGlobal
import OAI.Probability.SwitchChain.ActualTripleSquare

namespace SharpSwitchGap.SharpAssembly

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 PairResampling
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem disjoint_ge_generator (f : StateSpace n d) :
    ⟪f, generator n d f⟫ ≤
      ∑ a ∈ pairs n, ∑ b ∈ pairs n,
        if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0 := by
  let A := fun a b => if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0
  let g := fun a b => if Disjoint a b then ‖CrossToggle.gain a b f‖ ^ 2 else 0
  let R := fun a b => if Disjoint a b then ‖WeightedPairs.pairError a b f‖ ^ 2 else 0
  have hl a (ha : a ∈ pairs n) b (hb : b ∈ pairs n) :
      2 * g a b - R a b - R b a ≤ 2 * A a b := by
    by_cases hab : Disjoint a b
    · simp only [A,g,R,ite_eq_left hab,ite_eq_left hab.symm]
      exact WeightedPairs.interaction f a ha b hb hab
    · have hba : ¬ Disjoint b a := fun h => hab h.symm
      simp only [A,g,R,ite_eq_right hab,ite_eq_right hba]
      norm_num
  have hlocal := Finset.sum_le_sum (s := pairs n) (fun a ha =>
    Finset.sum_le_sum (s := pairs n) (fun b hb => hl a ha b hb))
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hlocal
  have hrev : (∑ a ∈ pairs n, ∑ b ∈ pairs n, R b a) =
      ∑ a ∈ pairs n, ∑ b ∈ pairs n, R a b := Finset.sum_comm
  rw [hrev] at hlocal
  have hb a (ha : a ∈ pairs n) :
      (∑ b ∈ pairs n, R a b) + ‖fluctuation n d a f‖ ^ 2 ≤ ∑ b ∈ pairs n, g a b := by
    dsimp only [R,g]
    rw [WeightedPairs.sum_disjoint_error, PairEquality.sum_gain_norm_sq]
    exact WeightedPairs.pair_budget a ha f
  have hbudget := Finset.sum_le_sum hb
  rw [Finset.sum_add_distrib, ← inner_generator] at hbudget
  change ⟪f,generator n d f⟫ ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n, A a b
  linarith

theorem generator_square (hn : 3 ≤ n) (f : StateSpace n d) :
    2 * ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫ := by
  let s := (Finset.univ : Finset (Fin n))
  let h := fun a => ‖fluctuation n d a f‖ ^ 2
  let B := fun a b => ⟪fluctuation n d a f, fluctuation n d b f⟫
  have ht : ∀ T ∈ s.powersetCard 3,
      (1 : ℝ) * (∑ a ∈ T.powersetCard 2, h a) ≤
        ∑ a ∈ T.powersetCard 2, ∑ b ∈ T.powersetCard 2, B a b := by
    intro T hT
    have hh := tripleGenerator_square f T (Finset.mem_powersetCard.mp hT).2
    dsimp only [h,B]
    rw [one_mul]
    rw [inner_tripleGenerator] at hh
    simp only [tripleGenerator_apply] at hh
    simp only [sum_inner] at hh
    simp only [inner_sum] at hh
    exact hh
  have hl := LocalToGlobal.square_lower_bound s (by simpa [s] using hn) h B 1
    (fun _ _ => real_inner_self_eq_norm_sq _) ht
  have hc : (1 : ℝ) * (s.card - 2 : ℕ) - (s.card - 3 : ℕ) = 1 := by
    simp only [s,Finset.card_univ,Fintype.card_fin]
    rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub hn]
    ring
  rw [hc,one_mul] at hl
  dsimp only [s,h,B] at hl
  have hl' : ⟪f,generator n d f⟫ +
      (∑ a ∈ pairs n, ∑ b ∈ pairs n,
        if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0) ≤
      ⟪generator n d f,generator n d f⟫ := by
    rw [inner_generator]
    simp only [generator_apply]
    simp only [sum_inner]
    simp only [inner_sum]
    exact hl
  linarith [disjoint_ge_generator f]

theorem centered_poincare (hn : 3 ≤ n) (f : StateSpace n d) (hf : ∑ G, f G = 0) :
    2 * ‖f‖ ^ 2 ≤ ⟪f,generator n d f⟫ := by
  let T := (1/2 : ℝ) • (generator n d).toLinearMap
  have hT : T.IsSymmetric := generator_isSymmetric.smul (by simp)
  have hpos (x : StateSpace n d) : 0 ≤ ⟪x,T x⟫ := by
    change 0 ≤ ⟪x,(1/2 : ℝ) • generator n d x⟫
    rw [real_inner_smul_right]
    exact mul_nonneg (by norm_num) (generator_nonneg x)
  have hsquare (x : StateSpace n d) : ⟪x,T x⟫ ≤ ⟪T x,T x⟫ := by
    change ⟪x,(1/2 : ℝ) • generator n d x⟫ ≤
      ⟪(1/2 : ℝ) • generator n d x,(1/2 : ℝ) • generator n d x⟫
    simp only [real_inner_smul_left,real_inner_smul_right]
    linarith [generator_square hn x]
  have hp := Analytic.norm_sq_le_inner_of_square_ge T hT hpos hsquare f (by
    intro y hy
    have hy' : generator n d y = 0 := by
      change (1/2 : ℝ) • generator n d y = 0 at hy
      exact (smul_eq_zero.mp hy).resolve_left (by norm_num)
    have hconst := (generator_eq_zero_iff_constant y).mp hy'
    by_cases hne : Nonempty (GraphState n d)
    · let G := Classical.choice hne
      rw [state_inner]
      simp_rw [hconst _ G]
      rw [← Finset.mul_sum,hf,mul_zero]
    · have : IsEmpty (GraphState n d) := not_nonempty_iff.mp hne
      simp [state_inner])
  change ‖f‖ ^ 2 ≤ ⟪f,(1/2 : ℝ) • generator n d f⟫ at hp
  rw [real_inner_smul_right] at hp
  linarith

end
end SharpSwitchGap.SharpAssembly
