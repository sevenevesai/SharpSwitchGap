import SharpSwitchGap.Main

namespace SharpSwitchGap.Curveball

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 PairResampling
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

/-- Uniform unordered pair, then uniform assignment in its entire fiber, including a hold. -/
def kernel (n : ℕ) (d : Fin n → ℕ) (G H : GraphState n d) : ℝ :=
  (∑ a ∈ pairs n, (if H ∈ fiberStates a G then (1 : ℝ) else 0) /
    ((fiberStates a G).card : ℝ)) / (Nat.choose n 2 : ℝ)

def operator (n : ℕ) (d : Fin n → ℕ) : StateSpace n d →L[ℝ] StateSpace n d :=
  ContinuousLinearMap.id ℝ (StateSpace n d) -
    (1 / (Nat.choose n 2 : ℝ)) • generator n d

theorem pairs_card : (pairs n).card = Nat.choose n 2 := by
  simp [pairs]

theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → StateSpace n d) (G : GraphState n d) :
    (∑ i ∈ s, f i) G = ∑ i ∈ s, f i G := by
  change (WithLp.ofLp (∑ i ∈ s, f i)) G = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]

theorem operator_eq_average (hn : 2 ≤ n) (f : StateSpace n d) (G : GraphState n d) :
    operator n d f G = (∑ a ∈ pairs n, expectation n d a f G) / (Nat.choose n 2 : ℝ) := by
  have hc : (Nat.choose n 2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hn).ne'
  change f G - (1 / (Nat.choose n 2 : ℝ)) * generator n d f G = _
  rw [generator_apply, sum_apply]
  simp_rw [fluctuation_eq_sub, PiLp.sub_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, pairs_card]
  field_simp
  ring

theorem operator_average (hn : 2 ≤ n) (f : StateSpace n d) :
    operator n d f = (1 / (Nat.choose n 2 : ℝ)) •
      (∑ a ∈ pairs n, expectation n d a f) := by
  ext G
  change operator n d f G = (1 / (Nat.choose n 2 : ℝ)) *
    (∑ a ∈ pairs n, expectation n d a f) G
  rw [sum_apply, one_div_mul_eq_div]
  exact operator_eq_average hn f G

theorem operator_nonneg (hn : 2 ≤ n) (f : StateSpace n d) : 0 ≤ ⟪f,operator n d f⟫ := by
  rw [operator_average hn, real_inner_smul_right, inner_sum]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro a _
  rw [real_inner_comm]
  exact Submodule.re_inner_starProjection_nonneg (fiberSpace n d a) f

theorem pair_kernel_apply (a : Finset (Fin n)) (f : GraphState n d → ℝ) (G : GraphState n d) :
    (∑ H, ((if H ∈ fiberStates a G then (1 : ℝ) else 0) /
      ((fiberStates a G).card : ℝ)) * f H) =
      (∑ H ∈ fiberStates a G, f H) / ((fiberStates a G).card : ℝ) := by
  simp_rw [div_mul_eq_mul_div, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_div]
  congr 1
  simp only [fiberStates, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ, true_and]

theorem kernel_apply (hn : 2 ≤ n) (f : GraphState n d → ℝ) (G : GraphState n d) :
    (∑ H, kernel n d G H * f H) = operator n d (WithLp.toLp 2 f) G := by
  rw [operator_eq_average hn]
  unfold kernel
  simp_rw [div_mul_eq_mul_div, Finset.sum_mul]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [pair_kernel_apply, expectation_eq_average]

theorem kernel_nonneg (G H : GraphState n d) : 0 ≤ kernel n d G H := by
  unfold kernel
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro a _
  apply div_nonneg _ (Nat.cast_nonneg _)
  split_ifs <;> norm_num

theorem kernel_row_sum (hn : 2 ≤ n) (G : GraphState n d) : ∑ H, kernel n d G H = 1 := by
  have h := kernel_apply hn (fun _ => 1) G
  simpa [operator] using h

theorem operator_isSymmetric : (operator n d).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪f - (1 / (Nat.choose n 2 : ℝ)) • generator n d f,g⟫ =
    ⟪f,g - (1 / (Nat.choose n 2 : ℝ)) • generator n d g⟫
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  congr 1
  congr 1
  exact generator_isSymmetric f g

theorem kernel_symm (hn : 2 ≤ n) (G H : GraphState n d) : kernel n d G H = kernel n d H G := by
  let eG : StateSpace n d := WithLp.toLp 2 (fun X => if X = G then 1 else 0)
  let eH : StateSpace n d := WithLp.toLp 2 (fun X => if X = H then 1 else 0)
  have h := operator_isSymmetric (n := n) (d := d) eG eH
  change ⟪operator n d eG,eH⟫ = ⟪eG,operator n d eH⟫ at h
  rw [state_inner,state_inner] at h
  simp only [eG,eH] at h
  simp only [mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  have hg := kernel_apply hn (fun X => if X = G then 1 else 0) H
  have hh := kernel_apply hn (fun X => if X = H then 1 else 0) G
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hg hh
  exact hh.trans (h.symm.trans hg.symm)

def dirichletEnergy (n : ℕ) (d : Fin n → ℕ) (f : GraphState n d → ℝ) : ℝ :=
  uniformInner n d f (fun G => f G - ∑ H, kernel n d G H * f H)

def hasSpectralGapAtLeast (n : ℕ) (d : Fin n → ℕ) (γ : ℝ) : Prop :=
  ∀ f : GraphState n d → ℝ, γ * uniformVariance n d f ≤ dirichletEnergy n d f

theorem energy_eq_generator (hn : 2 ≤ n) (f : GraphState n d → ℝ) :
    dirichletEnergy n d f =
      (⟪WithLp.toLp 2 f,generator n d (WithLp.toLp 2 f)⟫ / (stateCount n d : ℝ)) /
        (Nat.choose n 2 : ℝ) := by
  unfold dirichletEnergy uniformInner uniformAverage
  simp_rw [kernel_apply hn]
  change (∑ G ∈ allGraphStates n d,
    f G * (f G - (f G - (1 / (Nat.choose n 2 : ℝ)) *
      generator n d (WithLp.toLp 2 f) G))) / (stateCount n d : ℝ) = _
  simp only [sub_sub_cancel]
  rw [state_inner]
  simp only [allGraphStates]
  simp_rw [mul_left_comm (f _) (1 / (Nat.choose n 2 : ℝ))]
  rw [← Finset.mul_sum]
  ring

theorem gap (hn : 4 ≤ n) (hgraph : Graphical n d) :
    hasSpectralGapAtLeast n d (2 / (Nat.choose n 2 : ℝ)) := by
  intro f
  rw [energy_eq_generator (by omega)]
  have h := div_le_div_of_nonneg_right
    (twice_variance_le_generator (by omega) hgraph f)
    (Nat.cast_nonneg (Nat.choose n 2))
  simpa only [div_mul_eq_mul_div] using h

end
end SharpSwitchGap.Curveball
