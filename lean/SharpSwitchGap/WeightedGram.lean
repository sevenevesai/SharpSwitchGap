import Mathlib

/- Weighted version of the projection argument in upstream GramComparison.lean.
The orthogonal-complement estimate is an explicit hypothesis, not a proved
Johnson gap. This is reusable partial progress toward milestone B1. -/

namespace SharpSwitchGap.WeightedGram

noncomputable section
open scoped RealInnerProductSpace

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem range_bound
    (B : F →ₗ[ℝ] E) (G : E →ₗ[ℝ] E) (p μ₁ μ₂ lam₁ lam₂ : ℝ)
    (hbound₁ : p * μ₁ + 1 ≤ lam₁) (hbound₂ : p * μ₂ + 1 ≤ lam₂)
    (hdecomp : ∀ c : F, ∃ u v : F,
      B c = B u + B v ∧ ⟪u, v⟫ = 0 ∧
      LinearMap.adjoint B (B u) = μ₁ • u ∧
      LinearMap.adjoint B (B v) = μ₂ • v ∧
      G (B u) = lam₁ • B u ∧ G (B v) = lam₂ • B v)
    (c : F) :
    p * ‖LinearMap.adjoint B (B c)‖ ^ 2 + ‖B c‖ ^ 2 ≤ ⟪B c, G (B c)⟫ := by
  obtain ⟨u, v, hc, huv, hKu, hKv, hGu, hGv⟩ := hdecomp c
  have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  have hBu : ⟪B u, B u⟫ = μ₁ * ‖u‖ ^ 2 := by
    rw [← B.adjoint_inner_right, hKu, inner_smul_right, real_inner_self_eq_norm_sq]
  have hBv : ⟪B v, B v⟫ = μ₂ * ‖v‖ ^ 2 := by
    rw [← B.adjoint_inner_right, hKv, inner_smul_right, real_inner_self_eq_norm_sq]
  have hBuv : ⟪B u, B v⟫ = 0 := by
    rw [← B.adjoint_inner_right, hKv, inner_smul_right, huv, mul_zero]
  have hBvu : ⟪B v, B u⟫ = 0 := by rw [real_inner_comm]; exact hBuv
  have hposu : 0 ≤ μ₁ * ‖u‖ ^ 2 := by
    rw [← hBu, real_inner_self_eq_norm_sq]; positivity
  have hposv : 0 ≤ μ₂ * ‖v‖ ^ 2 := by
    rw [← hBv, real_inner_self_eq_norm_sq]; positivity
  have h₁ := mul_le_mul_of_nonneg_right hbound₁ hposu
  have h₂ := mul_le_mul_of_nonneg_right hbound₂ hposv
  rw [hc, map_add, hKu, hKv, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, map_add, hGu, hGv]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, huv, hvu, hBuv, hBvu, hBu, hBv,
    real_inner_self_eq_norm_sq, mul_zero, add_zero, zero_add]
  nlinarith

theorem extend_from_range
    (B : F →ₗ[ℝ] E) (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (C : Submodule ℝ E) (p : ℝ)
    (hBC : LinearMap.range B ≤ C)
    (hinv : ∀ y : E, y ∈ LinearMap.range B → G y ∈ LinearMap.range B)
    (hcomp : ∀ c : F,
      p * ‖LinearMap.adjoint B (B c)‖ ^ 2 + ‖B c‖ ^ 2 ≤ ⟪B c, G (B c)⟫)
    (hresidual : ∀ y : E, y ∈ C → y ∈ (LinearMap.range B)ᗮ → ‖y‖ ^ 2 ≤ ⟪y, G y⟫)
    (x : E) (hxC : x ∈ C) :
    p * ⟪x, B (LinearMap.adjoint B x)⟫ + ‖x‖ ^ 2 ≤ ⟪x, G x⟫ := by
  let M := LinearMap.range B
  let u := M.starProjection x
  let v := x - u
  have hu : u ∈ M := M.starProjection_apply_mem x
  have hv : v ∈ Mᗮ := M.sub_starProjection_mem_orthogonal x
  have hx : x = u + v := by dsimp only [v]; abel
  have hvC : v ∈ C := C.sub_mem hxC (hBC hu)
  have hBv : LinearMap.adjoint B v = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [LinearMap.adjoint_inner_left, real_inner_comm]
    exact hv (B (LinearMap.adjoint B v)) (LinearMap.mem_range_self _ _)
  have huv : ⟪u, v⟫ = 0 := hv u hu
  have hcross : ⟪u, G v⟫ = 0 := by
    rw [← hG u v]
    exact hv (G u) (hinv u hu)
  have hcross' : ⟪v, G u⟫ = 0 := by
    rw [real_inner_comm]
    exact hv (G u) (hinv u hu)
  have hnorm : ‖LinearMap.adjoint B x‖ ^ 2 = ‖LinearMap.adjoint B u‖ ^ 2 := by
    rw [hx, map_add, hBv, add_zero]
  have hsplit : ‖x‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    rw [hx, norm_add_sq_real, huv]
    ring
  have hform : ⟪x, G x⟫ = ⟪u, G u⟫ + ⟪v, G v⟫ := by
    rw [hx, map_add, inner_add_left, inner_add_right, inner_add_right,
      hcross, hcross']
    ring
  obtain ⟨c, hc⟩ := hu
  have hccomp := hcomp c
  rw [hc] at hccomp
  have hvcomp := hresidual v hvC hv
  rw [← LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq, hnorm, hsplit, hform]
  linarith

end
end SharpSwitchGap.WeightedGram

#print axioms SharpSwitchGap.WeightedGram.range_bound
#print axioms SharpSwitchGap.WeightedGram.extend_from_range
