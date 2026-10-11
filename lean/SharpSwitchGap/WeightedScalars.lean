import Mathlib

/- Scalar inequalities for the weighted slice and cell arguments.
These do not by themselves prove either operator inequality. -/

namespace SharpSwitchGap.WeightedScalars

theorem linear_slack_identity (N q r : ℝ) (hN : 3 ≤ N) (hsum : q + r = N) :
    N / 2 - (N - 2 * q) ^ 2 / (2 * (N - 2)) - 1 =
      2 * (q - 1) * (r - 1) / (N - 2) := by
  have hden : N - 2 ≠ 0 := by linarith
  rw [← hsum]
  have hden' : q + r - 2 ≠ 0 := by rw [hsum]; exact hden
  field_simp
  ring

theorem linear_slack_nonneg (N q r : ℝ) (hN : 3 ≤ N)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hsum : q + r = N) :
    0 ≤ N / 2 - (N - 2 * q) ^ 2 / (2 * (N - 2)) - 1 := by
  rw [linear_slack_identity N q r hN hsum]
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hq)) (sub_nonneg.mpr hr))
    (by linarith)

theorem quadratic_weight_le_one (N q r : ℝ) (hN : 4 ≤ N)
    (hsum : q + r = N) :
    2 * (q - 1) * (r - 1) / ((N - 2) * (N - 3)) ≤ 1 := by
  have hden : 0 < (N - 2) * (N - 3) := mul_pos (by linarith) (by linarith)
  apply (div_le_iff₀ hden).mpr
  have hprod := mul_nonneg (show 0 ≤ N - 2 by linarith) (show 0 ≤ N - 4 by linarith)
  nlinarith [sq_nonneg (q - r)]

theorem quadratic_slack_nonneg (N q r : ℝ) (hN : 4 ≤ N)
    (hsum : q + r = N) :
    0 ≤ N - 1 - 2 * (q - 1) * (r - 1) / ((N - 2) * (N - 3)) - 1 := by
  have h := quadratic_weight_le_one N q r hN hsum
  linarith

theorem equality_probability_le (N q r : ℝ) (hN : 2 ≤ N)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hsum : q + r = N) :
    (q * (q - 1) + r * (r - 1)) / (N * (N - 1)) ≤ (N - 2) / N := by
  have hN0 : 0 < N := by linarith
  have hden : 0 < N * (N - 1) := mul_pos hN0 (by linarith)
  apply (div_le_iff₀ hden).mpr
  have he : (N - 2) / N * (N * (N - 1)) = (N - 2) * (N - 1) := by
    field_simp
  rw [he, ← hsum]
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hr)]

theorem weighted_quadratic_bound (N p μ : ℝ) (hN : 4 ≤ N) (hp : 0 ≤ p)
    (hpbound : p ≤ (N - 2) / N) (hμ : μ ≤ (N - 1) / (N - 3)) :
    p * μ + 1 ≤ N - 1 := by
  have hN0 : 0 < N := by linarith
  have hN3 : 0 < N - 3 := by linarith
  have hratio : 0 ≤ (N - 1) / (N - 3) := div_nonneg (by linarith) hN3.le
  have hprod : p * μ ≤ (N - 2) / N * ((N - 1) / (N - 3)) :=
    (mul_le_mul_of_nonneg_left hμ hp).trans
      (mul_le_mul_of_nonneg_right hpbound hratio)
  have hlast : (N - 2) / N * ((N - 1) / (N - 3)) ≤ N - 2 := by
    rw [div_mul_div_comm]
    apply (div_le_iff₀ (mul_pos hN0 hN3)).mpr
    have hpoly : 0 ≤ N * (N - 3) - (N - 1) := by
      nlinarith [mul_nonneg hN0.le (show 0 ≤ N - 4 by linarith)]
    nlinarith [mul_nonneg (show 0 ≤ N - 2 by linarith) hpoly]
  linarith

theorem cell_weights (pr pc : ℝ) (hpr : 0 < pr) (hpc : 0 < pc)
    (hsum : pr + pc < 1) :
    (pr / (1 - pc)) * (pc / (1 - pr)) =
      (Real.sqrt (pc * pr / ((1 - pc) * (1 - pr)))) ^ 2 := by
  have hden : 0 < (1 - pc) * (1 - pr) := mul_pos (by linarith) (by linarith)
  rw [Real.sq_sqrt (div_nonneg (mul_nonneg hpc.le hpr.le) hden.le)]
  rw [div_mul_div_comm]
  congr 1
  ring

theorem weighted_square (α β ρ x y : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hρ : 0 ≤ ρ) (hfactor : α * β = ρ ^ 2) :
    0 ≤ β * x ^ 2 + 2 * ρ * x * y + α * y ^ 2 := by
  have hsα := Real.sq_sqrt hα
  have hsβ := Real.sq_sqrt hβ
  have hroot : Real.sqrt β * Real.sqrt α = ρ := by
    have hsquare : (Real.sqrt β * Real.sqrt α) ^ 2 = ρ ^ 2 := by
      rw [mul_pow, hsβ, hsα, mul_comm, hfactor]
    nlinarith [mul_nonneg (Real.sqrt_nonneg β) (Real.sqrt_nonneg α)]
  have he : (Real.sqrt β * x + Real.sqrt α * y) ^ 2 =
      β * x ^ 2 + 2 * ρ * x * y + α * y ^ 2 := by
    calc
      _ = (Real.sqrt β) ^ 2 * x ^ 2 +
          2 * (Real.sqrt β * Real.sqrt α) * x * y + (Real.sqrt α) ^ 2 * y ^ 2 := by ring
      _ = _ := by rw [hsβ, hsα, hroot]
  rw [← he]
  exact sq_nonneg _

end SharpSwitchGap.WeightedScalars

#print axioms SharpSwitchGap.WeightedScalars.linear_slack_nonneg
#print axioms SharpSwitchGap.WeightedScalars.quadratic_slack_nonneg
#print axioms SharpSwitchGap.WeightedScalars.cell_weights
#print axioms SharpSwitchGap.WeightedScalars.weighted_square
