import SharpSwitchGap.AffinePlane
import OAI.Probability.SwitchChain.FiniteEventVectors

namespace SharpSwitchGap.EventPlane

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 FiniteEventVectors DisjointIndicators
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

theorem affine_span (s : Finset Ω) (hp : 0 < probability s) (hp1 : probability s < 1)
    (f : EuclideanSpace ℝ Ω) (a b : ℝ)
    (hf : ∀ x, f x = a + b * rawIndicator s x) :
    ∃ A B : ℝ, f = A • constantVector +
      B • normalizedFlag constantVector (eventVector s) (probability s) := by
  let N : ℝ := Real.sqrt (Fintype.card Ω : ℝ)
  let D : ℝ := Real.sqrt (probability s * (1 - probability s))
  have hN : N ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast Fintype.card_pos (α := Ω))
  have hD : D ≠ 0 := Real.sqrt_ne_zero'.mpr (mul_pos hp (sub_pos.mpr hp1))
  refine ⟨N * (a + b * probability s), N * b * D, ?_⟩
  ext x
  rw [hf x]
  simp only [normalizedFlag, constantVector, eventVector, PiLp.add_apply,
    PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  change a + b * rawIndicator s x =
    N * (a + b * probability s) * (N⁻¹ * rawIndicator Finset.univ x) +
      (N * b * D) * (D⁻¹ * (N⁻¹ * rawIndicator s x - probability s *
        (N⁻¹ * rawIndicator Finset.univ x)))
  simp only [rawIndicator, Finset.mem_univ, ite_true]
  field_simp
  ring

theorem correlation_weights (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p + q < 1) :
    (q / (1 - p)) * (p / (1 - q)) = correlation p q ^ 2 := by
  have hp1 : p < 1 := by linarith
  have hq1 : q < 1 := by linarith
  unfold correlation
  rw [div_pow, mul_pow, Real.sq_sqrt (mul_nonneg hp.le (sub_nonneg.mpr hp1.le)),
    Real.sq_sqrt (mul_nonneg hq.le (sub_nonneg.mpr hq1.le))]
  field_simp

theorem weighted_interaction
    (P Q G R S : EuclideanSpace ℝ Ω →ₗ[ℝ] EuclideanSpace ℝ Ω)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (s t : Finset Ω) (hs : s.Nonempty) (ht : t.Nonempty) (hd : Disjoint s t)
    (hcenter : ∃ x : Ω, x ∉ s ∧ x ∉ t)
    (hPe : P constantVector = constantVector) (hQe : Q constantVector = constantVector)
    (hPs' : P (eventVector s) = eventVector s) (hQt : Q (eventVector t) = eventVector t)
    (hPQ : ∀ z, ∃ a b : ℝ, ∀ x, P (Q z) x = a + b * rawIndicator s x)
    (hQP : ∀ z, ∃ a b : ℝ, ∀ x, Q (P z) x = a + b * rawIndicator t x)
    (hRe : R constantVector = 0) (hSe : S constantVector = 0)
    (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (hRrange : ∀ z, R (Q (P z) - P (Q (P z))) = Q (P z) - P (Q (P z)))
    (hSrange : ∀ z, S (P (Q z) - Q (P (Q z))) = P (Q z) - Q (P (Q z)))
    (f : EuclideanSpace ℝ Ω) :
    2 * ‖G f‖ ^ 2 - (probability t / (1 - probability s)) * ‖R f‖ ^ 2 -
      (probability s / (1 - probability t)) * ‖S f‖ ^ 2 ≤
      2 * ⟪f - P f, f - Q f⟫ := by
  let p := probability s
  let q := probability t
  have hp : 0 < p := probability_pos s hs
  have hq : 0 < q := probability_pos t ht
  have hpq : p + q < 1 := probability_add_lt_one s t hd hcenter
  have hg := normalized_events_gram s t hs ht hd hcenter
  let u := normalizedFlag constantVector (eventVector s) p
  let v := normalizedFlag constantVector (eventVector t) q
  have hPu : P u = u := normalizedFlag_fixed P _ _ _ hPe hPs'
  have hQv : Q v = v := normalizedFlag_fixed Q _ _ _ hQe hQt
  have hPQ' z : ∃ a b : ℝ, P (Q z) = a • constantVector + b • u := by
    obtain ⟨a,b,hab⟩ := hPQ z
    exact affine_span s hp (by linarith) (P (Q z)) a b hab
  have hQP' z : ∃ a b : ℝ, Q (P z) = a • constantVector + b • v := by
    obtain ⟨a,b,hab⟩ := hQP z
    exact affine_span t hq (by linarith) (Q (P z)) a b hab
  have hcomp := WeightedInteraction.composition_of_affine_images P Q hPs hQs
    constantVector u v (correlation p q) hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1
    hg.2.2.2.2.1 hg.2.2.2.2.2.1 hPe hQe hPu hQv hPQ' hQP'
  have hc : correlation p q ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hp.ne' hq.ne'))
      (mul_ne_zero (Real.sqrt_ne_zero'.mpr (mul_pos hp (by linarith)))
        (Real.sqrt_ne_zero'.mpr (mul_pos hq (by linarith))))
  have hRline : R (v - P v) = v - P v := by
    apply (smul_right_injective (R := ℝ) (EuclideanSpace ℝ Ω) hc)
    have h := hRrange u
    simpa only [hPu, hcomp.2.2, map_smul, ← smul_sub] using h
  have hSline : S (u - Q u) = u - Q u := by
    apply (smul_right_injective (R := ℝ) (EuclideanSpace ℝ Ω) hc)
    have h := hSrange v
    simpa only [hQv, hcomp.2.1, map_smul, ← smul_sub] using h
  apply WeightedInteraction.disjoint_interaction_of_affine_images P Q G R S
    hPs hQs hGs hRs hSs hPi hQi hGi constantVector u v (correlation p q)
    (q / (1 - p)) (p / (1 - q)) (correlation_sq_lt_one p q hp hq hpq)
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hp.le hq.le))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    (div_nonneg hq.le (by linarith)) (div_nonneg hp.le (by linarith))
    (correlation_weights p q hp hq hpq) hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1
    hg.2.2.2.2.1 hg.2.2.2.2.2.1 hPe hQe
    hPu hQv hPQ' hQP' hRe hSe hGP hGQ hRline hSline f

end
end SharpSwitchGap.EventPlane
