import Mathlib.RingTheory.Nilpotent
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Polynomial.Lifts
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Ideal.QuotientOperations

variable {R : Type _}

open Finset Polynomial BigOperators

theorem isUnit_of_isNilpotent_sub_one [Ring R] {r : R} (hnil : IsNilpotent r) : IsUnit (r - 1) := by
  obtain ⟨n, hn⟩ := hnil
  refine' ⟨⟨r - 1, -∑ i in range n, r ^ i, _, _⟩, rfl⟩
  · rw [mul_neg, mul_geom_sum, hn]
    simp
  · rw [neg_mul, geom_sum_mul, hn]
    simp

variable [Ring R]

theorem isUnit_of_isUnit_add_isNilpotent {r : R} {u : Rˣ} (hnil : IsNilpotent r)
  (hru : Commute r (↑u⁻¹ : R)) : IsUnit (u + r) := by
  rw [← Units.isUnit_mul_units _ u⁻¹, add_mul, Units.mul_inv, ← IsUnit.neg_iff, add_comm, neg_add,
    ← sub_eq_add_neg]
  apply isUnit_of_isNilpotent_sub_one
  obtain ⟨n, hn⟩ := hnil
  refine' ⟨n, _⟩
  rw [neg_pow, hru.mul_pow, hn]
  simp

namespace Polynomial

theorem isNilpotent.C_mul_X_pow {r : R} (n : ℕ) (hnil : IsNilpotent r) :
    IsNilpotent ((C r) * X ^ n) := (Commute.all _ _).isNilpotent_mul_left (hnil.map _)

/-- Let P be a polynomial over R. If its constant term is a unit and its other coefficients are
nilpotent, then P is a unit. This is one implication of 'isUnit_iff'. -/
theorem isUnit_of_isUnit_of_isNilpotent {P : Polynomial R} (hunit : IsUnit (P.coeff 0))
    (hnil : ∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) : IsUnit P := by
  induction' h : P.natDegree using Nat.strong_induction_on with k hind generalizing P
  by_cases hdeg : P.natDegree = 0
  { rw [eq_C_of_natDegree_eq_zero hdeg]
    exact hunit.map C }
  let P₁ := P.eraseLead
  suffices IsUnit P₁ by
    rw [← eraseLead_add_monomial_natDegree_leadingCoeff P, ← C_mul_X_pow_eq_monomial]
    exact isUnit_of_isUnit_add_isNilpotent this (isNilpotent.C_mul_X_pow _ (hnil _ hdeg))
  have hdeg₂ := lt_of_le_of_lt P.eraseLead_natDegree_le (Nat.sub_lt
    (Nat.pos_of_ne_zero hdeg) zero_lt_one)
  refine' hind P₁.natDegree _ _ (fun i hi => _) rfl
  · simp_rw [← h, hdeg₂]
  · simp_rw [eraseLead_coeff_of_ne _ (Ne.symm hdeg), hunit]
  · by_cases H : i ≤ P₁.natDegree
    simp_rw [eraseLead_coeff_of_ne _ (ne_of_lt (lt_of_le_of_lt H hdeg₂)), hnil i hi]
    simp_rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge H), IsNilpotent.zero]

/-- Let P be a polynomial over R. If P is a unit, then all its coefficients are nilpotent, except
its constant term which is a unit. This is the other implication of 'isUnit_iff'. -/
theorem isUnit.coeff {P : Polynomial R} (hunit : IsUnit P) :
    IsUnit (P.coeff 0) ∧ (∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) := by
  obtain ⟨Q, hQ⟩ := IsUnit.exists_right_inv hunit
  constructor
  { refine' isUnit_of_mul_eq_one _ (Q.coeff 0) _
    have h := (mul_coeff_zero P Q).symm
    rwa [hQ, coeff_one_zero] at h }
  { intros n hn
    rw [nilpotent_iff_mem_prime]
    intros I hI
    let f := mapRingHom (Ideal.Quotient.mk I)
    have hPQ : degree (f P) = 0 ∧ degree (f Q) = 0 := by
      rw [← Nat.WithBot.add_eq_zero_iff, ← degree_mul, ← map_mul, hQ, map_one, degree_one]
    have hcoeff : (f P).coeff n = 0 := by
      refine' coeff_eq_zero_of_degree_lt _
      rw [hPQ.1]
      exact (@WithBot.coe_pos _ _ _ n).2 (Ne.bot_lt hn)
    rw [coe_mapRingHom, coeff_map, ← RingHom.mem_ker, Ideal.mk_ker] at hcoeff
    exact hcoeff }

/-- Let P be a polynomial over R. P is a unit if and only if all its coefficients are nilpotent,
except its constant term which is a unit. -/
theorem isUnit_iff (P : Polynomial R) :
    IsUnit P ↔ IsUnit (P.coeff 0) ∧ (∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) := ⟨isUnit.coeff,
  fun H => isUnit_of_isUnit_of_isNilpotent H.1 H.2⟩

end Polynomial
