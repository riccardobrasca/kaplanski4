import Mathlib
import Kaplanski4.Kaplanski

open PowerSeries Ideal Set BigOperators Finset

section for_mathlib

namespace PowerSeries

variable {R : Type*} [CommSemiring R]

lemma eq_trunc_add_X_pow_mul (g : R⟦X⟧) (n : ℕ) : g =
    trunc n g + (X ^ n : R⟦X⟧) * mk fun m ↦ coeff R (m + n) g:= by
  ext m
  by_cases hm : m < n <;>
  simp [coeff_trunc, hm, coeff_X_pow_mul', Nat.not_le_of_lt, Nat.le_of_not_lt]

end PowerSeries

end for_mathlib


noncomputable section

variable {R : Type*} [CommRing R]

-- Useful notation
local notation I"⁰" => Ideal.map (constantCoeff R) I
local notation f"⁰" => PowerSeries.constantCoeff R f

lemma mem_I0_iff {I : Ideal R⟦X⟧} {x : R} : x ∈ I⁰ ↔ ∃ f ∈ I, f⁰ = x :=
  I.mem_map_iff_of_surjective _ constantCoeff_surj

lemma f0_mem {I : Ideal R⟦X⟧} {f : R⟦X⟧} : f ∈ I → f⁰ ∈ I⁰ :=
  (mem_I0_iff.2 ⟨_, ·, rfl⟩)


section X_mem_I

variable {I : Ideal R⟦X⟧} (hXI : X ∈ I)
include hXI

theorem I0_subset_I : (C R)'' I⁰ ⊆ I := by
  intro _ ⟨_, _, ha⟩
  rcases mem_I0_iff.1 <| SetLike.mem_coe.1 ‹_› with ⟨g, _, hgr⟩
  rw [← ha, ← hgr]
  exact eq_sub_of_add_eq' g.eq_X_mul_shift_add_const.symm ▸ I.sub_mem ‹_› (I.mul_mem_right _ ‹_›)

variable {S : Set R} (hSI : span S = I.map (constantCoeff R))
include hSI

theorem bar : I = span ((C R)'' S ∪ {X}) := by
  ext f
  rw [union_singleton, mem_span_insert, ← map_span, hSI]
  exact ⟨fun _ ↦ ⟨mk fun p ↦ coeff R (p + 1) f, C R (f⁰),
        mem_map_of_mem _ (f0_mem ‹_›), f.eq_shift_mul_X_add_const⟩,
      fun ⟨_, _, _, _⟩ ↦ ‹_› ▸ I.add_mem (I.mul_mem_left _ ‹_›) (span_le.2 (I0_subset_I ‹_›) ‹_›)⟩

theorem bar' [Nontrivial R] (_ : S.Finite) : ∃ T, I = span T ∧ T.ncard = S.ncard + 1 := by
  have := bar ‹_› ‹_›
  refine ⟨_, ‹_›, ?_⟩
  have := injOn_of_injective C_injective (s := S)
  rw [ncard_eq_succ <| finite_union.2 ⟨(finite_image_iff ‹_›).2 ‹_›, finite_singleton _⟩]
  use X, (C R)'' S
  exact ⟨fun ⟨_, _, aX⟩ ↦ by simpa using congrArg (coeff R 1) aX, union_singleton.symm,
    (ncard_image_iff ‹_›).2 ‹_›⟩

end X_mem_I


section X_not_mem_P

variable {P : Ideal R⟦X⟧} (hP : X ∉ P) {k : ℕ} {a : Fin k → R}
  (haP : P.map (constantCoeff R) = span (range a)) {g : R⟦X⟧} (hg : g ∈ P)
include haP

lemma exists_f i : ∃ f ∈ P, f⁰ = a i := mem_I0_iff.1 <| haP ▸ subset_span (mem_range_self i)

def f i := (exists_f haP i).choose

lemma f_mem_P i : f haP i ∈ P := (exists_f haP i).choose_spec.1

lemma hfa i : (f haP i)⁰ = a i := (exists_f haP i).choose_spec.2

include hg in
lemma exists_r : ∃ r : Fin k → R, ∑ i, r i • a i = (constantCoeff R) g :=
  (mem_span_range_iff_exists_fun R).1 (haP ▸ f0_mem hg : _ ∈ span (range a))

def r : Fin k → R := (exists_r haP hg).choose

lemma hr : ∑ i, (r haP hg) i * a i = g⁰ := (exists_r haP hg).choose_spec

variable [P_prime : P.IsPrime]

def g' : ℕ → P
| 0 => ⟨g, hg⟩
| n + 1 =>
  ⟨mk fun p ↦ coeff R (p + 1) (g' n) - ∑ i, r haP (g' n).2 i * coeff R (p + 1) (f haP i), by
    have := sub_const_eq_X_mul_shift ((g' n).1 - ∑ i, C R (r haP (g' n).2 i) * f haP i)
    simp only [map_sub, map_sum, _root_.map_mul, constantCoeff_C, hfa, hr haP (g' n).2, sub_self,
      map_zero, sub_zero, coeff_C_mul] at this
    have hf : ∑ i, C R (r haP (g' n).2 i) * f haP i ∈ P :=
      P.sum_mem fun i _ ↦ P.mul_mem_left _ (f_mem_P haP i)
    exact  (P_prime.mul_mem_iff_mem_or_mem.1 (this ▸ P.sub_mem (g' n).2 hf)).resolve_left hP⟩

lemma hg' (n : ℕ) : (g' hP haP hg n).1 - ∑ i, C R (r haP (g' hP haP hg n).2 i) * f haP i =
    X * (g' hP haP hg (n + 1)).1 := by
  simpa [hr haP (g' hP haP hg n).2, hfa] using sub_const_eq_X_mul_shift
    ((g' hP haP hg n).1 - ∑ i, C R (r haP (g' hP haP hg n).2 i) * f haP i)

def h (i : Fin k) : R⟦X⟧ := mk fun n ↦ r haP (g' hP haP hg n).2 i

lemma key (n : ℕ) : g - ∑ i, trunc n ((h hP haP hg) i) * f haP i = X ^ n * (g' hP haP hg n).1 := by
  induction n with
  | zero => simp [g']
  | succ n H =>
    conv =>
      enter [1, 2, 2, i]
      rw [trunc_succ, Polynomial.coe_add, Polynomial.coe_monomial, add_mul, ← mul_one (coeff R n _),
        ← smul_eq_mul (b := 1), map_smul, ← X_pow_eq, smul_eq_C_mul, mul_comm _ (X ^ n), mul_assoc]
    rw [sum_add_distrib, sub_add_eq_sub_sub, H, ← mul_sum, ← mul_sub]
    simp only [h, coeff_mk, hg']
    ring

lemma sum_h_eq_g : ∑ i, (h hP haP hg) i * f haP i = g := by
  refine (sub_eq_zero.1 ?_).symm
  ext n
  conv =>
    enter [1, 2, 2, 2, i]
    rw [eq_trunc_add_X_pow_mul (h hP haP hg i) (n + 1), add_mul, mul_assoc]
  rw [sum_add_distrib, sub_add_eq_sub_sub, key, ← mul_sum]
  simp [coeff_X_pow_mul']

include hP in
theorem P_eq_span_range : P = span (range (f haP)) :=
  le_antisymm
    (fun _ hg ↦ (mem_span_range_iff_exists_fun _).2 ⟨_, sum_h_eq_g hP haP hg⟩)
    <| span_le.2 <| range_subset_iff.2 <| f_mem_P haP

omit haP in
theorem foo {S : Set R} (hS : S.Finite) (hPX : X ∉ P)
    (hSP : span S = P.map (constantCoeff R)) :
    ∃ T : Set R⟦X⟧, span T = P ∧ T.ncard = S.ncard := by
  sorry

end X_not_mem_P


section Kaplansky13_6

instance Kaplansky13_6 [principal_R : IsPrincipalIdealRing R] [IsDomain R]  :
    UniqueFactorizationMonoid R⟦X⟧ :=  by
  apply (uniqueFactorizationMonoid_iff ⟨_, X_prime⟩).2
  intro P P_ne_bot P_prime
  by_cases hxP : X ∈ P
  · exact ⟨_, hxP, X_prime⟩
  · obtain ⟨_, ha⟩ := (principal_R.principal (P⁰)).principal'
    obtain ⟨_, rfl, hT⟩ := foo (finite_singleton _) hxP ha.symm
    simp only [ncard_singleton, ncard_eq_one] at hT
    obtain ⟨f, rfl⟩ := hT
    exact ⟨_, subset_span (by simp),
      (span_singleton_prime (fun hf0 ↦ P_ne_bot (by simp [hf0]))).1 P_prime⟩

end Kaplansky13_6

end

variable {R : Type*} [CommRing R] {P : Ideal R⟦X⟧} [P.IsPrime]

-- Le théorème est censé être dans mathlib mais je ne l'ai pas trouvé.
lemma is_noetherian_of_prime_ideals_fg
  (h : ∀ (P : Ideal R), P.IsPrime → P.FG) : IsNoetherianRing R :=
  sorry

lemma p_fg_iff (P : Ideal R⟦X⟧)  [P.IsPrime]: P.FG ↔ (Ideal.map (constantCoeff R) P).FG :=
  sorry


instance [hR : IsNoetherianRing R] : IsNoetherianRing R⟦X⟧ := by
  apply is_noetherian_of_prime_ideals_fg
  intro P hP
  apply (p_fg_iff P ).2
  have := isNoetherian_def.1 hR
  specialize this (Ideal.map (constantCoeff R) P)
  assumption
