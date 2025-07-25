import Mathlib
import Kaplanski4.Kaplanski
import Kaplanski4.Cohen

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

lemma mem_map_constantCoeff {I : Ideal R⟦X⟧} {x : R} :
    x ∈ I.map (constantCoeff R) ↔ ∃ f ∈ I, f.constantCoeff R = x :=
  I.mem_map_iff_of_surjective _ constantCoeff_surj

lemma constantCoeff_mem_map_of_mem {I : Ideal R⟦X⟧} {f : R⟦X⟧} :
    f ∈ I → f.constantCoeff R ∈ I.map (constantCoeff R) :=
  (mem_map_constantCoeff.2 ⟨_, ·, rfl⟩)


section X_mem_I

variable {I : Ideal R⟦X⟧} (hXI : X ∈ I)
include hXI

theorem map_constantCoeff_subset_self : (C R)'' I.map (constantCoeff R) ⊆ I := by
  intro _ ⟨_, _, ha⟩
  rcases mem_map_constantCoeff.1 <| SetLike.mem_coe.1 ‹_› with ⟨g, _, hgr⟩
  rw [← ha, ← hgr]
  exact eq_sub_of_add_eq' g.eq_X_mul_shift_add_const.symm ▸ I.sub_mem ‹_› (I.mul_mem_right _ ‹_›)

variable {S : Set R} (hSI : span S = I.map (constantCoeff R))
include hSI

theorem eq_span_insert_X : I = span (insert X ((C R)'' S)) := by
  ext f
  rw [mem_span_insert, ← map_span, hSI]
  exact ⟨
    fun _ ↦ ⟨mk fun p ↦ coeff R (p + 1) f, C R (f.constantCoeff R),
      mem_map_of_mem _ (constantCoeff_mem_map_of_mem ‹_›), f.eq_shift_mul_X_add_const⟩,
    fun ⟨_, _, _, _⟩ ↦ ‹_› ▸ I.add_mem (I.mul_mem_left _ ‹_›)
      (span_le.2 (map_constantCoeff_subset_self ‹_›) ‹_›)
  ⟩

end X_mem_I


section X_notMem_P

variable {P : Ideal R⟦X⟧} (hP : X ∉ P) {k : ℕ} {a : Fin k → R}
  (haP : span (range a) = P.map (constantCoeff R))

/- Exctacting `f : Fin k → R⟦X⟧` from `a : Fin k → R` -/
section f

include haP in
private lemma exists_f : ∀ i, ∃ f ∈ P, f.constantCoeff R = a i :=
  fun i ↦ mem_map_constantCoeff.1 <| haP ▸ subset_span (mem_range_self i)

private def f i := (exists_f haP i).choose

private lemma f_mem_P : ∀ i, f haP i ∈ P := fun i ↦ (exists_f haP i).choose_spec.1

private lemma hfa : ∀ i, (f haP i).constantCoeff R = a i := fun i ↦ (exists_f haP i).choose_spec.2

end f

variable {g : R⟦X⟧} (hg : g ∈ P)

include haP hg in
private lemma exists_r : ∃ r : Fin k → R, ∑ i, r i * a i = g.constantCoeff R :=
  mem_span_range_iff_exists_fun.1 (haP ▸ constantCoeff_mem_map_of_mem ‹_›)

private def r : Fin k → R := (exists_r ‹_› hg).choose

private lemma hr : ∑ i, r ‹_› hg i * a i = g.constantCoeff R := (exists_r ‹_› ‹_›).choose_spec

/- We now want to show that g = ∑ i, h i * f i for some `h : Fin k → R⟦X⟧` -/

variable [P_prime : P.IsPrime]
include hP

private def g' : ℕ → P
| 0 => ⟨g, hg⟩
| n + 1 =>
  ⟨mk fun p ↦ coeff R (p + 1) (g' n) - ∑ i, r ‹_› (g' n).2 i * coeff R (p + 1) (f ‹_› i), by
    have h := sub_const_eq_X_mul_shift ((g' n).1 - ∑ i, C R (r ‹_› (g' n).2 i) * f ‹_› i)
    simp only [map_sub, map_sum, _root_.map_mul, constantCoeff_C, hfa, hr, sub_self, map_zero,
      sub_zero, coeff_C_mul] at h
    have : ∑ i, C R (r ‹_› (g' n).2 i) * f ‹_› i ∈ P :=
      P.sum_mem fun i _ ↦ P.mul_mem_left _ (f_mem_P ‹_› i)
    exact (P_prime.mul_mem_iff_mem_or_mem.1 (h ▸ P.sub_mem (g' n).2 ‹_›)).resolve_left hP⟩

private lemma hg' (n : ℕ) : (g' ‹_› ‹_› ‹_› n).1 - ∑ i, C R (r ‹_› (g' ‹_› ‹_› ‹_› n).2 i) * f ‹_› i
    = X * (g' ‹_› ‹_› ‹_› (n + 1)).1 := by
  simpa [hr, hfa] using sub_const_eq_X_mul_shift
    ((g' hP haP hg n).1 - ∑ i, C R (r haP (g' hP haP hg n).2 i) * f haP i)

private def h (i : Fin k) : R⟦X⟧ := mk fun n ↦ r ‹_› (g' ‹_› ‹_› ‹_› n).2 i

private lemma key (n : ℕ) :
    g - ∑ i, trunc n (h ‹_› ‹_› hg i) * f haP i = X ^ n * (g' ‹_› ‹_› ‹_› n).1 := by
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

private lemma sum_h_eq_g : ∑ i, h ‹_› ‹_› ‹_› i * f ‹_› i = g := by
  refine (sub_eq_zero.1 ?_).symm
  ext n
  conv =>
    enter [1, 2, 2, 2, i]
    rw [eq_trunc_add_X_pow_mul (h ‹_› ‹_› ‹_› i) (n + 1), add_mul, mul_assoc]
  rw [sum_add_distrib, sub_add_eq_sub_sub, key, ← mul_sum]
  simp [coeff_X_pow_mul']

/- We show that P is finitely generated  -/

private theorem P_eq_span_range : P = span (range (f ‹_›)) :=
  le_antisymm
    (fun _ hg ↦ mem_span_range_iff_exists_fun.2 ⟨_, sum_h_eq_g ‹_› ‹_› ‹_›⟩)
    (span_le.2 <| range_subset_iff.2 <| f_mem_P ‹_›)

theorem exist_eq_span_eq_ncard_of_X_notMem {S : Set R}
  (_ : span S = P.map (constantCoeff R)) (_ : S.Finite) :
    ∃ T, P = span T ∧ T.Finite ∧ T.ncard = S.ncard := by
  obtain ⟨k, a, a_injective, rfl⟩ := Finite.fin_param ‹_›
  have := P_eq_span_range ‹_› ‹_›
  refine ⟨_, this, finite_range _, ?_⟩
  have h₁ : (range a).ncard = k := by
    refine ncard_eq_of_bijective (a ⟨·, ·⟩) ?_ ?_ ?_
    · intro _ ⟨i, _⟩
      use i.1, i.2
    · exact fun _ _ ↦ mem_range_self _
    · exact fun _ _ _ _ _ ↦ Fin.mk_eq_mk.1 (a_injective ‹_›)
  have h₂ : (range (f ‹_›)).ncard = k := by
    refine ncard_eq_of_bijective (f ‹_› ⟨·, ·⟩) ?_ ?_ ?_
    · intro _ ⟨i, _⟩
      use i.1, i.2
    · exact fun _ _ ↦ mem_range_self _
    · intro _ _ _ _ this
      replace := congrArg (constantCoeff R) this
      simp [hfa] at this
      exact Fin.mk_eq_mk.1 (a_injective ‹_›)
  rw [h₁, h₂]

end X_notMem_P


section final_theorems

instance [hR : IsPrincipalIdealRing R] [IsDomain R] : UniqueFactorizationMonoid R⟦X⟧ := by
  apply (uniqueFactorizationMonoid_iff ⟨_, X_prime⟩).2
  intro P _ _
  by_cases X ∈ P
  · exact ⟨X, ‹_›, X_prime⟩
  · obtain ⟨_, h⟩ := (hR.principal (P.map (constantCoeff R))).principal
    obtain ⟨_, rfl, _, h⟩ := exist_eq_span_eq_ncard_of_X_notMem ‹_› (h.symm) (finite_singleton _)
    simp only [ncard_singleton, ncard_eq_one] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨_, mem_span_singleton_self _,
      (span_singleton_prime (span_singleton_eq_bot.not.1 ‹_›)).1 ‹_›⟩

lemma prime_fg_iff {P : Ideal R⟦X⟧} [P.IsPrime] : P.FG ↔ (P.map (constantCoeff R)).FG := by
  constructor
  · exact (FG.map · _)
  · intro ⟨S, _⟩
    by_cases X ∈ P
    · have H := eq_span_insert_X ‹_› ‹_›
      have : (insert X <| (C R)'' S).Finite := Finite.insert X <| Finite.image _ S.finite_toSet
      lift insert X <| (C R)'' S to Finset R⟦X⟧ using this with T hT
      exact ⟨T, hT ▸ H.symm⟩
    · obtain ⟨T, hT, hT₂, _⟩ := exist_eq_span_eq_ncard_of_X_notMem ‹_› ‹_› S.finite_toSet
      lift T to Finset R⟦X⟧ using hT₂
      exact ⟨T, hT.symm⟩

instance [IsNoetherianRing R] : IsNoetherianRing R⟦X⟧ :=
  IsNoetherianRing.of_prime fun P _ ↦
    prime_fg_iff.2 <| (isNoetherianRing_iff_ideal_fg R).1 ‹_› (P.map (constantCoeff R))

end final_theorems

end
