import Mathlib

open Ideal Set BigOperators Finset

def S (R : Type*) [CommRing R] := {I : Ideal R | ¬ I.FG}

variable {R : Type*} [CommRing R]

lemma hS {M I : Ideal R} (hM : Maximal (S R) M) (hI : M < I) : I.FG := by
  by_contra! h
  exact not_le_of_lt hI <| hM.2 h hI.le

section zorn

variable (h : ¬IsNoetherianRing R)
include h

lemma nonempty_S : (S R).Nonempty :=
  not_forall.1  <| (isNoetherianRing_iff_ideal_fg _).not.1 h

theorem cohen_zorn_lemma (C : Set (Ideal R)) (hC : C ⊆ S R) (hC₂ : IsChain (· ≤ ·) C) :
    ∃ P ∈ S R, ∀ I ∈ C, I ≤ P := by
  by_cases C.Nonempty
  · refine ⟨sSup C, ?_, fun _ ↦ le_sSup⟩
    intro ⟨G, hG⟩
    have : ∃ I ∈ C, G.toSet ⊆ I := by
      refine hC₂.directedOn.exists_mem_subset_of_finset_subset_biUnion ‹_› (fun _ hx ↦ ?_)
      simp only [mem_iUnion, SetLike.mem_coe, exists_prop]
      exact (Submodule.mem_sSup_of_directed ‹_› hC₂.directedOn).1 <| hG ▸ subset_span hx
    obtain ⟨I, _, _⟩ := this
    have : sSup C = I := LE.le.antisymm (hG ▸ Ideal.span_le.2 ‹_›) (le_sSup ‹_›)
    exact hC ‹_› ⟨G, this ▸ hG⟩
  · rw [Set.not_nonempty_iff_eq_empty.1 ‹¬C.Nonempty›]
    obtain ⟨_, _⟩ := (Set.nonempty_def.1 <| nonempty_S ‹_›)
    exact ⟨_, ‹_›, by simp⟩

theorem exists_maximal_not_fg : ∃ (M : Ideal R), Maximal (S R) M :=
  zorn_le₀ (S R) (cohen_zorn_lemma h)

end zorn

lemma mem_span_range_self {α : Type*} {f : α → R} : ∀ {x}, f x ∈ span (Set.range f) :=
  (subset_span <| mem_range_self _)

theorem is_noetherian_of_prime_ideals_fg (h : ∀ (P : Ideal R), P.IsPrime → P.FG) :
    IsNoetherianRing R := by
  classical
  by_contra _
  obtain ⟨P, hP⟩ := exists_maximal_not_fg ‹_›
  have htop : P ≠ ⊤ := fun h ↦ (h ▸ hP.1) ⟨{1}, by simp⟩
  suffices Pprime : P.IsPrime
  · exact absurd (h _ Pprime) hP.1
  · by_contra _
    obtain ⟨a, ha, b, hb, h⟩ := (not_isPrime_iff.1 ‹_›).resolve_left htop
    have hPa : (span (P ∪ {a})).FG := hS hP <| lt_of_le_of_ne
      (fun _ hx ↦ subset_span (by simp [hx])) (fun H ↦ ha <| H ▸ subset_span (by simp))
    obtain ⟨m, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hPa
    rw [union_comm, span_union, span_eq] at hf
    have H : ∀ (i : Fin m), ∃ r : R, ∃ p ∈ P, r * a + p = f i := fun _ ↦
      (mem_span_singleton_sup.1 <| hf ▸ mem_span_range_self)
    choose! r p HiP Hf using H
    have hI : (P.colon (span {a})).FG := by
      refine hS hP <| lt_of_le_of_ne
        (fun _ hx ↦ mem_colon_singleton.2 <| P.mul_mem_right a hx)
        (fun H ↦ hb <| H ▸ mem_colon_singleton.2 (mul_comm a b ▸ h))
    obtain ⟨n, i, hi⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hI
    refine hP.1 ⟨Finset.image p univ ∪ Finset.image (a • i) univ, le_antisymm ?_ (fun x hx ↦ ?_)⟩
    <;> simp only [coe_union, coe_image, coe_univ, image_univ, Pi.smul_apply, span_union]
    · simp only [sup_le_iff, span_le, range_subset_iff, smul_eq_mul]
      exact ⟨HiP, fun c ↦ mul_comm a _ ▸ mem_colon_singleton.1 (hi ▸ mem_span_range_self)⟩
    · rw [Submodule.mem_sup]
      have : x ∈ span ({a} ∪ P) := subset_span <| Set.mem_union_right _ hx
      rw [span_union, span_eq, ← hf] at this
      obtain ⟨s, H⟩ := (mem_span_range_iff_exists_fun R).1 this
      simp_rw [← Hf, smul_eq_mul] at H
      ring_nf at H
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, add_comm] at H
      refine ⟨(∑ k, s k * p k), sum_mem _ (fun _ _ ↦ mul_mem_left _ _ mem_span_range_self),
        (∑ k, s k * r k) * a, ?_, H⟩
      rw [mul_comm, ← smul_eq_mul, Set.range_smul, ← submodule_span_eq, Submodule.span_smul, hi]
      refine Set.smul_mem_smul_set <| mem_colon_singleton.2 ?_
      rw [← eq_sub_iff_add_eq'] at H
      exact H ▸ sub_mem hx (sum_mem (fun _ _ ↦ mul_mem_left _ _ <| HiP _))
