import Mathlib

open PowerSeries Ideal Set BigOperators Finset

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
      refine hC₂.directedOn.exists_mem_subset_of_finset_subset_biUnion ‹_› (fun x hx ↦ ?_)
      obtain ⟨I, _, _⟩ := (Submodule.mem_sSup_of_directed ‹_› hC₂.directedOn).1 <|
        hG ▸ subset_span ‹_›
      exact Set.mem_biUnion ‹_› ‹_›
    obtain ⟨I, I_mem_C, hGI⟩ := this
    have := hG ▸ Ideal.span_le.2 ‹_›
    have : sSup C = I := LE.le.antisymm (hG ▸ Ideal.span_le.2 ‹_›) (le_sSup ‹_›)
    refine hC I_mem_C ⟨G, this ▸ ‹_›⟩
  · rw [Set.not_nonempty_iff_eq_empty.1 ‹¬C.Nonempty›]
    obtain ⟨_, _⟩ := (Set.nonempty_def.1 <| nonempty_S ‹_›)
    exact ⟨_, ‹_›, by simp⟩


theorem exists_maximal_not_fg : ∃ (M : Ideal R), Maximal (· ∈ S R) M :=
  zorn_le₀ (S R) (cohen_zorn_lemma h)


end zorn

-- Le théorème est censé être dans mathlib mais je ne l'ai pas trouvé.
theorem is_noetherian_of_prime_ideals_fg
  (h : ∀ (P : Ideal R), P.IsPrime → P.FG) : IsNoetherianRing R := by
  classical
  by_contra _
  obtain ⟨P, hP⟩ := exists_maximal_not_fg ‹_›
  have htop : P ≠ ⊤ := fun h ↦ (h ▸ hP.1) ⟨{1}, by simp⟩
  suffices Pprime : P.IsPrime
  · exact absurd (h _ Pprime) (maximal_mem_iff.1 hP).1
  · by_contra M_not_prime
    obtain ⟨a, ha, b, hb, h⟩ := (not_isPrime_iff.1 M_not_prime).resolve_left htop
    have hPa : (span (P ∪ {a})).FG := hS hP <| lt_iff_le_and_ne.2
      ⟨fun _ hx ↦ subset_span (by simp [hx]), fun H ↦ ha <| H ▸ subset_span (by simp)⟩
    have hI : (P.colon (span {a})).FG := by
      refine hS hP <| lt_iff_le_and_ne.2 ⟨fun x hx ↦ mem_colon_singleton.2 <|
        mul_mem_right a P hx, fun H ↦ hb <| ?_⟩
      exact H ▸ Submodule.mem_colon_singleton.2 (by simp only [smul_eq_mul, mul_comm, h])
    rw [span_union] at hPa
    obtain ⟨m, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hPa
    rw [span_eq] at hf
    obtain ⟨n, i, hi⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hI
    have H : ∀ (i : Fin m), ∃ r : R, ∃ p ∈ P, r * a + p = f i := fun i ↦ by
      rw [← mem_span_singleton_sup, sup_comm, ← hf]
      exact subset_span (by simp)
    choose! r p HiP Hf using H
    refine hP.1 ⟨Finset.image p univ ∪ Finset.image (a • i) univ, le_antisymm ?_ (fun x hx ↦ ?_)⟩
    · simp only [coe_union, coe_image, coe_univ, image_univ, Pi.smul_apply, smul_eq_mul,
        span_union, sup_le_iff]
      refine ⟨span_le.2 <| fun b ⟨c, hbc⟩ ↦ hbc ▸ (HiP c), span_le.2 <| fun b ⟨c, hbc⟩ ↦ ?_⟩
      simp only [← hbc, SetLike.mem_coe]
      rw [mul_comm, ← smul_eq_mul]
      exact (Submodule.mem_colon (P := span {a})).1 (hi ▸ subset_span (by simp)) _
        (subset_span (by simp))
    · simp only [coe_union, coe_image, coe_univ, image_univ, Pi.smul_apply]
      rw [span_union, Submodule.mem_sup]
      have : x ∈ span (P ∪ {a}) := subset_span <| Set.mem_union_left _ hx
      rw [span_union, span_eq, ← hf] at this
      obtain ⟨s, hs⟩ := (mem_span_range_iff_exists_fun R).1 this
      have H : ∑ k, s k * p k + ∑ k, a * s k * r k = x := by
        rw [← hs, ← Finset.sum_add_distrib]
        congr
        ext
        rw [← Hf, smul_eq_mul]
        ring
      refine ⟨∑ k, (s k * p k), sum_mem _ (fun _ _ ↦ mul_mem_left _ _ <| subset_span (by simp)),
        ∑ k, (a * s k * r k), ?_, H⟩
      · simp_rw [mul_assoc, ← Finset.mul_sum, ← smul_eq_mul a, Set.range_smul, ← submodule_span_eq,
          Submodule.span_smul, hi]
        refine Set.smul_mem_smul_set <| Submodule.mem_colon_singleton.2 ?_
        simp_rw [mul_assoc a, mul_comm a, ← Finset.sum_mul, ← eq_sub_iff_add_eq'] at H
        rw [smul_eq_mul, H]
        exact sub_mem hx (sum_mem (fun k _ ↦ mul_mem_left _ _ <| HiP _))
