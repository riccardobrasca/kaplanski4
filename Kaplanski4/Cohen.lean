import Mathlib
import Kaplanski4.Oka

open Ideal Set Finset

namespace AddedToMathlib --PR #28451

variable {R : Type*} [CommRing R]

theorem nonFG_maximal (H : ∃ I : Ideal R, ¬I.FG) : ∃ I : Ideal R, Maximal (¬FG ·) I := by
  obtain ⟨I, hI⟩ := H
  apply zorn_le₀
  intro C hC hC₂
  by_cases h : C.Nonempty
  · refine ⟨sSup C, ?_, fun _ ↦ le_sSup⟩
    intro ⟨G, hG⟩
    have : ∃ I ∈ C, G.toSet ⊆ I := by
      refine hC₂.directedOn.exists_mem_subset_of_finset_subset_biUnion h (fun _ hx ↦ ?_)
      simp only [mem_iUnion, SetLike.mem_coe, exists_prop]
      exact (Submodule.mem_sSup_of_directed h hC₂.directedOn).1 <| hG ▸ subset_span hx
    obtain ⟨I, I_mem_C, G_subset_I⟩ := this
    have : sSup C = I := LE.le.antisymm (hG ▸ Ideal.span_le.2 G_subset_I) (le_sSup I_mem_C)
    exact hC I_mem_C ⟨G, this ▸ hG⟩
  · rw [not_nonempty_iff_eq_empty.1 h]
    exact ⟨I, hI, by simp⟩

lemma mem_span_range_self {α : Type*} {f : α → R} : ∀ {x}, f x ∈ span (Set.range f) :=
  (subset_span <| mem_range_self _)

theorem isOka_FG : IsOka (FG (R := R)) := by
  classical
  constructor
  · exact ⟨{1}, by simp⟩
  · intro I a hsup hcolon
    obtain ⟨_, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hsup
    obtain ⟨_, i, hi⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hcolon
    rw [submodule_span_eq] at hf
    have H : ∀ k, ∃ r : R, ∃ p ∈ I, r * a + p = f k := by
      intro _
      apply mem_span_singleton_sup.1
      rw [sup_comm, ← hf]
      exact mem_span_range_self
    choose! r p p_mem_I Hf using H
    refine ⟨image p univ ∪ image (a • i) univ, le_antisymm ?_ (fun y hy ↦ ?_)⟩
    <;> simp only [coe_union, coe_image, coe_univ, image_univ, Pi.smul_apply, span_union]
    · simp only [sup_le_iff, span_le, range_subset_iff, smul_eq_mul]
      exact ⟨p_mem_I, fun c ↦ mul_comm a _ ▸ mem_colon_singleton.1 (hi ▸ mem_span_range_self)⟩
    · rw [Submodule.mem_sup]
      have : y ∈ span (range f) := hf ▸ Ideal.mem_sup_left hy
      obtain ⟨s, H⟩ := mem_span_range_iff_exists_fun.1 this
      simp_rw [← Hf] at H
      ring_nf at H
      rw [sum_add_distrib, ← sum_mul, add_comm] at H
      refine ⟨(∑ k, s k * p k), sum_mem _ (fun _ _ ↦ mul_mem_left _ _ mem_span_range_self),
        (∑ k, s k * r k) * a, ?_, H⟩
      rw [mul_comm, ← smul_eq_mul, range_smul, ← submodule_span_eq, Submodule.span_smul, hi]
      refine smul_mem_smul_set <| mem_colon_singleton.2 ?_
      exact (I.add_mem_iff_right <| sum_mem (fun _ _ ↦ mul_mem_left _ _ <| p_mem_I _)).1 (H ▸ hy)

theorem IsNoetherianRing.of_prime : (∀ I : Ideal R, I.IsPrime → I.FG) → IsNoetherianRing R :=
  (isNoetherianRing_iff_ideal_fg R).2 ∘ Ideal.forall_of_forall_prime_isOka isOka_FG nonFG_maximal

end AddedToMathlib
