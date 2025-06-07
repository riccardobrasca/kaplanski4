import Mathlib
import Kaplanski4.Oka

open Ideal

variable {R : Type*} [CommRing R]

theorem nonPrincipal_maximal :
    (∃ I : Ideal R, ¬I.IsPrincipal) → ∃ I : Ideal R, Maximal (¬·.IsPrincipal) I := by
  intro ⟨I, hI⟩
  obtain ⟨m, _, hm⟩ := zorn_le_nonempty₀ _ nonPrincipals_zorn I hI
  exact ⟨m, hm⟩

theorem isOka_isPrincipal : IsOka (Submodule.IsPrincipal (R := R)) := by
  constructor
  · exact ⟨1, by simp⟩
  · intro a I ⟨x, hx⟩ ⟨y, hy⟩
    use x * y
    rw [submodule_span_eq] at *
    apply le_antisymm
    · intro i hi
      have hisup : i ∈ I ⊔ span {a} := mem_sup_left hi
      have hasup : a ∈ I ⊔ span {a} := mem_sup_right (mem_span_singleton_self a)
      rw [hx, mem_span_singleton'] at hisup hasup
      obtain ⟨u, rfl⟩ := hisup
      obtain ⟨v, rfl⟩ := hasup
      have hucolon : u ∈ I.colon (span {v * x}) := by
        rw [mem_colon_singleton, mul_comm v, ← mul_assoc]
        exact mul_mem_right _ _ hi
      rw [hy, mem_span_singleton'] at hucolon
      obtain ⟨z, rfl⟩ := hucolon
      exact mem_span_singleton'.2 ⟨z, by ring⟩
    · rw [← span_singleton_mul_span_singleton, ← hx, Ideal.sup_mul, sup_le_iff,
        span_singleton_mul_span_singleton, mul_comm a, span_singleton_le_iff_mem]
      exact ⟨mul_le_right, mem_colon_singleton.1 <| hy ▸ mem_span_singleton_self y⟩

#check IsPrincipalIdealRing.of_prime

theorem IsPrincipalIdealRing.of_prime' (H : ∀ (P : Ideal R), P.IsPrime → Submodule.IsPrincipal P) :
    IsPrincipalIdealRing R :=
  (isPrincipalIdealRing_iff R).2 <| isOka_isPrincipal.forall_of_forall_prime nonPrincipal_maximal H
