import Mathlib

open Ideal

variable {R : Type*} [CommSemiring R]

section base

-- Question 1 : est-ce que ça devrait être une classe ?
-- Question 2 : (P : Ideal R → Prop) ou (P : Set (Ideal R)) ?
def IsOka (P : Ideal R → Prop) : Prop :=
  P ⊤ ∧ (∀ {a : R} {I : Ideal R}, P (I ⊔ span {a}) → P (I.colon (span {a})) → P I)

instance instIsPrimeOfIsOkaOfMaximalNot {P : Ideal R → Prop} (hP : IsOka P) {I : Ideal R}
    (hI : Maximal (¬P ·) I) : I.IsPrime := by
  by_contra h
  have I_ne_top : I ≠ ⊤ := fun hI' ↦ hI.1 (hI' ▸ hP.1)
  obtain ⟨a, ha, b, hb, hab⟩ := (not_isPrime_iff.1 h).resolve_left I_ne_top
  have h₁ : P (I ⊔ span {a}) := of_not_not <| hI.not_prop_of_gt (Submodule.lt_sup_iff_notMem.2 ha)
  have h₂ : P (I.colon (span {a})) :=
    of_not_not <| hI.not_prop_of_gt <| lt_of_le_of_ne
      (fun x hx ↦ mem_colon_singleton.2 <| I.mul_mem_right a hx)
      (fun H ↦ hb <| H ▸ mem_colon_singleton.2 (mul_comm a b ▸ hab))
  exact hI.1 (hP.2 h₁ h₂)

theorem IsOka.forall_of_forall_prime {P : Ideal R → Prop} (hP : IsOka P)
    (hmax : (∃ I, ¬P I) → ∃ I, Maximal (¬P ·) I) : (∀ I, I.IsPrime → P I) → ∀ I, P I := by
  intro h
  by_contra!
  obtain ⟨I, hI⟩ := hmax this
  exact hI.1 <| h I (instIsPrimeOfIsOkaOfMaximalNot hP hI)

end base

section application
-- TODO: Une fois fini, il faudra déplacer les résultats de cette section dans les bons fichiers

theorem isOka_inter_subSemigroup_ne_empty {S : Subsemigroup R} (hS : (S : Set R).Nonempty) :
    IsOka (fun I : Ideal R ↦ (I : Set R) ∩ S ≠ ∅) := by
  constructor
  · simp [hS.ne_empty]
  · intro a I hsup hcolon
    rw [← Set.nonempty_iff_ne_empty] at hsup hcolon ⊢
    obtain ⟨x, hxI, hxS⟩ := hsup
    obtain ⟨y, hyI, hyS⟩ := hcolon
    use x * y
    constructor
    · simp only [SetLike.mem_coe, mem_colon_singleton] at hxI hyI ⊢
      rw [sup_comm, mem_span_singleton_sup] at hxI
      obtain ⟨r, i, hi, rfl⟩ := hxI
      ring_nf
      exact I.add_mem
        (by rw [mul_assoc, mul_comm a]; exact I.mul_mem_left _ hyI)
        (I.mul_mem_right _ hi)
    · exact S.mul_mem hxS hyS

end application
