import Mathlib

open Ideal

-- CommRing à cause de `mem_colon_singleton` mais est ce que ce thm à vraiment besoin de CommRing ?
variable {R : Type*} [CommRing R]

-- Question 1 : est-ce que ça devrait être une classe ?
-- Question 2 : (P : Ideal R → Prop) ou (P : Set (Ideal R)) ?
def IsOka (P : Ideal R → Prop) : Prop :=
  P ⊤ ∧ (∀ {a : R}, ∀ {I : Ideal R}, P (I ⊔ span {a}) → P (I.colon (span {a})) → P I)

-- TODO: lt_sup_iff_not_mem est déprécié au profit de lt_sup_iff_notMem depuis le 23/5/25
instance {I : Ideal R} {P : Ideal R → Prop} (hP : IsOka P) (hI : Maximal (¬P ·) I) : IsPrime I := by
  by_contra h
  have I_ne_top : I ≠ ⊤ := fun hI' ↦ hI.1 (hI' ▸ hP.1)
  obtain ⟨a, ha, b, hb, hab⟩ := (not_isPrime_iff.1 h).resolve_left I_ne_top
  have h₁ : P (I ⊔ span {a}) := of_not_not <| hI.not_prop_of_gt (Submodule.lt_sup_iff_not_mem.2 ha)
  have h₂ : P (I.colon (span {a})) :=
    of_not_not <| hI.not_prop_of_gt <| lt_of_le_of_ne
      (fun x hx ↦ mem_colon_singleton.2 <| I.mul_mem_right a hx)
      (fun H ↦ hb <| H ▸ mem_colon_singleton.2 (mul_comm a b ▸ hab))
  exact hI.1 (hP.2 h₁ h₂)
