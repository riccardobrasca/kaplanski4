import Mathlib.GroupTheory.Submonoid.Membership
import Mathlib.RingTheory.Prime

namespace Submonoid

variable {M N : Type _} [CommMonoid M] [CommMonoid N]

def Absorbing (S : Submonoid M) : Prop :=
  ∀ x y, x * y ∈ S → ∃ z ∈ S, Associated x z ∧ ∃ z ∈ S, Associated y z

section Basic

theorem absorbing_def {S : Submonoid M} :
    Absorbing S ↔ ∀ x y, x * y ∈ S → ∃ z ∈ S, Associated x z ∧ ∃ z ∈ S, Associated y z :=
  Iff.rfl

variable (M) (N)

theorem top_absorbing : (⊤ : Submonoid M).Absorbing := fun x y _ =>
  ⟨x, Submonoid.mem_top _, Associated.refl _, y, Submonoid.mem_top _, Associated.refl _⟩

theorem bot_absorbing : (⊥ : Submonoid M).Absorbing := fun _ _ hxy =>
  ⟨1, (⊥ : Submonoid M).one_mem, associated_one_of_mul_eq_one _ hxy, 1,
    (⊥ : Submonoid M).one_mem,
    associated_one_of_mul_eq_one _ (by rwa [mul_comm] at hxy)⟩

theorem IsUnit.submonoid_absorbing : (IsUnit.submonoid M).Absorbing := fun x y hxy =>
  ⟨x, isUnit_of_mul_isUnit_left hxy, Associated.refl _, y, isUnit_of_mul_isUnit_right hxy,
    Associated.refl _⟩

theorem Associated.prod (x z : M × N) : Associated x z ↔ Associated x.1 z.1 ∧ Associated x.2 z.2 :=
  by
  refine'
    ⟨fun ⟨u, hu⟩ => _, fun ⟨⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩⟩ =>
      ⟨MulEquiv.prodUnits.invFun (u₁, u₂), Prod.eq_iff_fst_eq_snd_eq.2 ⟨hu₁, hu₂⟩⟩⟩
  cases' u.isUnit.exists_right_inv with b hb
  rw [Prod.mk_eq_one] at hb
  rw [← hu]
  exact
    ⟨(associated_mul_isUnit_right_iff (isUnit_of_mul_eq_one _ _ hb.1)).2 (Associated.refl _),
      (associated_mul_isUnit_right_iff (isUnit_of_mul_eq_one _ _ hb.2)).2 (Associated.refl _)⟩

theorem Submonoid.prod_absorbing_right_s (s : Submonoid M) (t : Submonoid N) :
    (s.prod t).Absorbing → Absorbing s := by
  rintro h x y hxy
  specialize h (x, 1) (y, 1)
  rw [Prod.mk_one_mul_mk_one] at h
  rcases h (Submonoid.mem_prod.2 ⟨hxy, t.one_mem⟩) with ⟨a, ha, ha₂, ⟨b, hb, hb₂⟩⟩
  exact
    ⟨a.1, (Submonoid.mem_prod.1 ha).1, ((Associated.prod _ _ _ _).1 ha₂).1, b.1,
      (Submonoid.mem_prod.1 hb).1, ((Associated.prod _ _ _ _).1 hb₂).1⟩

theorem Submonoid.prod_absorbing_right_t (s : Submonoid M) (t : Submonoid N) :
    (s.prod t).Absorbing → Absorbing t := by
  rintro h x y hxy
  specialize h (1, x) (1, y)
  rw [Prod.one_mk_mul_one_mk] at h
  rcases h (Submonoid.mem_prod.2 ⟨s.one_mem, hxy⟩) with ⟨a, ha, ha₂, ⟨b, hb, hb₂⟩⟩
  exact
    ⟨a.2, (Submonoid.mem_prod.1 ha).2, ((Associated.prod _ _ _ _).1 ha₂).2, b.2,
      (Submonoid.mem_prod.1 hb).2, ((Associated.prod _ _ _ _).1 hb₂).2⟩

theorem Submonoid.prod_absorbing_right (s : Submonoid M) (t : Submonoid N) :
    (s.prod t).Absorbing → Absorbing s ∧ Absorbing t := fun h => ⟨Submonoid.prod_absorbing_right_s _ _ s t h, Submonoid.prod_absorbing_right_t _ _ s t h⟩

theorem Submonoid.prod_absorbing_left (s : Submonoid M) (t : Submonoid N) :
    Absorbing s ∧ Absorbing t → (s.prod t).Absorbing := by
  rintro ⟨hs, ht⟩ x y hxy
  rcases hs x.1 y.1 hxy.1 with ⟨z, hz, hz₂, ⟨z', hz', hz'₂⟩⟩
  rcases ht x.2 y.2 hxy.2 with ⟨w, hw, hw₂, ⟨w', hw', hw'₂⟩⟩
  exact
    ⟨(z, w), Submonoid.mem_prod.2 ⟨hz, hw⟩, (Associated.prod _ _ _ _).2 ⟨hz₂, hw₂⟩, (z', w'),
      Submonoid.mem_prod.2 ⟨hz', hw'⟩, (Associated.prod _ _ _ _).2 ⟨hz'₂, hw'₂⟩⟩

theorem Submonoid.prod_absorbing (s : Submonoid M) (t : Submonoid N) :
    (s.prod t).Absorbing ↔ Absorbing s ∧ Absorbing t := ⟨Submonoid.prod_absorbing_right _ _ s t, Submonoid.prod_absorbing_left _ _ s t⟩

theorem Submonoid.powers_prime_absorbing {R : Type _} [CommRing R] [IsDomain R] (p : R) (hn : Prime p) : (Submonoid.powers p).Absorbing :=
  by
  rintro x y hxy
  cases' ((Submonoid.mem_powers_iff _ _).1 hxy) with m hm
  rw [← one_mul (p^m)] at hm
  rcases (mul_eq_mul_prime_pow hn hm.symm) with ⟨i, j, _, _, ⟨_, hbc, hx, hy⟩⟩
  rw [hx, hy]
  refine' ⟨p^i, (Submonoid.mem_powers_iff _ _).2 ⟨i, rfl⟩, (associated_isUnit_mul_left_iff (isUnit_of_mul_eq_one _ _ hbc.symm)).2 (Associated.refl (p^i)), p^j, (Submonoid.mem_powers_iff _ _).2 ⟨j, rfl⟩, _⟩
  rw [mul_comm] at hbc
  exact (associated_isUnit_mul_left_iff (isUnit_of_mul_eq_one _ _ hbc.symm)).2 (Associated.refl (p^j))

end Basic

section CommMonoid

theorem absorbing_iff_of_comm {S : Submonoid M} :
    Absorbing S ↔ ∀ x y, x * y ∈ S → ∃ z ∈ S, Associated x z :=
  by
  refine' ⟨fun hS x y hxy => _, fun h x y hxy => _⟩
  · rcases hS x y hxy with ⟨z, hz, hz₂, _⟩
    exact ⟨z, hz, hz₂⟩
  · obtain ⟨z, hz, hz₂⟩ := h x y hxy
    rw [mul_comm] at hxy
    exact ⟨z, hz, hz₂, h y x hxy⟩

end CommMonoid

end Submonoid
