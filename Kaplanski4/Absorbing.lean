import Mathlib.GroupTheory.Submonoid.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.GroupTheory.Submonoid.Membership
import Mathlib.Algebra.Associated
import Mathlib.RingTheory.Prime

namespace Submonoid

variable {M N : Type _} [CommMonoid M] [CommMonoid N]

def Absorbing (S : Submonoid M) : Prop :=
  ∀ x y, x * y ∈ S → ∃ z ∈ S, Associated x z ∧ ∃ z ∈ S, Associated y z

section Basic

theorem absorbing_def {S : Submonoid M} :
    Absorbing S ↔ ∀ x y, x * y ∈ S → ∃ z ∈ S, Associated x z ∧ ∃ z ∈ S, Associated y z :=
  Iff.rfl

variable (M)

variable (N)

theorem top_absorbing : (⊤ : Submonoid M).Absorbing := fun x y _ =>
  ⟨x, Submonoid.mem_top _, Associated.refl _, y, Submonoid.mem_top _, Associated.refl _⟩

theorem bot_absorbing : (⊥ : Submonoid M).Absorbing := fun x y hxy =>
  ⟨1, (⊥ : Submonoid M).one_mem, associated_one_of_mul_eq_one _ (Submonoid.mem_bot.1 hxy), 1,
    (⊥ : Submonoid M).one_mem,
    associated_one_of_mul_eq_one _ (Submonoid.mem_bot.1 (by rwa [mul_comm] at hxy))⟩

theorem IsUnit.submonoid_absorbing : (IsUnit.submonoid M).Absorbing := fun x y hxy =>
  ⟨x, isUnit_of_mul_isUnit_left hxy, Associated.refl _, y, isUnit_of_mul_isUnit_right hxy,
    Associated.refl _⟩

theorem Associated.prod (x z : M × N) : Associated x z ↔ Associated x.1 z.1 ∧ Associated x.2 z.2 :=
  by
  refine'
    ⟨_, fun ⟨⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩⟩ =>
      ⟨MulEquiv.prodUnits.invFun (u₁, u₂), Prod.eq_iff_fst_eq_snd_eq.2 ⟨hu₁, hu₂⟩⟩⟩
  rintro ⟨u, hu⟩
  cases' u.isUnit.exists_right_inv with b hb
  rw [Prod.mul_def, Prod.mk_eq_one] at hb
  rw [← hu, Prod.fst_mul, Prod.snd_mul]
  refine'
    ⟨(associated_mul_isUnit_right_iff (isUnit_of_mul_eq_one _ _ hb.1)).2 (Associated.refl _),
      (associated_mul_isUnit_right_iff (isUnit_of_mul_eq_one _ _ hb.2)).2 (Associated.refl _)⟩

theorem Submonoid.prod_absorbing (s : Submonoid M) (t : Submonoid N) :
    (s.prod t).Absorbing ↔ Absorbing s ∧ Absorbing t :=
  by
  refine' ⟨fun h => ⟨fun x y hxy => _, fun x y hxy => _⟩, _⟩
  · specialize h (x, 1) (y, 1)
    rw [Prod.mk_one_mul_mk_one] at h
    rcases h (Submonoid.mem_prod.2 ⟨hxy, t.one_mem⟩) with ⟨a, ha, ha₂, ⟨b, hb, hb₂⟩⟩
    exact
      ⟨a.1, (Submonoid.mem_prod.1 ha).1, ((Associated.prod _ _ _ _).1 ha₂).1, b.1,
        (Submonoid.mem_prod.1 hb).1, ((Associated.prod _ _ _ _).1 hb₂).1⟩
  · specialize h (1, x) (1, y)
    rw [Prod.one_mk_mul_one_mk] at h
    rcases h (Submonoid.mem_prod.2 ⟨s.one_mem, hxy⟩) with ⟨a, ha, ha₂, ⟨b, hb, hb₂⟩⟩
    exact
      ⟨a.2, (Submonoid.mem_prod.1 ha).2, ((Associated.prod _ _ _ _).1 ha₂).2, b.2,
        (Submonoid.mem_prod.1 hb).2, ((Associated.prod _ _ _ _).1 hb₂).2⟩
  · rintro ⟨hs, ht⟩ x y hxy
    rcases hs x.1 y.1 hxy.1 with ⟨z, hz, hz₂, ⟨z', hz', hz'₂⟩⟩
    rcases ht x.2 y.2 hxy.2 with ⟨w, hw, hw₂, ⟨w', hw', hw'₂⟩⟩
    exact
      ⟨(z, w), Submonoid.mem_prod.2 ⟨hz, hw⟩, (Associated.prod _ _ _ _).2 ⟨hz₂, hw₂⟩, (z', w'),
        Submonoid.mem_prod.2 ⟨hz', hw'⟩, (Associated.prod _ _ _ _).2 ⟨hz'₂, hw'₂⟩⟩

theorem Submonoid.powers_prime_absorbing {R : Type _} [CommRing R] [IsDomain R] (p : R) (hn : Prime p) : (Submonoid.powers p).Absorbing :=
  by
  rintro x y hxy
  cases' ((Submonoid.mem_powers_iff _ _).1 hxy) with m hm
  
  let a := (1 : R)
  have ha : a=1 := rfl
  rw [← one_mul (p^m), ← ha] at hm
  have hxy₂ := mul_eq_mul_prime_pow hn (Eq.symm hm)
  rw [ha] at hxy₂
  rcases hxy₂ with ⟨i, j, b, c, ⟨hij, hbc, hx, hy⟩⟩ 

  refine' ⟨p^i, (Submonoid.mem_powers_iff _ _).2 ⟨i, rfl⟩, (associated_isUnit_mul_right_iff (isUnit_of_mul_eq_one _ _ (Eq.symm hbc))).1 _, p^j, (Submonoid.mem_powers_iff _ _).2 ⟨j, rfl⟩, _⟩
  rw [← hx]
  exact Associated.refl x

  rw [mul_comm] at hbc
  refine' (associated_isUnit_mul_right_iff (isUnit_of_mul_eq_one _ _ (Eq.symm hbc))).1 _
  rw [← hy]
  exact Associated.refl y

end Basic

section CommMonoid

theorem absorbing_iff_of_comm {S : Submonoid M} :
    Absorbing S ↔ ∀ x y, x * y ∈ S → ∃ z ∈ S, Associated x z :=
  by
  refine' ⟨fun hS x y hxy => _, fun h x y hxy => _⟩
  · rcases hS x y hxy with ⟨z, hz, hz₂, _⟩
    exact ⟨z, hz, hz₂⟩
  · obtain ⟨z, hz, hz₂⟩ := h x y hxy
    refine' ⟨z, hz, hz₂, _⟩
    rw [mul_comm] at hxy
    exact h y x hxy


end CommMonoid

end Submonoid
