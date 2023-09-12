import Mathlib.GroupTheory.Submonoid.Membership
import Mathlib.RingTheory.Prime

variable {M N : Type _}

namespace Subsemigroup

/-- We define a property for subsemigroups. We then give examples of subsemigroups
(in the namespace Subsemigroup) and more precisely, of submonoids (in the namespace Submonoid)
which satisfy this property. -/
def ProdProperty [Monoid M] (S : Subsemigroup M) : Prop :=
  ∀ x y, x * y ∈ S → (∃ z ∈ S, Associated x z) ∧ ∃ z ∈ S, Associated y z

section Basic

theorem prodProperty_def [Monoid M] {S : Subsemigroup M} :
    S.ProdProperty ↔ ∀ x y, x * y ∈ S → (∃ z ∈ S, Associated x z) ∧ ∃ z ∈ S, Associated y z :=
  Iff.rfl

theorem top_prodProperty [Monoid M] : (⊤ : Subsemigroup M).ProdProperty :=
  fun x y _ =>
  ⟨⟨x, Subsemigroup.mem_top _, Associated.refl _⟩, y, Subsemigroup.mem_top _, Associated.refl _⟩

/-- The proof of `prod_prodProperty_iff` uses several results. The first one is below. -/
theorem prod_associated_iff [Monoid M] [Monoid N] (x z : M × N) :
    Associated x z ↔ Associated x.1 z.1 ∧ Associated x.2 z.2 := by
  refine' ⟨fun h => ⟨_, _⟩,
  fun ⟨⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩⟩ =>
  ⟨MulEquiv.prodUnits.invFun (u₁, u₂), Prod.eq_iff_fst_eq_snd_eq.2 ⟨hu₁, hu₂⟩⟩⟩
  · cases' h with u hu
    exact ⟨(MulEquiv.prodUnits.toFun u).1, (Prod.eq_iff_fst_eq_snd_eq.1 hu).1⟩
  · cases' h with u hu
    exact ⟨(MulEquiv.prodUnits.toFun u).2, (Prod.eq_iff_fst_eq_snd_eq.1 hu).2⟩

theorem fst_prodProperty [Monoid M] [Monoid N] (s : Submonoid M) (t : Submonoid N) :
    (s.prod t).ProdProperty → s.ProdProperty := by
  rintro h x y hxy
  specialize h (x, 1) (y, 1)
  rw [Prod.mk_one_mul_mk_one] at h
  rcases h (Submonoid.mem_prod.2 ⟨hxy, t.one_mem⟩) with ⟨⟨a, ha, ha₂⟩, b, hb, hb₂⟩
  exact ⟨⟨a.1, (Submonoid.mem_prod.1 ha).1, ((prod_associated_iff _ _).1 ha₂).1⟩, b.1,
    (Submonoid.mem_prod.1 hb).1, ((prod_associated_iff _ _).1 hb₂).1⟩

theorem snd_prodProperty [Monoid M] [Monoid N] (s : Submonoid M) (t : Submonoid N) :
    (s.prod t).ProdProperty → t.ProdProperty := by
  rintro h x y hxy
  specialize h (1, x) (1, y)
  rw [Prod.one_mk_mul_one_mk] at h
  rcases h (Submonoid.mem_prod.2 ⟨s.one_mem, hxy⟩) with ⟨⟨a, ha, ha₂⟩, b, hb, hb₂⟩
  exact ⟨⟨a.2, (Submonoid.mem_prod.1 ha).2, ((prod_associated_iff _ _).1 ha₂).2⟩, b.2,
    (Submonoid.mem_prod.1 hb).2, ((prod_associated_iff _ _).1 hb₂).2⟩

theorem prodProperty_of_prod [Monoid M] [Monoid N] (s : Submonoid M) (t : Submonoid N) :
    (s.prod t).ProdProperty → s.ProdProperty ∧ t.ProdProperty := fun h =>
  ⟨fst_prodProperty s t h, snd_prodProperty s t h⟩

theorem prod_of_prodProperty [Monoid M] [Monoid N] (s : Submonoid M) (t : Submonoid N) :
    s.ProdProperty ∧ t.ProdProperty → (s.prod t).ProdProperty := by
  rintro ⟨hs, ht⟩ x y hxy
  rcases hs x.1 y.1 hxy.1 with ⟨⟨z, hz, hz₂⟩, z', hz', hz'₂⟩
  rcases ht x.2 y.2 hxy.2 with ⟨⟨w, hw, hw₂⟩, w', hw', hw'₂⟩
  exact ⟨⟨(z, w), Submonoid.mem_prod.2 ⟨hz, hw⟩, (prod_associated_iff _ _).2 ⟨hz₂, hw₂⟩⟩, (z', w'),
    Submonoid.mem_prod.2 ⟨hz', hw'⟩, (prod_associated_iff _ _).2 ⟨hz'₂, hw'₂⟩⟩

/-- Given two subsemigroups `s` and `t` of semigroups `M`, `N` respectively,
`s × t` satisfies the property if and only if `s` and `t` both satisfy it. -/
theorem prod_prodProperty_iff [Monoid M] [Monoid N] (s : Submonoid M) (t : Submonoid N) :
    (s.prod t).ProdProperty ↔ s.ProdProperty ∧ t.ProdProperty :=
  ⟨prodProperty_of_prod s t, prod_of_prodProperty s t⟩

theorem submonoid.powers_absorbing {R : Type _} [CommRing R] [IsDomain R] (p : R) (hp : Prime p) :
    (Submonoid.powers p).ProdProperty := by
  rintro x y hxy
  cases' ((Submonoid.mem_powers_iff _ _).1 hxy) with m hm
  rw [← one_mul (p^m)] at hm
  rcases (mul_eq_mul_prime_pow hp hm.symm) with ⟨i, j, _, _, ⟨_, hbc, hx, hy⟩⟩
  rw [hx, hy]
  refine' ⟨⟨p^i, (Submonoid.mem_powers_iff _ _).2 ⟨i, rfl⟩,
    (associated_isUnit_mul_left_iff (isUnit_of_mul_eq_one _ _ hbc.symm)).2 (Associated.refl (p^i))⟩,
      p^j, (Submonoid.mem_powers_iff _ _).2 ⟨j, rfl⟩, _⟩
  rw [mul_comm] at hbc
  exact (associated_isUnit_mul_left_iff (isUnit_of_mul_eq_one _ _ hbc.symm)).2
    (Associated.refl (p^j))

end Basic

section CommMonoid

theorem prodProperty_iff_of_comm [CommMonoid M] {S : Subsemigroup M} :
    S.ProdProperty ↔ ∀ x y, x * y ∈ S → ∃ z ∈ S, Associated x z :=
  ⟨fun hS x y hxy => (hS x y hxy).1, fun h x y hxy => ⟨h x y hxy, h y x (by rwa [mul_comm] at hxy)⟩⟩

end CommMonoid

end Subsemigroup

namespace Submonoid

section Basic

theorem bot_prodProperty [CommMonoid M] : (⊥ : Submonoid M).ProdProperty :=
  fun _ _ hxy =>
  ⟨⟨_, (⊥ : Submonoid M).one_mem, associated_one_of_mul_eq_one _ hxy⟩, _, (⊥ : Submonoid M).one_mem,
  associated_one_of_mul_eq_one _ (by rwa [mul_comm] at hxy)⟩

/-- The submonoid consisting of the units of a monoid satisfies the property. -/
theorem IsUnit.submonoid_prodProperty [CommMonoid M] : (IsUnit.submonoid M).ProdProperty :=
  fun _ _ hxy =>
  ⟨⟨_, isUnit_of_mul_isUnit_left hxy, Associated.refl _⟩, _, isUnit_of_mul_isUnit_right hxy,
  Associated.refl _⟩

end Basic

end Submonoid
