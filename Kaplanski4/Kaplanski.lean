import Mathlib.RingTheory.PrincipalIdealDomain
import Kaplanski4.Absorbing

variable {R : Type _}

/-- The set of ideals of the ring R which do not intersect the submonoid S -/
def Kaplansky.set [Semiring R] (S : Submonoid R) :=
  { I : Ideal R | (I : Set R) ∩ S = ∅ }

theorem Kaplansky.set_def [Semiring R] (S : Submonoid R) {P : Ideal R} :
    P ∈ Kaplansky.set S ↔ (P : Set R) ∩ S = ∅ := Iff.rfl

section Existence

/-- The proof of 'exists_maximal_ideal' uses Zorn's lemma so the following theorem checks that
every chain of 'Kaplansky.set S' has an upper bound. -/
theorem hypothesis_zorn_lemma [Semiring R] {S : Submonoid R} (C : Set (Ideal R))
    (hC : C ⊆ Kaplansky.set S) (hC₂ : IsChain (· ≤ ·) C) {I : Ideal R} (hI : I ∈ C) :
    ∃ P, P ∈ Kaplansky.set S ∧ ∀ J, J ∈ C → J ≤ P := by
  refine' ⟨supₛ C, _, fun z hz => le_supₛ hz⟩
  rw [Kaplansky.set_def, Set.eq_empty_iff_forall_not_mem]
  rintro x hx
  rcases (Submodule.mem_supₛ_of_directed ⟨_, hI⟩ hC₂.directedOn).1 hx.1 with ⟨J, hJ₁, hJ₂⟩
  have hx₂ : (J : Set R) ∩ S ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨x, hJ₂, hx.2⟩
  exact hx₂ (hC hJ₁)

/-- The existence of a maximal element of 'Kaplansky.set S'
(which we will use to prove Kaplansky's criterion). -/
theorem exists_maximal_ideal (hS : 0 ∉ S) :
    ∃ P ∈ Kaplansky.set S, ∀ I ∈ Kaplansky.set S, P ≤ I → I = P := by
  have hx : 0 ∈ Kaplansky.set S := by
    rw [Kaplansky.set_def, Set.eq_empty_iff_forall_not_mem]
    rintro y ⟨hy₁, hy₂⟩
    rw [SetLike.mem_coe, Ideal.zero_eq_bot, Ideal.mem_bot] at hy₁
    rw [hy₁] at hy₂
    exact hS hy₂
  rcases zorn_nonempty_partialOrder₀ _ hypothesis_zorn_lemma _ hx with ⟨J, hJ, _, hJ₃⟩
  exact ⟨J, hJ, hJ₃⟩

end Existence

section Basic

/-- If an ideal P satisfies the condition P ∩ S = ∅, then P ≠ R
(this is used to prove that P is prime). -/
theorem ideal_neq_top [Semiring R] {S : Submonoid R} {P : Ideal R}
    (hP : P ∈ Kaplansky.set S) : P ≠ ⊤ :=
  fun h => ((Set.disjoint_left.1 (Set.disjoint_iff_inter_eq_empty.2 ((Kaplansky.set_def _).1 hP)))
    (P.eq_top_iff_one.1 h)) S.one_mem

theorem exists_mem_inter [Semiring R] {S : Submonoid R} {P : Ideal R} {I : Ideal R}
    (hmax : ∀ I ∈ Kaplansky.set S, P ≤ I → I = P) (h : P < I) : ∃ x : R, x ∈ (I : Set R) ∩ S :=
  Set.inter_nonempty.1
    (Set.nonempty_iff_ne_empty.2 fun h₂ =>
      (lt_iff_le_and_ne.1 h).2 ((hmax I) h₂ (lt_iff_le_and_ne.1 h).1).symm)

-- Semiring?
/-- This is checked to prove that an ideal P which is maximal with respect to
the condition P ∩ S = ∅ is also prime. -/
theorem mem_or_mem_of_mul_mem [CommSemiring R] {P : Ideal R} {S : Submonoid R} (x y : R)
    (hP : P ∈ Kaplansky.set S) (hmax : ∀ I ∈ Kaplansky.set S, P ≤ I → I = P) :
    x * y ∈ P → x ∈ P ∨ y ∈ P := by
  intro hxy
  by_contra h
  push_neg  at h
  cases' h with h' h''
  let I := P ⊔ Ideal.span {x}
  let J := P ⊔ Ideal.span {y}
  have h₁ : ∃ x : R, x ∈ (I : Set R) ∩ S := by
    refine' exists_mem_inter hmax (lt_of_le_of_ne' le_sup_left _)
    intro hI
    rw [← hI, ← I.span_singleton_le_iff_mem] at h'
    exact h' le_sup_right
  have h₂ : ∃ x : R, x ∈ (J : Set R) ∩ S := by
    refine' exists_mem_inter hmax (lt_of_le_of_ne' le_sup_left _)
    intro hJ
    rw [← hJ, ← J.span_singleton_le_iff_mem] at h''
    exact h'' le_sup_right
  rcases h₁, h₂ with ⟨⟨s, ⟨hs, hs'⟩⟩, ⟨t, ⟨ht, ht'⟩⟩⟩
  have h₃ : I * J ≤ P := by
    rw [Ideal.mul_sup, Ideal.sup_mul, Ideal.sup_mul, Ideal.span_singleton_mul_span_singleton]
    exact
      sup_le (sup_le Ideal.mul_le_right Ideal.mul_le_left)
        (sup_le Ideal.mul_le_right (P.span_singleton_le_iff_mem.2 hxy))
  exact
    Set.eq_empty_iff_forall_not_mem.1 hP (s * t) ⟨h₃ (Ideal.mul_mem_mul hs ht), S.mul_mem hs' ht'⟩

-- Semiring?
/-- If an ideal P is maximal with respect to the condition P ∩ S = ∅, then it is prime. -/
theorem isPrime_of_maximal [CommSemiring R] {P : Ideal R} {S : Submonoid R}
    (hP : P ∈ Kaplansky.set S) (hmax : ∀ I ∈ Kaplansky.set S, P ≤ I → I = P) : P.IsPrime :=
  ⟨ideal_neq_top hP, fun h => mem_or_mem_of_mul_mem _ _ hP hmax h⟩

end Basic

section Kaplansky

-- Semiring?
theorem exists_mem_of_mem [CommSemiring R] {I : Ideal R} (s : Multiset R) (hI : I.IsPrime) :
    Multiset.prod s ∈ I → ∃ (p : R) (_ : p ∈ s), p ∈ I := by
  intro hs
  by_contra h
  push_neg at h
  have hs₃ : s.prod ∉ I
  refine' Multiset.prod_induction _ _ _ _ h
  · rintro a b ha hb
    by_contra h
    cases' (Ideal.isPrime_iff.1 hI).2 h with hI₂ hI₃
    exact ha hI₂
    exact hb hI₃
  exact fun h₂ => (Ideal.isPrime_iff.1 hI).1 (I.eq_top_iff_one.2 h₂)
  exact hs₃ hs

-- Semiring?
theorem mem_iff [CommSemiring R] {I : Ideal R} (s : Multiset R) (hI : I.IsPrime) :
    s.prod ∈ I ↔ ∃ (p : R) (_ : p ∈ s), p ∈ I := by
  classical
    constructor
    exact exists_mem_of_mem s hI
    · intro hs
      rcases hs with ⟨p, ⟨hs₂, hs₃⟩⟩
      rw [← Multiset.prod_erase hs₂]
      exact Ideal.mul_mem_right _ _ hs₃

/-- One implication of Kaplansky's criterion (if an integral domain R is a UFD, then every nonzero
prime ideal contains a prime element). -/
theorem exists_prime_of_uniqueFactorizationMonoid [Semiring R] [CancelCommMonoidWithZero R]
  [UniqueFactorizationMonoid R] {I : Ideal R}
  (hI : I ≠ ⊥) (hI₂ : I.IsPrime) : ∃ x ∈ I, Prime x := by
    classical
    have ha : ∃ a : R, a ∈ I ∧ a ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot hI
    rcases ha with ⟨a, ⟨ha₁, ha₂⟩⟩
    cases' UniqueFactorizationMonoid.factors_prod ha₂ with u ha₃
    rw [← ha₃] at ha₁
    cases' (Ideal.IsPrime.mem_or_mem hI₂) ha₁ with ha₄ ha₅
    · rcases (mem_iff (UniqueFactorizationMonoid.factors a) hI₂).1 ha₄ with ⟨p, ha₅, ha₆⟩
      refine' ⟨p, ha₆, UniqueFactorizationMonoid.prime_of_factor p ha₅⟩
    · exfalso
      exact (Ideal.isPrime_iff.1 hI₂).1 (Ideal.eq_top_of_isUnit_mem _ ha₅ u.isUnit)

/-- The set of prime elements. -/
def primes (R : Type) [CommMonoidWithZero R] :=
  { r : R | Prime r }

/-- Let a, b ∈ R. If ab can be written as a product of prime elements, then a can be written as
a product of a unit and prime elements. The same goes for b. -/
theorem submonoid.closure_primes_absorbing [CancelCommMonoidWithZero R] :
    (Submonoid.closure (primes R)).Absorbing := by
  classical
  rw [Submonoid.absorbing_iff_of_comm]
  intro a b hab
  obtain ⟨m, hm⟩ := Submonoid.exists_multiset_of_mem_closure hab
  revert hm a b
  refine' Multiset.strongInductionOn m _
  rintro s hind b a _ ⟨hprime, hprod⟩
  rcases s.empty_or_exists_mem with (hempty | ⟨i, hi⟩)
  · simp [hempty] at hprod
    exact ⟨1, (Submonoid.closure (primes R)).one_mem, associated_one_of_mul_eq_one _ hprod.symm⟩
  rw [← Multiset.prod_erase hi] at hprod
  rcases(hprime i hi).dvd_or_dvd ⟨(s.erase i).prod, hprod.symm⟩ with (⟨x, hxb⟩ | ⟨x, hxa⟩)
  · suffices ∃ z ∈ Submonoid.closure (primes R), Associated x z by
      obtain ⟨z, hz, hzx⟩ := this
      refine' ⟨z * i, Submonoid.mul_mem _ hz (Submonoid.subset_closure (hprime _ hi)), _⟩
      rw [hxb, mul_comm z i]
      exact Associated.mul_left i hzx
    rw [hxb, mul_assoc] at hprod
    replace hprod := IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (hprime _ hi).ne_zero hprod
    have hxamem : x * a ∈ Submonoid.closure (primes R) := by
      rw [← hprod]
      exact Submonoid.multiset_prod_mem _ _ fun x hx =>
        Submonoid.subset_closure (hprime _ (Multiset.erase_subset _ _ hx))
    exact hind (s.erase i) (Multiset.erase_lt.2 hi) _ _ hxamem
      ⟨fun y hy => hprime y ((s.erase_subset _) hy), hprod⟩
  · rw [hxa, ← mul_assoc, mul_comm b i, mul_assoc] at hprod
    replace hprod := IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (hprime i hi).ne_zero hprod
    have hbxmem : b * x ∈ Submonoid.closure (primes R) := by
      rw [← hprod]
      exact Submonoid.multiset_prod_mem _ _ fun x hx =>
        Submonoid.subset_closure (hprime _ (Multiset.erase_subset _ _ hx))
    exact hind (s.erase i) (Multiset.erase_lt.2 hi) _ _ hbxmem
      ⟨fun y hy => hprime y ((s.erase_subset _) hy), hprod⟩

theorem ideal.span_ne_mem_kaplanski.set [Semiring R] {a : R} (ha : a ≠ 0)
    (H : ∀ (I : Ideal R) (_ : I ≠ ⊥) (_ : I.IsPrime), ∃ x ∈ I, Prime x) :
    Ideal.span {a} ∉ Kaplansky.set (Submonoid.closure (primes R)) := by
  have hzero : 0 ∉ Submonoid.closure (primes R) := by
    intro h
    rcases Submonoid.exists_multiset_of_mem_closure h with ⟨l, ⟨hl, hprod⟩⟩
    exact not_prime_zero (hl 0 (Multiset.prod_eq_zero_iff.1 hprod))
  intro h
  rcases exists_maximal_ideal hzero with ⟨P, hP, hP₂⟩
  have hP₃ : P ≠ ⊥ := by
    intro h₂
    rw [h₂] at hP₂
    exact ha (Ideal.span_singleton_eq_bot.1 (hP₂ (Ideal.span {a}) h (zero_le (Ideal.span {a}))))
  rcases (H P) hP₃ (isPrime_of_maximal hP hP₂) with ⟨x, H₃, H₄⟩
  rw [Kaplansky.set_def, Set.eq_empty_iff_forall_not_mem] at hP
  exact hP x ⟨H₃, Submonoid.subset_closure H₄⟩

/-- The other implication of Kaplansky's criterion (if every nonzero prime ideal of
an integral domain R contains a prime element, then R is a UFD). -/
theorem uniqueFactorizationMonoid_of_exists_prime [Semiring R] [CancelCommMonoidWithZero R]
    (H : ∀ (I : Ideal R) (_ : I ≠ ⊥) (_ : I.IsPrime), ∃ x ∈ I, Prime x) :
    UniqueFactorizationMonoid R := by
  refine' UniqueFactorizationMonoid.of_exists_prime_factors fun a ha => _
  have ha₂ := ideal.span_ne_mem_kaplanski.set _ ha H
  rw [Kaplansky.set_def, ← Ne.def] at ha₂
  rcases Set.nonempty_iff_ne_empty.2 ha₂ with ⟨x, ⟨hx, hx₂⟩⟩
  cases' Ideal.mem_span_singleton'.1 (SetLike.mem_coe.1 hx) with b hb
  rw [← hb, mul_comm] at hx₂
  obtain ⟨z, hzmem, hass⟩ := Submonoid.absorbing_iff_of_comm.1
    (submonoid.closure_primes_absorbing _) _ _ hx₂
  obtain ⟨m, hprime, hprod⟩ := Submonoid.exists_multiset_of_mem_closure hzmem
  refine' ⟨m, hprime, _⟩
  rwa [hprod, Associated.comm]

/-- Kaplansky's criterion (an integral domain R is a UFD if and only if every nonzero prime ideal
contains a prime element). -/
theorem uniqueFactorizationMonoid_iff [Semiring R] [CancelCommMonoidWithZero R] :
  UniqueFactorizationMonoid R ↔ ∀ (I : Ideal R) (_ : I ≠ ⊥) (_ : I.IsPrime), ∃ x ∈ I, Prime x := by
  constructor
  intro u I hI hI₂
  exact exists_prime_of_uniqueFactorizationMonoid hI hI₂
  intro H
  exact uniqueFactorizationMonoid_of_exists_prime H

end Kaplansky
