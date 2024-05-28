import Mathlib.RingTheory.PrincipalIdealDomain

variable {R : Type*}

/-- The set of ideals of the ring R which do not intersect the subsemigroup S -/
def Kaplansky.set [Semiring R] (S : Subsemigroup R) :=
  { I : Ideal R | (I : Set R) ∩ S = ∅ }

theorem Kaplansky.set_def [Semiring R] (S : Subsemigroup R) (P : Ideal R) :
    P ∈ Kaplansky.set S ↔ (P : Set R) ∩ S = ∅ := Iff.rfl

section Existence

/-- Every chain of 'Kaplansky.set S' has an upper bound. -/
theorem hypothesis_zorn_lemma [Semiring R] (S : Subsemigroup R) (hS : 0 ∉ S) (C : Set (Ideal R))
    (hC : C ⊆ Kaplansky.set S) (hC₂ : IsChain (· ≤ ·) C) :
    ∃ P, P ∈ Kaplansky.set S ∧ ∀ J, J ∈ C → J ≤ P := by
  by_cases h : C.Nonempty
  · cases' (Set.nonempty_def.1 h) with I hI
    refine' ⟨sSup C, _, fun z hz => le_sSup hz⟩
    rw [Kaplansky.set_def, Set.eq_empty_iff_forall_not_mem]
    rintro x hx
    rcases (Submodule.mem_sSup_of_directed ⟨_, hI⟩ hC₂.directedOn).1 hx.1 with ⟨J, hJ₁, hJ₂⟩
    have hx₂ : (J : Set R) ∩ S ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨x, hJ₂, hx.2⟩
    exact hx₂ (hC hJ₁)
  · rw [Set.not_nonempty_iff_eq_empty.1 h]
    use ⊥
    rw [Kaplansky.set_def, Set.eq_empty_iff_forall_not_mem]
    simp
    exact hS

/-- The existence of a maximal element of 'Kaplansky.set S'
(which we will use to prove Kaplansky's criterion). -/
theorem exists_maximal_ideal [Semiring R] (S : Subsemigroup R) (hS : 0 ∉ S) :
    ∃ P ∈ Kaplansky.set S, ∀ I ∈ Kaplansky.set S, P ≤ I → I = P :=
  zorn_partialOrder₀ (Kaplansky.set S) (hypothesis_zorn_lemma S hS)

end Existence

section Basic

/-- If an ideal P satisfies the condition P ∩ S = ∅, then P ≠ R
(this is used to prove that P is prime). -/
theorem ideal_neq_top [Semiring R] {S : Subsemigroup R} (hS : (S : Set R).Nonempty) {P : Ideal R}
    (hP : P ∈ Kaplansky.set S) : P ≠ ⊤ := by
  intro h
  rw [Kaplansky.set, h, Set.mem_setOf, Set.eq_empty_iff_forall_not_mem] at hP
  rw [Set.nonempty_def] at hS
  cases' hS with x h₂
  specialize hP x
  apply hP
  exact (Set.mem_inter (Set.mem_univ x) h₂)

theorem exists_mem_inter [Semiring R] {S : Subsemigroup R} {P : Ideal R} {I : Ideal R}
    (hmax : ∀ I ∈ Kaplansky.set S, P ≤ I → I = P) (h : P < I) : ∃ x : R, x ∈ (I : Set R) ∩ S :=
  Set.inter_nonempty.1
    (Set.nonempty_iff_ne_empty.2 fun h₂ =>
      (lt_iff_le_and_ne.1 h).2 ((hmax I) h₂ (lt_iff_le_and_ne.1 h).1).symm)

/-- This is checked to prove that an ideal P which is maximal with respect to
the condition P ∩ S = ∅ is also prime. -/
theorem mem_or_mem_of_mul_mem [CommSemiring R] {P : Ideal R} {S : Subsemigroup R} (x y : R)
    (hP : P ∈ Kaplansky.set S) (hmax : ∀ I ∈ Kaplansky.set S, P ≤ I → I = P) :
    x * y ∈ P → x ∈ P ∨ y ∈ P := by
  intro hxy
  by_contra h
  push_neg at h
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

/-- If an ideal P is maximal with respect to the condition P ∩ S = ∅, then it is prime. -/
theorem isPrime_of_maximal [CommSemiring R] {P : Ideal R} {S : Subsemigroup R}
    (hS : (S : Set R).Nonempty) (hP : P ∈ Kaplansky.set S)
    (hmax : ∀ I ∈ Kaplansky.set S, P ≤ I → I = P) : P.IsPrime :=
  ⟨ideal_neq_top hS hP, fun h => mem_or_mem_of_mul_mem _ _ hP hmax h⟩

end Basic

section Kaplansky

open Submonoid in
theorem Submonoid.closure_mem_of_prod_mem [CancelCommMonoidWithZero R] :
    ∀ x y, x * y ∈ closure { r : R | IsUnit r ∨ Prime r} →
    x ∈ closure { r : R | IsUnit r ∨ Prime r} := by
  intros a b hab
  obtain ⟨m, hm⟩ := exists_multiset_of_mem_closure hab
  revert a b hm
  refine m.induction (p := fun m ↦ ∀ a b, a * b ∈ closure {r | IsUnit r ∨ Prime r} →
    (∃ (_ : ∀ y ∈ m, y ∈ {r | IsUnit r ∨ Prime r}), m.prod = a * b) →
    a ∈ closure {r | IsUnit r ∨ Prime r}) (fun _ _ _ hprod => subset_closure (Set.mem_def.2 ?_)) ?_
  · left ; exact isUnit_of_mul_eq_one _ _ hprod.2.symm
  · simp only [exists_prop, and_imp, Multiset.prod_cons, Multiset.mem_cons, forall_eq_or_imp]
    intros _ s hind x y _ ha hs hprod
    rcases ha with ha₁ | ha₂
    · rcases ha₁.exists_right_inv with ⟨k, hk⟩
      refine hind x (y*k) ?_ hs ?_
      simp only [← mul_assoc, ← hprod, ← Multiset.prod_cons, mul_comm]
      refine multiset_prod_mem _ _ (Multiset.forall_mem_cons.2 ⟨subset_closure (Set.mem_def.2 ?_),
        Multiset.forall_mem_cons.2 ⟨subset_closure (Set.mem_def.2 ?_), (fun t ht =>
        subset_closure (hs t ht))⟩⟩)
      left ; exact isUnit_of_mul_eq_one_right _ _ hk
      left ; exact ha₁
      rw [← mul_one s.prod, ← hk, ← mul_assoc, ← mul_assoc, mul_eq_mul_right_iff, mul_comm]
      left ; exact hprod
    · rcases ha₂.dvd_mul.1 (Dvd.intro _ hprod) with ⟨c, hc⟩ | ⟨c, hc⟩
      rw [hc] ; rw [hc, mul_assoc] at hprod
      refine' Submonoid.mul_mem _ (subset_closure (Set.mem_def.2 _))
        (hind _ _ _ hs (mul_left_cancel₀ ha₂.ne_zero hprod))
      right ; exact ha₂
      rw [← mul_left_cancel₀ ha₂.ne_zero hprod]
      exact multiset_prod_mem _ _ (fun t ht => subset_closure (hs t ht))
      rw [hc, mul_comm x _, mul_assoc, mul_comm c _] at hprod
      refine' hind x c _ hs (mul_left_cancel₀ ha₂.ne_zero hprod)
      rw [← mul_left_cancel₀ ha₂.ne_zero hprod]
      exact multiset_prod_mem _ _ (fun t ht => subset_closure (hs t ht))

local notation "P" => { r : R | Prime r }
local notation "S" => Submonoid.closure P

theorem ideal.span_ne_mem_kaplanski.set [CommSemiring R] [IsDomain R] {a : R} (ha : a ≠ 0)
    (H : ∀ (I : Ideal R) (_ : I ≠ ⊥) (_ : I.IsPrime), ∃ x ∈ I, Prime x)
    (hP : (P : Set R).Nonempty) :
    Ideal.span {a} ∉ Kaplansky.set (Submonoid.toSubsemigroup S) := by
  have hzero : 0 ∉ S := by
    intro h
    rcases Submonoid.exists_multiset_of_mem_closure h with ⟨l, ⟨hl, hprod⟩⟩
    exact not_prime_zero (hl 0 (Multiset.prod_eq_zero_iff.1 hprod))
  intro h
  rcases exists_maximal_ideal _ hzero with ⟨T, hT, hT₂⟩
  have hT₃ : T ≠ ⊥ := by
    intro h₂
    rw [h₂] at hT₂
    exact ha (Ideal.span_singleton_eq_bot.1 (hT₂ (Ideal.span {a}) h (zero_le (Ideal.span {a}))))
  rw [Set.nonempty_def] at hP
  cases' hP with x hx
  have := Set.mem_of_subset_of_mem Submonoid.subset_closure hx
  simp at this
  rw [← Submonoid.mem_toSubsemigroup] at this
  have := Set.nonempty_def.2 ⟨x, this⟩
  rcases (H T) hT₃ (isPrime_of_maximal this hT hT₂) with ⟨x, H₃, H₄⟩
  rw [Kaplansky.set_def, Set.eq_empty_iff_forall_not_mem] at hT
  exact hT x ⟨H₃, Submonoid.subset_closure H₄⟩

theorem exists_prime_factors_of_exists_multiset [CommMonoidWithZero R] (a : R)
    (h : ∃ (l : Multiset R), ∃ (_ : ∀ y ∈ l, y ∈ {r | IsUnit r ∨ Prime r}), l.prod = a) :
    ∃ (f : Multiset R), (∀ b ∈ f, Prime b) ∧ Associated f.prod a := by
  rcases h with ⟨l ,hl, hl₂⟩
  revert a hl hl₂
  refine' l.induction (p := fun l => ∀ a, (∀ y ∈ l, y ∈ {r | IsUnit r ∨ Prime r}) →
    l.prod = a → ∃ (f : Multiset R), (∀ b ∈ f, Prime b) ∧ Associated f.prod a) _ _
  · simp only [Multiset.not_mem_zero, Set.mem_setOf_eq, IsEmpty.forall_iff, forall_const,
      Multiset.prod_zero, forall_true_left, forall_eq']
    use 0
    simp only [Multiset.not_mem_zero, IsEmpty.forall_iff, forall_const, Multiset.prod_zero,
      true_and]
    exact Associated.refl 1
  · simp only [Set.mem_setOf_eq, forall_apply_eq_imp_iff, Multiset.mem_cons, forall_eq_or_imp,
      Multiset.prod_cons, and_imp, forall_apply_eq_imp_iff₂]
    intros a s hind ha hs
    rcases ha with ha₁ | ha₂
    · rcases (hind hs) with ⟨f, hf, hf₂⟩
      exact ⟨f, hf, (associated_isUnit_mul_right_iff ha₁).2 hf₂⟩
    · rcases (hind hs) with ⟨f, hf, hf₂⟩
      refine' ⟨f.cons a, Multiset.forall_mem_cons.2 ⟨ha₂, hf⟩, _⟩
      rw [Multiset.prod_cons]
      exact Associated.mul_left a hf₂

/-- The other implication of Kaplansky's criterion (if every nonzero prime ideal of
an integral domain R contains a prime element, then R is a UFD). -/
theorem uniqueFactorizationMonoid_of_exists_prime [CommSemiring R] [IsDomain R]
    (H : ∀ (I : Ideal R) (_ : I ≠ ⊥) (_ : I.IsPrime), ∃ x ∈ I, Prime x)
    (hP : (P : Set R).Nonempty) : UniqueFactorizationMonoid R := by
  refine' UniqueFactorizationMonoid.of_exists_prime_factors fun a ha => _
  have ha₂ := ideal.span_ne_mem_kaplanski.set ha H
  rw [Kaplansky.set_def, ← Ne.def] at ha₂
  rcases Set.nonempty_iff_ne_empty.2 (ha₂ hP) with ⟨x, ⟨hx, hx₂⟩⟩
  cases' Ideal.mem_span_singleton'.1 (SetLike.mem_coe.1 hx) with b hb
  rw [← hb, mul_comm] at hx₂
  have hsubset : Submonoid.closure {r : R | Prime r} ≤
      Submonoid.closure {r : R | IsUnit r ∨ Prime r} := by
    refine' Submonoid.closure_mono (Set.setOf_subset_setOf.2 (fun _ ha => _))
    right
    exact ha
  exact exists_prime_factors_of_exists_multiset a (Submonoid.exists_multiset_of_mem_closure
    (Submonoid.closure_mem_of_prod_mem _ _ (hsubset hx₂)))

/-- Kaplansky's criterion (an integral domain R is a UFD if and only if every nonzero prime ideal
contains a prime element). -/
theorem uniqueFactorizationMonoid_iff [CommSemiring R] [IsDomain R] (hP : (P : Set R).Nonempty) :
  UniqueFactorizationMonoid R ↔ ∀ (I : Ideal R) (_ : I ≠ ⊥) (_ : I.IsPrime), ∃ x ∈ I, Prime x := by
  classical
  constructor
  intro _ _ hI hI₂
  exact Ideal.IsPrime.exists_mem_prime_of_ne_bot hI₂ hI
  intro H
  exact uniqueFactorizationMonoid_of_exists_prime H hP

end Kaplansky
