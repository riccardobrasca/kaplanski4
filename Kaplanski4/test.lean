import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.PowerSeries.Basic

variable (σ : Type _) [Inhabited σ]
variable (R : Type _) [CommRing R] [IsPrincipalIdealRing R]

lemma lemma1 : CancelCommMonoidWithZero (MvPowerSeries σ R) := sorry

theorem uniqueFactorizationMonoid_iff [Semiring R] [CancelCommMonoidWithZero R] :
    UniqueFactorizationMonoid R ↔ ∀ (I : Ideal R) (_ : I ≠ ⊥) (_ : I.IsPrime), ∃ x ∈ I, Prime x :=
  sorry

lemma lemma21 : RingHomClass (MvPowerSeries σ R →ₗ[R] R) (MvPowerSeries σ R) R := sorry

lemma lemma2 (I : Ideal (MvPowerSeries σ R)) (hI : I.IsPrime) :
    I.FG ↔ (@Ideal.map _ (S := R) (F := MvPowerSeries σ R →ₗ[R] R) _ _
    (lemma21 σ R) (MvPowerSeries.coeff R 0) I).FG := sorry

theorem theorem1 : @UniqueFactorizationMonoid (MvPowerSeries σ R) (lemma1 σ R) := by
  rw [@uniqueFactorizationMonoid_iff (MvPowerSeries σ R) _ (lemma1 σ R)]
  rintro β hβ₁ hβ₂
