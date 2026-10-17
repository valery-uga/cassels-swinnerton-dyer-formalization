import AllCharacteristics.CompleteDVRPrimeUniformizer
import AllCharacteristics.AlgebraicExtensionTransfiniteDVRGlobal

/-! SOURCE ONLY / UNVERIFIED. An invariant on existing retained tower data.
No weak lift-existence choice is used to recover the prime uniformizer. -/
noncomputable section
namespace AllCharacteristics
universe u

def UniformizerEqPrimeNat (p : ℕ) {k : Type u} [Field k]
    (D : CompleteCharZeroDVRLiftWithUniformizer k) : Prop :=
  letI : CommRing D.lift.R := D.lift.commRing
  D.uniformizer = (p : D.lift.R)

def CompleteDVRPrimeLiftData.retainedUniformizer {p : ℕ} {k : Type u} [Field k]
    (D : CompleteDVRPrimeLiftData p k) :
    CompleteCharZeroDVRLiftWithUniformizer k := by
  letI : CommRing D.lift.R := D.lift.commRing
  exact ⟨D.lift, (p : D.lift.R), D.prime_irreducible⟩

theorem CompleteDVRPrimeLiftData.retainedUniformizer_eq_prime
    {p : ℕ} {k : Type u} [Field k] (D : CompleteDVRPrimeLiftData p k) :
    UniformizerEqPrimeNat p D.retainedUniformizer := rfl

def CompleteCharZeroDVRLiftWithUniformizer.toPrimeNat
    {p : ℕ} {k : Type u} [Field k]
    (D : CompleteCharZeroDVRLiftWithUniformizer k)
    (hD : UniformizerEqPrimeNat p D) : CompleteDVRPrimeLiftData p k := by
  letI : CommRing D.lift.R := D.lift.commRing
  letI : IsDomain D.lift.R := D.lift.domain
  letI : IsDiscreteValuationRing D.lift.R := D.lift.dvr
  change D.uniformizer = (p : D.lift.R) at hD
  refine ⟨D.lift, ?_⟩
  simpa only [hD] using D.uniformizer_irreducible

namespace TransfiniteDVRLiftPrefix
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

def PrimeNat (p : ℕ) {ι : Type u} [LinearOrder ι]
    {e : ι → L} {a : ι} (P : TransfiniteDVRLiftPrefix (K := K) e a) : Prop :=
  ∀ i, UniformizerEqPrimeNat p (P.lift i)

abbrev PrimePrefix (p : ℕ) {ι : Type u} [LinearOrder ι]
    (e : ι → L) (a : ι) :=
  {P : TransfiniteDVRLiftPrefix (K := K) e a // PrimeNat p P}

theorem primeNat_restrict {p : ℕ} {ι : Type u} [LinearOrder ι]
    {e : ι → L} {a : ι} (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (hP : PrimeNat p P) (b : ι) (hba : b ≤ a) :
    PrimeNat p (restrict P b hba) := by
  intro i
  exact hP ⟨i.1, i.2.trans_le hba⟩

/-- Any actual cocone from a nonempty prime prefix inherits p as uniformizer.
This applies to the existing finite successor AND direct-limit completion. -/
theorem cocone_uniformizer_eq_prime {p : ℕ} {ι : Type u} [LinearOrder ι]
    {e : ι → L} {a : ι} (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (hP : PrimeNat p P) [Nonempty (Set.Iio a)]
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a))
    (C : TransfiniteDVRLiftCocone e a P D) : UniformizerEqPrimeNat p D := by
  let i : Set.Iio a := Classical.choice inferInstance
  letI : CommRing (P.lift i).lift.R := (P.lift i).lift.commRing
  letI : CommRing D.lift.R := D.lift.commRing
  have hi := hP i
  change (P.lift i).uniformizer = (p : (P.lift i).lift.R) at hi
  change D.uniformizer = (p : D.lift.R)
  calc
    D.uniformizer = C.inclusion i (P.lift i).uniformizer :=
      (C.uniformizer_maps i).symm
    _ = C.inclusion i (p : (P.lift i).lift.R) := congrArg (C.inclusion i) hi
    _ = (p : D.lift.R) := map_natCast (C.inclusion i) p

theorem primeNat_successorPrefix {p : ℕ} {ι : Type u}
    [LinearOrder ι] [SuccOrder ι] (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e a) (hP : PrimeNat p P)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a)) (hD : UniformizerEqPrimeNat p D)
    (C : TransfiniteDVRLiftCocone e a P D) :
    PrimeNat p (successorPrefix e a ha P D C) := by
  intro i
  change UniformizerEqPrimeNat p (successorPrefixLift e a ha P D i)
  by_cases hi : i.1 < a
  · rw [successorPrefixLift_of_lt e a ha P D i hi]
    exact hP ⟨i.1, hi⟩
  · have hia : i = successorIndex a ha :=
      Subtype.ext (index_eq_of_lt_succ_of_not_lt a ha i hi)
    subst i
    rw [successorPrefixLift_new]
    exact hD

theorem primeNat_ofCompatibleFamily {p : ℕ} {ι : Type u}
    [LinearOrder ι] [SuccOrder ι] {e : ι → L} {a : ι}
    (ha : Order.IsSuccLimit a) (F : CompatiblePrefixFamily (K := K) e a)
    (hF : ∀ b, PrimeNat p (F.tower b)) :
    PrimeNat p (ofCompatibleFamily ha F) := by
  intro i
  change UniformizerEqPrimeNat p
    ((F.tower (limitFamilyNext ha i)).lift
      ⟨i.1, Order.lt_succ_of_not_isMax (not_isMax_of_lt i.2)⟩)
  exact hF (limitFamilyNext ha i) _

end TransfiniteDVRLiftPrefix
end AllCharacteristics
