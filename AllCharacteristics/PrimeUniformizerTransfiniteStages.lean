import AllCharacteristics.PrimeUniformizerPrefixInvariant

/-! SOURCE ONLY / UNVERIFIED. Refine the existing stage constructions,
replacing only the minimal choice by a specified retained prime lift. -/
noncomputable section
namespace AllCharacteristics.TransfiniteDVRLiftPrefix
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

abbrev PrimeStageData (p : ℕ) {ι : Type u} [LinearOrder ι]
    (e : ι → L) (a : ι) (P : TransfiniteDVRLiftPrefix (K := K) e a) :=
  {S : TransfiniteDVRLiftStageData e a P // UniformizerEqPrimeNat p S.lift}

def primeMinStageData {p : ℕ} {ι : Type u} [LinearOrder ι]
    (e : ι → L) (a : ι) (ha : IsMin a)
    (seed : CompleteDVRPrimeLiftData p K)
    (P : TransfiniteDVRLiftPrefix (K := K) e a) : PrimeStageData p e a P := by
  let D : {D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a) // UniformizerEqPrimeNat p D} := by
    rw [transfiniteStageField_eq_bot_of_isMin e a ha]
    let B := seed.ofEquiv (IntermediateField.botEquiv K L).symm.toRingEquiv
    exact ⟨B.retainedUniformizer, B.retainedUniformizer_eq_prime⟩
  refine ⟨{
    lift := D.val
    cocone := {
      inclusion := fun i => (ha.not_lt i.2).elim
      inclusion_injective := fun i => (ha.not_lt i.2).elim
      inclusion_comp := fun i => (ha.not_lt i.2).elim
      residue_commutes := fun i => (ha.not_lt i.2).elim
      uniformizer_maps := fun i => (ha.not_lt i.2).elim
    }
  }, D.property⟩

def primeSuccessorStageData {p : ℕ} {ι : Type u}
    [LinearOrder ι] [SuccOrder ι] [Algebra.IsAlgebraic K L]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (P : TransfiniteDVRLiftPrefix (K := K) e (Order.succ a))
    (hP : PrimeNat p P) : PrimeStageData p e (Order.succ a) P := by
  letI : Nonempty (Set.Iio (Order.succ a)) := ⟨successorIndex a ha⟩
  let S := successorStageData e a ha P
  exact ⟨S, cocone_uniformizer_eq_prime P hP S.lift S.cocone⟩

def primeLimitStageData {p : ℕ} {ι : Type u}
    [LinearOrder ι] [SuccOrder ι] (e : ι → L) (a : ι)
    (ha : Order.IsSuccLimit a) (P : TransfiniteDVRLiftPrefix (K := K) e a)
    (hP : PrimeNat p P) : PrimeStageData p e a P := by
  letI : Nonempty (Set.Iio a) := ha.nonempty_Iio.to_subtype
  let S := limitStageData e a ha P
  exact ⟨S, cocone_uniformizer_eq_prime P hP S.lift S.cocone⟩

def primeStageData {p : ℕ} {ι : Type u}
    [LinearOrder ι] [SuccOrder ι] [Algebra.IsAlgebraic K L]
    (e : ι → L) (seed : CompleteDVRPrimeLiftData p K) (a : ι) :
    ∀ P : TransfiniteDVRLiftPrefix (K := K) e a,
      PrimeNat p P → PrimeStageData p e a P :=
  Order.isSuccLimitRecOn
    (motive := fun b => ∀ P : TransfiniteDVRLiftPrefix (K := K) e b,
      PrimeNat p P → PrimeStageData p e b P)
    a
    (fun b hb P _ => primeMinStageData e b hb seed P)
    (fun b hb P hP => primeSuccessorStageData e b hb P hP)
    (fun b hb P hP => primeLimitStageData e b hb P hP)

def primeRestrict {p : ℕ} {ι : Type u} [LinearOrder ι]
    {e : ι → L} {a : ι} (P : PrimePrefix (K := K) p e a)
    (b : ι) (hba : b ≤ a) : PrimePrefix (K := K) p e b :=
  ⟨restrict P.val b hba, primeNat_restrict P.val P.property b hba⟩

theorem primeRestrict_self {p : ℕ} {ι : Type u} [LinearOrder ι]
    {e : ι → L} {a : ι} (P : PrimePrefix (K := K) p e a) :
    primeRestrict P a le_rfl = P := by
  apply Subtype.ext
  exact restrict_self P.val

theorem primeRestrict_trans {p : ℕ} {ι : Type u} [LinearOrder ι]
    {e : ι → L} {a b c : ι} (P : PrimePrefix (K := K) p e a)
    (hcb : c ≤ b) (hba : b ≤ a) :
    primeRestrict (primeRestrict P b hba) c hcb =
      primeRestrict P c (hcb.trans hba) := by
  apply Subtype.ext
  exact restrict_trans P.val hcb hba

def primeMinPrefix (p : ℕ) {ι : Type u} [LinearOrder ι]
    (e : ι → L) (a : ι) (ha : IsMin a) : PrimePrefix (K := K) p e a :=
  ⟨minPrefix e a ha, fun i => (ha.not_lt i.2).elim⟩

def primeExtendPrefix {p : ℕ} {ι : Type u}
    [LinearOrder ι] [SuccOrder ι] [Algebra.IsAlgebraic K L]
    (e : ι → L) (seed : CompleteDVRPrimeLiftData p K)
    (a : ι) (ha : ¬ IsMax a) (P : PrimePrefix (K := K) p e a) :
    PrimePrefix (K := K) p e (Order.succ a) := by
  let S := primeStageData e seed a P.val P.property
  exact ⟨successorPrefix e a ha P.val S.val.lift S.val.cocone,
    primeNat_successorPrefix e a ha P.val P.property S.val.lift
      S.property S.val.cocone⟩

theorem primeRestrict_primeExtendPrefix {p : ℕ} {ι : Type u}
    [LinearOrder ι] [SuccOrder ι] [Algebra.IsAlgebraic K L]
    (e : ι → L) (seed : CompleteDVRPrimeLiftData p K)
    (a : ι) (ha : ¬ IsMax a) (P : PrimePrefix (K := K) p e a) :
    primeRestrict (primeExtendPrefix e seed a ha P) a (Order.le_succ a) = P := by
  apply Subtype.ext
  exact restrict_successorPrefix e a ha P.val
    (primeStageData e seed a P.val P.property).val.lift
    (primeStageData e seed a P.val P.property).val.cocone

end AllCharacteristics.TransfiniteDVRLiftPrefix
