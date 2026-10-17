import AllCharacteristics.PrimeUniformizerTransfiniteStages

/-! SOURCE ONLY / UNVERIFIED. The existing well-ordered prefix construction,
refined by the actual equation uniformizer = p at every retained stage. -/
noncomputable section
open CategoryTheory
namespace AllCharacteristics.TransfiniteDVRLiftPrefix
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

def primeRestrictionFunctor (p : ℕ) {ι : Type u} [LinearOrder ι]
    (e : ι → L) : ιᵒᵖ ⥤ Type (u + 1) where
  obj a := PrimePrefix (K := K) p e a.unop
  map {X Y} f := ↾fun P => primeRestrict P Y.unop f.unop.le
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro P
    exact primeRestrict_self P
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro P
    exact (primeRestrict_trans P g.unop.le f.unop.le).symm

def primeCompatibleFamilyOfSection (p : ℕ) {ι : Type u} [LinearOrder ι]
    (e : ι → L) (a : ι)
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio a)).monotone.functor.op ⋙
      primeRestrictionFunctor (K := K) p e).sections) :
    CompatiblePrefixFamily (K := K) e a where
  tower b := (x.val (.op b)).val
  restrict_eq b c h := by
    have hx := x.property (homOfLE h).op
    change primeRestrict (x.val (.op c)) b.1 h = x.val (.op b) at hx
    exact congrArg Subtype.val hx

def primeOfCompatibleSection (p : ℕ) {ι : Type u}
    [LinearOrder ι] [SuccOrder ι] (e : ι → L) (a : ι)
    (ha : Order.IsSuccLimit a)
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio a)).monotone.functor.op ⋙
      primeRestrictionFunctor (K := K) p e).sections) :
    PrimePrefix (K := K) p e a :=
  ⟨ofCompatibleFamily ha (primeCompatibleFamilyOfSection p e a x),
    primeNat_ofCompatibleFamily ha (primeCompatibleFamilyOfSection p e a x)
      (fun b => (x.val (.op b)).property)⟩

def primeWellOrderInductionData {p : ℕ} {ι : Type u}
    [LinearOrder ι] [SuccOrder ι] [Algebra.IsAlgebraic K L]
    (e : ι → L) (seed : CompleteDVRPrimeLiftData p K) :
    (primeRestrictionFunctor (K := K) p e).WellOrderInductionData where
  succ j hj P := primeExtendPrefix e seed j hj P
  map_succ j hj P := primeRestrict_primeExtendPrefix e seed j hj P
  lift j hj x := primeOfCompatibleSection p e j hj x
  map_lift j hj x i hi := by
    apply Subtype.ext
    exact restrict_ofCompatibleFamily hj
      (primeCompatibleFamilyOfSection p e j x) ⟨i, hi⟩

def primeGlobalPrefixSection {p : ℕ} {ι : Type u}
    [LinearOrder ι] [OrderBot ι] [SuccOrder ι] [WellFoundedLT ι]
    [Algebra.IsAlgebraic K L]
    (e : ι → L) (seed : CompleteDVRPrimeLiftData p K) :
    (primeRestrictionFunctor (K := K) p e).sections :=
  (primeWellOrderInductionData e seed).sectionsMk
    (primeMinPrefix p e ⊥ isMin_bot)

def primeGlobalPrefix {p : ℕ} {ι : Type u}
    [LinearOrder ι] [OrderBot ι] [SuccOrder ι] [WellFoundedLT ι]
    [Algebra.IsAlgebraic K L] (e : ι → L)
    (seed : CompleteDVRPrimeLiftData p K) (a : ι) :
    PrimePrefix (K := K) p e a :=
  (primeGlobalPrefixSection e seed).val (.op a)

def primeLiftOfTopStage {p : ℕ} {ι : Type u}
    [LinearOrder ι] [OrderBot ι] [OrderTop ι] [SuccOrder ι] [WellFoundedLT ι]
    [Algebra.IsAlgebraic K L] (e : ι → L)
    (seed : CompleteDVRPrimeLiftData p K)
    (htop : transfiniteStageField (K := K) e ⊤ = ⊤) :
    CompleteDVRPrimeLiftData p L := by
  let P := primeGlobalPrefix e seed ⊤
  let S := primeStageData e seed ⊤ P.val P.property
  let D : CompleteDVRPrimeLiftData p (transfiniteStageField (K := K) e ⊤) :=
    S.val.lift.toPrimeNat S.property
  have hD : Nonempty (CompleteDVRPrimeLiftData p (⊤ : IntermediateField K L)) := by
    rw [← htop]
    exact ⟨D⟩
  exact (Classical.choice hD).ofEquiv IntermediateField.topEquiv.toRingEquiv

end AllCharacteristics.TransfiniteDVRLiftPrefix

namespace AllCharacteristics.CompleteDVRPrimeLiftData
universe u

/-- Arbitrary algebraic residue extensions retain p, including inseparable
extensions; the actual tower maps and completion preserve its irreducibility. -/
def algebraicExtension {p : ℕ} {K L : Type u}
    [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (seed : CompleteDVRPrimeLiftData p K) : CompleteDVRPrimeLiftData p L := by
  let κ := Cardinal.mk L
  let α := κ.ord.ToType
  letI : Nonempty α := Cardinal.nonempty_ord_toType (Cardinal.mk_ne_zero L)
  letI : OrderBot α := WellFoundedLT.toOrderBot α
  let q : α ≃ L := (Cardinal.eq.mp (Cardinal.mk_ord_toType κ)).some
  let e : WithTop α → L := WithTop.recTopCoe 0 q
  have htop : transfiniteStageField (K := K) e (⊤ : WithTop α) = ⊤ := by
    apply top_unique
    intro x hx
    apply IntermediateField.subset_adjoin K
    refine ⟨(q.symm x : WithTop α), WithTop.coe_lt_top _, ?_⟩
    change q (q.symm x) = x
    exact q.apply_symm_apply x
  exact TransfiniteDVRLiftPrefix.primeLiftOfTopStage e seed htop

end AllCharacteristics.CompleteDVRPrimeLiftData
