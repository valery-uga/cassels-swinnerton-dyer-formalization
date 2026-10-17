import PfaffianDescent.ActualPositiveTwistPullbackTensorIso

/- SOURCE ONLY / UNVERIFIED. Actual standard Spec(chart) positive-twist
unit Iso, derived from its exact basicOpenIsoSpec factorization. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Construct the actual positive module over an abstract grading before
specializing native polynomial-quotient/category dictionaries. -/
private def nativePositiveTwistModuleObject
    {A τ : Type u} [CommRing A] [SetLike τ A] [AddSubgroupClass τ A]
    (𝒜 : ℕ → τ) [GradedRing 𝒜] (m : ℕ) : (Proj 𝒜).Modules :=
  positiveSheafOfModules 𝒜 m

/-- Derive the native-chart pullback Iso over an abstract grading. The
local restriction Iso is supplied internally by the final native producer. -/
private def nativePositiveTwistChartUnitIsoOfRestriction
    {A τ : Type u} [CommRing A] [SetLike τ A] [AddSubgroupClass τ A]
    (𝒜 : ℕ → τ) [GradedRing 𝒜] (ell : 𝒜 1) (m : ℕ)
    (q : Spec (.of (HomogeneousLocalization.Away 𝒜 (ell : A))) ⟶ Proj 𝒜)
    (hq : q = Proj.awayι 𝒜 (ell : A) ell.property (by decide : 0 < 1))
    (u : (Scheme.Modules.restrictFunctor
        (Proj.basicOpen 𝒜 (ell : A)).ι).obj
        (nativePositiveTwistModuleObject 𝒜 m) ≅
      SheafOfModules.unit
        ((Proj.basicOpen 𝒜 (ell : A) : Scheme).ringCatSheaf)) :
    (Scheme.Modules.pullback q).obj (nativePositiveTwistModuleObject 𝒜 m) ≅
      SheafOfModules.unit
        (Spec (.of (HomogeneousLocalization.Away 𝒜 (ell : A)))).ringCatSheaf := by
  cases hq
  let U := Proj.basicOpen 𝒜 (ell : A)
  let e := Proj.basicOpenIsoSpec 𝒜 (ell : A) ell.property (by decide : 0 < 1)
  let M := nativePositiveTwistModuleObject 𝒜 m
  let eU : (Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ u
  letI : IsIso (pullbackUnitComparison e.inv) :=
    isIso_pullbackUnitComparison e.inv
  change (Scheme.Modules.pullback (e.inv ≫ U.ι)).obj M ≅ _
  exact (Scheme.Modules.pullbackComp e.inv U.ι).symm.app M ≪≫
    (Scheme.Modules.pullback e.inv).mapIso eU ≪≫
    asIso (pullbackUnitComparison e.inv)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def actualPositiveTwistNativeChartUnitIso
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) (j : Fin 4) (m : ℕ) :=
  let ell : grading (R := K) (σ := Fin 4) I 1 :=
    ⟨coordinate (R := K) (σ := Fin 4) I j,
      coordinate_mem (R := K) (σ := Fin 4) I j⟩
  nativePositiveTwistChartUnitIsoOfRestriction
    (A := CoordinateRing (R := K) (σ := Fin 4) I)
    (τ := Submodule K (CoordinateRing (R := K) (σ := Fin 4) I))
    (grading (R := K) (σ := Fin 4) I) ell m
    (chartι (R := K) (σ := Fin 4) I j)
    (by rfl)
    (actualPositiveTwistChartUnitIso (K := K) I ell m)

/-- Compute the native construction before specializing the coefficient-ring
and grading dictionaries. The specialization below uses this opaque equality. -/
private lemma nativePositiveTwistChartUnitIsoOfRestriction_hom
    {A τ : Type u} [CommRing A] [SetLike τ A] [AddSubgroupClass τ A]
    (𝒜 : ℕ → τ) [GradedRing 𝒜] (ell : 𝒜 1) (m : ℕ)
    (u : (Scheme.Modules.restrictFunctor
        (Proj.basicOpen 𝒜 (ell : A)).ι).obj
        (nativePositiveTwistModuleObject 𝒜 m) ≅
      SheafOfModules.unit
        ((Proj.basicOpen 𝒜 (ell : A) : Scheme).ringCatSheaf)) :
    let U := Proj.basicOpen 𝒜 (ell : A)
    let e := Proj.basicOpenIsoSpec 𝒜 (ell : A) ell.property (by decide : 0 < 1)
    let M := nativePositiveTwistModuleObject 𝒜 m
    let eU : (Scheme.Modules.pullback U.ι).obj M ≅
        SheafOfModules.unit (U : Scheme).ringCatSheaf :=
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ u
    (nativePositiveTwistChartUnitIsoOfRestriction 𝒜 ell m
      (Proj.awayι 𝒜 (ell : A) ell.property (by decide : 0 < 1)) rfl u).hom =
      (Scheme.Modules.pullbackComp e.inv U.ι).inv.app M ≫
        (Scheme.Modules.pullback e.inv).map eU.hom ≫ pullbackUnitComparison e.inv := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The hom of the existing native twist Iso is its actual pullback composition.
The construction is unchanged; its computation is proved over an abstract grading. -/
lemma actualPositiveTwistNativeChartUnitIso_hom
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (a : Fin 4) (m : ℕ) :
    let ell : grading (R := K) (σ := Fin 4) I 1 :=
      ⟨coordinate (R := K) (σ := Fin 4) I a,
        coordinate_mem (R := K) (σ := Fin 4) I a⟩
    let U := Proj.basicOpen (grading (R := K) (σ := Fin 4) I)
      (coordinate (R := K) (σ := Fin 4) I a)
    let e := Proj.basicOpenIsoSpec (grading (R := K) (σ := Fin 4) I)
      (coordinate (R := K) (σ := Fin 4) I a)
      (coordinate_mem (R := K) (σ := Fin 4) I a) (by decide : 0 < 1)
    let T := positiveSheafOfModules (grading (R := K) (σ := Fin 4) I) m
    let eU : (Scheme.Modules.pullback U.ι).obj T ≅
        SheafOfModules.unit (U : Scheme).ringCatSheaf :=
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app T ≪≫
        actualPositiveTwistChartUnitIso (K := K) I ell m
    (actualPositiveTwistNativeChartUnitIso I a m).hom =
      (Scheme.Modules.pullbackComp e.inv U.ι).inv.app T ≫
        (Scheme.Modules.pullback e.inv).map eU.hom ≫ pullbackUnitComparison e.inv := by
  exact nativePositiveTwistChartUnitIsoOfRestriction_hom
    (A := CoordinateRing (R := K) (σ := Fin 4) I)
    (τ := Submodule K (CoordinateRing (R := K) (σ := Fin 4) I))
    (grading (R := K) (σ := Fin 4) I)
    ⟨coordinate (R := K) (σ := Fin 4) I a,
      coordinate_mem (R := K) (σ := Fin 4) I a⟩ m
    (actualPositiveTwistChartUnitIso (K := K) I
      ⟨coordinate (R := K) (σ := Fin 4) I a,
        coordinate_mem (R := K) (σ := Fin 4) I a⟩ m)

end PfaffianDescent
