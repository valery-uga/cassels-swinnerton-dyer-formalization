import PfaffianDescent.SchemeModuleClosedPointTensorDualIncrement
import PfaffianDescent.SchemeModuleClosedPointSupportCohomology
import PfaffianDescent.FiniteFiveTermLinearRank

/-! Actual positive and negative closed-point low-degree sequences. The
first maps are SAME tensor(delta) and ideal-tensor inclusion; projections
are SAME adjunction units. Point-fiber H1 vanishing is internal. No assumed
exactness, section comparison, residue frame or cohomology certificate.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open IdealSheafDataModule
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [HasExt.{u} X.Modules]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual positive five-term sequence. Rank-one charts produce
short exactness and actual closed-point support produces H1 surjectivity. -/
theorem schemeModuleClosedPoint_positiveIncrement_lowDegreeExact
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X) (L : X.Modules)
    (hM : let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i))
    (hL : schemeModuleLocallyRankOne L) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let T := schemeModuleTensor L (SchemeModuleInternalHom.dual M)
    let deltaL := schemeModuleRankOneTensorDualIncrement (closedImmersionModuleToUnit i) L
    let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T
    ∃ hzero : deltaL ≫ eta = 0,
      let S := ShortComplex.mk deltaL eta hzero
      ∃ hS : S.ShortExact,
        Function.Injective (schemeModuleOpenTopCoefficientLinearMapOver pi deltaL) ∧
        Function.Exact (schemeModuleOpenTopCoefficientLinearMapOver pi deltaL)
          (schemeModuleOpenTopCoefficientLinearMapOver pi eta) ∧
        Function.Exact (schemeModuleOpenTopCoefficientLinearMapOver pi eta)
          (schemeModuleOpenTopConnectingLinearMapOver pi S hS) ∧
        Function.Exact (schemeModuleOpenTopConnectingLinearMapOver pi S hS)
          (schemeModuleCohomologyLinearMapOver pi deltaL 1) ∧
        Function.Surjective (schemeModuleCohomologyLinearMapOver pi deltaL 1) := by
  classical
  dsimp only
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let T := schemeModuleTensor L (SchemeModuleInternalHom.dual M)
  let deltaL := schemeModuleRankOneTensorDualIncrement (closedImmersionModuleToUnit i) L
  let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T
  obtain ⟨hz, hS, _E⟩ := schemeModuleClosedPointTensorDualIncrement_canonical_fiberSequence P L hM hL
  let S := ShortComplex.mk deltaL eta hz
  letI : Mono deltaL := hS.mono_f
  letI : Subsingleton (schemeModuleCohomology X S.X₃ 1) :=
    schemeModuleResiduePointPushforward_cohomology_succ_subsingleton P
      ((Scheme.Modules.pullback i).obj T) 0
  have hex := schemeModuleOpenTopConnectingLinearMaps_exact pi S hS
  exact ⟨hz, hS, schemeModuleOpenTopCoefficientLinearMapOver_injective_of_mono pi deltaL,
    schemeModuleOpenTopCoefficientLinearMaps_exact pi S hS, hex.1, hex.2,
    schemeModuleCohomologyOneMap_surjective_of_quotient_subsingleton pi S hS⟩

/-- The actual negative five-term sequence. Its first map is the
original ideal-tensor inclusion followed by the actual left unitor. -/
theorem schemeModuleClosedPoint_negativeIncrement_lowDegreeExact
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X) (L : X.Modules)
    (hL : schemeModuleLocallyRankOne L) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let S0 := closedImmersionIdealTwistSequence i L
    let beta := S0.f ≫ (schemeModuleTensorUnitLeftIso L).hom
    let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L
    ∃ hzero : beta ≫ eta = 0,
      let S := ShortComplex.mk beta eta hzero
      ∃ hS : S.ShortExact,
        Function.Injective (schemeModuleOpenTopCoefficientLinearMapOver pi beta) ∧
        Function.Exact (schemeModuleOpenTopCoefficientLinearMapOver pi beta)
          (schemeModuleOpenTopCoefficientLinearMapOver pi eta) ∧
        Function.Exact (schemeModuleOpenTopCoefficientLinearMapOver pi eta)
          (schemeModuleOpenTopConnectingLinearMapOver pi S hS) ∧
        Function.Exact (schemeModuleOpenTopConnectingLinearMapOver pi S hS)
          (schemeModuleCohomologyLinearMapOver pi beta 1) ∧
        Function.Surjective (schemeModuleCohomologyLinearMapOver pi beta 1) := by
  classical
  dsimp only
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let S0 := closedImmersionIdealTwistSequence i L
  let beta := S0.f ≫ (schemeModuleTensorUnitLeftIso L).hom
  let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L
  obtain ⟨hz, hS, _E⟩ := schemeModuleLocallyRankOne_closedPoint_idealTensor_fiberSequence P L hL
  let S := ShortComplex.mk beta eta hz
  letI : Mono beta := hS.mono_f
  letI : Subsingleton (schemeModuleCohomology X S.X₃ 1) :=
    schemeModuleResiduePointPushforward_cohomology_succ_subsingleton P
      ((Scheme.Modules.pullback i).obj L) 0
  have hex := schemeModuleOpenTopConnectingLinearMaps_exact pi S hS
  exact ⟨hz, hS, schemeModuleOpenTopCoefficientLinearMapOver_injective_of_mono pi beta,
    schemeModuleOpenTopCoefficientLinearMaps_exact pi S hS, hex.1, hex.2,
    schemeModuleCohomologyOneMap_surjective_of_quotient_subsingleton pi S hS⟩

end PfaffianDescent.Coray
