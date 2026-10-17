import PfaffianDescent.SchemeModuleSupportedFiberGroundDimension
import PfaffianDescent.FiniteFiveTermLinearRank
import PfaffianDescent.CorayProjectiveIntersectionGlobalConstants
import PfaffianDescent.CorayGlobalOriginalSectionsFinite
import PfaffianDescent.CorayGenericNormalizationUnitMono

/-! Finite actual normalization global constants, retaining their actual
field/space. Original curve H0=K, the finite canonical normalization quotient
and the genuine original normalization exact sequence prove finiteness.
No equality H0(normalization)=K is assumed or concluded.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine finite ORIGINAL-K top-open sections of the ACTUAL normalization
unit. Both finite outer spaces and actual Hom exactness are internal; the
full original normalization-function projection image is retained. -/
theorem projectiveIntersection_genericNormalization_unit_topSections_finite_native
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    Module.Finite K (SchemeModuleOpenSectionsOver (nu ≫ toBase I)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let ON : N.Modules := SheafOfModules.unit N.ringCatSheaf
  let Q := genericNormalizationQuotientSheaf X
  let S := ShortComplex.cokernelSequence (genericNormalizationUnitToPushforwardUnit X)
  have hS : S.ShortExact := genericNormalization_cokernelSequence_shortExact X
  letI hOXFinite : Module.Finite K (SchemeModuleOpenSectionsOver pi OX ⊤) :=
    Module.Finite.equiv (projectiveIntersection_globalFunctionsLinearEquiv_native p q hp hp0 n hn hq hnot)
  letI : Module.Finite K (SchemeModuleGlobalSectionsOver pi Q) :=
    projectiveIntersection_genericNormalizationQuotient_globalSections_finite p q hp hp0 n hq hnot
  letI hQFinite : Module.Finite K (SchemeModuleOpenSectionsOver pi Q ⊤) :=
    Module.Finite.equiv (schemeModuleGlobalSectionsLinearEquivOpenTop pi Q)
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) := hOXFinite
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) := hQFinite
  let f := schemeModuleOpenTopCoefficientLinearMapOver pi S.f
  let g := schemeModuleOpenTopCoefficientLinearMapOver pi S.g
  letI : Module.Finite K
      (SchemeModuleOpenSectionsOver pi ((Scheme.Modules.pushforward nu).obj ON) ⊤) :=
    moduleFinite_middle_of_exact f g (schemeModuleOpenTopCoefficientLinearMaps_exact pi S hS)
  exact Module.Finite.equiv (schemeModulePushforward_topSectionsLinearEquiv pi nu ON)

end PfaffianDescent.Coray
