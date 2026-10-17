import PfaffianDescent.CorayProjectiveIntersectionIntrinsicH1Finite
import PfaffianDescent.CorayProjectiveNormalizationLowDegreeLinearExact
import Mathlib.RingTheory.Finiteness.Basic

/-! Independently staged finite intrinsic original-K normalization H¹ core.
The original theorem declaration below is copied byte-for-byte.
SOURCE ONLY / UNVERIFIED; root owns production and deep acceptance. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Finite INTRINSIC ORIGINAL-K H¹ of the ACTUAL normalization of the SAME
original integral projective p/q curve. Original curve H¹ finiteness comes
from the primitive equation producer. The actual original-K map onto
normalization H¹ is surjective by the actual normalization sequence and
finite-support affine quotient vanishing; its intrinsic comparison is proved
internally by the existing actual linear comparison producer. -/
theorem projectiveIntersection_genericNormalization_unit_cohomology_one_finite_native
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ toBase I)
    Module.Finite K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  letI : LocallyOfFiniteType pi := inferInstance
  letI : Module.Finite K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) :=
    projectiveIntersection_unit_cohomology_one_finite_native p q hp hp0 n hq hnot
  let g := genericNormalizationCohomologyOneToNormalizationLinearMap X pi
  have hsurj : Function.Surjective g :=
    (projectiveIntersection_genericNormalization_lowDegreeLinearExact_surjective_and_kernel
      p q hp hp0 n hq hnot).2.2.1
  exact Module.Finite.of_surjective g hsurj

end PfaffianDescent.Coray
