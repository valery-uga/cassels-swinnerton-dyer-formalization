import PfaffianDescent.CorayGlobalOriginalSectionsFinite
import PfaffianDescent.SchemeModuleUnitHomGroundSections
import PfaffianDescent.CorayGenericNormalizationLowDegreeLinearExact
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Genuine finite-dimensional normalization correction over the original K.
The actual global normalization-function image is retained in the dimension
formula. No finite-dimensionality of H¹, constants equality or genus premise.
STATUS: SOURCE ONLY / UNVERIFIED. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual categorical Hom(O_X,Q) is finite over the ORIGINAL K for the
literal smooth-cubic/projective p/q curve. Chart finiteness is derived by the
existing primitive construction; the independent Hom action is matched by the
proved actual Hom/global-sections equivalence. No finiteness premise is added. -/
theorem projectiveIntersection_genericNormalizationUnitHomQuotient_finite
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
    Module.Finite K
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
        genericNormalizationQuotientSheaf X) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  let Q := genericNormalizationQuotientSheaf X
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Module.Finite K (SchemeModuleGlobalSectionsOver pi Q) :=
    projectiveIntersection_genericNormalizationQuotient_globalSections_finite
      p q hp hp0 n hq hnot
  exact Module.Finite.equiv (schemeModuleUnitHomGroundLinearEquivGlobalSections pi Q).symm

/-- Ordinary finite middle-term range/kernel arithmetic for the given maps.
Geometric callers derive both kernel equalities for their original maps. -/
private theorem finiteKernel_and_finrank_of_finite_middle
    {K : Type*} [Field K] {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module K A] [Module K B] [Module K C] [Module K D]
    [Module.Finite K B]
    (σ : A →ₗ[K] B) (δ : B →ₗ[K] C) (g : C →ₗ[K] D)
    (hδ : δ.ker = LinearMap.range σ) (hg : g.ker = LinearMap.range δ) :
    Module.Finite K g.ker ∧
      Module.finrank K g.ker + Module.finrank K (LinearMap.range σ) =
        Module.finrank K B := by
  constructor
  · rw [hg]
    exact Module.Finite.range δ
  · have hdim := δ.finrank_range_add_finrank_ker
    rw [← hg, hδ] at hdim
    exact hdim

/-- The kernel of the SAME canonical map to intrinsic normalization H¹ is
finite-dimensional, and its dimension plus the dimension of the SAME global
projection image equals the actual quotient-section dimension. No finiteness
of either H¹, equality of constants, or vanishing of this image is assumed. -/
theorem projectiveIntersection_genericNormalizationCohomologyOneToNormalization_ker_finite_and_finrank
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let pi := toBase I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    let g := genericNormalizationCohomologyOneToNormalizationLinearMap X pi
    let σ := genericNormalizationHomQuotientLinearMap X pi
    Module.Finite K g.ker ∧
      Module.finrank K g.ker + Module.finrank K (LinearMap.range σ) =
        Module.finrank K
          ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
            genericNormalizationQuotientSheaf X) := by
  intro I X pi N ν g σ
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  letI : LocallyOfFiniteType pi := inferInstance
  letI : Module.Finite K
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
        genericNormalizationQuotientSheaf X) :=
    projectiveIntersection_genericNormalizationUnitHomQuotient_finite p q hp hp0 n hq hnot
  let δ := genericNormalizationHomConnectingLinearMap X pi
  have hδ : δ.ker = LinearMap.range σ := by
    apply Submodule.ext
    intro s
    change δ s = 0 ↔ ∃ z, σ z = s
    exact (genericNormalization_lowDegreeLinearMaps_exact X pi).1 s
  have hg : g.ker = LinearMap.range δ :=
    (genericNormalization_connecting_intrinsicCohomologyOne_exact_and_kernel X pi).2
  exact finiteKernel_and_finrank_of_finite_middle σ δ g hδ hg

end PfaffianDescent.Coray
