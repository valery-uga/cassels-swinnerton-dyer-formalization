import PfaffianDescent.VoisinCubicConstantFunctions
import Mathlib.Algebra.CharZero.Infinite
import PfaffianDescent.ClosedFieldPointGroundScalarResidue
import PfaffianDescent.CubicFiniteSubschemeHyperplane
import Mathlib.AlgebraicGeometry.FunctionField
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

theorem cubicConfigurationGenericMarkedOutsideSupport_generic_not_mem
    (F : Type u) [Field F] [CharZero F]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (hP0 : P ≠ 0)
    [Smooth (hypersurfaceToBase P hP)]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) F)).Modules]
    {L : Type u} [Field L] [Algebra F L]
    (i : Spec (.of L) ⟶ hypersurface P hP) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase P hP = Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (hL : Module.finrank F L = 11) :
    letI : IsIntegral (hypersurface P hP) :=
      isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite P hP hP0
    genericPoint (hypersurface P hP) ∉ Set.range i := by
  let X := hypersurface P hP
  let base := hypersurfaceToBase P hP
  letI : IsIntegral X := isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite P hP hP0
  intro hgen
  have hclosed : IsClosed (Set.range i) := i.isClosedMap.isClosed_range
  have hsubset : Set.univ ⊆ Set.range i := by
    simpa only [genericPoint_closure] using
      (closure_minimal (Set.singleton_subset_iff.mpr hgen) hclosed)
  letI : Surjective i := (surjective_iff i).mpr (fun x => hsubset (Set.mem_univ x))
  letI : IsIso i := isIso_of_isClosedImmersion_of_surjective i
  letI : HasExt.{u} (SheafOfModules.{u}
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) F)).ringCatSheaf) :=
    ‹HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) F)).Modules›
  have hs : Function.Surjective (affineFunctionHom base) :=
    p3_smoothCubicGlobalFunctions_surjective F P hP hP0
  have hiSurj : Function.Surjective i.appTop := (ConcreteCategory.bijective_of_isIso i.appTop).2
  have hidInj : Function.Injective (affineFunctionHom (𝟙 (Spec (.of L)))) := by
    unfold affineFunctionHom
    simp only [Scheme.Hom.id_appTop, Category.comp_id]
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of L)).inv).1
  have hsurj : Function.Surjective (algebraMap F L) := by
    intro l
    obtain ⟨v, hv⟩ := hiSurj (affineFunctionHom (𝟙 (Spec (.of L))) l)
    obtain ⟨c, hc⟩ := hs v
    refine ⟨c, hidInj ?_⟩
    exact (fieldPoint_appTop_ground_constant base i hi c).symm.trans
      ((congrArg i.appTop hc).trans hv)
  have hdim := LinearMap.finrank_le_finrank_of_surjective
    (f := Algebra.linearMap F L) hsurj
  rw [hL, Module.finrank_self] at hdim
  omega
end PfaffianDescent.ProjectiveNegativeTwist
