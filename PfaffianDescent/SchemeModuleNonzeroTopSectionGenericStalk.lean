import PfaffianDescent.SchemeModuleNonzeroTopSectionMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-! The SAME given nonzero section's original map is invertible on the
actual generic stalk. Surjectivity is proved by division by its original
field value, with the native generic-stalk algebraMap proved to be the
identity. The SAME categorical cokernel consequently has zero generic
stalk via the genuine cokernel-preserving stalk functor. SOURCE ONLY. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem genericStalk_algebraMap_apply (r : X.presheaf.stalk (genericPoint X)) :
    letI : Algebra (X.presheaf.stalk (genericPoint X)) X.functionField :=
      AlgebraicGeometry.stalkFunctionFieldAlgebra X (genericPoint X)
    algebraMap (X.presheaf.stalk (genericPoint X)) X.functionField r = r := by
  change (X.presheaf.stalkSpecializes
    ((genericPoint_spec X).specializes (Set.mem_univ (genericPoint X)))).hom r = r
  calc
    (X.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes (Set.mem_univ (genericPoint X)))).hom r =
        CommRingCat.Hom.hom (𝟙 X.functionField) r :=
      congrArg (fun f : CommRingCat.Hom X.functionField X.functionField => f.hom r)
        (X.presheaf.stalkSpecializes_refl (genericPoint X))
    _ = r := rfl

/-- The ACTUAL local-ring module stalk map of the SAME nonzero-section
morphism is an isomorphism at the original generic point. The preimage of
b is the original unit-stalk inverse of psi(b)/f; no bijectivity, dimension
or cokernel certificate is assumed. -/
theorem schemeModuleTopSectionHom_genericStalk_isIso
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M)
    (C : X.Opens) (hgC : genericPoint X ∈ C)
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (s : M.val.obj (op ⊤)) (hs : s ≠ 0) :
    IsIso ((schemeModuleStalkModuleFunctor X (genericPoint X)).map
      (schemeModuleTopSectionHom M s)) := by
  let x := genericPoint X
  letI : Nonempty C := ⟨⟨x, hgC⟩⟩
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  letI := schemeModuleStalkModule O x
  letI := schemeModuleStalkModule M x
  let φ := schemeModuleTopSectionHom M s
  let Φ := schemeModuleTopSectionsToFunctionFieldLinearMap pi M C hgC e
  let ψ := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e x
  let ψO := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi O C (Iso.refl _) x
  let E := (schemeModuleUnitStalkIso X x).toLinearEquiv
  let f : X.functionField := Φ s
  have hf : f ≠ 0 := by
    intro hf
    exact hs (schemeModuleTopSectionsToFunctionFieldLinearMap_injective pi M hM C hgC e
      (hf.trans Φ.map_zero.symm))
  letI : Mono φ := (schemeModuleTopSectionHom_mono_and_cokernelSequence_shortExact
    pi M hM C hgC e s hs).1
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (schemeModuleStalkLinearMap φ x)
  refine ⟨schemeModuleStalkLinearMap_injective_of_mono φ x, ?_⟩
  intro b
  let r : X.presheaf.stalk x := ψ b / f
  refine ⟨E.symm r, ?_⟩
  apply schemeModuleFixedFrameStalkToFunctionFieldLinearMap_injective_of_locallyRankOne
    pi M hM C e x
  have hu : ψO (E.symm r) = r :=
    (DFunLike.congr_fun (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_unit_comp_inv pi C x) r).trans
      (genericStalk_algebraMap_apply (X := X) r)
  have hv : ψ (schemeModuleStalkLinearMap φ x (E.symm r)) =
      @HMul.hMul X.functionField X.functionField X.functionField inferInstance
        (ψO (E.symm r)) f :=
    (schemeModuleUnitHom_stalkField_apply pi M C hgC e φ x (E.symm r)).trans
      (congrArg (fun t : M.val.obj (op ⊤) =>
        @HMul.hMul X.functionField X.functionField X.functionField inferInstance
          (ψO (E.symm r)) (Φ t)) (schemeModuleTopSectionHom_value M s))
  exact hv.trans ((congrArg (fun t : X.functionField => t * f) hu).trans
    (div_mul_cancel₀ (ψ b) hf))

/-- The LITERAL categorical cokernel of the original nonzero-section map
has zero generic stalk as a native local-ring module. The genuine stalk
functor's existing finite-colimit preservation gives its actual cokernel
comparison; no zero-stalk or preservation premise is supplied. -/
theorem schemeModuleTopSectionHom_cokernel_genericStalk_isZero
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M)
    (C : X.Opens) (hgC : genericPoint X ∈ C)
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (s : M.val.obj (op ⊤)) (hs : s ≠ 0) :
    IsZero ((schemeModuleStalkModuleFunctor X (genericPoint X)).obj
      (cokernel (schemeModuleTopSectionHom M s))) := by
  let φ := schemeModuleTopSectionHom M s
  let F := schemeModuleStalkModuleFunctor X (genericPoint X)
  letI : IsIso (F.map φ) := schemeModuleTopSectionHom_genericStalk_isIso pi M hM C hgC e s hs
  exact (isZero_cokernel_of_epi (F.map φ)).of_iso (PreservesCokernel.iso F φ)

end PfaffianDescent
