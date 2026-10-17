import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentAffineIdeal

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

noncomputable def cubicClosedPointSerreSurfaceJetCotangent_nativeGlobalKernelAddEquivIdeal
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of B :=
      CommRingCat.ofHom g
    let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ)
    ((moduleSpecΓFunctor (R := CommRingCat.of A)).map q).hom.ker ≃+ (RingHom.ker g) := by
  dsimp only
  let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
    (Spec.map (CommRingCat.ofHom g))
  let K := ((moduleSpecΓFunctor (R := CommRingCat.of A)).map q).hom.ker
  refine
    { toFun := fun x => ⟨e x.1, (affineStructureToPushforwardUnit_globalKernel_mem_iff (CommRingCat.ofHom g) x.1).mp x.2⟩
      invFun := fun x => ⟨e.symm x.1,
        (affineStructureToPushforwardUnit_globalKernel_mem_iff (CommRingCat.ofHom g) (e.symm x.1)).mpr
          (by
            change e (e.symm x.1) ∈ (RingHom.ker g)
            rw [e.apply_symm_apply]
            exact x.2)⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_ }
  · intro x
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  · intro x
    apply Subtype.ext
    exact e.apply_symm_apply x.1
  · intro x y
    apply Subtype.ext
    exact e.map_add x.1 y.1


noncomputable def cubicClosedPointSerreSurfaceJetCotangent_nativeGlobalKernelLinearEquivIdeal
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of B :=
      CommRingCat.ofHom g
    let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ)
    ((moduleSpecΓFunctor (R := CommRingCat.of A)).map q).hom.ker ≃ₗ[A] (RingHom.ker g) := by
  dsimp only
  let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  refine (cubicClosedPointSerreSurfaceJetCotangent_nativeGlobalKernelAddEquivIdeal g).toLinearEquiv ?_
  intro a x
  apply Subtype.ext
  change e (a • x.1) = a * e x.1
  exact affineGlobalSectionsUnit_ringEquiv_map_smul a x.1


noncomputable def cubicClosedPointSerreSurfaceJetCotangent_nativeGlobalKernelModuleIsoIdeal
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of B :=
      CommRingCat.ofHom g
    let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ)
    kernel ((moduleSpecΓFunctor (R := CommRingCat.of A)).map q) ≅
      ModuleCat.of A (RingHom.ker g) := by
  dsimp only
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
    (Spec.map (CommRingCat.ofHom g))
  exact ModuleCat.kernelIsoKer ((moduleSpecΓFunctor (R := CommRingCat.of A)).map q) ≪≫
    (cubicClosedPointSerreSurfaceJetCotangent_nativeGlobalKernelLinearEquivIdeal g).toModuleIso


theorem cubicClosedPointSerreSurfaceJetCotangent_nativeGlobalKernelModuleIsoIdeal_hom_subtype
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) :
    let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
      (Spec.map (CommRingCat.ofHom g))
    (cubicClosedPointSerreSurfaceJetCotangent_nativeGlobalKernelModuleIsoIdeal g).hom ≫
      ModuleCat.ofHom (RingHom.ker g).subtype =
        kernel.ι ((moduleSpecΓFunctor (R := CommRingCat.of A)).map q) ≫
          (affineGlobalSectionsUnitLinearEquiv (A := A)).toModuleIso.hom := by
  dsimp only
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
    (Spec.map (CommRingCat.ofHom g))
  let f := (moduleSpecΓFunctor (R := CommRingCat.of A)).map q
  let eK := cubicClosedPointSerreSurfaceJetCotangent_nativeGlobalKernelLinearEquivIdeal g
  let eU := affineGlobalSectionsUnitLinearEquiv (A := A)
  change ((ModuleCat.kernelIsoKer f).hom ≫ eK.toModuleIso.hom) ≫
    ModuleCat.ofHom (RingHom.ker g).subtype = kernel.ι f ≫ eU.toModuleIso.hom
  apply ModuleCat.hom_ext
  ext x
  rfl


end PfaffianDescent
