import PfaffianDescent.AffineIdealTildeKernel
import PfaffianDescent.IdealSheafModule

/-! The actual pushforward structure sheaf of an affine quotient is a `tilde` module. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- On the top affine open, the module-sheaf map from the structure sheaf
to the pushforward structure sheaf is the underlying map of the scheme
morphism. -/
theorem affineStructureToPushforwardUnit_map_apply
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (x : (moduleSpecΓFunctor (R := R)).obj
      (SheafOfModules.unit (Spec R).ringCatSheaf)) :
    ((moduleSpecΓFunctor (R := R)).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ))).hom x =
        (Spec.map φ).appTop.hom x := by
  rfl

/-- Membership in the global kernel of the actual affine sheaf map is
membership in the kernel of the corresponding coordinate-ring map. -/
theorem affineStructureToPushforwardUnit_globalKernel_mem_iff
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (x : (moduleSpecΓFunctor (R := R)).obj
      (SheafOfModules.unit (Spec R).ringCatSheaf)) :
    x ∈ ((moduleSpecΓFunctor (R := R)).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ))).hom.ker ↔
        (Scheme.ΓSpecIso R).hom.hom x ∈ RingHom.ker φ.hom := by
  let eR := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  let eS := (Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv
  have hnat : eS ((Spec.map φ).appTop.hom x) = φ.hom (eR x) := by
    exact congrArg (fun f : Γ(Spec R, ⊤) ⟶ S => f.hom x)
      (Scheme.ΓSpecIso_naturality φ)
  constructor
  · intro hx
    rw [LinearMap.mem_ker, affineStructureToPushforwardUnit_map_apply] at hx
    change φ.hom (eR x) = 0
    rw [← hnat, hx]
    exact eS.map_zero
  · intro hx
    change φ.hom (eR x) = 0 at hx
    rw [LinearMap.mem_ker, affineStructureToPushforwardUnit_map_apply]
    apply eS.injective
    rw [hnat, hx]
    exact eS.map_zero.symm

/-- The global kernel of the actual quotient sheaf map is the original
ideal, transported through the affine global-sections isomorphism. -/
theorem affineQuotientPushforwardUnit_globalKernel_mem_iff
    {A : Type u} [CommRing A] (I : Ideal A)
    (x : (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf)) :
    x ∈ ((moduleSpecΓFunctor (R := CommRingCat.of A)).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).hom.ker ↔
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x ∈ I := by
  rw [affineStructureToPushforwardUnit_globalKernel_mem_iff]
  change (Ideal.Quotient.mk I) ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x) = 0 ↔
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x ∈ I
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The global kernel of the actual affine quotient sequence is, as an
additive group, the original ideal. -/
noncomputable def affineQuotientGlobalKernelAddEquivIdeal
    {A : Type u} [CommRing A] (I : Ideal A) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ)
    ((moduleSpecΓFunctor (R := CommRingCat.of A)).map q).hom.ker ≃+ I := by
  dsimp only
  let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  let K := ((moduleSpecΓFunctor (R := CommRingCat.of A)).map q).hom.ker
  refine
    { toFun := fun x => ⟨e x.1, (affineQuotientPushforwardUnit_globalKernel_mem_iff I x.1).mp x.2⟩
      invFun := fun x => ⟨e.symm x.1,
        (affineQuotientPushforwardUnit_globalKernel_mem_iff I (e.symm x.1)).mpr
          (by
            change e (e.symm x.1) ∈ I
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

/-- The canonical affine global-sections equivalence is linear over the
coordinate ring, with the module structure used by `moduleSpecΓFunctor`. -/
theorem affineGlobalSectionsUnit_ringEquiv_map_smul
    {A : Type u} [CommRing A] (a : A)
    (x : (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf)) :
    let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
    e (a • x) = a * e x := by
  dsimp only
  let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  let y : Γ(Spec (CommRingCat.of A), ⊤) := x
  change e ((e.symm a) • y) = a * e y
  rw [smul_eq_mul, e.map_mul, e.apply_symm_apply]

/-- The affine global sections of the structure sheaf, with the scalar
structure used by the tilde adjunction, are linearly equivalent to the
coordinate ring. -/
noncomputable def affineGlobalSectionsUnitLinearEquiv
    {A : Type u} [CommRing A] :
    (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf) ≃ₗ[A] A := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  let e' : (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf) ≃+ A :=
    e.toAddEquiv
  refine e'.toLinearEquiv ?_
  intro a x
  exact affineGlobalSectionsUnit_ringEquiv_map_smul a x

/-- The global kernel of the actual affine quotient sheaf map is the
original ideal as an `A`-module. -/
noncomputable def affineQuotientGlobalKernelLinearEquivIdeal
    {A : Type u} [CommRing A] (I : Ideal A) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ)
    ((moduleSpecΓFunctor (R := CommRingCat.of A)).map q).hom.ker ≃ₗ[A] I := by
  dsimp only
  let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  refine (affineQuotientGlobalKernelAddEquivIdeal I).toLinearEquiv ?_
  intro a x
  apply Subtype.ext
  change e (a • x.1) = a * e x.1
  exact affineGlobalSectionsUnit_ringEquiv_map_smul a x.1

/-- If both terms of a map on an affine scheme come from `tilde`, so does
its actual sheaf kernel. The isomorphism is induced by the counit of the
`tilde`–global-sections adjunction and preservation of kernels. -/
noncomputable def affineKernelFromTildeGammaIso
    {R : CommRingCat.{u}} {M N : (Spec R).Modules} (f : M ⟶ N)
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) M)]
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) N)] :
    (tilde.functor R).obj (kernel (moduleSpecΓFunctor.map f)) ≅ kernel f := by
  let F := tilde.functor R
  let G := moduleSpecΓFunctor (R := R)
  letI : F.IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  letI : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  letI : PreservesFiniteLimits F := tilde_preservesFiniteLimits
  letI hm : IsIso ((tilde.adjunction (R := R)).counit.app M) := by
    change IsIso (Scheme.Modules.fromTildeΓ (R := R) M)
    infer_instance
  letI hn : IsIso ((tilde.adjunction (R := R)).counit.app N) := by
    change IsIso (Scheme.Modules.fromTildeΓ (R := R) N)
    infer_instance
  let eM : F.obj (G.obj M) ≅ M := asIso ((tilde.adjunction (R := R)).counit.app M)
  let eN : F.obj (G.obj N) ≅ N := asIso ((tilde.adjunction (R := R)).counit.app N)
  have hnat : F.map (G.map f) ≫ eN.hom = eM.hom ≫ f := by
    change (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫
      (tilde.adjunction (R := R)).counit.app N =
      (tilde.adjunction (R := R)).counit.app M ≫ f
    simpa only [Functor.comp_map, Functor.id_map] using
      (tilde.adjunction (R := R)).counit.naturality f
  exact PreservesKernel.iso F (G.map f) ≪≫
    kernel.mapIso (f := F.map (G.map f)) f eM eN hnat

/-- The affine kernel comparison commutes with the kernel inclusion into
the source sheaf. -/
theorem affineKernelFromTildeGammaIso_hom_ι
    {R : CommRingCat.{u}} {M N : (Spec R).Modules} (f : M ⟶ N)
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) M)]
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) N)] :
    (affineKernelFromTildeGammaIso f).hom ≫ kernel.ι f =
      (tilde.functor R).map (kernel.ι (moduleSpecΓFunctor.map f)) ≫
        Scheme.Modules.fromTildeΓ (R := R) M := by
  let F := tilde.functor R
  let G := moduleSpecΓFunctor (R := R)
  letI : F.IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  letI : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  letI : PreservesFiniteLimits F := tilde_preservesFiniteLimits
  letI hm : IsIso ((tilde.adjunction (R := R)).counit.app M) := by
    change IsIso (Scheme.Modules.fromTildeΓ (R := R) M)
    infer_instance
  letI hn : IsIso ((tilde.adjunction (R := R)).counit.app N) := by
    change IsIso (Scheme.Modules.fromTildeΓ (R := R) N)
    infer_instance
  let eM : F.obj (G.obj M) ≅ M := asIso ((tilde.adjunction (R := R)).counit.app M)
  let eN : F.obj (G.obj N) ≅ N := asIso ((tilde.adjunction (R := R)).counit.app N)
  have hnat : F.map (G.map f) ≫ eN.hom = eM.hom ≫ f := by
    change (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫
      (tilde.adjunction (R := R)).counit.app N =
      (tilde.adjunction (R := R)).counit.app M ≫ f
    simpa only [Functor.comp_map, Functor.id_map] using
      (tilde.adjunction (R := R)).counit.naturality f
  change (PreservesKernel.iso F (G.map f) ≪≫
      kernel.mapIso (f := F.map (G.map f)) f eM eN hnat).hom ≫ kernel.ι f =
    F.map (kernel.ι (G.map f)) ≫ eM.hom
  rw [Iso.trans_hom, Category.assoc, kernel.mapIso_hom, kernel.lift_ι,
    PreservesKernel.iso_hom]
  simp only [← Category.assoc, kernelComparison_comp_ι]

/-- The structure sheaf of an affine quotient, pushed to the ambient affine
scheme, lies in the essential image of the affine `tilde` functor. -/
theorem affineQuotientPushforwardUnit_fromTildeΓ_isIso
    {A : Type u} [CommRing A] (I : Ideal A) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A)
      ((Scheme.Modules.pushforward (Spec.map φ)).obj
      (SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf))) := by
  dsimp only
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of (A ⧸ I))
      (SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  exact isIso_fromTildeΓ_pushforward
    (φ := CommRingCat.ofHom (Ideal.Quotient.mk I))
    (SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)

/-- The literal kernel of the affine quotient's structure-sheaf map is the
`tilde` sheaf of the kernel of its map on global module sections. -/
noncomputable def affineQuotientClosedImmersionKernelFromTildeGammaIso
    {A : Type u} [CommRing A] (I : Ideal A) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ)
    (tilde.functor (CommRingCat.of A)).obj
      (kernel (moduleSpecΓFunctor.map q)) ≅
        IdealSheafDataModule.closedImmersionKernelModule (Spec.map φ) := by
  dsimp only
  let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let O := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  let T := (Scheme.Modules.pushforward (Spec.map φ)).obj
    (SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) O) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) T) :=
    affineQuotientPushforwardUnit_fromTildeΓ_isIso I
  exact affineKernelFromTildeGammaIso
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ))

/-- The categorical global-sections kernel of the actual affine quotient
sequence is the coordinate ideal as a module. -/
noncomputable def affineQuotientGlobalKernelModuleIsoIdeal
    {A : Type u} [CommRing A] (I : Ideal A) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ)
    kernel ((moduleSpecΓFunctor (R := CommRingCat.of A)).map q) ≅
      ModuleCat.of A I := by
  dsimp only
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  exact ModuleCat.kernelIsoKer ((moduleSpecΓFunctor (R := CommRingCat.of A)).map q) ≪≫
    (affineQuotientGlobalKernelLinearEquivIdeal I).toModuleIso

/-- The affine structure sheaf is obtained from the free rank-one module
through the global-sections equivalence and its counit. -/
noncomputable def affineGlobalSectionsUnitTildeIso
    {A : Type u} [CommRing A] :
    (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A A) ≅
      SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf := by
  let R := CommRingCat.of A
  let O := SheafOfModules.unit (Spec R).ringCatSheaf
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := R) O) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  letI h : IsIso ((tilde.adjunction (R := R)).counit.app O) := by
    change IsIso (Scheme.Modules.fromTildeΓ (R := R) O)
    infer_instance
  exact (tilde.functor R).mapIso
      (affineGlobalSectionsUnitLinearEquiv (A := A)).toModuleIso.symm ≪≫
    asIso ((tilde.adjunction (R := R)).counit.app O)

/-- The inverse affine global-sections equivalence is the unit of the
`tilde`–global-sections adjunction at the free rank-one module. -/
theorem affineGlobalSectionsUnitLinearEquiv_symm_eq_tildeAdjunctionUnit
    {A : Type u} [CommRing A] :
    (affineGlobalSectionsUnitLinearEquiv (A := A)).symm.toModuleIso.hom =
      ((tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom.app
        (ModuleCat.of A A)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

/-- The affine structure-sheaf isomorphism built from global sections
agrees with Mathlib's identity identification of `tilde A` and the
structure sheaf. -/
theorem affineGlobalSectionsUnitTildeIso_hom_eq_tildeSelf
    {A : Type u} [CommRing A] :
    (affineGlobalSectionsUnitTildeIso (A := A)).hom =
      (tildeSelf (R := CommRingCat.of A)).hom := by
  let R := CommRingCat.of A
  let F := tilde.functor R
  let adj := tilde.adjunction (R := R)
  change F.map (affineGlobalSectionsUnitLinearEquiv (A := A)).symm.toModuleIso.hom ≫
    adj.counit.app (F.obj (ModuleCat.of A A)) =
      𝟙 (F.obj (ModuleCat.of A A))
  rw [affineGlobalSectionsUnitLinearEquiv_symm_eq_tildeAdjunctionUnit]
  exact adj.left_triangle_components (ModuleCat.of A A)

/-- The full affine structure-sheaf isomorphism is the identity
identification of `tilde A` with the structure sheaf. -/
theorem affineGlobalSectionsUnitTildeIso_eq_tildeSelf
    {A : Type u} [CommRing A] :
    affineGlobalSectionsUnitTildeIso (A := A) =
      tildeSelf (R := CommRingCat.of A) := by
  apply Iso.ext
  exact affineGlobalSectionsUnitTildeIso_hom_eq_tildeSelf

/-- The global-kernel identification respects the inclusion into the
global sections of the structure sheaf. -/
theorem affineQuotientGlobalKernelModuleIsoIdeal_hom_subtype
    {A : Type u} [CommRing A] (I : Ideal A) :
    let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (affineQuotientGlobalKernelModuleIsoIdeal I).hom ≫
      ModuleCat.ofHom I.subtype =
        kernel.ι ((moduleSpecΓFunctor (R := CommRingCat.of A)).map q) ≫
          (affineGlobalSectionsUnitLinearEquiv (A := A)).toModuleIso.hom := by
  dsimp only
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  let f := (moduleSpecΓFunctor (R := CommRingCat.of A)).map q
  let eK := affineQuotientGlobalKernelLinearEquivIdeal I
  let eU := affineGlobalSectionsUnitLinearEquiv (A := A)
  change ((ModuleCat.kernelIsoKer f).hom ≫ eK.toModuleIso.hom) ≫
    ModuleCat.ofHom I.subtype = kernel.ι f ≫ eU.toModuleIso.hom
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- The `tilde` sheaf of an affine quotient ideal is isomorphic to the
literal kernel sheaf of the affine closed immersion. -/
noncomputable def affineQuotientIdealTildeClosedImmersionKernelIso
    {A : Type u} [CommRing A] (I : Ideal A) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A I) ≅
      IdealSheafDataModule.closedImmersionKernelModule (Spec.map φ) := by
  dsimp only
  exact (tilde.functor (CommRingCat.of A)).mapIso
      (affineQuotientGlobalKernelModuleIsoIdeal I).symm ≪≫
    affineQuotientClosedImmersionKernelFromTildeGammaIso I

/-- The affine ideal comparison respects the canonical inclusion of the
literal ideal kernel into the structure sheaf. -/
theorem affineQuotientIdealTildeClosedImmersionKernelIso_hom_ι
    {A : Type u} [CommRing A] (I : Ideal A) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    (affineQuotientIdealTildeClosedImmersionKernelIso I).hom ≫
      IdealSheafDataModule.closedImmersionKernelModuleToUnit (Spec.map φ) =
        (tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom I.subtype) ≫
          (affineGlobalSectionsUnitTildeIso (A := A)).hom := by
  dsimp only
  let R := CommRingCat.of A
  let F := tilde.functor R
  let G := moduleSpecΓFunctor (R := R)
  let φ : R ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ)
  let O := SheafOfModules.unit (Spec R).ringCatSheaf
  let T := (Scheme.Modules.pushforward (Spec.map φ)).obj
    (SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)
  let eK := affineQuotientGlobalKernelModuleIsoIdeal I
  let eU := (affineGlobalSectionsUnitLinearEquiv (A := A)).toModuleIso
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := R) O) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := R) T) :=
    affineQuotientPushforwardUnit_fromTildeΓ_isIso I
  letI hO : IsIso ((tilde.adjunction (R := R)).counit.app O) := by
    change IsIso (Scheme.Modules.fromTildeΓ (R := R) O)
    infer_instance
  have hglob : eK.hom ≫ ModuleCat.ofHom I.subtype =
      kernel.ι (G.map q) ≫ eU.hom :=
    affineQuotientGlobalKernelModuleIsoIdeal_hom_subtype I
  have hglob' : eK.inv ≫ kernel.ι (G.map q) =
      ModuleCat.ofHom I.subtype ≫ eU.inv := by
    apply (eK.inv_comp_eq).2
    simpa only [Category.assoc] using ((eU.comp_inv_eq).2 hglob).symm
  have hK := affineKernelFromTildeGammaIso_hom_ι q
  change (F.mapIso eK.symm ≪≫
      affineQuotientClosedImmersionKernelFromTildeGammaIso I).hom ≫ kernel.ι q =
    F.map (ModuleCat.ofHom I.subtype) ≫
      (F.mapIso eU.symm ≪≫
        asIso ((tilde.adjunction (R := R)).counit.app O)).hom
  change (F.map eK.inv ≫
      (affineQuotientClosedImmersionKernelFromTildeGammaIso I).hom) ≫ kernel.ι q =
    F.map (ModuleCat.ofHom I.subtype) ≫
      (F.map eU.inv ≫ Scheme.Modules.fromTildeΓ (R := R) O)
  calc
    (F.map eK.inv ≫ (affineQuotientClosedImmersionKernelFromTildeGammaIso I).hom) ≫
        kernel.ι q =
      F.map eK.inv ≫
        ((affineQuotientClosedImmersionKernelFromTildeGammaIso I).hom ≫ kernel.ι q) :=
          Category.assoc _ _ _
    _ = F.map eK.inv ≫
        (F.map (kernel.ι (G.map q)) ≫ Scheme.Modules.fromTildeΓ (R := R) O) :=
          congrArg (fun h => F.map eK.inv ≫ h) hK
    _ = F.map (eK.inv ≫ kernel.ι (G.map q)) ≫
        Scheme.Modules.fromTildeΓ (R := R) O :=
          (congrArg (fun h => h ≫ Scheme.Modules.fromTildeΓ (R := R) O)
            (F.map_comp eK.inv (kernel.ι (G.map q)))).symm
    _ = F.map (ModuleCat.ofHom I.subtype ≫ eU.inv) ≫
        Scheme.Modules.fromTildeΓ (R := R) O := by rw [hglob']
    _ = F.map (ModuleCat.ofHom I.subtype) ≫ F.map eU.inv ≫
        Scheme.Modules.fromTildeΓ (R := R) O := by
          calc
            F.map (ModuleCat.ofHom I.subtype ≫ eU.inv) ≫
                Scheme.Modules.fromTildeΓ (R := R) O =
              (F.map (ModuleCat.ofHom I.subtype) ≫ F.map eU.inv) ≫
                Scheme.Modules.fromTildeΓ (R := R) O := by
                  rw [F.map_comp]
            _ = _ := Category.assoc _ _ _

/-- The affine `tilde` ideal is the project's actual image-defined ideal
module for the quotient closed immersion. -/
noncomputable def affineQuotientIdealTildeClosedImmersionModuleIso
    {A : Type u} [CommRing A] (I : Ideal A) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A I) ≅
      IdealSheafDataModule.closedImmersionModule (Spec.map φ) := by
  dsimp only
  letI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  exact affineQuotientIdealTildeClosedImmersionKernelIso I ≪≫
    (IdealSheafDataModule.closedImmersionModuleToKernelIso
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).symm

/-- The affine quotient comparison with the actual image-defined ideal
module preserves its inclusion into the structure sheaf. -/
theorem affineQuotientIdealTildeClosedImmersionModuleIso_hom_toUnit
    {A : Type u} [CommRing A] (I : Ideal A) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    (affineQuotientIdealTildeClosedImmersionModuleIso I).hom ≫
      IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ) =
        (tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom I.subtype) ≫
          (affineGlobalSectionsUnitTildeIso (A := A)).hom := by
  dsimp only
  let φ : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  letI : IsClosedImmersion (Spec.map φ) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  let e := IdealSheafDataModule.closedImmersionModuleToKernelIso (Spec.map φ)
  have he : e.inv ≫
      IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ) =
        IdealSheafDataModule.closedImmersionKernelModuleToUnit (Spec.map φ) := by
    have hc := IdealSheafDataModule.closedImmersionModuleToKernel_comp (Spec.map φ)
    change e.hom ≫ IdealSheafDataModule.closedImmersionKernelModuleToUnit
      (Spec.map φ) = IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ) at hc
    calc
      e.inv ≫ IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ) =
        e.inv ≫ (e.hom ≫ IdealSheafDataModule.closedImmersionKernelModuleToUnit
          (Spec.map φ)) := by rw [hc]
      _ = IdealSheafDataModule.closedImmersionKernelModuleToUnit (Spec.map φ) := by simp
  change ((affineQuotientIdealTildeClosedImmersionKernelIso I ≪≫ e.symm).hom ≫
      IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ)) = _
  change ((affineQuotientIdealTildeClosedImmersionKernelIso I).hom ≫ e.inv) ≫
      IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ) = _
  calc
    ((affineQuotientIdealTildeClosedImmersionKernelIso I).hom ≫ e.inv) ≫
        IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ) =
      (affineQuotientIdealTildeClosedImmersionKernelIso I).hom ≫
        (e.inv ≫ IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ)) :=
          Category.assoc _ _ _
    _ = (affineQuotientIdealTildeClosedImmersionKernelIso I).hom ≫
        IdealSheafDataModule.closedImmersionKernelModuleToUnit (Spec.map φ) :=
          congrArg (fun h => (affineQuotientIdealTildeClosedImmersionKernelIso I).hom ≫ h) he
    _ = _ := affineQuotientIdealTildeClosedImmersionKernelIso_hom_ι I

end PfaffianDescent
