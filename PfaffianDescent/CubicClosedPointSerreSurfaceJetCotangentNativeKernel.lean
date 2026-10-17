import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernelGlobal

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreSurfaceJetCotangent_nativePushforwardUnit_fromTildeΓ_isIso
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of B :=
      CommRingCat.ofHom g
    IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A)
      ((Scheme.Modules.pushforward (Spec.map φ)).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))) := by
  dsimp only
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of B)
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  exact isIso_fromTildeΓ_pushforward
    (φ := CommRingCat.ofHom g)
    (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)


noncomputable def cubicClosedPointSerreSurfaceJetCotangent_nativeClosedImmersionKernelFromTildeGammaIso
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of B :=
      CommRingCat.ofHom g
    let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ)
    (tilde.functor (CommRingCat.of A)).obj
      (kernel (moduleSpecΓFunctor.map q)) ≅
        IdealSheafDataModule.closedImmersionKernelModule (Spec.map φ) := by
  dsimp only
  let φ : CommRingCat.of A ⟶ CommRingCat.of B :=
    CommRingCat.ofHom g
  let O := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  let T := (Scheme.Modules.pushforward (Spec.map φ)).obj
    (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) O) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) T) :=
    cubicClosedPointSerreSurfaceJetCotangent_nativePushforwardUnit_fromTildeΓ_isIso g
  exact affineKernelFromTildeGammaIso
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ))


noncomputable def cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionKernelIso
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of B :=
      CommRingCat.ofHom g
    (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A (RingHom.ker g)) ≅
      IdealSheafDataModule.closedImmersionKernelModule (Spec.map φ) := by
  dsimp only
  exact (tilde.functor (CommRingCat.of A)).mapIso
      (cubicClosedPointSerreSurfaceJetCotangent_nativeGlobalKernelModuleIsoIdeal g).symm ≪≫
    cubicClosedPointSerreSurfaceJetCotangent_nativeClosedImmersionKernelFromTildeGammaIso g


theorem cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionKernelIso_hom_ι
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) :
    let φ : CommRingCat.of A ⟶ CommRingCat.of B :=
      CommRingCat.ofHom g
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionKernelIso g).hom ≫
      IdealSheafDataModule.closedImmersionKernelModuleToUnit (Spec.map φ) =
        (tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom (RingHom.ker g).subtype) ≫
          (affineGlobalSectionsUnitTildeIso (A := A)).hom := by
  dsimp only
  let R := CommRingCat.of A
  let F := tilde.functor R
  let G := moduleSpecΓFunctor (R := R)
  let φ : R ⟶ CommRingCat.of B :=
    CommRingCat.ofHom g
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Spec.map φ)
  let O := SheafOfModules.unit (Spec R).ringCatSheaf
  let T := (Scheme.Modules.pushforward (Spec.map φ)).obj
    (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
  let eK := cubicClosedPointSerreSurfaceJetCotangent_nativeGlobalKernelModuleIsoIdeal g
  let eU := (affineGlobalSectionsUnitLinearEquiv (A := A)).toModuleIso
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := R) O) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := R) T) :=
    cubicClosedPointSerreSurfaceJetCotangent_nativePushforwardUnit_fromTildeΓ_isIso g
  letI hO : IsIso ((tilde.adjunction (R := R)).counit.app O) := by
    change IsIso (Scheme.Modules.fromTildeΓ (R := R) O)
    infer_instance
  have hglob : eK.hom ≫ ModuleCat.ofHom (RingHom.ker g).subtype =
      kernel.ι (G.map q) ≫ eU.hom :=
    cubicClosedPointSerreSurfaceJetCotangent_nativeGlobalKernelModuleIsoIdeal_hom_subtype g
  have hglob' : eK.inv ≫ kernel.ι (G.map q) =
      ModuleCat.ofHom (RingHom.ker g).subtype ≫ eU.inv := by
    apply (eK.inv_comp_eq).2
    simpa only [Category.assoc] using ((eU.comp_inv_eq).2 hglob).symm
  have hK := affineKernelFromTildeGammaIso_hom_ι q
  change (F.mapIso eK.symm ≪≫
      cubicClosedPointSerreSurfaceJetCotangent_nativeClosedImmersionKernelFromTildeGammaIso g).hom ≫ kernel.ι q =
    F.map (ModuleCat.ofHom (RingHom.ker g).subtype) ≫
      (F.mapIso eU.symm ≪≫
        asIso ((tilde.adjunction (R := R)).counit.app O)).hom
  change (F.map eK.inv ≫
      (cubicClosedPointSerreSurfaceJetCotangent_nativeClosedImmersionKernelFromTildeGammaIso g).hom) ≫ kernel.ι q =
    F.map (ModuleCat.ofHom (RingHom.ker g).subtype) ≫
      (F.map eU.inv ≫ Scheme.Modules.fromTildeΓ (R := R) O)
  calc
    (F.map eK.inv ≫ (cubicClosedPointSerreSurfaceJetCotangent_nativeClosedImmersionKernelFromTildeGammaIso g).hom) ≫
        kernel.ι q =
      F.map eK.inv ≫
        ((cubicClosedPointSerreSurfaceJetCotangent_nativeClosedImmersionKernelFromTildeGammaIso g).hom ≫ kernel.ι q) :=
          Category.assoc _ _ _
    _ = F.map eK.inv ≫
        (F.map (kernel.ι (G.map q)) ≫ Scheme.Modules.fromTildeΓ (R := R) O) :=
          congrArg (fun h => F.map eK.inv ≫ h) hK
    _ = F.map (eK.inv ≫ kernel.ι (G.map q)) ≫
        Scheme.Modules.fromTildeΓ (R := R) O :=
          (congrArg (fun h => h ≫ Scheme.Modules.fromTildeΓ (R := R) O)
            (F.map_comp eK.inv (kernel.ι (G.map q)))).symm
    _ = F.map (ModuleCat.ofHom (RingHom.ker g).subtype ≫ eU.inv) ≫
        Scheme.Modules.fromTildeΓ (R := R) O := by rw [hglob']
    _ = F.map (ModuleCat.ofHom (RingHom.ker g).subtype) ≫ F.map eU.inv ≫
        Scheme.Modules.fromTildeΓ (R := R) O := by
          calc
            F.map (ModuleCat.ofHom (RingHom.ker g).subtype ≫ eU.inv) ≫
                Scheme.Modules.fromTildeΓ (R := R) O =
              (F.map (ModuleCat.ofHom (RingHom.ker g).subtype) ≫ F.map eU.inv) ≫
                Scheme.Modules.fromTildeΓ (R := R) O := by
                  rw [F.map_comp]
            _ = _ := Category.assoc _ _ _


noncomputable def cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionModuleIso
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) 
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))] :
    let φ : CommRingCat.of A ⟶ CommRingCat.of B :=
      CommRingCat.ofHom g
    (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A (RingHom.ker g)) ≅
      IdealSheafDataModule.closedImmersionModule (Spec.map φ) := by
  dsimp only
  exact cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionKernelIso g ≪≫
    (IdealSheafDataModule.closedImmersionModuleToKernelIso
      (Spec.map (CommRingCat.ofHom g))).symm


theorem cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionModuleIso_hom_toUnit
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) 
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))] :
    let φ : CommRingCat.of A ⟶ CommRingCat.of B :=
      CommRingCat.ofHom g
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionModuleIso g).hom ≫
      IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ) =
        (tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom (RingHom.ker g).subtype) ≫
          (affineGlobalSectionsUnitTildeIso (A := A)).hom := by
  dsimp only
  let φ : CommRingCat.of A ⟶ CommRingCat.of B :=
    CommRingCat.ofHom g
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
  change ((cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionKernelIso g ≪≫ e.symm).hom ≫
      IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ)) = _
  change ((cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionKernelIso g).hom ≫ e.inv) ≫
      IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ) = _
  calc
    ((cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionKernelIso g).hom ≫ e.inv) ≫
        IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ) =
      (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionKernelIso g).hom ≫
        (e.inv ≫ IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ)) :=
          Category.assoc _ _ _
    _ = (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionKernelIso g).hom ≫
        IdealSheafDataModule.closedImmersionKernelModuleToUnit (Spec.map φ) :=
          congrArg (fun h => (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionKernelIso g).hom ≫ h) he
    _ = _ := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealTildeClosedImmersionKernelIso_hom_ι g


end PfaffianDescent
