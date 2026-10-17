import PfaffianDescent.CorayAffineSheafCokernelSections
import PfaffianDescent.CorayLocalNormalizationDefect
import PfaffianDescent.AffineGammaPushforward

/-! Actual affine normalization quotient sheaf and literal defect sections.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (A : Type u) [CommRing A] [IsDomain A]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual affine integral-closure normalization morphism. -/
def affineIntegralClosureNormalization :
    Spec (CommRingCat.of (integralClosure A (FractionRing A))) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A))))

/-- The original structure-sheaf map into the actual affine normalization
pushforward. Its component is the original normalization section-ring map. -/
def affineNormalizationUnitToPushforwardUnit :
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ⟶
      (Scheme.Modules.pushforward (affineIntegralClosureNormalization A)).obj
        (SheafOfModules.unit
          (Spec (CommRingCat.of (integralClosure A (FractionRing A)))).ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit (affineIntegralClosureNormalization A).toRingCatSheafHom

/-- The actual quotient SHEAF, not merely the quotient of global sections. -/
def affineNormalizationQuotientSheaf : (Spec (CommRingCat.of A)).Modules :=
  cokernel (affineNormalizationUnitToPushforwardUnit A)

/-- Actual global sections of the normalization pushforward, with their
ORIGINAL A-module structure, identify with the actual integral closure. -/
def affineNormalizationPushforwardSectionsIso :
    (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      ((Scheme.Modules.pushforward (affineIntegralClosureNormalization A)).obj
        (SheafOfModules.unit
          (Spec (CommRingCat.of (integralClosure A (FractionRing A)))).ringCatSheaf)) ≅
      ModuleCat.of A (integralClosure A (FractionRing A)) := by
  let eIC :
      (moduleSpecΓFunctor (R := CommRingCat.of (integralClosure A (FractionRing A)))).obj
        (SheafOfModules.unit
          (Spec (CommRingCat.of (integralClosure A (FractionRing A)))).ringCatSheaf) ≅
      ModuleCat.of (integralClosure A (FractionRing A))
        (integralClosure A (FractionRing A)) :=
    (affineGlobalSectionsUnitLinearEquiv
      (A := integralClosure A (FractionRing A))).toModuleIso
  let eScalar :
      (ModuleCat.restrictScalars
        (algebraMap A (integralClosure A (FractionRing A)))).obj
        (ModuleCat.of (integralClosure A (FractionRing A))
          (integralClosure A (FractionRing A))) ≃ₗ[A]
      integralClosure A (FractionRing A) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => by
        let y : integralClosure A (FractionRing A) := x
        change (algebraMap A (integralClosure A (FractionRing A)) a) * y = a • y
        exact (Algebra.smul_def a y).symm }
  exact (affineGammaPushforwardNatIso
    (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A))))).app _ ≪≫
    (ModuleCat.restrictScalars
      (algebraMap A (integralClosure A (FractionRing A)))).mapIso eIC ≪≫
    eScalar.toModuleIso

/-- The section comparison retains the actual original algebra inclusion. -/
theorem affineNormalizationUnit_sections_comp :
    (moduleSpecΓFunctor (R := CommRingCat.of A)).map
      (affineNormalizationUnitToPushforwardUnit A) ≫
        (affineNormalizationPushforwardSectionsIso A).hom =
      (affineGlobalSectionsUnitLinearEquiv (A := A)).toModuleIso.hom ≫
        ModuleCat.ofHom (Algebra.linearMap A (integralClosure A (FractionRing A))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  dsimp only [affineNormalizationPushforwardSectionsIso, Iso.trans_hom,
    Functor.mapIso_hom]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  change (Scheme.ΓSpecIso
      (CommRingCat.of (integralClosure A (FractionRing A)))).hom.hom
    ((Spec.map (CommRingCat.ofHom
      (algebraMap A (integralClosure A (FractionRing A))))).appTop.hom x) =
    algebraMap A (integralClosure A (FractionRing A))
      ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x)
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A))))) x

/-- ACTUAL sections of the ACTUAL quotient SHEAF identify with the literal
IC(A,Frac(A))/A module. Affine exactness is proved by the tilde counit,
cokernel preservation and tilde.isoTop, not assumed as a certificate. -/
def affineNormalizationQuotientSheaf_sectionsIso :
    (moduleSpecΓFunctor (R := CommRingCat.of A)).obj (affineNormalizationQuotientSheaf A) ≅
      ModuleCat.of A (localNormalizationDefect A (FractionRing A)) := by
  let G := moduleSpecΓFunctor (R := CommRingCat.of A)
  let O : (Spec (CommRingCat.of A)).Modules :=
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  let N : (Spec (CommRingCat.of A)).Modules :=
    (Scheme.Modules.pushforward (affineIntegralClosureNormalization A)).obj
      (SheafOfModules.unit
        (Spec (CommRingCat.of (integralClosure A (FractionRing A)))).ringCatSheaf)
  let q : O ⟶ N := affineNormalizationUnitToPushforwardUnit A
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) O) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  letI : IsIso (Scheme.Modules.fromTildeΓ
      (R := CommRingCat.of (integralClosure A (FractionRing A)))
      (SheafOfModules.unit
        (Spec (CommRingCat.of (integralClosure A (FractionRing A)))).ringCatSheaf)) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) N) :=
    isIso_fromTildeΓ_pushforward
      (φ := CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A))))
      (SheafOfModules.unit
        (Spec (CommRingCat.of (integralClosure A (FractionRing A)))).ringCatSheaf)
  let eA : G.obj O ≅ ModuleCat.of A A :=
    (affineGlobalSectionsUnitLinearEquiv (A := A)).toModuleIso
  let eB : G.obj N ≅ ModuleCat.of A (integralClosure A (FractionRing A)) :=
    affineNormalizationPushforwardSectionsIso A
  let g : ModuleCat.of A A ⟶ ModuleCat.of A (integralClosure A (FractionRing A)) :=
    ModuleCat.ofHom (Algebra.linearMap A (integralClosure A (FractionRing A)))
  have hq : G.map q ≫ eB.hom = eA.hom ≫ g :=
    affineNormalizationUnit_sections_comp A
  let e₁ : G.obj (cokernel q) ≅ cokernel (G.map q) :=
    affineSheafCokernelSectionsIso (R := CommRingCat.of A) (M := O) (N := N) q
  let e₂ : cokernel (G.map q) ≅ cokernel g :=
    cokernel.mapIso (G.map q) g eA eB hq
  let e₃ : cokernel g ≅ ModuleCat.of A (localNormalizationDefect A (FractionRing A)) :=
    ModuleCat.cokernelIsoRangeQuotient g
  change G.obj (cokernel q) ≅ ModuleCat.of A (localNormalizationDefect A (FractionRing A))
  exact e₁ ≪≫ e₂ ≪≫ e₃

/-- The comparison of actual quotient-sheaf sections preserves the literal
projection to the original integral-closure quotient. -/
theorem affineNormalizationQuotientSheaf_sectionsIso_π :
    (moduleSpecΓFunctor (R := CommRingCat.of A)).map
      (cokernel.π (affineNormalizationUnitToPushforwardUnit A)) ≫
        (affineNormalizationQuotientSheaf_sectionsIso A).hom =
      (affineNormalizationPushforwardSectionsIso A).hom ≫
        ModuleCat.ofHom
          (LinearMap.range (Algebra.linearMap A (integralClosure A (FractionRing A)))).mkQ := by
  let G := moduleSpecΓFunctor (R := CommRingCat.of A)
  let O : (Spec (CommRingCat.of A)).Modules :=
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  let N : (Spec (CommRingCat.of A)).Modules :=
    (Scheme.Modules.pushforward (affineIntegralClosureNormalization A)).obj
      (SheafOfModules.unit
        (Spec (CommRingCat.of (integralClosure A (FractionRing A)))).ringCatSheaf)
  let q : O ⟶ N := affineNormalizationUnitToPushforwardUnit A
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) O) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  letI : IsIso (Scheme.Modules.fromTildeΓ
      (R := CommRingCat.of (integralClosure A (FractionRing A)))
      (SheafOfModules.unit
        (Spec (CommRingCat.of (integralClosure A (FractionRing A)))).ringCatSheaf)) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) N) :=
    isIso_fromTildeΓ_pushforward
      (φ := CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A))))
      (SheafOfModules.unit
        (Spec (CommRingCat.of (integralClosure A (FractionRing A)))).ringCatSheaf)
  let eA : G.obj O ≅ ModuleCat.of A A :=
    (affineGlobalSectionsUnitLinearEquiv (A := A)).toModuleIso
  let eB : G.obj N ≅ ModuleCat.of A (integralClosure A (FractionRing A)) :=
    affineNormalizationPushforwardSectionsIso A
  let g : ModuleCat.of A A ⟶ ModuleCat.of A (integralClosure A (FractionRing A)) :=
    ModuleCat.ofHom (Algebra.linearMap A (integralClosure A (FractionRing A)))
  have hq : G.map q ≫ eB.hom = eA.hom ≫ g :=
    affineNormalizationUnit_sections_comp A
  let e₁ : G.obj (cokernel q) ≅ cokernel (G.map q) :=
    affineSheafCokernelSectionsIso (R := CommRingCat.of A) (M := O) (N := N) q
  let e₂ : cokernel (G.map q) ≅ cokernel g :=
    cokernel.mapIso (G.map q) g eA eB hq
  let e₃ : cokernel g ≅ ModuleCat.of A (localNormalizationDefect A (FractionRing A)) :=
    ModuleCat.cokernelIsoRangeQuotient g
  have h₁ : G.map (cokernel.π q) ≫ e₁.hom = cokernel.π (G.map q) :=
    affineSheafCokernelSectionsIso_π (R := CommRingCat.of A) (M := O) (N := N) q
  have h₂ : cokernel.π (G.map q) ≫ e₂.hom = eB.hom ≫ cokernel.π g :=
    cokernel.π_desc _ _ _
  have h₃ : cokernel.π g ≫ e₃.hom =
      ModuleCat.ofHom
        (LinearMap.range (Algebra.linearMap A (integralClosure A (FractionRing A)))).mkQ :=
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom g
  change G.map (cokernel.π q) ≫ (e₁ ≪≫ e₂ ≪≫ e₃).hom =
    eB.hom ≫ ModuleCat.ofHom
      (LinearMap.range (Algebra.linearMap A (integralClosure A (FractionRing A)))).mkQ
  simp only [Iso.trans_hom]
  rw [← Category.assoc, ← Category.assoc, h₁, h₂, Category.assoc, h₃]

/-- The constructed affine quotient-section identification also preserves
any ORIGINAL ground algebra K→A, by actual restriction of scalars. -/
def affineNormalizationQuotientSheaf_groundSectionsIso
    (K : Type u) [CommRing K] [Algebra K A] :
    (ModuleCat.restrictScalars (algebraMap K A)).obj
      ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj (affineNormalizationQuotientSheaf A)) ≅
    (ModuleCat.restrictScalars (algebraMap K A)).obj
      (ModuleCat.of A (localNormalizationDefect A (FractionRing A))) :=
  (ModuleCat.restrictScalars (algebraMap K A)).mapIso
    (affineNormalizationQuotientSheaf_sectionsIso A)

end PfaffianDescent.Coray
