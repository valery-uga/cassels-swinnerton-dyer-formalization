import PfaffianDescent.AffineGammaPushforward

/-! # The actual affine structure-sheaf quotient in module coordinates -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

section
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

def cubicPointTraceFieldBaseChangeAffineResidueModule : ModuleCat R :=
  (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)

def cubicPointTraceFieldBaseChangeAffineModuleQuotient :
    ModuleCat.of R R ⟶ cubicPointTraceFieldBaseChangeAffineResidueModule φ :=
  @ModuleCat.ofHom R _ R (cubicPointTraceFieldBaseChangeAffineResidueModule φ) _ _ _
    (ModuleCat.isModule (cubicPointTraceFieldBaseChangeAffineResidueModule φ)) {
      toFun := φ
      map_add' := map_add _
      map_smul' := fun r s => by
        change φ (r * s) = φ r * φ s
        exact map_mul φ r s }

def cubicPointTraceFieldBaseChangeAffinePushforward : (Spec (.of R)).Modules :=
  (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))).obj
    (SheafOfModules.unit (Spec (.of S)).ringCatSheaf)

def cubicPointTraceFieldBaseChangeAffinePushforwardGammaIso :
    (moduleSpecΓFunctor (R := .of R)).obj
      (cubicPointTraceFieldBaseChangeAffinePushforward φ) ≅
        cubicPointTraceFieldBaseChangeAffineResidueModule φ :=
  ((affineGammaPushforwardNatIso (CommRingCat.ofHom φ)).app
      (SheafOfModules.unit (Spec (.of S)).ringCatSheaf)) ≪≫
    (ModuleCat.restrictScalars φ).mapIso
      (affineGlobalSectionsUnitLinearEquiv (A := S)).toModuleIso

instance cubicPointTraceFieldBaseChangeAffinePushforward_fromTilde_isIso :
    IsIso (Scheme.Modules.fromTildeΓ (R := .of R)
      (cubicPointTraceFieldBaseChangeAffinePushforward φ)) := by
  have hunit : IsIso (Scheme.Modules.fromTildeΓ (R := .of S)
      (SheafOfModules.unit (Spec (.of S)).ringCatSheaf)) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  exact @isIso_fromTildeΓ_pushforward (.of R) (.of S) (CommRingCat.ofHom φ)
    (SheafOfModules.unit (Spec (.of S)).ringCatSheaf) hunit

def cubicPointTraceFieldBaseChangeAffineTildeIso :
    (tilde.functor (.of R)).obj
      (cubicPointTraceFieldBaseChangeAffineResidueModule φ) ≅
        cubicPointTraceFieldBaseChangeAffinePushforward φ :=
  (tilde.functor (.of R)).mapIso
      (cubicPointTraceFieldBaseChangeAffinePushforwardGammaIso φ).symm ≪≫
    asIso (Scheme.Modules.fromTildeΓ (R := .of R)
      (cubicPointTraceFieldBaseChangeAffinePushforward φ))

theorem cubicPointTraceFieldBaseChangeAffineTildeIso_quotient :
    (tilde.functor (.of R)).map
        (cubicPointTraceFieldBaseChangeAffineModuleQuotient φ) ≫
      (cubicPointTraceFieldBaseChangeAffineTildeIso φ).hom =
    (affineGlobalSectionsUnitTildeIso (A := R)).hom ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (Spec.map (CommRingCat.ofHom φ)) := by
  let F := tilde.functor (.of R)
  let G := moduleSpecΓFunctor (R := .of R)
  let M := cubicPointTraceFieldBaseChangeAffinePushforward φ
  let O := SheafOfModules.unit (Spec (.of R)).ringCatSheaf
  let q : O ⟶ M := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
    (Spec.map (CommRingCat.ofHom φ))
  let eO := (affineGlobalSectionsUnitLinearEquiv (A := R)).toModuleIso
  let eM := cubicPointTraceFieldBaseChangeAffinePushforwardGammaIso φ
  let m := cubicPointTraceFieldBaseChangeAffineModuleQuotient φ
  have hgamma : eO.inv ≫ G.map q ≫ eM.hom = m := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact affineCanonicalUnitGlobalSections φ t
  have hgamma' : m ≫ eM.inv = eO.inv ≫ G.map q := by
    rw [← hgamma]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hnat : F.map (G.map q) ≫ Scheme.Modules.fromTildeΓ (R := .of R) M =
      Scheme.Modules.fromTildeΓ (R := .of R) O ≫ q :=
    (tilde.adjunction (R := .of R)).counit.naturality q
  change F.map m ≫ (F.map eM.inv ≫ Scheme.Modules.fromTildeΓ (R := .of R) M) =
    (F.map eO.inv ≫ Scheme.Modules.fromTildeΓ (R := .of R) O) ≫ q
  rw [← Category.assoc, ← F.map_comp, hgamma', F.map_comp, Category.assoc]
  exact (congrArg (fun t => F.map eO.inv ≫ t) hnat).trans
    (Category.assoc _ _ _).symm

end
end PfaffianDescent
