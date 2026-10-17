import PfaffianDescent.ThreeQuadricTwistedEntryNaturality

/-! SOURCE ONLY / UNVERIFIED. The native positive/zero-negative fraction
pairing is the actual tensor-unit identification. This fixes the possible
unit normalization in the induced H0 map internally. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open scoped DirectSum Pointwise TensorProduct
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
universe u
-- Concrete production feedback: actual Proj/sheaf/site aliases obstruct matching.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Abstract categorical precursor: prove the adjunction composition before
specializing the scalar/site dictionaries of actual scheme modules. -/
private theorem mappedRawRelationToAdjoint
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X Y Z : C} {W : D}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ G.obj W) (d : X ⟶ G.obj W)
    (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z)
    (h : F.obj Z ⟶ W) (k : F.obj X ⟶ W)
    (hf : f = F.map a) (hg : g = F.map b)
    (hh : h = (adj.homEquiv Z W).symm c)
    (hk : k = F.map d ≫ adj.counit.app W)
    (hraw : a ≫ b ≫ c = d) : f ≫ g ≫ h = k := by
  subst f
  subst g
  subst h
  subst k
  change F.map a ≫ F.map b ≫ (F.map c ≫ adj.counit.app W) =
    F.map d ≫ adj.counit.app W
  calc
    _ = (F.map a ≫ F.map b ≫ F.map c) ≫ adj.counit.app W := by
      simp only [Category.assoc]
    _ = F.map (a ≫ b ≫ c) ≫ adj.counit.app W := by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    _ = _ := congrArg (fun z => F.map z ≫ adj.counit.app W) hraw

/-- Only one mapped composite is specialized at a time. -/
private theorem mappedCompositeToAdjoint
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X Y Z : C} {W : D} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ G.obj W) :
    F.map (a ≫ b) ≫ (adj.homEquiv Z W).symm c =
      F.map (a ≫ b ≫ c) ≫ adj.counit.app W := by
  change F.map (a ≫ b) ≫ (F.map c ≫ adj.counit.app W) = _
  calc
    _ = (F.map (a ≫ b) ≫ F.map c) ≫ adj.counit.app W :=
      (Category.assoc _ _ _).symm
    _ = F.map ((a ≫ b) ≫ c) ≫ adj.counit.app W :=
      congrArg (fun f => f ≫ adj.counit.app W) (F.map_comp (a ≫ b) c).symm
    _ = _ := congrArg (fun f => F.map f ≫ adj.counit.app W) (Category.assoc a b c)

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Each actual map presentation is checked independently; no result about
unit normalization is assumed at the native categorical caller. -/
private theorem nativeUnitTensorMapPresentation :
    letI : MonoidalCategory (PresheafOfModules (Proj 𝒜).ringCatSheaf.obj) :=
      PresheafOfModules.monoidalCategory
    schemeModuleTensorMap (unitToZeroTwist 𝒜) (𝟙 (positiveSheafOfModules 𝒜 3)) =
      (PresheafOfModules.sheafification (𝟙 (Proj 𝒜).ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (unitToZeroTwist 𝒜).val
          (𝟙 (positiveModulePresheaf 𝒜 3))) := by
  exact schemeModuleTensorMap_eq_sheafification _ _

private theorem nativeUnitSymmetryPresentation :
    letI : MonoidalCategory (PresheafOfModules (Proj 𝒜).ringCatSheaf.obj) :=
      PresheafOfModules.monoidalCategory
    letI : SymmetricCategory (PresheafOfModules (Proj 𝒜).ringCatSheaf.obj) :=
      PresheafOfModules.symmetricCategory
    (schemeModuleTensorSymmetry (sheafOfModules 𝒜 0)
      (positiveSheafOfModules 𝒜 3)).hom =
      (PresheafOfModules.sheafification (𝟙 (Proj 𝒜).ringCatSheaf.obj)).map
        (β_ (modulePresheaf 𝒜 0) (positiveModulePresheaf 𝒜 3)).hom := by
  rfl

private theorem nativeUnitDifferencePairingPresentation :
    positiveNegativePositiveDifferencePairing 𝒜 3 0 (by decide) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Proj 𝒜).ringCatSheaf.obj)).homEquiv
        (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 3).val
          (sheafOfModules 𝒜 0).val) (positiveSheafOfModules 𝒜 3)).symm
        (positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 0 (by decide)) := by
  rfl

private theorem nativeUnitLeftIsoPresentation :
    (schemeModuleTensorUnitLeftIso (positiveSheafOfModules 𝒜 3)).hom =
      (PresheafOfModules.sheafification (𝟙 (Proj 𝒜).ringCatSheaf.obj)).map
        (schemeModuleTensorUnitLeftRawIso (positiveSheafOfModules 𝒜 3)).hom ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Proj 𝒜).ringCatSheaf.obj)).counit.app (positiveSheafOfModules 𝒜 3) := by
  rfl

/-- Actual tensor map followed by actual symmetry, as ONE mapped raw map. -/
private theorem nativeUnitTensorSymmetryComposite :
    letI : MonoidalCategory (PresheafOfModules (Proj 𝒜).ringCatSheaf.obj) :=
      PresheafOfModules.monoidalCategory
    letI : SymmetricCategory (PresheafOfModules (Proj 𝒜).ringCatSheaf.obj) :=
      PresheafOfModules.symmetricCategory
    schemeModuleTensorMap (unitToZeroTwist 𝒜) (𝟙 (positiveSheafOfModules 𝒜 3)) ≫
      (schemeModuleTensorSymmetry (sheafOfModules 𝒜 0)
        (positiveSheafOfModules 𝒜 3)).hom =
      (PresheafOfModules.sheafification (𝟙 (Proj 𝒜).ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (unitToZeroTwist 𝒜).val
          (𝟙 (positiveModulePresheaf 𝒜 3)) ≫
          (β_ (modulePresheaf 𝒜 0) (positiveModulePresheaf 𝒜 3)).hom) := by
  letI : MonoidalCategory (PresheafOfModules (Proj 𝒜).ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  letI : SymmetricCategory (PresheafOfModules (Proj 𝒜).ringCatSheaf.obj) :=
    PresheafOfModules.symmetricCategory
  let F := PresheafOfModules.sheafification (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  calc
    _ = F.map (PresheafOfModules.Monoidal.tensorHom (unitToZeroTwist 𝒜).val
          (𝟙 (positiveModulePresheaf 𝒜 3))) ≫
        F.map (β_ (modulePresheaf 𝒜 0) (positiveModulePresheaf 𝒜 3)).hom :=
      congrArg₂ (fun f g => f ≫ g)
        (nativeUnitTensorMapPresentation 𝒜) (nativeUnitSymmetryPresentation 𝒜)
    _ = _ := (F.map_comp _ _).symm

/-- Composing that ONE mapped raw map with the actual adjoint pairing. -/
private theorem nativeUnitPairingComposite :
    letI : MonoidalCategory (PresheafOfModules (Proj 𝒜).ringCatSheaf.obj) :=
      PresheafOfModules.monoidalCategory
    letI : SymmetricCategory (PresheafOfModules (Proj 𝒜).ringCatSheaf.obj) :=
      PresheafOfModules.symmetricCategory
    (PresheafOfModules.sheafification (𝟙 (Proj 𝒜).ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (unitToZeroTwist 𝒜).val
          (𝟙 (positiveModulePresheaf 𝒜 3)) ≫
          (β_ (modulePresheaf 𝒜 0) (positiveModulePresheaf 𝒜 3)).hom) ≫
      positiveNegativePositiveDifferencePairing 𝒜 3 0 (by decide) =
      (PresheafOfModules.sheafification (𝟙 (Proj 𝒜).ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (unitToZeroTwist 𝒜).val
          (𝟙 (positiveModulePresheaf 𝒜 3)) ≫
          (β_ (modulePresheaf 𝒜 0) (positiveModulePresheaf 𝒜 3)).hom ≫
          positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 0 (by decide)) ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Proj 𝒜).ringCatSheaf.obj)).counit.app (positiveSheafOfModules 𝒜 3) := by
  letI : MonoidalCategory (PresheafOfModules (Proj 𝒜).ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  letI : SymmetricCategory (PresheafOfModules (Proj 𝒜).ringCatSheaf.obj) :=
    PresheafOfModules.symmetricCategory
  let F := PresheafOfModules.sheafification (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  let a := PresheafOfModules.Monoidal.tensorHom (unitToZeroTwist 𝒜).val
    (𝟙 (positiveModulePresheaf 𝒜 3))
  let b := (β_ (modulePresheaf 𝒜 0) (positiveModulePresheaf 𝒜 3)).hom
  let c := positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 0 (by decide)
  exact (congrArg (fun h => F.map (a ≫ b) ≫ h)
    (nativeUnitDifferencePairingPresentation 𝒜)).trans
      (mappedCompositeToAdjoint (W := positiveSheafOfModules 𝒜 3) adj a b c)

/-- The raw degree-zero fraction inclusion, the raw tensor symmetry, and
fraction pairing are the literal left unit scalar multiplication. -/
theorem threePositiveZeroNegativePairing_raw_unit :
    letI : MonoidalCategory (PresheafOfModules (Proj 𝒜).ringCatSheaf.obj) :=
      PresheafOfModules.monoidalCategory
    letI : SymmetricCategory (PresheafOfModules (Proj 𝒜).ringCatSheaf.obj) :=
      PresheafOfModules.symmetricCategory
    PresheafOfModules.Monoidal.tensorHom (unitToZeroTwist 𝒜).val
      (𝟙 (positiveModulePresheaf 𝒜 3)) ≫
        (β_ (modulePresheaf 𝒜 0) (positiveModulePresheaf 𝒜 3)).hom ≫
          positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 0 (by decide) =
      (schemeModuleTensorUnitLeftRawIso (positiveSheafOfModules 𝒜 3)).hom := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro r p
  apply Subtype.ext
  funext x
  change p.1 x * (r.1 x).val = (r.1 x).val * p.1 x
  ring

/-- The native pairing has exactly the tensor-unit normalization, proved
by the genuine sheafification adjunction and the raw fraction formula. -/
theorem threePositiveZeroNegativePairing_unit :
    schemeModuleTensorMap (unitToZeroTwist 𝒜) (𝟙 (positiveSheafOfModules 𝒜 3)) ≫
      (schemeModuleTensorSymmetry (sheafOfModules 𝒜 0)
        (positiveSheafOfModules 𝒜 3)).hom ≫
      positiveNegativePositiveDifferencePairing 𝒜 3 0 (by decide) =
        (schemeModuleTensorUnitLeftIso (positiveSheafOfModules 𝒜 3)).hom := by
  let F := PresheafOfModules.sheafification (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  letI : MonoidalCategory (PresheafOfModules (Proj 𝒜).ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  letI : SymmetricCategory (PresheafOfModules (Proj 𝒜).ringCatSheaf.obj) :=
    PresheafOfModules.symmetricCategory
  let a := PresheafOfModules.Monoidal.tensorHom (unitToZeroTwist 𝒜).val
    (𝟙 (positiveModulePresheaf 𝒜 3))
  let b := (β_ (modulePresheaf 𝒜 0) (positiveModulePresheaf 𝒜 3)).hom
  let c := positiveNegativePositiveDifferencePairingPresheaf 𝒜 3 0 (by decide)
  let d := (schemeModuleTensorUnitLeftRawIso (positiveSheafOfModules 𝒜 3)).hom
  have hraw : a ≫ b ≫ c = d := threePositiveZeroNegativePairing_raw_unit 𝒜
  calc
    _ = F.map (a ≫ b) ≫ positiveNegativePositiveDifferencePairing 𝒜 3 0 (by decide) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ positiveNegativePositiveDifferencePairing 𝒜 3 0 (by decide))
          (nativeUnitTensorSymmetryComposite 𝒜))
    _ = F.map (a ≫ b ≫ c) ≫ adj.counit.app (positiveSheafOfModules 𝒜 3) :=
      nativeUnitPairingComposite 𝒜
    _ = F.map d ≫ adj.counit.app (positiveSheafOfModules 𝒜 3) :=
      congrArg (fun z => F.map z ≫ adj.counit.app (positiveSheafOfModules 𝒜 3)) hraw
    _ = _ := (nativeUnitLeftIsoPresentation 𝒜).symm

/-- Removing the degree-zero fraction inclusion gives the exact native
zero-negative pairing in the opposite order. -/
theorem threePositiveZeroNegativePairing_eq_unit :
    (schemeModuleTensorSymmetry (sheafOfModules 𝒜 0)
      (positiveSheafOfModules 𝒜 3)).hom ≫
        positiveNegativePositiveDifferencePairing 𝒜 3 0 (by decide) =
      schemeModuleTensorMap (unitIsoZeroTwist 𝒜).inv
        (𝟙 (positiveSheafOfModules 𝒜 3)) ≫
        (schemeModuleTensorUnitLeftIso (positiveSheafOfModules 𝒜 3)).hom := by
  letI : IsIso (schemeModuleTensorMap (unitIsoZeroTwist 𝒜).hom
      (𝟙 (positiveSheafOfModules 𝒜 3))) :=
    (schemeModuleTensorMapIso (unitIsoZeroTwist 𝒜)
      (Iso.refl (positiveSheafOfModules 𝒜 3))).isIso_hom
  have hCancel :
      schemeModuleTensorMap (unitIsoZeroTwist 𝒜).hom
          (𝟙 (positiveSheafOfModules 𝒜 3)) ≫
        schemeModuleTensorMap (unitIsoZeroTwist 𝒜).inv
          (𝟙 (positiveSheafOfModules 𝒜 3)) =
      𝟙 (schemeModuleTensor (SheafOfModules.unit (Proj 𝒜).ringCatSheaf)
        (positiveSheafOfModules 𝒜 3)) := by
    calc
      _ = schemeModuleTensorMap
          ((unitIsoZeroTwist 𝒜).hom ≫ (unitIsoZeroTwist 𝒜).inv)
          ((𝟙 (positiveSheafOfModules 𝒜 3)) ≫
            (𝟙 (positiveSheafOfModules 𝒜 3))) :=
        schemeModuleTensorMap_comp (unitIsoZeroTwist 𝒜).hom
          (𝟙 (positiveSheafOfModules 𝒜 3)) (unitIsoZeroTwist 𝒜).inv
          (𝟙 (positiveSheafOfModules 𝒜 3))
      _ = schemeModuleTensorMap
          (𝟙 (SheafOfModules.unit (Proj 𝒜).ringCatSheaf))
          (𝟙 (positiveSheafOfModules 𝒜 3)) := by
        rw [(unitIsoZeroTwist 𝒜).hom_inv_id, Category.id_comp]
      _ = _ := schemeModuleTensorMap_id _ _
  have hHom : (unitIsoZeroTwist 𝒜).hom = unitToZeroTwist 𝒜 := rfl
  have hLeft :
      schemeModuleTensorMap (unitIsoZeroTwist 𝒜).hom
          (𝟙 (positiveSheafOfModules 𝒜 3)) ≫
        (schemeModuleTensorSymmetry (sheafOfModules 𝒜 0)
          (positiveSheafOfModules 𝒜 3)).hom ≫
        positiveNegativePositiveDifferencePairing 𝒜 3 0 (by decide) =
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules 𝒜 3)).hom :=
    (congrArg
      (fun z : SheafOfModules.unit (Proj 𝒜).ringCatSheaf ⟶ sheafOfModules 𝒜 0 =>
        schemeModuleTensorMap z (𝟙 (positiveSheafOfModules 𝒜 3)) ≫
          (schemeModuleTensorSymmetry (sheafOfModules 𝒜 0)
            (positiveSheafOfModules 𝒜 3)).hom ≫
          positiveNegativePositiveDifferencePairing 𝒜 3 0 (by decide)) hHom).trans
      (threePositiveZeroNegativePairing_unit 𝒜)
  apply (cancel_epi (schemeModuleTensorMap (unitIsoZeroTwist 𝒜).hom
    (𝟙 (positiveSheafOfModules 𝒜 3)))).mp
  calc
    _ = (schemeModuleTensorUnitLeftIso (positiveSheafOfModules 𝒜 3)).hom := hLeft
    _ = (schemeModuleTensorMap (unitIsoZeroTwist 𝒜).hom
          (𝟙 (positiveSheafOfModules 𝒜 3)) ≫
        schemeModuleTensorMap (unitIsoZeroTwist 𝒜).inv
          (𝟙 (positiveSheafOfModules 𝒜 3))) ≫
        (schemeModuleTensorUnitLeftIso (positiveSheafOfModules 𝒜 3)).hom := by
      rw [hCancel]
      exact (Category.id_comp _).symm
    _ = _ := Category.assoc _ _ _

end PfaffianDescent.ProjectiveNegativeTwist
