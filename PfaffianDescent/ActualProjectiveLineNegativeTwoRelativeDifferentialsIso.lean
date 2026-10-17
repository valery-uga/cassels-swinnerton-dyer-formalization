import PfaffianDescent.ActualProjectiveLinePolynomialDifferentialUnitSectionIso
import PfaffianDescent.ActualProjectiveLineNegativeTwoToRelativeDifferentialsHom
import PfaffianDescent.SchemeModuleActualLocalIsoGluing

/-! SOURCE ONLY / UNVERIFIED. Invert the SAME original signed local maps
and the SAME already glued global O(-2)→Omega morphism. The three unsigned
polynomial D unit roots are a pending dependency until independently accepted. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist SchemeModuleInternalHom
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private instance signedLocalNativeSectionModule {X : Scheme.{u}}
    (N : X.Modules) (U : X.Opens) : Module Γ(X, U) (N.val.obj (op U)) :=
  (N.val.obj (op U)).isModule

/-- Actual whole local over-site law implies the corresponding ENTIRE
unit-section factorization on any open-immersion chart of that same open. -/
private theorem nativeLocalUnitHom_chartFactorization001
    {X Y : Scheme.{u}} (M N : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    (U : X.Opens) (s : N.val.obj (op U))
    (a : M ⟶ SheafOfModules.unit X.ringCatSheaf) (phi : M ⟶ N)
    (himage : f ''ᵁ ⊤ = U)
    (hlocal : phi.over U = a.over U ≫ unitSectionOver N U s) :
    (Scheme.Modules.restrictFunctor f).map phi =
      (Scheme.Modules.restrictFunctor f).map a ≫
        (Scheme.Modules.restrictUnitIso f).hom ≫
          schemeModuleTopSectionHom (N.restrict f)
            (N.val.map (eqToHom himage).op s) := by
  cases himage
  have hid : N.val.map (eqToHom (rfl : f ''ᵁ ⊤ = f ''ᵁ ⊤)).op s = s := by
    exact ConcreteCategory.congr_hom
      (CategoryTheory.Functor.map_id N.presheaf (op (f ''ᵁ ⊤)))
      (show N.presheaf.obj (op (f ''ᵁ ⊤)) from s)
  rw [hid]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let hVU : f ''ᵁ V.unop ≤ f ''ᵁ ⊤ := Scheme.Hom.image_mono f le_top
  let W : Over (f ''ᵁ ⊤) := Over.mk (homOfLE hVU)
  have hphi := ConcreteCategory.congr_hom
    (congrArg (fun g : M.over (f ''ᵁ ⊤) ⟶ N.over (f ''ᵁ ⊤) =>
      g.val.app (op W)) hlocal) z
  change phi.val.app (op (f ''ᵁ V.unop)) z =
    (show Γ(X, f ''ᵁ V.unop) from a.val.app (op (f ''ᵁ V.unop)) z) •
      (N.val.map (homOfLE hVU).op s) at hphi
  let p := schemeModuleTopSectionHom (N.restrict f) s
  let c : Γ(X, f ''ᵁ V.unop) := a.val.app (op (f ''ᵁ V.unop)) z
  let r : Γ(Y, V.unop) := (f.appIso V.unop).hom c
  have hgen := schemeModuleUnitHom_restrict_one (N.restrict f) p V.unop
  rw [schemeModuleTopSectionHom_value] at hgen
  change p.val.app V (1 : Γ(Y, V.unop)) =
    (N.restrict f).val.map
      (homOfLE (show V.unop ≤ ⊤ from le_top)).op s at hgen
  have hres : (N.restrict f).val.map
      (homOfLE (show V.unop ≤ ⊤ from le_top)).op s =
        N.val.map (homOfLE hVU).op s := rfl
  have hgenNative : p.val.app V (1 : Γ(Y, V.unop)) =
      N.val.map (homOfLE hVU).op s := hgen.trans hres
  have hr := schemeModuleUnitHom_apply_eq_smul_one (N.restrict f) p V.unop r
  have hrNative := hr.trans
    (congrArg (fun t : (N.restrict f).val.obj V => r • t) hgenNative)
  have hscalar := congrArg
    (fun t : (N.restrict f).val.obj V => (N.restrictAppIso f V.unop).hom t) hrNative
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply] at hscalar
  simp only [Scheme.Modules.restrictAppIso, Iso.refl_hom,
    Iso.refl_inv, r, Iso.hom_inv_id_apply] at hscalar
  change phi.val.app (op (f ''ᵁ V.unop)) z = p.val.app V r
  exact hphi.trans hscalar.symm

/-- Ordinary top-value ext on the original unit sheaf, no frame assumption. -/
private theorem signedUnitHom_top_ext001
    {Y : Scheme.{u}} (N : Y.Modules)
    (a b : SheafOfModules.unit Y.ringCatSheaf ⟶ N)
    (h : a.val.app (op ⊤) (1 : Γ(Y, ⊤)) =
      b.val.app (op ⊤) (1 : Γ(Y, ⊤))) : a = b := by
  apply N.unitHomEquiv.injective
  apply (schemeModuleSectionsEquivTop N).injective
  exact h

/-- The true-chart sign is an actual invertible unit endomorphism, in every
characteristic including 2. It is not an extra nonvanishing premise. -/
private theorem topSectionHom_neg_signIso001
    {Y : Scheme.{u}} (N : Y.Modules) (x : N.val.obj (op ⊤)) :
    schemeModuleTopSectionHom N (-x) =
      (-Iso.refl (SheafOfModules.unit Y.ringCatSheaf)).hom ≫
        schemeModuleTopSectionHom N x := by
  apply signedUnitHom_top_ext001 N
  rw [schemeModuleTopSectionHom_value]
  change -x = (schemeModuleTopSectionHom N x).val.app (op ⊤)
    (-(1 : Γ(Y, ⊤)))
  rw [map_neg, schemeModuleTopSectionHom_value]

/-- Any actual open-immersion restriction is invertible when its original
map is invertible at every point in its own source image. -/
private theorem nativeChartRestriction_isIso_of_originalStalks001
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {M N : X.Modules} (a : M ⟶ N)
    (h : ∀ y : Y, IsIso ((schemeModuleStalkFunctor X (f y)).map a)) :
    IsIso ((Scheme.Modules.restrictFunctor f).map a) := by
  let g := (Scheme.Modules.restrictFunctor f).map a
  have hg : IsIso ((SheafOfModules.toSheaf Y.ringCatSheaf).map g) := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
    intro y
    exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso f y) a).mpr (h y)
  let q := (SheafOfModules.toSheaf Y.ringCatSheaf).map g
  have hqForget : IsIso ((TopCat.Sheaf.forget _ Y).map q) :=
    @CategoryTheory.Functor.map_isIso _ _ _ _ _ _
      (TopCat.Sheaf.forget _ Y) q hg
  have hgPresheaf : IsIso ((Scheme.Modules.toPresheaf Y).map g) := by
    change IsIso ((TopCat.Sheaf.forget _ Y).map q)
    exact hqForget
  letI : IsIso ((Scheme.Modules.toPresheaf Y).map g) := hgPresheaf
  exact isIso_of_reflects_iso g (Scheme.Modules.toPresheaf Y)

/-- Recover the original module stalk at a point of any actual chart from
invertibility after restricting to that chart. -/
private theorem nativeOriginalStalk_isIso_of_chartRestriction001
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (y : Y)
    {M N : X.Modules} (a : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor f).map a)] :
    IsIso ((schemeModuleStalkModuleFunctor X (f y)).map a) := by
  let G := Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  have hlocal : IsIso (G.map ((Scheme.Modules.restrictFunctor f).map a)) :=
    Functor.map_isIso G _
  have hstalk : IsIso ((schemeModuleStalkFunctor X (f y)).map a) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso f y) a).mp hlocal
  let H := forget₂ (ModuleCat (X.presheaf.stalk (f y))) AddCommGrpCat
  have hforget : IsIso (H.map ((schemeModuleStalkModuleFunctor X (f y)).map a)) := by
    change IsIso ((schemeModuleStalkFunctor X (f y)).map a)
    exact hstalk
  letI := hforget
  exact isIso_of_reflects_iso ((schemeModuleStalkModuleFunctor X (f y)).map a) H

attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [CommRing K]
local notation "Iline" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))
local notation "Xline" => projectiveLineProj K
local notation "Omega" => schemeRelativeDifferentials (projectiveLineProjToBase K)
local notation "NegTwo" => sheafOfModules (grading Iline) 2

/-- The SAME already glued global morphism restricts to the SAME whole
native signed local morphism, by the already proved exact gluing theorem. -/
private theorem originalSignedGlobalHom_over_local001 (b : Bool) :
    (actualProjectiveLineNegativeTwoToRelativeDifferentialsHom K).over
        (actualProjectiveLineCoordinateOpen K b) =
      actualProjectiveLineNegativeTwoDifferentialLocalHom K b :=
  schemeModuleHomGlueOfActualCompatibleOverMorphisms_over NegTwo Omega
    (fun i : ULift.{u} Bool => actualProjectiveLineCoordinateOpen K i.down)
    (actualProjectiveLineCoordinateOpen_lifted_cover K)
    (fun i => actualProjectiveLineNegativeTwoDifferentialLocalHom K i.down)
    (fun i j => actualProjectiveLineNegativeTwoDifferentialLocalHom_compatible K i.down j.down)
    (ULift.up b)

/-- Whole factorization of the SAME global Hom on the actual polynomial
chart. Every section/sign/local law is the original one, derived internally. -/
theorem actualProjectiveLineNegativeTwoDifferentials_polynomialChart_factorization
    (b : Bool) :
    (Scheme.Modules.restrictFunctor (actualProjectiveLinePolynomialChartToLine K b)).map
        (actualProjectiveLineNegativeTwoToRelativeDifferentialsHom K) =
      (Scheme.Modules.restrictFunctor (actualProjectiveLinePolynomialChartToLine K b)).map
          (nativeNegativeTwoPowerFrameHom (grading Iline)
            ⟨coordinate Iline b, coordinate_mem Iline b⟩) ≫
        (Scheme.Modules.restrictUnitIso (actualProjectiveLinePolynomialChartToLine K b)).hom ≫
          schemeModuleTopSectionHom
            ((Scheme.Modules.restrictFunctor (actualProjectiveLinePolynomialChartToLine K b)).obj Omega)
            ((Omega).val.map
              (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K b)).op
              (actualProjectiveLineSignedCoordinateDifferential K b)) :=
  nativeLocalUnitHom_chartFactorization001 NegTwo Omega
    (actualProjectiveLinePolynomialChartToLine K b)
    (actualProjectiveLineCoordinateOpen K b)
    (actualProjectiveLineSignedCoordinateDifferential K b)
    (nativeNegativeTwoPowerFrameHom (grading Iline)
      ⟨coordinate Iline b, coordinate_mem Iline b⟩)
    (actualProjectiveLineNegativeTwoToRelativeDifferentialsHom K)
    (actualProjectiveLinePolynomialChartToLine_image_top K b)
    (originalSignedGlobalHom_over_local001 K b)

/-- Actual original signed D still generates the whole polynomial-chart
Omega. Unsigned input is the checked local unit root, sign an actual Iso. -/
private theorem originalSignedPolynomialDifferentialUnitHom_isIso001 (b : Bool) :
    IsIso (schemeModuleTopSectionHom
      ((Scheme.Modules.restrictFunctor (actualProjectiveLinePolynomialChartToLine K b)).obj Omega)
      ((Omega).val.map
        (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K b)).op
        (actualProjectiveLineSignedCoordinateDifferential K b))) := by
  cases b
  · change IsIso (actualProjectiveLinePolynomialCoordinateDifferentialUnitHom K false)
    exact actualProjectiveLinePolynomialCoordinateDifferentialUnitHom_isIso K false
  · let f := actualProjectiveLinePolynomialChartToLine K true
    let N := (Scheme.Modules.restrictFunctor f).obj Omega
    let O := SheafOfModules.unit
      (Spec (.of (MvPolynomial {i : Bool // i ≠ true} K))).ringCatSheaf
    let d := actualRelativeDifferentialSection (projectiveLineProjToBase K)
      (actualProjectiveLineCoordinateOpen K true) (actualProjectiveLineCoordinateSection K true)
    let x : N.val.obj (op ⊤) := (Omega).val.map
      (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K true)).op d
    have signedSection : actualProjectiveLineSignedCoordinateDifferential K true = -d :=
      if_pos (rfl : true = true)
    have mappedSigned :
        (Omega).val.map
          (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K true)).op
          (actualProjectiveLineSignedCoordinateDifferential K true) = -x :=
      (congrArg (fun z : (Omega).val.obj (op (actualProjectiveLineCoordinateOpen K true)) =>
        (Omega).val.map
          (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K true)).op z)
        signedSection).trans
          (((Omega).val.map
            (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K true)).op).hom.map_neg d)
    have signedHom :
        schemeModuleTopSectionHom N
          ((Omega).val.map
            (eqToHom (actualProjectiveLinePolynomialChartToLine_image_top K true)).op
            (actualProjectiveLineSignedCoordinateDifferential K true)) =
          (-Iso.refl O).hom ≫ actualProjectiveLinePolynomialCoordinateDifferentialUnitHom K true :=
      (congrArg (schemeModuleTopSectionHom N) mappedSigned).trans
        (topSectionHom_neg_signIso001 N x)
    have signedIso : IsIso ((-Iso.refl O).hom ≫
        actualProjectiveLinePolynomialCoordinateDifferentialUnitHom K true) := by
      haveI : IsIso (actualProjectiveLinePolynomialCoordinateDifferentialUnitHom K true) :=
        actualProjectiveLinePolynomialCoordinateDifferentialUnitHom_isIso K true
      infer_instance
    exact Eq.mpr (congrArg (fun a : O ⟶ N => IsIso a) signedHom) signedIso

/-- The actual native negative power frame is invertible on the SAME
polynomial chart, by its original coordinate-open stalk calculation. -/
private theorem originalNegativePowerFrame_polynomialChart_isIso001 (b : Bool) :
    IsIso ((Scheme.Modules.restrictFunctor (actualProjectiveLinePolynomialChartToLine K b)).map
      (nativeNegativeTwoPowerFrameHom (grading Iline)
        ⟨coordinate Iline b, coordinate_mem Iline b⟩)) := by
  let f := actualProjectiveLinePolynomialChartToLine K b
  let U := actualProjectiveLineCoordinateOpen K b
  let a := nativeNegativeTwoPowerFrameHom (grading Iline)
    ⟨coordinate Iline b, coordinate_mem Iline b⟩
  haveI : IsIso ((Scheme.Modules.restrictFunctor U.ι).map a) :=
    nativeNegativeTwoPowerFrameHom_restrict_isIso (grading Iline)
      ⟨coordinate Iline b, coordinate_mem Iline b⟩
      (actualProjectiveLine_irrelevant_le_span_degreeOne K)
  apply nativeChartRestriction_isIso_of_originalStalks001 f a
  intro y
  have hy : f y ∈ U := by
    rw [show U = f ''ᵁ ⊤ from (actualProjectiveLinePolynomialChartToLine_image_top K b).symm]
    exact ⟨y, trivial, rfl⟩
  have hmodule : IsIso ((schemeModuleStalkModuleFunctor Xline (f y)).map a) :=
    schemeModuleStalkMap_isIso_of_restrict U ⟨f y, hy⟩ a
  exact @CategoryTheory.Functor.map_isIso _ _ _ _ _ _
    (forget₂ (ModuleCat ((Xline).presheaf.stalk (f y))) AddCommGrpCat)
    ((schemeModuleStalkModuleFunctor Xline (f y)).map a) hmodule

/-- The restriction of the ORIGINAL global map is an actual Iso on every
polynomial chart; no local invertibility assumption is supplied. -/
theorem actualProjectiveLineNegativeTwoDifferentials_polynomialChart_isIso (b : Bool) :
    IsIso ((Scheme.Modules.restrictFunctor (actualProjectiveLinePolynomialChartToLine K b)).map
      (actualProjectiveLineNegativeTwoToRelativeDifferentialsHom K)) := by
  rw [actualProjectiveLineNegativeTwoDifferentials_polynomialChart_factorization]
  letI := originalNegativePowerFrame_polynomialChart_isIso001 K b
  letI := originalSignedPolynomialDifferentialUnitHom_isIso001 K b
  infer_instance

/-- Global invertibility of the SAME original glued O(-2)→Omega map,
proved on the actual internally constructed atlas and original stalks. -/
theorem actualProjectiveLineNegativeTwoToRelativeDifferentialsHom_isIso :
    IsIso (actualProjectiveLineNegativeTwoToRelativeDifferentialsHom K) := by
  apply schemeModuleMap_isIso_of_stalk (actualProjectiveLineNegativeTwoToRelativeDifferentialsHom K)
  intro x
  obtain ⟨b, y, hy⟩ := exists_actualProjectiveLinePolynomialChart K x
  haveI := actualProjectiveLineNegativeTwoDifferentials_polynomialChart_isIso K b
  rw [← hy]
  exact nativeOriginalStalk_isIso_of_chartRestriction001
    (actualProjectiveLinePolynomialChartToLine K b) y
    (actualProjectiveLineNegativeTwoToRelativeDifferentialsHom K)

/-- The SAME native signed local morphisms are invertible, obtained from
the SAME global map's proved invertibility and exact original restriction. -/
theorem actualProjectiveLineNegativeTwoDifferentialLocalHom_isIso (b : Bool) :
    IsIso (actualProjectiveLineNegativeTwoDifferentialLocalHom K b) := by
  haveI := actualProjectiveLineNegativeTwoToRelativeDifferentialsHom_isIso K
  have h := Functor.map_isIso
    (SheafOfModules.overFunctor (Xline).ringCatSheaf (actualProjectiveLineCoordinateOpen K b))
    (actualProjectiveLineNegativeTwoToRelativeDifferentialsHom K)
  change IsIso ((actualProjectiveLineNegativeTwoToRelativeDifferentialsHom K).over
    (actualProjectiveLineCoordinateOpen K b)) at h
  rw [originalSignedGlobalHom_over_local001 K b] at h
  exact h

/-- Literal Omega identification on original P1, with all comparison maps
constructed and the original signed global map retained as its hom. -/
def actualProjectiveLineNegativeTwoToRelativeDifferentialsIso : NegTwo ≅ Omega := by
  letI := actualProjectiveLineNegativeTwoToRelativeDifferentialsHom_isIso K
  exact asIso (actualProjectiveLineNegativeTwoToRelativeDifferentialsHom K)

theorem actualProjectiveLineNegativeTwoToRelativeDifferentialsIso_hom :
    (actualProjectiveLineNegativeTwoToRelativeDifferentialsIso K).hom =
      actualProjectiveLineNegativeTwoToRelativeDifferentialsHom K := rfl

end PfaffianDescent
end
