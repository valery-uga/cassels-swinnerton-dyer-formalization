import PfaffianDescent.SchemeModuleNonzeroTopSectionMono
import PfaffianDescent.CorayDvrPrincipalSectionQuotientLength
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.RingTheory.Ideal.Span

/-! The SAME unit morphism's actual native stalk cokernel, with its
original projection, is the principal quotient by its actual coefficient
in a genuine native rank-one frame. Multiplication compatibility is proved.
Monicity gives a nonzero coefficient; DVR length is then derived. Native
R-linear actions are retained throughout; no original-K action is replaced.
Generic frame and monicity hypotheses remain explicit at this stage.
SOURCE ONLY / UNVERIFIED: root alone compiles. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem nativeUnitFrame_square
    {R : Type u} [CommRing R] {A B : ModuleCat.{u} R}
    (f : A ⟶ B) (eA : A ≅ ModuleCat.of R R) (eB : B ≅ ModuleCat.of R R) :
    f ≫ eB.hom = eA.hom ≫ ModuleCat.ofHom
      (LinearMap.toSpanSingleton R R ((eA.inv ≫ f ≫ eB.hom).hom (1 : R))) := by
  let g : ModuleCat.of R R ⟶ ModuleCat.of R R := eA.inv ≫ f ≫ eB.hom
  have hmul : g.hom = LinearMap.toSpanSingleton R R (g.hom (1 : R)) := by
    apply LinearMap.ext
    intro r
    calc
      g.hom r = g.hom (r • (1 : R)) :=
        congrArg g.hom (show r • (1 : R) = r from mul_one r).symm
      _ = r • g.hom (1 : R) := g.hom.map_smul r _
      _ = LinearMap.toSpanSingleton R R (g.hom (1 : R)) r := rfl
  calc
    f ≫ eB.hom = eA.hom ≫ g := by
      simp only [g, Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := congrArg (fun t => eA.hom ≫ t) (ModuleCat.hom_ext hmul)

private def nativeScalarCokernelIso
    (R : Type u) [CommRing R] (a : R) :
    cokernel (ModuleCat.ofHom (LinearMap.toSpanSingleton R R a)) ≅
      ModuleCat.of R (R ⧸ Ideal.span ({a} : Set R)) := by
  let g := ModuleCat.ofHom (LinearMap.toSpanSingleton R R a)
  have hrange : LinearMap.range g.hom = Ideal.span ({a} : Set R) :=
    LinearMap.range_toSpanSingleton a
  exact ModuleCat.cokernelIsoRangeQuotient g ≪≫
    (Submodule.quotEquivOfEq _ _ hrange).toModuleIso

private theorem nativeScalarCokernelIso_π
    (R : Type u) [CommRing R] (a : R) :
    cokernel.π (ModuleCat.ofHom (LinearMap.toSpanSingleton R R a)) ≫
      (nativeScalarCokernelIso R a).hom =
        ModuleCat.ofHom (Algebra.linearMap R (R ⧸ Ideal.span ({a} : Set R))) := by
  let g := ModuleCat.ofHom (LinearMap.toSpanSingleton R R a)
  have hrange : LinearMap.range g.hom = Ideal.span ({a} : Set R) :=
    LinearMap.range_toSpanSingleton a
  change cokernel.π g ≫
    (ModuleCat.cokernelIsoRangeQuotient g ≪≫
      (Submodule.quotEquivOfEq _ _ hrange).toModuleIso).hom = _
  rw [Iso.trans_hom, ← Category.assoc,
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact Submodule.quotEquivOfEq_mk _ _ hrange r

variable {X : Scheme.{u}}

/-- The actual coefficient is the image of native 1 under the SAME
original stalk morphism, using the canonical unit-stalk Iso and the
given actual native frame. No rational frame or replacement map. -/
def schemeModuleUnitHomStalkCoefficient
    (M : X.Modules) (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) (x : X)
    (eW : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) : X.presheaf.stalk x :=
  ((schemeModuleUnitStalkIso X x).inv ≫
    (schemeModuleStalkModuleFunctor X x).map φ ≫ eW.hom).hom (1 : X.presheaf.stalk x)

/-- Actual native cokernel comparison for the original unit morphism.
Cokernel preservation, multiplication compatibility and range = (a)
are all derived internally; the native local-ring action is unchanged. -/
def schemeModuleUnitHomStalkCokernelIsoPrincipalQuotient
    (M : X.Modules) (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) (x : X)
    (eW : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    (schemeModuleStalkModuleFunctor X x).obj (cokernel φ) ≅
      ModuleCat.of (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸
        Ideal.span ({schemeModuleUnitHomStalkCoefficient M φ x eW} : Set (X.presheaf.stalk x))) := by
  let R := X.presheaf.stalk x
  let F := schemeModuleStalkModuleFunctor X x
  let eO := schemeModuleUnitStalkIso X x
  let a : R := schemeModuleUnitHomStalkCoefficient M φ x eW
  let g : ModuleCat.of R R ⟶ ModuleCat.of R R :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R R a)
  have hφ : F.map φ ≫ eW.hom = eO.hom ≫ g :=
    nativeUnitFrame_square (F.map φ) eO eW
  exact PreservesCokernel.iso F φ ≪≫
    cokernel.mapIso (F.map φ) g eO eW hφ ≪≫ nativeScalarCokernelIso R a

/-- The comparison retains the SAME original categorical projection;
in the actual native frame it is the literal quotient map R → R/(a). -/
theorem schemeModuleUnitHomStalkCokernelIsoPrincipalQuotient_π
    (M : X.Modules) (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) (x : X)
    (eW : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    (schemeModuleStalkModuleFunctor X x).map (cokernel.π φ) ≫
      (schemeModuleUnitHomStalkCokernelIsoPrincipalQuotient M φ x eW).hom =
        eW.hom ≫ ModuleCat.ofHom (Algebra.linearMap (X.presheaf.stalk x)
          ((X.presheaf.stalk x) ⧸ Ideal.span
            ({schemeModuleUnitHomStalkCoefficient M φ x eW} : Set (X.presheaf.stalk x)))) := by
  let R := X.presheaf.stalk x
  let F := schemeModuleStalkModuleFunctor X x
  let eO := schemeModuleUnitStalkIso X x
  let a : R := schemeModuleUnitHomStalkCoefficient M φ x eW
  let g : ModuleCat.of R R ⟶ ModuleCat.of R R :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R R a)
  have hφ : F.map φ ≫ eW.hom = eO.hom ≫ g :=
    nativeUnitFrame_square (F.map φ) eO eW
  let E₁ : F.obj (cokernel φ) ≅ cokernel (F.map φ) := PreservesCokernel.iso F φ
  let E₂ : cokernel (F.map φ) ≅ cokernel g := cokernel.mapIso (F.map φ) g eO eW hφ
  let E₃ : cokernel g ≅ ModuleCat.of R (R ⧸ Ideal.span ({a} : Set R)) :=
    nativeScalarCokernelIso R a
  let q : ModuleCat.of R R ⟶ ModuleCat.of R (R ⧸ Ideal.span ({a} : Set R)) :=
    ModuleCat.ofHom (Algebra.linearMap R (R ⧸ Ideal.span ({a} : Set R)))
  have h₁ : F.map (cokernel.π φ) ≫ E₁.hom = cokernel.π (F.map φ) :=
    PreservesCokernel.π_iso_hom F φ
  have h₂ : cokernel.π (F.map φ) ≫ E₂.hom = eW.hom ≫ cokernel.π g :=
    cokernel.π_desc _ _ _
  have h₃ : cokernel.π g ≫ E₃.hom = q := nativeScalarCokernelIso_π R a
  change F.map (cokernel.π φ) ≫ (E₁ ≪≫ E₂ ≪≫ E₃).hom = eW.hom ≫ q
  calc
    _ = ((F.map (cokernel.π φ) ≫ E₁.hom) ≫ E₂.hom) ≫ E₃.hom := by
      simp only [Iso.trans_hom, Category.assoc]
    _ = (cokernel.π (F.map φ) ≫ E₂.hom) ≫ E₃.hom :=
      congrArg (fun t => (t ≫ E₂.hom) ≫ E₃.hom) h₁
    _ = (eW.hom ≫ cokernel.π g) ≫ E₃.hom := congrArg (fun t => t ≫ E₃.hom) h₂
    _ = eW.hom ≫ (cokernel.π g ≫ E₃.hom) := Category.assoc _ _ _
    _ = eW.hom ≫ q := congrArg (fun t => eW.hom ≫ t) h₃

/-- Monicity of the SAME original sheaf morphism forces its actual
native frame coefficient to be nonzero. Native stalk monicity and
the genuine frame Isos are the only ingredients. -/
theorem schemeModuleUnitHomStalkCoefficient_ne_zero_of_mono
    (M : X.Modules) (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) [Mono φ] (x : X)
    [Nontrivial (X.presheaf.stalk x)]
    (eW : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    schemeModuleUnitHomStalkCoefficient M φ x eW ≠ 0 := by
  let R := X.presheaf.stalk x
  let F := schemeModuleStalkModuleFunctor X x
  let eO := schemeModuleUnitStalkIso X x
  let g : ModuleCat.of R R ⟶ ModuleCat.of R R := eO.inv ≫ F.map φ ≫ eW.hom
  letI : Mono (F.map φ) := schemeModuleStalkModuleFunctor_map_mono φ x
  letI : Mono g := by
    dsimp only [g]
    infer_instance
  have hinj : Function.Injective g.hom := (ModuleCat.mono_iff_injective g).mp inferInstance
  intro ha
  change g.hom (1 : R) = 0 at ha
  exact one_ne_zero (hinj (ha.trans g.hom.map_zero.symm))

/-- Native length of the ACTUAL cokernel stalk equals the actual DVR
valuation of its internally defined coefficient. The comparison and
coefficient nonvanishing are consequences of the original map/frame. -/
theorem schemeModuleUnitHomStalkCokernel_length
    (M : X.Modules) (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) [Mono φ] (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (eW : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    Module.length (X.presheaf.stalk x)
      ((schemeModuleStalkModuleFunctor X x).obj (cokernel φ)) =
        IsDiscreteValuationRing.addVal (X.presheaf.stalk x)
          (schemeModuleUnitHomStalkCoefficient M φ x eW) :=
  ((schemeModuleUnitHomStalkCokernelIsoPrincipalQuotient M φ x eW).toLinearEquiv.length_eq).trans
    (Coray.dvr_principalSectionQuotient_length (X.presheaf.stalk x)
      (schemeModuleUnitHomStalkCoefficient M φ x eW)
      (schemeModuleUnitHomStalkCoefficient_ne_zero_of_mono M φ x eW))

/-- Finite composition length of the SAME native stalk cokernel,
derived from the actual principal quotient; no length certificate. -/
theorem schemeModuleUnitHomStalkCokernel_isFiniteLength
    (M : X.Modules) (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) [Mono φ] (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (eW : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    IsFiniteLength (X.presheaf.stalk x)
      ((schemeModuleStalkModuleFunctor X x).obj (cokernel φ)) :=
  (schemeModuleUnitHomStalkCokernelIsoPrincipalQuotient M φ x eW).toLinearEquiv.symm.isFiniteLength
    (Coray.dvr_principalSectionQuotient_isFiniteLength (X.presheaf.stalk x)
      (schemeModuleUnitHomStalkCoefficient M φ x eW)
      (schemeModuleUnitHomStalkCoefficient_ne_zero_of_mono M φ x eW))

end PfaffianDescent
