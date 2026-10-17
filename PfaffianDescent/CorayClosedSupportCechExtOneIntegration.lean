import PfaffianDescent.CorayClosedSupportCechHomExact
import PfaffianDescent.CechExtVanishingLowDegree
import PfaffianDescent.SectionRepresenterCechAugmentationExact
import PfaffianDescent.SchemeCoverIntrinsicCohomology

/-! SOURCE ONLY / UNVERIFIED. Actual degree-one Hom exactness combines with
the actual image of the first categorical Čech differential and the actual
covering augmentation. The sole unproved acyclicity input to the Ext¹
conclusion is explicitly Ext¹ of the actual degree-zero coproduct into M.
No normalization-quotient Ext¹ vanishing is asserted in this file.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace
universe u

/-- A literal covering inequality implies the actual site's covering
condition; no Grothendieck-cover certificate is supplied by the caller. -/
theorem schemeOpenFamily_coversTop_of_top_le_iSup
    {X : Scheme.{u}} {ι : Type u} (W : ι → X.Opens) (hW : ⊤ ≤ ⨆ i, W i) :
    (Opens.grothendieckTopology X).CoversTop W := by
  apply (Opens.coversTop_iff X W).mpr
  exact le_antisymm le_top hW

/-- The actual abelian image of d₁, its actual inclusion into C₀, and the
actual covering augmentation form the short complex used for Ext¹. -/
def schemeModuleCechImageAugmentationShortComplex
    {X : Scheme.{u}} {ι : Type u} (W : ι → X.Opens) : ShortComplex X.Modules :=
  let L : ChainComplex X.Modules ℕ := sectionRepresenterCechChain X.ringCatSheaf W
  let P : X.Modules :=
    (sectionRepresenterCechAugmented X.ringCatSheaf W ⊤ isTerminalTop).right
  let epsilon : L.X 0 ⟶ P :=
    sectionRepresenterCechAugmentation X.ringCatSheaf W ⊤ isTerminalTop
  ShortComplex.mk (Abelian.image.ι (L.d 1 0)) epsilon
    (Abelian.image_ι_comp_eq_zero
      (sectionRepresenterCech_d_one_zero_comp_augmentation
        X.ringCatSheaf W ⊤ isTerminalTop))

/-- Short exactness is derived from the actual covering augmentation and
the actual epi-mono image factorization, rather than assumed as a premise. -/
theorem schemeModuleCechImageAugmentationShortComplex_shortExact
    {X : Scheme.{u}} {ι : Type u} (W : ι → X.Opens) (hW : ⊤ ≤ ⨆ i, W i) :
    (schemeModuleCechImageAugmentationShortComplex W).ShortExact := by
  let L : ChainComplex X.Modules ℕ := sectionRepresenterCechChain X.ringCatSheaf W
  let P : X.Modules :=
    (sectionRepresenterCechAugmented X.ringCatSheaf W ⊤ isTerminalTop).right
  let epsilon : L.X 0 ⟶ P :=
    sectionRepresenterCechAugmentation X.ringCatSheaf W ⊤ isTerminalTop
  let h10 : L.d 1 0 ≫ epsilon = 0 :=
    sectionRepresenterCech_d_one_zero_comp_augmentation
      X.ringCatSheaf W ⊤ isTerminalTop
  have haug := sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    X.ringCatSheaf W (schemeOpenFamily_coversTop_of_top_le_iSup W hW) ⊤ isTerminalTop
  have hbase : (ShortComplex.mk (L.d 1 0) epsilon h10).Exact := haug.1
  letI : Epi epsilon := haug.2
  change (ShortComplex.mk (Abelian.image.ι (L.d 1 0)) epsilon
    (Abelian.image_ι_comp_eq_zero h10)).ShortExact
  exact ShortComplex.ShortExact.mk'
    (((ShortComplex.mk (L.d 1 0) epsilon h10).exact_iff_exact_image_ι).mp hbase)
    (by infer_instance) (by infer_instance)

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) {ι : Type u}

include pi in
/-- The genuine closed-support contraction derives Hom lifting against
the inclusion of the actual image of d₁. No Hom-exactness or lifting
certificate is supplied by the caller, and no cover is needed for this step. -/
theorem schemeModule_augmentedCechImage_hom_precomp_surjective_of_closedSupport_subset
    (U : X.Opens) (V : ι → X.Opens) (C : Set X) (hC : IsClosed C)
    (hsupport : schemeModuleStalkSupport M ⊆ C) (hCU : C ⊆ U) :
    Function.Surjective
      (fun h : (schemeModuleCechImageAugmentationShortComplex
          (supportAugmentedOpenFamily U V)).X₂ ⟶ M =>
        (schemeModuleCechImageAugmentationShortComplex
          (supportAugmentedOpenFamily U V)).f ≫ h) := by
  let A := supportAugmentedOpenFamily U V
  let L : ChainComplex X.Modules ℕ := sectionRepresenterCechChain X.ringCatSheaf A
  change Function.Surjective (fun h : L.X 0 ⟶ M => Abelian.image.ι (L.d 1 0) ≫ h)
  have hd : L.d 2 1 ≫ Abelian.factorThruImage (L.d 1 0) = 0 := by
    apply (cancel_mono (Abelian.image.ι (L.d 1 0))).1
    simpa only [Category.assoc, Abelian.image.fac, zero_comp] using L.d_comp_d 2 1 0
  apply hom_precomp_surjective_of_exact_and_epi M
    (Abelian.image.ι (L.d 1 0)) (Abelian.factorThruImage (L.d 1 0)) (L.d 2 1) hd
  simpa only [Abelian.image.fac] using
    schemeModule_augmentedCechHom_exact_one_of_closedSupport_subset pi M U V C hC hsupport hCU

include pi in
/-- CONDITIONAL Ext¹ integration. Closed support, its actual containing
open, and a literal cover derive every Hom/image/augmentation condition.
The explicitly named `hDegreeZeroExt` is the remaining genuine Ext¹ input
for the ACTUAL categorical degree-zero coproduct. It is not established
here for the canonical normalization quotient.
-/
theorem schemeModule_unit_ext_one_subsingleton_of_closedSupport_of_degreeZeroExt
    [hExt : HasExt.{u} X.Modules]
    (U : X.Opens) (V : ι → X.Opens) (hV : ⊤ ≤ ⨆ i, V i)
    (C : Set X) (hC : IsClosed C)
    (hsupport : schemeModuleStalkSupport M ⊆ C) (hCU : C ⊆ U)
    (hDegreeZeroExt : Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf
        (supportAugmentedOpenFamily U V)).X 0) M 1)) :
    Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) M 1) := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  let A := supportAugmentedOpenFamily U V
  let S : ShortComplex X.Modules := schemeModuleCechImageAugmentationShortComplex A
  have hS : S.ShortExact :=
    schemeModuleCechImageAugmentationShortComplex_shortExact A
      (supportAugmentedOpenFamily_covers U V hV)
  have hsurj : Function.Surjective (fun h : S.X₂ ⟶ M => S.f ≫ h) :=
    schemeModule_augmentedCechImage_hom_precomp_surjective_of_closedSupport_subset
      pi M U V C hC hsupport hCU
  letI : Subsingleton (Ext.{u} (C := X.Modules) S.X₂ M 1) := hDegreeZeroExt
  have hTarget : Subsingleton (Ext.{u} (C := X.Modules) S.X₃ M 1) :=
    ext_one_subsingleton_of_hom_precomp_surjective (A := X.Modules) M S hS hsurj
  letI : Subsingleton (Ext.{u} (C := X.Modules)
      (sectionRepresenterCechAugmented X.ringCatSheaf A ⊤ isTerminalTop).right M 1) := hTarget
  exact ext_subsingleton_of_iso_left (C := X.Modules) (Y := M)
    (schemeCoverCechTargetIsoUnit A) 1

end PfaffianDescent.Coray
