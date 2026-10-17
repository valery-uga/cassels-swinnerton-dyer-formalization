import PfaffianDescent.ActualP3HomogeneousChartCoefficient
import PfaffianDescent.SchemeModuleGlobalSectionsTop
import PfaffianDescent.ActualUnitChartKernelInvariance

/- SOURCE ONLY / UNVERIFIED. Actual closed-immersion augmentation on an
actual chart, identified with the original morphism's map i.app on sections.
No affine algebra presentation, reducedness, finiteness or chart certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open IdealSheafDataModule BundleSectionZeroLocus ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

lemma actualUnitSourceMorphism_zero_iff_topValue
    {X : Scheme.{u}} {Q : X.Modules}
    (f : schemeModuleUnit X ⟶ Q) :
    f = 0 ↔ f.val.app (op ⊤) (1 : Γ(X, ⊤)) = 0 := by
  constructor
  · intro hf
    rw [hf]
    rfl
  · intro hf
    apply Q.unitHomEquiv.injective
    apply (schemeModuleSectionsEquivTop Q).injective
    change f.val.app (op ⊤) (1 : Γ(X, ⊤)) =
      (0 : schemeModuleUnit X ⟶ Q).val.app (op ⊤) (1 : Γ(X, ⊤))
    change f.val.app (op ⊤) (1 : Γ(X, ⊤)) = 0
    exact hf

/-- The actual untwisted restricted augmentation kills a scalar coordinate
exactly when the SAME original i.app kills its ambient chart function. -/
lemma p3ActualRestrictedAugmentation_zero_iff_value
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    [IsClosedImmersion i]
    (U : (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Opens)
    (c : SheafOfModules.unit (U : Scheme).ringCatSheaf ⟶
      SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (c ≫ (Scheme.Modules.restrictUnitIso U.ι).inv) ≫
        (Scheme.Modules.restrictFunctor U.ι).map
          (closedImmersionUnitToPushforwardUnit i) = 0 ↔
      i.app U (U.topIso.hom (unitEndomorphismValue c)) = 0 := by
  let X := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let Q := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let R := Scheme.Modules.restrictFunctor U.ι
  let aug := closedImmersionUnitToPushforwardUnit i
  let u := Scheme.Modules.restrictUnitIso U.ι
  let v := unitEndomorphismValue c
  let r := U.topIso.hom v
  have hu : (u.inv.val.app (op ⊤)) v = (moduleRestrictTopIso O U).inv r := by
    apply (moduleRestrictTopIso O U).addCommGroupIsoToAddEquiv.injective
    change (moduleRestrictTopIso O U).hom (u.inv.val.app (op ⊤) v) =
      (moduleRestrictTopIso O U).hom ((moduleRestrictTopIso O U).inv r)
    rw [Iso.inv_hom_id_apply]
    have h := congrArg (fun t => t v) (restrictUnit_inv_comp_moduleRestrictTop K U)
    change (moduleRestrictTopIso O U).hom (u.inv.val.app (op ⊤) v) = r at h
    exact h
  have hmap :=
    cubicClosedPointSerreSurfaceJetCotangent_restrictTopSectionIso_map U aug r
  have hcalc : (moduleRestrictTopIso Q U).hom
      (((c ≫ u.inv) ≫ R.map aug).val.app (op ⊤) (1 : Γ((U : Scheme), ⊤))) =
      i.app U r := by
    change (moduleRestrictTopIso Q U).hom
      ((R.map aug).val.app (op ⊤) (u.inv.val.app (op ⊤) v)) = _
    rw [hu]
    change (schemeModuleRestrictTopSectionIso U Q).hom
      ((R.map aug).val.app (op ⊤)
        ((schemeModuleRestrictTopSectionIso U O).inv r)) = _
    exact hmap.trans (SheafOfModules.unitToPushforwardObjUnit_val_app_apply
      i.toRingCatSheafHom (X := op U) r)
  rw [actualUnitSourceMorphism_zero_iff_topValue]
  constructor
  · intro h
    change ((c ≫ u.inv) ≫ R.map aug).val.app (op ⊤)
      (1 : Γ((U : Scheme), ⊤)) = 0 at h
    exact hcalc.symm.trans ((congrArg (fun t => (moduleRestrictTopIso Q U).hom t) h).trans
      (map_zero _))
  · intro h
    apply (moduleRestrictTopIso Q U).addCommGroupIsoToAddEquiv.injective
    change (moduleRestrictTopIso Q U).hom
      (((c ≫ u.inv) ≫ R.map aug).val.app (op ⊤)
        (1 : Γ((U : Scheme), ⊤))) = (moduleRestrictTopIso Q U).hom 0
    exact (hcalc.trans h).trans (map_zero _).symm

/-- A morphism from the actual structure sheaf is zero if and only if its
restrictions to the actual four standard P3 charts are zero. -/
lemma p3ActualUnitSourceMorphism_zero_iff_standard_restrictions
    {K : Type u} [Field K]
    {Q : (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules}
    (f : SheafOfModules.unit
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).ringCatSheaf ⟶ Q) :
    f = 0 ↔ ∀ j : Fin 4,
      (Scheme.Modules.restrictFunctor (p3StandardOpen (K := K) j).ι).map f = 0 := by
  constructor
  · intro hf j
    rw [hf]
    exact Functor.map_zero (Scheme.Modules.restrictFunctor (p3StandardOpen (K := K) j).ι) _ _
  · intro hf
    apply (actualUnitSourceMorphism_zero_iff_topValue f).mpr
    apply TopCat.Presheaf.IsSheaf.section_ext Q.isSheaf
    intro x hx
    have hxcover : x ∈ ⨆ j : Fin 4, p3StandardOpen (K := K) j := by
      rw [p3StandardOpen_iSup K]
      trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxcover
    let U := p3StandardOpen (K := K) j
    refine ⟨U, le_top, hj, ?_⟩
    have hlocal := cubicClosedPointSerreSurfaceJetCotangent_restrictTopSectionIso_map
      U f (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K), U))
    rw [hf j] at hlocal
    have hzero : f.val.app (op U)
        (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K), U)) = 0 := by
      refine hlocal.symm.trans ?_
      rw [Functor.map_zero]
      change (schemeModuleRestrictTopSectionIso U Q).hom 0 = 0
      exact map_zero _
    have hnat := f.val.naturality
      (homOfLE (show U ≤ ⊤ from le_top)).op
    have hnat' := ConcreteCategory.congr_hom hnat
      (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K), ⊤))
    change f.val.app (op U)
      ((Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).presheaf.map
        (homOfLE (show U ≤ ⊤ from le_top)).op 1) =
      Q.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (f.val.app (op ⊤)
          (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K), ⊤))) at hnat'
    rw [map_one, hzero] at hnat'
    rw [map_zero]
    exact hnat'.symm

end PfaffianDescent
