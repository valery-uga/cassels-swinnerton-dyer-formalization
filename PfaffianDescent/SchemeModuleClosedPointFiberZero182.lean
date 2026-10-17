import PfaffianDescent.SchemeModuleUnitHomStalkPrincipalQuotient
import PfaffianDescent.SchemeModuleClosedPointRankOneFiberSequence
import PfaffianDescent.CorayNormalizationClosedPointIdealStalk
import PfaffianDescent.CorayTildeActualStalkSupport
import PfaffianDescent.SchemeModuleRestrictStalkLinear
import PfaffianDescent.VoisinHypersurfaceCokernel

/-! Actual support of the original unit-to-line cokernel forces the
original adjunction-unit fiber restriction to vanish. No fiber-zero,
DVR, residue-comparison or connecting-map certificate is an input.
SOURCE ONLY / UNVERIFIED; root owns all compiler checks. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The coefficient in any actual native frame belongs to the maximal
ideal whenever the SAME original cokernel stalk is nonzero. -/
theorem schemeModuleUnitHomStalkCoefficient_mem_maximalIdeal_of_support182
    (M : X.Modules) (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) (x : X)
    (eW : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (hx : x ∈ Coray.schemeModuleStalkSupport (cokernel φ)) :
    schemeModuleUnitHomStalkCoefficient M φ x eW ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  classical
  let R := X.presheaf.stalk x
  let F := schemeModuleStalkModuleFunctor X x
  let a : R := schemeModuleUnitHomStalkCoefficient M φ x eW
  let E := schemeModuleUnitHomStalkCokernelIsoPrincipalQuotient M φ x eW
  letI : Nontrivial ((F.obj (cokernel φ))) := hx
  apply (IsLocalRing.mem_maximalIdeal a).mpr
  change ¬ IsUnit a
  intro ha
  have htop : Ideal.span ({a} : Set R) = ⊤ := Ideal.span_singleton_eq_top.mpr ha
  have hzero (z : R ⧸ Ideal.span ({a} : Set R)) : z = 0 := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [htop]
    trivial
  have hsub : Subsingleton (F.obj (cokernel φ)) := ⟨fun y z =>
    E.toLinearEquiv.injective ((hzero (E.hom.hom y)).trans (hzero (E.hom.hom z)).symm)⟩
  exact not_subsingleton (F.obj (cokernel φ)) hsub

/-- Tensor-stalk naturality expressed in the genuine induced right-factor
frame. The original ideal inclusion is not changed to a scalar surrogate. -/
theorem schemeModuleIdealTensor_stalk_frame_square182
    (U : X.Opens) (x : U) (M : X.Modules)
    (eM : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (I : X.Modules) (j : I ⟶ SheafOfModules.unit X.ringCatSheaf) :
    let F := schemeModuleStalkModuleFunctor X (U.ι x)
    let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    let t := fun A : X.Modules =>
      schemeModuleTensorStalkModuleIsoOfLocalTrivialization U x A M eM
    let eW := F.mapIso (schemeModuleTensorUnitLeftIso M).symm ≪≫ t O ≪≫
      schemeModuleUnitStalkIso X (U.ι x)
    let beta := schemeModuleTensorMap j (𝟙 M) ≫ (schemeModuleTensorUnitLeftIso M).hom
    F.map beta ≫ eW.hom =
      (t I).hom ≫ F.map j ≫ (schemeModuleUnitStalkIso X (U.ι x)).hom := by
  dsimp only
  let F := schemeModuleStalkModuleFunctor X (U.ι x)
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let t := fun A : X.Modules =>
    schemeModuleTensorStalkModuleIsoOfLocalTrivialization U x A M eM
  let mu := schemeModuleTensorUnitLeftIso M
  have hn : F.map (schemeModuleTensorMap j (𝟙 M)) ≫ (t O).hom =
      (t I).hom ≫ F.map j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact ConcreteCategory.congr_hom
      (schemeModuleTensorStalkIsoOfLocalTrivialization_naturality U x eM j) z
  have hc : F.map mu.hom ≫ F.map mu.inv =
      𝟙 (F.obj (schemeModuleTensor O M)) := by
    rw [← F.map_comp, mu.hom_inv_id, F.map_id]
  change F.map (schemeModuleTensorMap j (𝟙 M) ≫ mu.hom) ≫
      (F.map mu.inv ≫ (t O).hom ≫ (schemeModuleUnitStalkIso X (U.ι x)).hom) = _
  rw [F.map_comp]
  calc
    _ = F.map (schemeModuleTensorMap j (𝟙 M)) ≫ (t O).hom ≫
        (schemeModuleUnitStalkIso X (U.ι x)).hom := by
      simp only [← Category.assoc]
      rw [Category.assoc (F.map (schemeModuleTensorMap j (𝟙 M)))
        (F.map mu.hom) (F.map mu.inv), hc, Category.comp_id]
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun z => z ≫ (schemeModuleUnitStalkIso X (U.ι x)).hom) hn

/-- Generic actual closed-point bridge. Its sole support premise is
membership in the nonzero stalk locus of the literal original cokernel.
Original M, phi and the actual intrinsic fiber/adjunction unit are retained. -/
theorem schemeModuleUnitHom_closedPoint_fiber_zero_of_cokernel_support182
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) (P : closedPoints X)
    (hP : P.1 ∈ Coray.schemeModuleStalkSupport (cokernel φ)) :
    φ ≫ (Scheme.Modules.pullbackPushforwardAdjunction
      (X.fromSpecResidueField P.1)).unit.app M = 0 := by
  classical
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let I := (show X.Modules from closedImmersionModule i)
  let j := closedImmersionModuleToUnit i
  let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M
  let Q := (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj M)
  obtain ⟨hzero, _hS, _hIso⟩ :=
    schemeModuleLocallyRankOne_closedPoint_idealTensor_fiberSequence P M hM
  let beta := schemeModuleTensorMap j (𝟙 M) ≫ (schemeModuleTensorUnitLeftIso M).hom
  have hbeta : beta ≫ eta = 0 := hzero
  apply schemeModule_hom_ext_of_stalkMap_eq
  intro y
  let F := schemeModuleStalkModuleFunctor X y
  have hnative : F.map (φ ≫ eta) = 0 := by
    by_cases hy : y = P.1
    · subst y
      obtain ⟨U, hPU, ⟨eM⟩⟩ := hM P.1
      let x : U := ⟨P.1, hPU⟩
      let t := fun A : X.Modules =>
        schemeModuleTensorStalkModuleIsoOfLocalTrivialization U x A M eM
      let eO := schemeModuleUnitStalkIso X P.1
      let eW := F.mapIso (schemeModuleTensorUnitLeftIso M).symm ≪≫ t O ≪≫ eO
      let a := schemeModuleUnitHomStalkCoefficient M φ P.1 eW
      have ha : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk P.1) :=
        schemeModuleUnitHomStalkCoefficient_mem_maximalIdeal_of_support182 M φ P.1 eW hP
      letI := schemeModuleStalkModule I P.1
      have hrange := Coray.closedPointIdeal_stalk_range_eq_maximalIdeal X P
      have hamem : a ∈ LinearMap.range (closedImmersionModuleStalkToRingLinearMap i P.1) := by
        rw [hrange]
        exact ha
      obtain ⟨z, hz⟩ := hamem
      let w : F.obj (schemeModuleTensor I M) := (t I).inv.hom z
      have hsquare : F.map beta ≫ eW.hom =
          (t I).hom ≫ F.map j ≫ eO.hom :=
        schemeModuleIdealTensor_stalk_frame_square182 U x M eM I j
      have hw : (F.map beta ≫ eW.hom).hom w = a := by
        rw [hsquare]
        change (closedImmersionModuleStalkToRingLinearMap i P.1)
          ((t I).hom.hom ((t I).inv.hom z)) = a
        have htinv : (t I).hom.hom ((t I).inv.hom z) = z :=
          ConcreteCategory.congr_hom (t I).inv_hom_id z
        exact (congrArg (closedImmersionModuleStalkToRingLinearMap i P.1) htinv).trans hz
      have hs : (F.map beta).hom w = (F.map φ).hom (eO.inv.hom (1 : X.presheaf.stalk P.1)) := by
        apply eW.toLinearEquiv.injective
        exact hw
      have hcomp : F.map beta ≫ F.map eta = 0 := by
        rw [← F.map_comp, hbeta, F.map_zero]
      have hunit : (F.map eta).hom ((F.map φ).hom (eO.inv.hom (1 : X.presheaf.stalk P.1))) = 0 := by
        rw [← hs]
        exact ConcreteCategory.congr_hom hcomp w
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      let r : X.presheaf.stalk P.1 := eO.hom.hom v
      have hv : v = r • eO.inv.hom (1 : X.presheaf.stalk P.1) := by
        have hcancel : eO.inv.hom (eO.hom.hom v) = v :=
          ConcreteCategory.congr_hom eO.hom_inv_id v
        calc
          v = eO.inv.hom r := hcancel.symm
          _ = eO.inv.hom (r • (1 : X.presheaf.stalk P.1)) :=
            congrArg eO.inv.hom (mul_one r).symm
          _ = r • eO.inv.hom (1 : X.presheaf.stalk P.1) :=
            eO.inv.hom.map_smul r (1 : X.presheaf.stalk P.1)
      rw [F.map_comp]
      change (F.map eta).hom ((F.map φ).hom v) = 0
      rw [hv, (F.map φ).hom.map_smul, (F.map eta).hom.map_smul, hunit, smul_zero]
    · have hoff : y ∉ Set.range i := by
        rintro ⟨z, hz⟩
        exact hy (hz.symm.trans (Scheme.fromSpecResidueField_apply P.1 z))
      have hQsub : Subsingleton (F.obj Q) := by
        change Subsingleton (Q.presheaf.stalk y)
        exact schemeModulePushforward_stalk_subsingleton_off_range i
          ((Scheme.Modules.pullback i).obj M) y hoff
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      exact @Subsingleton.elim (F.obj Q) hQsub _ _
  apply AddCommGrpCat.hom_ext
  ext v
  change (F.map (φ ≫ eta)).hom v = (F.map (0 : O ⟶ Q)).hom v
  rw [hnative, F.map_zero]
  rfl

/-- The exact SAME given original section is used, with support of its
whole categorical cokernel; no replacement section or reduced quotient. -/
theorem schemeModuleTopSectionHom_closedPoint_fiber_zero182
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (s : M.val.obj (op ⊤)) (P : closedPoints X)
    (hP : P.1 ∈ Coray.schemeModuleStalkSupport (cokernel (schemeModuleTopSectionHom M s))) :
    schemeModuleTopSectionHom M s ≫
      (Scheme.Modules.pullbackPushforwardAdjunction
        (X.fromSpecResidueField P.1)).unit.app M = 0 :=
  schemeModuleUnitHom_closedPoint_fiber_zero_of_cokernel_support182 M hM
    (schemeModuleTopSectionHom M s) P hP

end PfaffianDescent
