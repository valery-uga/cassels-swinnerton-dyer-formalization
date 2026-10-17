import PfaffianDescent.VoisinFieldBaseChangeSurfaceEvaluationEndpoint
import PfaffianDescent.VoisinFieldBaseChangeBasisPointEvaluation

/-!
# Geometric evaluation from a vanishing hypothesis

The canonical global coordinate evaluator supplies the basis comparison in
the fixed-linear-system descent endpoint. The remaining geometric input is
its vanishing on the selected section at each marked point.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open BundleSectionZeroLocus

universe u

noncomputable section

/-- Every coordinate of a locally free section evaluates to zero at a
field-valued point of its scheme-theoretic zero subscheme. -/
theorem sectionCoordinateOfFreeIso_fieldPoint_eq_zero_of_zeroSubschemeLift
    {L : Type u} [Field L] {X : Scheme.{u}} [IsAffine X]
    {E : X.Modules} (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (σ : E.sections)
    (y : Spec (.of L) ⟶ sectionZeroSubschemeOfFreeIso I e σ)
    (a : I) :
    fieldPointΓevaluation
      (y ≫ sectionZeroSubschemeOfFreeIsoι I e σ)
      (sectionCoordinateOfFreeIso I e σ a) = 0 := by
  let f := y ≫ sectionZeroSubschemeOfFreeIsoι I e σ
  have hz : X.Γevaluation
      (f (IsLocalRing.closedPoint L))
      (sectionCoordinateOfFreeIso I e σ a) = 0 := by
    change X.Γevaluation
      (sectionZeroSubschemeOfFreeIsoι I e σ
        (y (IsLocalRing.closedPoint L)))
      (sectionCoordinateOfFreeIso I e σ a) = 0
    exact idealSheafSubscheme_Γevaluation_eq_zero
      (sectionZeroIdealOfFreeIso I e σ)
      (y (IsLocalRing.closedPoint L)) _
      (sectionCoordinateOfFreeIso_mem_zeroIdeal I e σ a)
  exact fieldPointΓevaluation_eq_zero_of_Γevaluation_eq_zero f _ hz

/-- If every free coordinate of a section vanishes at a field-valued point,
that point factors through the section's zero subscheme over the same field. -/
theorem exists_sectionZeroSubschemeOfFreeIso_fieldPoint_lift_of_coordinates_eq_zero
    {L : Type u} [Field L] {X : Scheme.{u}} [IsAffine X]
    {E : X.Modules} (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (σ : E.sections) (x : Spec (.of L) ⟶ X)
    (hzero : ∀ a : I,
      fieldPointΓevaluation x (sectionCoordinateOfFreeIso I e σ a) = 0) :
    ∃ y : Spec (.of L) ⟶ sectionZeroSubschemeOfFreeIso I e σ,
      y ≫ sectionZeroSubschemeOfFreeIsoι I e σ = x := by
  let J := sectionZeroIdealOfFreeIso I e σ
  let x₀ : X := x (IsLocalRing.closedPoint L)
  have hsupport : x₀ ∈ J.support := by
    change x₀ ∈ X.zeroLocus
      (↑(Ideal.span (Set.range (fun a : I =>
        sectionCoordinateOfFreeIso I e σ a))) : Set Γ(X, ⊤))
    rw [Scheme.mem_zeroLocus_iff]
    intro f hf
    apply (X.evaluation_eq_zero_iff_notMem_basicOpen
      (U := (⊤ : X.Opens)) x₀ (Set.mem_univ x₀) f).mp
    change f ∈ RingHom.ker (X.Γevaluation x₀).hom
    apply (Ideal.span_le.mpr ?_) hf
    rintro _ ⟨a, rfl⟩
    exact Γevaluation_eq_zero_of_fieldPointΓevaluation_eq_zero
      x _ (hzero a)
  have hrange : x₀ ∈ Set.range J.subschemeι := by
    rw [J.range_subschemeι]
    exact hsupport
  let y₀ : Spec (.of ((Spec (.of L)).residueField
      (IsLocalRing.closedPoint L : Spec (.of L)))) ⟶ J.subscheme :=
    closedImmersionFieldPointLiftOfMemRange J.subschemeι x
      (IsLocalRing.closedPoint L) hrange
  let f := AllCharacteristics.specFieldClosedPointResidueIso L
  let y : Spec (.of L) ⟶ J.subscheme :=
    Spec.map f.toCommRingCatIso.hom ≫ y₀
  have hy₀ : y₀ ≫ J.subschemeι =
      (Spec (.of L)).fromSpecResidueField
        (IsLocalRing.closedPoint L : Spec (.of L)) ≫ x :=
    closedImmersionFieldPointLiftOfMemRange_comp J.subschemeι x
      (IsLocalRing.closedPoint L : Spec (.of L)) hrange
  have hresidue : Spec.map f.toCommRingCatIso.hom ≫
      (Spec (.of L)).fromSpecResidueField
        (IsLocalRing.closedPoint L : Spec (.of L)) =
      𝟙 (Spec (.of L)) := by
    have hsymm :=
      AllCharacteristics.specFieldClosedPointResidueIso_symm_specMap L
    change Spec.map f.toCommRingCatIso.inv =
      (Spec (.of L)).fromSpecResidueField
        (IsLocalRing.closedPoint L : Spec (.of L)) at hsymm
    rw [← hsymm, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  refine ⟨y, ?_⟩
  change y ≫ J.subschemeι = x
  calc
    y ≫ J.subschemeι =
        Spec.map f.toCommRingCatIso.hom ≫
          (y₀ ≫ J.subschemeι) := Category.assoc _ _ _
    _ = Spec.map f.toCommRingCatIso.hom ≫
          ((Spec (.of L)).fromSpecResidueField
            (IsLocalRing.closedPoint L : Spec (.of L)) ≫ x) :=
      congrArg (fun q => Spec.map f.toCommRingCatIso.hom ≫ q) hy₀
    _ = (Spec.map f.toCommRingCatIso.hom ≫
          (Spec (.of L)).fromSpecResidueField
            (IsLocalRing.closedPoint L : Spec (.of L))) ≫ x :=
      (Category.assoc _ _ _).symm
    _ = x := by rw [hresidue, Category.id_comp]

/-- A field-valued point factors through a section's zero subscheme exactly
when all coordinates of that section vanish at the point. -/
theorem sectionZeroSubschemeOfFreeIso_fieldPoint_lift_iff_coordinates_eq_zero
    {L : Type u} [Field L] {X : Scheme.{u}} [IsAffine X]
    {E : X.Modules} (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (σ : E.sections) (x : Spec (.of L) ⟶ X) :
    (∃ y : Spec (.of L) ⟶ sectionZeroSubschemeOfFreeIso I e σ,
      y ≫ sectionZeroSubschemeOfFreeIsoι I e σ = x) ↔
      ∀ a : I,
        fieldPointΓevaluation x (sectionCoordinateOfFreeIso I e σ a) = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ a
    exact sectionCoordinateOfFreeIso_fieldPoint_eq_zero_of_zeroSubschemeLift
      I e σ y a
  · exact exists_sectionZeroSubschemeOfFreeIso_fieldPoint_lift_of_coordinates_eq_zero
      I e σ x

/-- Reading a coordinate through the top-open linear equivalence agrees
with the coordinate of the underlying categorical global section. -/
theorem moduleOpenTopLinearEquivOfFreeIsoOver_sectionCoordinate
    {L : Type u} [Field L] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of L))
    {E : X.Modules} (I : Type u) [Fintype I] [DecidableEq I]
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (σ : E.sections) (a : I) :
    moduleOpenTopLinearEquivOfFreeIsoOver p I E e
      (schemeModuleSectionsEquivTop E σ) a =
    sectionCoordinateOfFreeIso I e σ a := by
  change ((freeCoordinateMap I a).val.app (Opposite.op ⊤)).hom
    ((e.inv.val.app (Opposite.op ⊤)).hom (σ.val (Opposite.op ⊤))) = _
  unfold sectionCoordinateOfFreeIso freeSectionCoordinate unitSectionAtTop
  rw [SheafOfModules.unitHomEquiv_comp_apply]
  rw [Equiv.apply_symm_apply]
  rfl

/-- The chosen free coordinate of a section evaluates to zero at a
field-valued point of that section's zero subscheme. -/
theorem freeCoordinateEvaluation_eq_zero_of_zeroSubschemeLift
    {L : Type u} [Field L] {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (.of L))
    {E : X.Modules} (I : Type u) [Fintype I] [DecidableEq I]
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (σ : E.sections) (a : I)
    (x : Spec (.of L) ⟶ X)
    (y : Spec (.of L) ⟶ sectionZeroSubschemeOfFreeIso I e σ)
    (hy : y ≫ sectionZeroSubschemeOfFreeIsoι I e σ = x) :
    fieldPointΓevaluation x
      (moduleOpenTopLinearEquivOfFreeIsoOver p I E e
        (schemeModuleSectionsEquivTop E σ) a) = 0 := by
  rw [moduleOpenTopLinearEquivOfFreeIsoOver_sectionCoordinate]
  rw [← hy]
  exact sectionCoordinateOfFreeIso_fieldPoint_eq_zero_of_zeroSubschemeLift
    I e σ y a

/-- The named open evaluator on a categorical restricted section is just
field-point evaluation of that section's free coordinate. -/
theorem fieldBaseChangeOpenPointCoordinateEvaluation_restrictedSection
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
    (hxU : xU ≫ (U.ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (a : I) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let ML := (Scheme.Modules.pullback g).obj M
    let pL := schemeFieldBaseChangeToField (L := L) base
    let eV := schemeFieldBaseChangeOpenRestrictedFreeIso base M U I t
    let qV := moduleRestrictTopLinearEquivOpenSectionsOver pL ML V
    let xV := schemeFieldBaseChangeOpenPoint base U xU hxU
    ∀ σ : (ML.restrict V.ι).sections,
      fieldBaseChangeOpenPointCoordinateEvaluation
        base M U I t xU hxU a
        (qV (schemeModuleSectionsEquivTop (ML.restrict V.ι) σ)) =
      fieldPointΓevaluation xV
        (sectionCoordinateOfFreeIso I eV σ a) := by
  dsimp only
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  let pL := schemeFieldBaseChangeToField (L := L) base
  let pV := V.ι ≫ pL
  let eV := schemeFieldBaseChangeOpenRestrictedFreeIso (L := L) base M U I t
  let xV := schemeFieldBaseChangeOpenPoint (L := L) base U xU hxU
  let qV := moduleRestrictTopLinearEquivOpenSectionsOver pL ML V
  intro σ
  let w := schemeModuleSectionsEquivTop (ML.restrict V.ι) σ
  have hq : qV.symm (qV w) = w := qV.symm_apply_apply w
  have hval := congrArg (fun z => fieldPointΓevaluation xV
    (moduleOpenTopLinearEquivOfFreeIsoOver pV I (ML.restrict V.ι) eV z a)) hq
  have hc := moduleOpenTopLinearEquivOfFreeIsoOver_sectionCoordinate
    pV I eV σ a
  have hcoord := congrArg (fieldPointΓevaluation xV) hc
  unfold fieldBaseChangeOpenPointCoordinateEvaluation
  rw [hval, hcoord]

/-- A lift of the canonical field point to the local zero subscheme of a
global pulled-back section makes the global coordinate functional vanish. -/
theorem fieldBaseChangeGlobalPointCoordinateEvaluationLinearMap_eq_zero_of_zeroSubschemeLift
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
    (hxU : xU ≫ (U.ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (a : I) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let ML := (Scheme.Modules.pullback g).obj M
    let pL := schemeFieldBaseChangeToField (L := L) base
    let eV := schemeFieldBaseChangeOpenRestrictedFreeIso base M U I t
    let xV := schemeFieldBaseChangeOpenPoint base U xU hxU
    ∀ (σ : ML.sections)
      (y : Spec (.of L) ⟶ sectionZeroSubschemeOfFreeIso I eV
        (restrictModuleSection V.ι ML σ)),
      y ≫ sectionZeroSubschemeOfFreeIsoι I eV
        (restrictModuleSection V.ι ML σ) = xV →
      fieldBaseChangeGlobalPointCoordinateEvaluationLinearMap
        base M U I t xU hxU a
        ((schemeModuleGlobalSectionsOverEquivSections pL ML).symm σ) = 0 := by
  dsimp only
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  let pL := schemeFieldBaseChangeToField (L := L) base
  let pV := V.ι ≫ pL
  let eV := schemeFieldBaseChangeOpenRestrictedFreeIso (L := L) base M U I t
  let xV := schemeFieldBaseChangeOpenPoint (L := L) base U xU hxU
  letI : IsAffine (V : Scheme.{u}) :=
    isAffine_schemeFieldBaseChangeOpen (L := L) base U
  intro σ y hy
  rw [fieldBaseChangeGlobalPointCoordinateEvaluationLinearMap_apply]
  rw [fieldBaseChangeOpenPointCoordinateEvaluationLinearMap_apply]
  rw [fieldBaseChangeOpenPointCoordinateEvaluation_restrictedSection]
  have hz := freeCoordinateEvaluation_eq_zero_of_zeroSubschemeLift
    pV I eV (restrictModuleSection V.ι ML σ) a xV y hy
  rw [moduleOpenTopLinearEquivOfFreeIsoOver_sectionCoordinate] at hz
  exact hz

/-- A chart lift of a marked point over the field-valued generic point is
automatically a field-valued point of its affine surface open. -/
theorem SchemeModuleFiniteFreeAffineCover.projectiveSectionMarkedLift_surfaceChart_toField
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {A Q : Scheme.{u}}
    (base : A ⟶ Spec (.of K)) (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u}
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    (marked : Q ⟶ A) (hmarked : marked ≫ base = qBase)
    (r : Spec (.of L) ⟶ Q)
    (hrBase : r ≫ qBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (ri : Spec (.of L) ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (hri : ri ≫ C.projectiveSectionOpenCoverToSurface base M ij =
      r ≫ marked) :
    (ri ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij) ≫
      ((C.U ij.1).ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  calc
    (ri ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij) ≫
        ((C.U ij.1).ι ≫ base) =
      (ri ≫ C.projectiveSectionOpenCoverToSurface base M ij) ≫ base := by
        simp only [SchemeModuleFiniteFreeAffineCover.projectiveSectionOpenCoverToSurface,
          Category.assoc]
    _ = (r ≫ marked) ≫ base := congrArg (fun f => f ≫ base) hri
    _ = r ≫ qBase := by rw [Category.assoc, hmarked]
    _ = Spec.map (CommRingCat.ofHom (algebraMap K L)) := hrBase

/-- In the surface-basis endpoint, the geometric evaluator and all of its
basis comparisons are canonical. It suffices to prove that this evaluator
annihilates the chosen nonzero section at each marked chart point. -/
theorem SchemeModuleFiniteFreeAffineCover.no_generic_projectiveSection_fieldMember_of_geometricEvaluationVanishing
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {A Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    [Fintype C.ι] [DecidableEq C.ι]
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (havoid : Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField) ∉
      fixedLinearSystemBadLocus qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M))
    (r : Spec (.of L) ⟶ Q)
    (hr : r (IsLocalRing.closedPoint L) =
      Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField))
    (hrBase : r ≫ qBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (s : SchemeModuleGlobalSectionsOver
      (schemeFieldBaseChangeToField (L := L) base)
      ((Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := L) base)).obj M))
    (hs : s ≠ 0)
    (hvanishing : ∀ (i : Fin n)
      (ij : (C.projectiveSectionOpenCover base M).I₀)
      (ri : Spec (.of L) ⟶
        (C.projectiveSectionOpenCover base M).X ij)
      (hri : ri ≫ C.projectiveSectionOpenCoverToSurface base M ij =
        r ≫ marked i)
      (a : I),
      let hx := C.projectiveSectionMarkedLift_surfaceChart_toField
        base M qBase (marked i) (hmarked i) r hrBase ij ri hri
      let U := C.U ij.1
      let xU := ri ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij
      letI : IsAffine (U : Scheme.{u}) := C.affine ij.1
      fieldBaseChangeGlobalPointCoordinateEvaluationLinearMap
        base M U I (C.trivialization ij.1) xU hx a s = 0) :
    False := by
  apply C.no_generic_projectiveSection_fieldMember_of_surfaceBasisEvaluation
    base M qBase n marked hmarked havoid r hr hrBase s hs
  intro i ij ri hri a
  let hx := C.projectiveSectionMarkedLift_surfaceChart_toField
    base M qBase (marked i) (hmarked i) r hrBase ij ri hri
  let U := C.U ij.1
  let xU := ri ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij
  letI : IsAffine (U : Scheme.{u}) := C.affine ij.1
  refine ⟨fieldBaseChangeGlobalPointCoordinateEvaluationLinearMap
    base M U I (C.trivialization ij.1) xU hx a, ?_, ?_⟩
  · intro k
    rw [C.fieldBaseChangeGlobalPointCoordinateEvaluationLinearMap_basis_eq_surface
      base M ij ri hx a k]
  · have hv := hvanishing i ij ri hri a
    dsimp only at hv
    rw [hv]

/-- The fixed-linear-system contradiction from literal zero-subscheme lifts
of the selected pulled-back section at every marked chart point. -/
theorem SchemeModuleFiniteFreeAffineCover.no_generic_projectiveSection_fieldMember_of_geometricZeroLifts
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {A Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    [Fintype C.ι] [DecidableEq C.ι]
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (havoid : Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField) ∉
      fixedLinearSystemBadLocus qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M))
    (r : Spec (.of L) ⟶ Q)
    (hr : r (IsLocalRing.closedPoint L) =
      Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField))
    (hrBase : r ≫ qBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (σ : ((Scheme.Modules.pullback
      (schemeFieldBaseChangeToOriginal (L := L) base)).obj M).sections)
    (hs : (schemeModuleGlobalSectionsOverEquivSections
      (schemeFieldBaseChangeToField (L := L) base)
      ((Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)).symm σ ≠ 0)
    (hzeroLifts : ∀ (i : Fin n)
      (ij : (C.projectiveSectionOpenCover base M).I₀)
      (ri : Spec (.of L) ⟶
        (C.projectiveSectionOpenCover base M).X ij)
      (hri : ri ≫ C.projectiveSectionOpenCoverToSurface base M ij =
        r ≫ marked i),
      let hx := C.projectiveSectionMarkedLift_surfaceChart_toField
        base M qBase (marked i) (hmarked i) r hrBase ij ri hri
      let U := C.U ij.1
      let xU := ri ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij
      let g := schemeFieldBaseChangeToOriginal (L := L) base
      let V := g ⁻¹ᵁ U
      let ML := (Scheme.Modules.pullback g).obj M
      let eV := schemeFieldBaseChangeOpenRestrictedFreeIso base M U I
        (C.trivialization ij.1)
      letI : IsAffine (U : Scheme.{u}) := C.affine ij.1
      ∃ y : Spec (.of L) ⟶ sectionZeroSubschemeOfFreeIso I eV
          (restrictModuleSection V.ι ML σ),
        y ≫ sectionZeroSubschemeOfFreeIsoι I eV
          (restrictModuleSection V.ι ML σ) =
        schemeFieldBaseChangeOpenPoint base U xU hx) :
    False := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let ML := (Scheme.Modules.pullback g).obj M
  let pL := schemeFieldBaseChangeToField (L := L) base
  let s := (schemeModuleGlobalSectionsOverEquivSections pL ML).symm σ
  apply C.no_generic_projectiveSection_fieldMember_of_geometricEvaluationVanishing
    base M qBase n marked hmarked havoid r hr hrBase s hs
  intro i ij ri hri a
  let hx := C.projectiveSectionMarkedLift_surfaceChart_toField
    base M qBase (marked i) (hmarked i) r hrBase ij ri hri
  let U := C.U ij.1
  let xU := ri ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij
  let V := g ⁻¹ᵁ U
  let eV := schemeFieldBaseChangeOpenRestrictedFreeIso (L := L) base M U I
    (C.trivialization ij.1)
  letI : IsAffine (U : Scheme.{u}) := C.affine ij.1
  obtain ⟨y, hy⟩ := hzeroLifts i ij ri hri
  have hz := fieldBaseChangeGlobalPointCoordinateEvaluationLinearMap_eq_zero_of_zeroSubschemeLift
    base M U I (C.trivialization ij.1) xU hx a σ y hy
  dsimp only at hz ⊢
  rw [hz]

/-- Coordinate-wise vanishing of the selected geometric section at every
marked chart point supplies the zero-subscheme lifts automatically and hence
contradicts generic fixed-linear-system avoidance. -/
theorem SchemeModuleFiniteFreeAffineCover.no_generic_projectiveSection_fieldMember_of_geometricCoordinates
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {A Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    [Fintype C.ι] [DecidableEq C.ι]
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (havoid : Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField) ∉
      fixedLinearSystemBadLocus qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M))
    (r : Spec (.of L) ⟶ Q)
    (hr : r (IsLocalRing.closedPoint L) =
      Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField))
    (hrBase : r ≫ qBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (σ : ((Scheme.Modules.pullback
      (schemeFieldBaseChangeToOriginal (L := L) base)).obj M).sections)
    (hs : (schemeModuleGlobalSectionsOverEquivSections
      (schemeFieldBaseChangeToField (L := L) base)
      ((Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)).symm σ ≠ 0)
    (hcoordinates : ∀ (i : Fin n)
      (ij : (C.projectiveSectionOpenCover base M).I₀)
      (ri : Spec (.of L) ⟶
        (C.projectiveSectionOpenCover base M).X ij)
      (hri : ri ≫ C.projectiveSectionOpenCoverToSurface base M ij =
        r ≫ marked i),
      let hx := C.projectiveSectionMarkedLift_surfaceChart_toField
        base M qBase (marked i) (hmarked i) r hrBase ij ri hri
      let U := C.U ij.1
      let xU := ri ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij
      let g := schemeFieldBaseChangeToOriginal (L := L) base
      let V := g ⁻¹ᵁ U
      let ML := (Scheme.Modules.pullback g).obj M
      let eV := schemeFieldBaseChangeOpenRestrictedFreeIso base M U I
        (C.trivialization ij.1)
      letI : IsAffine (U : Scheme.{u}) := C.affine ij.1
      ∀ a : I,
        fieldPointΓevaluation
          (schemeFieldBaseChangeOpenPoint base U xU hx)
          (sectionCoordinateOfFreeIso I eV
            (restrictModuleSection V.ι ML σ) a) = 0) :
    False := by
  apply C.no_generic_projectiveSection_fieldMember_of_geometricZeroLifts
    base M qBase n marked hmarked havoid r hr hrBase σ hs
  intro i ij ri hri
  let hx := C.projectiveSectionMarkedLift_surfaceChart_toField
    base M qBase (marked i) (hmarked i) r hrBase ij ri hri
  let U := C.U ij.1
  let xU := ri ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  let eV := schemeFieldBaseChangeOpenRestrictedFreeIso (L := L) base M U I
    (C.trivialization ij.1)
  let xV := schemeFieldBaseChangeOpenPoint (L := L) base U xU hx
  letI : IsAffine (U : Scheme.{u}) := C.affine ij.1
  letI : IsAffine (V : Scheme.{u}) :=
    isAffine_schemeFieldBaseChangeOpen (L := L) base U
  have hzero := hcoordinates i ij ri hri
  dsimp only at hzero
  exact exists_sectionZeroSubschemeOfFreeIso_fieldPoint_lift_of_coordinates_eq_zero
    I eV (restrictModuleSection V.ι ML σ) xV hzero

end

end PfaffianDescent
