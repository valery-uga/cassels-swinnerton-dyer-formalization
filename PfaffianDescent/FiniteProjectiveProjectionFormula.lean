import PfaffianDescent.FiniteProjectiveTwistTriviality
import PfaffianDescent.LocalExtResidueInjective
import PfaffianDescent.FiniteSchemeAlgebra
import PfaffianDescent.SchemeAffineFunctions
import PfaffianDescent.VoisinSerreRestrictionNonvanishing

/-!
# A supported projection formula from one trivializing chart

For a closed subscheme contained in an open chart on which a twisting module
is trivial, the restriction--pushforward unit on the twisted quotient term is
an isomorphism.  The proof is stalkwise: it is the adjunction triangle on the
chart, while away from the chart both source and target have zero stalks.
-/

noncomputable section

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
open TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open HomogeneousLocalization
open ProjectiveNegativeTwist

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false

/-- At a point of an open immersion, invertibility after restriction implies
invertibility on the original scheme-module stalk. -/
theorem schemeModuleStalkMap_isIso_of_restrict
    {X : Scheme.{u}} (U : X.Opens) (x : U)
    {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)] :
    IsIso ((schemeModuleStalkModuleFunctor X (U.ι x)).map f) := by
  let G := Scheme.Modules.toPresheaf (U : Scheme) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hlocal : IsIso
      (G.map ((Scheme.Modules.restrictFunctor U.ι).map f)) := by
    exact Functor.map_isIso G ((Scheme.Modules.restrictFunctor U.ι).map f)
  have hstalk : IsIso ((schemeModuleStalkFunctor X (U.ι x)).map f) := by
    exact (NatIso.isIso_map_iff
      (Scheme.Modules.restrictStalkNatIso U.ι x) f).mp hlocal
  have hforget : IsIso
      ((forget₂ (ModuleCat (X.presheaf.stalk (U.ι x))) AddCommGrpCat).map
        ((schemeModuleStalkModuleFunctor X (U.ι x)).map f)) := by
    change IsIso ((schemeModuleStalkFunctor X (U.ι x)).map f)
    exact hstalk
  letI : IsIso
      ((forget₂ (ModuleCat (X.presheaf.stalk (U.ι x))) AddCommGrpCat).map
        ((schemeModuleStalkModuleFunctor X (U.ι x)).map f)) := hforget
  exact isIso_of_reflects_iso
    ((schemeModuleStalkModuleFunctor X (U.ι x)).map f)
    (forget₂ (ModuleCat (X.presheaf.stalk (U.ι x))) AddCommGrpCat)

/-- The restriction--pushforward unit of the twisted closed-immersion target
is globally invertible when the support lies in one trivializing chart and
the twist is locally trivial on a cover. -/
theorem closedImmersionIdealTwistTarget_restrictAdjunctionUnit_isIso
    {X Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)]
    (T : X.Modules)
    (eT : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf)
    {I : Type u} (V : I → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ k, (SheafOfModules.overFunctor X.ringCatSheaf (V k)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V k)))) :
    IsIso ((Scheme.Modules.restrictAdjunction U.ι).unit.app
      (closedImmersionIdealTwistSequence (j ≫ U.ι) T).X₃) := by
  let i : Z ⟶ X := j ≫ U.ι
  let M : X.Modules := (closedImmersionIdealTwistSequence i T).X₃
  let eta : M ⟶ (Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj M) :=
    (Scheme.Modules.restrictAdjunction U.ι).unit.app M
  apply schemeModuleMap_isIso_of_stalk eta
  intro x
  by_cases hx : x ∈ U
  · let xU : U := ⟨x, hx⟩
    haveI : IsIso ((Scheme.Modules.restrictFunctor U.ι).map eta) := by
      exact restrictAdjunctionUnit_restrict_isIso U.ι M
    exact schemeModuleStalkMap_isIso_of_restrict U xU eta
  · have hxRange : x ∉ Set.range i := by
      rintro ⟨z, hz⟩
      apply hx
      rw [← hz]
      exact (j z).property
    have hsrcSub : Subsingleton (M.presheaf.stalk x) := by
      exact closedImmersionPushforwardTwist_stalk_subsingleton_off_range_of_coversTop_iso_unit
        i T V hV eV x hxRange
    let N : X.Modules := (Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj M)
    let E : N ≅ (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf) :=
      pushforwardRestrictClosedImmersionIdealTwistTargetFactorThroughOpenIso
        U j T eT
    have hpushSub : Subsingleton
        (((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)).presheaf.stalk x) :=
      schemeModulePushforward_stalk_subsingleton_off_range i
        (SheafOfModules.unit Z.ringCatSheaf) x hxRange
    have htgtSub : Subsingleton (N.presheaf.stalk x) :=
      schemeModule_stalk_subsingleton_of_iso x E hpushSub
    let src := (schemeModuleStalkModuleFunctor X x).obj M
    let tgt := (schemeModuleStalkModuleFunctor X x).obj N
    letI : Subsingleton src := by
      change Subsingleton (M.presheaf.stalk x)
      exact hsrcSub
    letI : Subsingleton tgt := by
      change Subsingleton (N.presheaf.stalk x)
      exact htgtSub
    have hsrc : IsZero src := ModuleCat.isZero_of_subsingleton src
    have htgt : IsZero tgt := ModuleCat.isZero_of_subsingleton tgt
    let e : src ≅ tgt := hsrc.iso htgt
    have he : (schemeModuleStalkModuleFunctor X x).map eta = e.hom :=
      hsrc.eq_of_src _ _
    rw [he]
    infer_instance

/-- The supported projection-formula isomorphism obtained from the global
restriction--pushforward unit and the chart-level tensor comparison. -/
noncomputable def closedImmersionIdealTwistTargetProjectionFormulaIso
    {X Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)]
    (T : X.Modules)
    (eT : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf)
    {I : Type u} (V : I → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ k, (SheafOfModules.overFunctor X.ringCatSheaf (V k)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V k)))) :
    schemeModuleTensor
        ((Scheme.Modules.pushforward (j ≫ U.ι)).obj
          (SheafOfModules.unit Z.ringCatSheaf)) T ≅
      (Scheme.Modules.pushforward (j ≫ U.ι)).obj
        (SheafOfModules.unit Z.ringCatSheaf) := by
  let M := schemeModuleTensor
    ((Scheme.Modules.pushforward (j ≫ U.ι)).obj
      (SheafOfModules.unit Z.ringCatSheaf)) T
  let eta := (Scheme.Modules.restrictAdjunction U.ι).unit.app M
  letI : IsIso eta :=
    closedImmersionIdealTwistTarget_restrictAdjunctionUnit_isIso
      U j T eT V hV eV
  exact asIso eta ≪≫
    pushforwardRestrictClosedImmersionIdealTwistTargetFactorThroughOpenIso
      U j T eT

/-- For a finite closed subscheme of a homogeneous projective polynomial
quotient, tensoring its structure-sheaf pushforward by `O(2)` is canonically
identified with the ordinary pushforward.  This is the projection-formula
comparison required in the Serre restriction sequence. -/
noncomputable def finiteProjectiveClosedSubschemePositiveTwoProjectionFormulaIso
    {K : Type u} {sigma : Type} [Field K] [Infinite K] [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ AllCharacteristics.HomogeneousProjective.toBase I)] :
    (closedImmersionIdealTwistSequence i
      (positiveSheafOfModules (grading I) 2)).X₃ ≅
      (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf) := by
  letI : IsAffine Z := isAffine_of_isAffineHom
    (i ≫ AllCharacteristics.HomogeneousProjective.toBase I)
  letI := finiteSchemeCoefficientAlgebra
    (i ≫ AllCharacteristics.HomogeneousProjective.toBase I)
  let hchart := finite_projective_closed_subscheme_chart I i
  let z := Classical.choose hchart
  let hz := Classical.choose (Classical.choose_spec hchart)
  let z1 : grading I 1 := ⟨z, hz⟩
  let g := Classical.choose
    (Classical.choose_spec (Classical.choose_spec hchart))
  have hfac : Spec.map (CommRingCat.ofHom g) ≫
      Proj.awayι (grading I) z hz (by decide : 0 < 1) = Z.isoSpec.inv ≫ i :=
    (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec hchart))).2.2
  let U : (scheme I).Opens := homogeneousBasicOpen (grading I) z
  let j : Z ⟶ (U : Scheme) :=
    Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g) ≫
      (Proj.basicOpenIsoSpec (grading I) z hz (by decide : 0 < 1)).inv
  have haway :
      (Proj.basicOpenIsoSpec (grading I) z hz (by decide : 0 < 1)).inv ≫
          U.ι =
        Proj.awayι (grading I) z hz (by decide : 0 < 1) := by
    rfl
  have hji : j ≫ U.ι = i := by
    calc
      j ≫ U.ι = Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g) ≫
          ((Proj.basicOpenIsoSpec (grading I) z hz
            (by decide : 0 < 1)).inv ≫ U.ι) := by
              simp only [j, Category.assoc]
      _ = Z.isoSpec.hom ≫
          (Spec.map (CommRingCat.ofHom g) ≫
            Proj.awayι (grading I) z hz (by decide : 0 < 1)) := by
              rw [haway]
      _ = Z.isoSpec.hom ≫ (Z.isoSpec.inv ≫ i) := by rw [hfac]
      _ = i := by rw [← Category.assoc, Z.isoSpec.hom_inv_id,
        Category.id_comp]
  letI : IsClosedImmersion (j ≫ U.ι) := hji.symm ▸ inferInstance
  let eT : (Scheme.Modules.restrictFunctor U.ι).obj
      (positiveSheafOfModules (grading I) 2) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf := by
    exact quotientPositiveTwoTwistUnitIso_on_degreeOne_basicOpen I z1
  let V : ULift.{u} sigma → (scheme I).Opens := fun k =>
    quotientCoordinateOpen I k.down
  have hV : (Opens.grothendieckTopology (scheme I)).CoversTop V := by
    rw [Opens.coversTop_iff]
    change ⨆ k : ULift.{u} sigma, quotientCoordinateOpen I k.down = ⊤
    rw [← quotientCoordinateOpen_iSup I]
    apply le_antisymm
    · apply iSup_le
      intro k
      exact le_iSup (fun j : sigma => quotientCoordinateOpen I j) k.down
    · apply iSup_le
      intro k
      exact le_iSup_of_le (ULift.up k) le_rfl
  let eV : ∀ k, (SheafOfModules.overFunctor (scheme I).ringCatSheaf (V k)).obj
        (positiveSheafOfModules (grading I) 2) ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver (scheme I).sheaf (V k))) := fun k =>
    overFunctorIsoUnit_of_restrictIsoUnit (V k)
      (quotientCoordinatePositiveTwistUnitIso_all I k.down 2)
  let E := closedImmersionIdealTwistTargetProjectionFormulaIso
    U j (positiveSheafOfModules (grading I) 2) eT
      (I := ULift.{u} sigma) V hV eV
  change schemeModuleTensor
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf))
      (positiveSheafOfModules (grading I) 2) ≅
    (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)
  exact (schemeModuleTensorRight
      (positiveSheafOfModules (grading I) 2)).mapIso
        ((Scheme.Modules.pushforwardCongr hji).symm.app
          (SheafOfModules.unit Z.ringCatSheaf)) ≪≫
    E ≪≫
    (Scheme.Modules.pushforwardCongr hji).app
      (SheafOfModules.unit Z.ringCatSheaf)

/-- The global sections of the actual quotient term in the positively
twisted closed-immersion sequence are the coordinate algebra of the finite
closed subscheme. -/
noncomputable def finiteProjectiveClosedSubschemePositiveTwoTargetSectionsEquiv
    {K : Type u} {sigma : Type} [Field K] [Infinite K] [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ toBase I)] :
    (closedImmersionIdealTwistSequence i
      (positiveSheafOfModules (grading I) 2)).X₃.sections ≃ Γ(Z, ⊤) :=
  (schemeModuleSectionsEquivOfIso
    (finiteProjectiveClosedSubschemePositiveTwoProjectionFormulaIso I i)).trans
      (pushforwardUnitSectionsEquiv i)

/-- A degree-two homogeneous element gives a section of the middle term of
the twisted ideal sequence.  The tensor-unit isomorphism is inserted
explicitly because that middle term is definitionally `O_X ⊗ O_X(2)`. -/
noncomputable def finiteProjectiveClosedSubschemePositiveTwoSourceSection
    {K : Type u} {sigma : Type} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    (q : grading I 2) :
    (closedImmersionIdealTwistSequence i
      (positiveSheafOfModules (grading I) 2)).X₂.sections := by
  let T := positiveSheafOfModules (grading I) 2
  change (schemeModuleTensor
    (SheafOfModules.unit (scheme I).ringCatSheaf) T).sections
  exact (schemeModuleSectionsEquivOfIso
    (schemeModuleTensorUnitLeftIso T)).symm
      (positiveGlobalSectionOfHomogeneous (grading I) 2 q)

/-- The literal sheaf-theoretic restriction of a homogeneous quadric to a
finite projective closed subscheme, with the target identified with the
coordinate algebra by the supported projection formula. -/
noncomputable def finiteProjectiveClosedSubschemePositiveTwoRestriction
    {K : Type u} {sigma : Type} [Field K] [Infinite K] [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ toBase I)] :
    grading I 2 → Γ(Z, ⊤) := fun q =>
  finiteProjectiveClosedSubschemePositiveTwoTargetSectionsEquiv I i
    (SheafOfModules.sectionsMap
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading I) 2)).g
      (finiteProjectiveClosedSubschemePositiveTwoSourceSection I i q))

@[simp]
theorem finiteProjectiveClosedSubschemePositiveTwoRestriction_apply
    {K : Type u} {sigma : Type} [Field K] [Infinite K] [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ toBase I)] (q : grading I 2) :
    finiteProjectiveClosedSubschemePositiveTwoTargetSectionsEquiv I i
        (SheafOfModules.sectionsMap
          (closedImmersionIdealTwistSequence i
            (positiveSheafOfModules (grading I) 2)).g
          (finiteProjectiveClosedSubschemePositiveTwoSourceSection I i q)) =
      finiteProjectiveClosedSubschemePositiveTwoRestriction I i q := rfl

/-- Once homogeneous degree-two elements generate the global sections of
`O(2)`, nonsurjectivity of their literal restriction to the finite
subscheme gives the nonzero first cohomology class used in Voisin's Serre
construction.  Exactness is proved from the standard coordinate-open
trivializations, so no global tensor-exactness assumption is required. -/
theorem finiteProjectiveClosedSubschemePositiveTwo_not_cohomology_one_subsingleton
    {K : Type u} {sigma : Type} [Field K] [Infinite K] [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ toBase I)]
    [HasExt.{u} (scheme I).Modules]
    (hsource : Function.Surjective
      (positiveGlobalSectionOfHomogeneous (grading I) 2))
    (hnot : ¬ Function.Surjective
      (finiteProjectiveClosedSubschemePositiveTwoRestriction I i)) :
    ¬ Subsingleton (schemeModuleCohomology (scheme I)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading I) 2)) 1) := by
  let V : ULift.{u} sigma → (scheme I).Opens := fun k =>
    quotientCoordinateOpen I k.down
  have hV : (Opens.grothendieckTopology (scheme I)).CoversTop V := by
    rw [Opens.coversTop_iff]
    change ⨆ k : ULift.{u} sigma, quotientCoordinateOpen I k.down = ⊤
    rw [← quotientCoordinateOpen_iSup I]
    apply le_antisymm
    · apply iSup_le
      intro k
      exact le_iSup (fun j : sigma => quotientCoordinateOpen I j) k.down
    · apply iSup_le
      intro k
      exact le_iSup_of_le (ULift.up k) le_rfl
  let eV : ∀ k, (SheafOfModules.overFunctor (scheme I).ringCatSheaf (V k)).obj
        (positiveSheafOfModules (grading I) 2) ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver (scheme I).sheaf (V k))) := fun k =>
    overFunctorIsoUnit_of_restrictIsoUnit (V k)
      (quotientCoordinatePositiveTwistUnitIso_all I k.down 2)
  have hshort :=
    closedImmersionIdealTwistSequence_shortExact_of_coversTop_iso_unit
      i (I := ULift.{u} sigma) V hV eV
  apply not_schemeModuleCohomology_one_subsingleton_of_section_parameterizations
    (scheme I)
    (closedImmersionIdealTwistSequence i
      (positiveSheafOfModules (grading I) 2)) hshort
    (finiteProjectiveClosedSubschemePositiveTwoSourceSection I i)
    (finiteProjectiveClosedSubschemePositiveTwoTargetSectionsEquiv I i)
    ?_ (finiteProjectiveClosedSubschemePositiveTwoTargetSectionsEquiv I i).surjective
    (finiteProjectiveClosedSubschemePositiveTwoRestriction I i) (fun q => rfl) hnot
  let E := schemeModuleSectionsEquivOfIso
    (schemeModuleTensorUnitLeftIso
      (positiveSheafOfModules (grading I) 2))
  exact E.symm.surjective.comp hsource

@[instance_reducible]
noncomputable def projectiveGlobalSectionsAlgebra
    {K : Type u} {sigma : Type} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K)) :
    Algebra K Γ(Proj (grading I), ⊤) :=
  (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (toBase I).appTop).hom).toAlgebra

lemma affineFunctionHom_eq_finiteSchemeCoefficient_algebraMap
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] :
    letI := finiteSchemeCoefficientAlgebra f
    affineFunctionHom f = algebraMap K Γ(X, ⊤) := by
  letI := finiteSchemeCoefficientAlgebra f
  letI : IsAffine X := isAffine_of_isAffineHom f
  have hs : CommRingCat.ofHom (affineFunctionHom f) =
      CommRingCat.ofHom (algebraMap K Γ(X, ⊤)) := by
    apply Spec.map_injective
    rw [finiteSchemeCoefficient_spec f]
    apply (cancel_epi X.isoSpec.hom).mp
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    change X.toSpecΓ ≫ Spec.map
      (CommRingCat.ofHom (affineFunctionHom f)) = f
    exact from_affineFunctionHom f
  exact congrArg CommRingCat.Hom.hom hs

lemma pushforwardUnitSectionsEquiv_apply
    {K : Type u} {sigma : Type} [Field K] [Infinite K] [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ toBase I)]
    (s : ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)).sections) :
    pushforwardUnitSectionsEquiv i s = s.val (op (⊤ : (scheme I).Opens)) := by
  change (moduleSectionsEquivTop Z (SheafOfModules.unit Z.ringCatSheaf))
      ((moduleSectionsEquivTop Z (SheafOfModules.unit Z.ringCatSheaf)).symm
        (moduleSectionsEquivTop (scheme I)
          ((Scheme.Modules.pushforward i).obj
            (SheafOfModules.unit Z.ringCatSheaf)) s)) =
    moduleSectionsEquivTop (scheme I)
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) s
  exact (moduleSectionsEquivTop Z
    (SheafOfModules.unit Z.ringCatSheaf)).apply_symm_apply _

lemma positiveGlobalSection_eval_add
    {K : Type u} {sigma : Type} [Field K] [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    (q r : grading I 2) :
    PresheafOfModules.sections.eval
        (ProjectiveNegativeTwist.positiveGlobalSectionOfHomogeneous
          (grading I) 2 (q + r)) (op (⊤ : (scheme I).Opens)) =
      PresheafOfModules.sections.eval
          (ProjectiveNegativeTwist.positiveGlobalSectionOfHomogeneous
            (grading I) 2 q) (op (⊤ : (scheme I).Opens)) +
        PresheafOfModules.sections.eval
          (ProjectiveNegativeTwist.positiveGlobalSectionOfHomogeneous
            (grading I) 2 r) (op (⊤ : (scheme I).Opens)) := by
  apply Subtype.ext
  funext x
  change
    (ProjectiveNegativeTwist.positiveSectionValue (grading I) 2
      (op (⊤ : Opens (Proj (grading I))))
      (PresheafOfModules.sections.eval
        (ProjectiveNegativeTwist.positiveGlobalSectionOfHomogeneous
          (grading I) 2 (q + r)) (op (⊤ : Opens (Proj (grading I)))))
      ⟨x.1, trivial⟩).1 =
    (ProjectiveNegativeTwist.positiveSectionValue (grading I) 2
      (op (⊤ : Opens (Proj (grading I))))
      (PresheafOfModules.sections.eval
        (ProjectiveNegativeTwist.positiveGlobalSectionOfHomogeneous
          (grading I) 2 q) (op (⊤ : Opens (Proj (grading I)))))
      ⟨x.1, trivial⟩).1 +
    (ProjectiveNegativeTwist.positiveSectionValue (grading I) 2
      (op (⊤ : Opens (Proj (grading I))))
      (PresheafOfModules.sections.eval
        (ProjectiveNegativeTwist.positiveGlobalSectionOfHomogeneous
          (grading I) 2 r) (op (⊤ : Opens (Proj (grading I)))))
      ⟨x.1, trivial⟩).1
  change Localization.mk ((q + r : grading I 2) : CoordinateRing I)
      (1 : (ProjectiveNegativeTwist.positivePointIdeal (grading I) x.1).primeCompl) =
    Localization.mk (q : CoordinateRing I)
        (1 : (ProjectiveNegativeTwist.positivePointIdeal (grading I) x.1).primeCompl) +
      Localization.mk (r : CoordinateRing I)
        (1 : (ProjectiveNegativeTwist.positivePointIdeal (grading I) x.1).primeCompl)
  change Localization.mk ((q : CoordinateRing I) + (r : CoordinateRing I))
      (1 : (ProjectiveNegativeTwist.positivePointIdeal (grading I) x.1).primeCompl) = _
  exact (Localization.add_mk_self
    (q : CoordinateRing I)
      (1 : (ProjectiveNegativeTwist.positivePointIdeal (grading I) x.1).primeCompl)
      (r : CoordinateRing I)).symm

lemma affineFunctionHom_toSpecZero_section
    {K : Type u} {sigma : Type} [Field K] [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    (b : grading I 0) :
    affineFunctionHom (Proj.toSpecZero (grading I)) b =
      ((CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom (grading I) (Submonoid.powers 1)) ≫
        Proj.awayToSection (grading I) 1 ≫
        (Proj.basicOpen (grading I) 1).topIso.inv ≫
        ((Proj (grading I)).isoOfEq (Proj.basicOpen_one (grading I))).inv.appTop ≫
        (Proj (grading I)).topIso.inv.appTop).hom b) := by
  unfold affineFunctionHom
  rw [Proj.toSpecZero]
  simp only [Scheme.Hom.comp_appTop, Category.assoc]
  simp only [Proj.basicOpenToSpec, Scheme.Hom.comp_appTop,
    Scheme.Opens.toSpecΓ_appTop, Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc
    (Proj.awayToSection (grading I) 1)]
  simp

lemma open_eq_top_section_transport
    (X : Scheme.{u}) (U : X.Opens) (e : U = ⊤) (s : Γ(X, U)) :
    ((U.topIso.inv ≫ (X.isoOfEq e).inv.appTop ≫ X.topIso.inv.appTop).hom s) =
      e ▸ s := by
  subst U
  simp only [Scheme.isoOfEq_rfl, Iso.refl_inv, Category.id_comp]
  change (X.topIso.hom.appTop ≫ X.topIso.inv.appTop).hom s = s
  rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
  rfl

lemma localizationMap_mk_one
    {R : Type u} [CommRing R] (M N : Submonoid R)
    (h : M ≤ Submonoid.comap (RingHom.id R) N) (r : R) :
    IsLocalization.map (Localization N) (RingHom.id R)
        h (Localization.mk r (1 : M)) =
      Localization.mk r (1 : N) := by
  rw [Localization.mk_eq_mk', IsLocalization.map_mk']
  rw [← Localization.mk_eq_mk']
  congr 2

set_option backward.isDefEq.respectTransparency false in
lemma projective_open_eq_top_section_transport_apply
    {A sigma : Type u} [CommRing A] [SetLike sigma A]
    [AddSubgroupClass sigma A] (𝒜 : ℕ → sigma) [GradedRing 𝒜]
    (U : (Proj 𝒜).Opens) (e : U = ⊤) (s : Γ(Proj 𝒜, U)) (x : Proj 𝒜) :
    (((U.topIso.inv ≫ ((Proj 𝒜).isoOfEq e).inv.appTop ≫
      (Proj 𝒜).topIso.inv.appTop).hom s).1 ⟨x, trivial⟩) =
        s.1 ⟨x, e.symm ▸ trivial⟩ := by
  rw [open_eq_top_section_transport]
  subst U
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma positiveGlobalSection_eval_smul_degree
    {K : Type u} {sigma : Type} [Field K] [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    (m : ℕ) (a : K) (q : grading I m) :
    letI := projectiveGlobalSectionsAlgebra I
    PresheafOfModules.sections.eval
        (ProjectiveNegativeTwist.positiveGlobalSectionOfHomogeneous
          (grading I) m (a • q))
          (op (⊤ : Opens (ProjectiveSpectrum.top (grading I)))) =
      (algebraMap K Γ(Proj (grading I), ⊤) a) •
        (show Γ(ProjectiveNegativeTwist.positiveSheafOfModules (grading I) m, ⊤) from
          PresheafOfModules.sections.eval
          (ProjectiveNegativeTwist.positiveGlobalSectionOfHomogeneous
            (grading I) m q)
            (op (⊤ : Opens (ProjectiveSpectrum.top (grading I))))) := by
  letI := projectiveGlobalSectionsAlgebra I
  apply Subtype.ext
  funext x
  change
    (ProjectiveNegativeTwist.positiveSectionValue (grading I) m
      (op (⊤ : Opens (ProjectiveSpectrum.top (grading I))))
      (PresheafOfModules.sections.eval
        (ProjectiveNegativeTwist.positiveGlobalSectionOfHomogeneous
          (grading I) m (a • q))
          (op (⊤ : Opens (ProjectiveSpectrum.top (grading I)))))
      ⟨x.1, trivial⟩).1 = _
  change Localization.mk ((a • q : grading I m) : CoordinateRing I)
      (1 : (ProjectiveNegativeTwist.positivePointIdeal (grading I) x.1).primeCompl) = _
  have hq : ((a • q : grading I m) : CoordinateRing I) =
      a • (q : CoordinateRing I) :=
    (Submodule.subtype (grading I m)).map_smul a q
  have hqmul : ((a • q : grading I m) : CoordinateRing I) =
      algebraMap K (CoordinateRing I) a * (q : CoordinateRing I) := by
    rw [hq]
    exact Algebra.smul_def a (q : CoordinateRing I)
  rw [hqmul]
  change Localization.mk ((algebraMap K (CoordinateRing I) a) * (q : CoordinateRing I))
      (1 : (ProjectiveNegativeTwist.positivePointIdeal (grading I) x.1).primeCompl) =
    ((algebraMap K Γ(Proj (grading I), ⊤) a).1 ⟨x.1, trivial⟩).val *
      Localization.mk (q : CoordinateRing I)
        (1 : (ProjectiveNegativeTwist.positivePointIdeal (grading I) x.1).primeCompl)
  have ha : ((algebraMap K Γ(Proj (grading I), ⊤) a).1 ⟨x.1, trivial⟩).val =
      Localization.mk (algebraMap K (CoordinateRing I) a)
        (1 : (ProjectiveNegativeTwist.positivePointIdeal (grading I) x.1).primeCompl) := by
    change ((affineFunctionHom (toBase I) a).1 ⟨x.1, trivial⟩).val = _
    change ((affineFunctionHom
      (Proj.toSpecZero (grading I) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (grading I 0)))) a).1
          ⟨x.1, trivial⟩).val = _
    have hbase : affineFunctionHom
        (Proj.toSpecZero (grading I) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K (grading I 0)))) a =
        affineFunctionHom (Proj.toSpecZero (grading I))
          (algebraMap K (grading I 0) a) := by
      simpa using congrArg (fun f => f a)
        (affineFunctionHom_comp_Spec (Proj.toSpecZero (grading I))
          (algebraMap K (grading I 0)))
    rw [hbase]
    rw [affineFunctionHom_toSpecZero_section I]
    let U := Proj.basicOpen (grading I) 1
    let e : U = (⊤ : (Proj (grading I)).Opens) := Proj.basicOpen_one (grading I)
    let b : grading I 0 := algebraMap K (grading I 0) a
    let s : Γ(Proj (grading I), U) :=
      (Proj.awayToSection (grading I) 1).hom
        (HomogeneousLocalization.fromZeroRingHom
          (grading I) (Submonoid.powers 1) b)
    have htransport :=
      projective_open_eq_top_section_transport_apply
        (grading I) U e s x.1
    have hsection :
        ((CommRingCat.ofHom
            (HomogeneousLocalization.fromZeroRingHom
              (grading I) (Submonoid.powers 1)) ≫
          Proj.awayToSection (grading I) 1 ≫ U.topIso.inv ≫
          ((Proj (grading I)).isoOfEq e).inv.appTop ≫
          (Proj (grading I)).topIso.inv.appTop).hom b) =
        ((U.topIso.inv ≫ ((Proj (grading I)).isoOfEq e).inv.appTop ≫
          (Proj (grading I)).topIso.inv.appTop).hom s) := by
      rfl
    rw [hsection, htransport]
    dsimp only [s, b]
    let y : U := ⟨x.1, e.symm ▸ trivial⟩
    have haw := ProjectiveSpectrum.Proj.awayToSection_apply
      (grading I) (1 : CoordinateRing I)
      (HomogeneousLocalization.fromZeroRingHom
        (grading I) (Submonoid.powers 1) b) y
    change HomogeneousLocalization.val
      (((CommRingCat.Hom.hom (Proj.awayToSection (grading I) 1))
        (HomogeneousLocalization.fromZeroRingHom
          (grading I) (Submonoid.powers 1) b)).1 y) = _ at haw
    have hbval :
        (HomogeneousLocalization.fromZeroRingHom
          (grading I) (Submonoid.powers 1) b).val =
          Localization.mk (b : CoordinateRing I)
            (1 : Submonoid.powers (1 : CoordinateRing I)) := by
      rfl
    rw [hbval] at haw
    have hMN : Submonoid.powers (1 : CoordinateRing I) ≤
        Submonoid.comap (RingHom.id (CoordinateRing I))
          (x.1.asHomogeneousIdeal.toIdeal).primeCompl := by
      intro z hz
      exact (Submonoid.powers_le.mpr y.2) hz
    have hmap := localizationMap_mk_one
      (Submonoid.powers (1 : CoordinateRing I))
      (x.1.asHomogeneousIdeal.toIdeal).primeCompl hMN (b : CoordinateRing I)
    rw [hmap] at haw
    have hbcoord : (b : CoordinateRing I) =
        algebraMap K (CoordinateRing I) a := by
      rfl
    have hright :
        Localization.mk (b : CoordinateRing I)
            (1 : (x.1.asHomogeneousIdeal.toIdeal).primeCompl) =
          Localization.mk (algebraMap K (CoordinateRing I) a)
            (1 : (x.1.asHomogeneousIdeal.toIdeal).primeCompl) :=
      congrArg (fun z => Localization.mk z
        (1 : (x.1.asHomogeneousIdeal.toIdeal).primeCompl)) hbcoord
    have haw' := haw.trans hright
    simpa only [y, b] using haw'
  let d : (ProjectiveNegativeTwist.positivePointIdeal
      (grading I) x.1).primeCompl := 1
  have hprod :
      Localization.mk ((algebraMap K (CoordinateRing I) a) *
          (q : CoordinateRing I)) d =
        Localization.mk (algebraMap K (CoordinateRing I) a) d *
          Localization.mk (q : CoordinateRing I) d := by
    rw [Localization.mk_mul]
    congr 2
    dsimp [d]
    ext
    simp
  have hscalar := congrArg
    (fun z => z * Localization.mk (q : CoordinateRing I) d) ha
  exact hprod.trans hscalar.symm

/-- Degree-two specialization used by the finite-subscheme restriction map. -/
lemma positiveGlobalSection_eval_smul
    {K : Type u} {sigma : Type} [Field K] [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    (a : K) (q : grading I 2) :
    letI := projectiveGlobalSectionsAlgebra I
    PresheafOfModules.sections.eval
        (ProjectiveNegativeTwist.positiveGlobalSectionOfHomogeneous
          (grading I) 2 (a • q))
          (op (⊤ : Opens (ProjectiveSpectrum.top (grading I)))) =
      (algebraMap K Γ(Proj (grading I), ⊤) a) •
        (show Γ(ProjectiveNegativeTwist.positiveSheafOfModules (grading I) 2, ⊤) from
          PresheafOfModules.sections.eval
          (ProjectiveNegativeTwist.positiveGlobalSectionOfHomogeneous
            (grading I) 2 q)
            (op (⊤ : Opens (ProjectiveSpectrum.top (grading I))))) :=
  positiveGlobalSection_eval_smul_degree I 2 a q

lemma finiteProjectiveClosedSubschemePositiveTwoRestriction_add
    {K : Type u} {sigma : Type} [Field K] [Infinite K] [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ toBase I)]
    (q r : grading I 2) :
  finiteProjectiveClosedSubschemePositiveTwoRestriction I i (q + r) =
      finiteProjectiveClosedSubschemePositiveTwoRestriction I i q +
        finiteProjectiveClosedSubschemePositiveTwoRestriction I i r := by
  unfold finiteProjectiveClosedSubschemePositiveTwoRestriction
  dsimp only [finiteProjectiveClosedSubschemePositiveTwoTargetSectionsEquiv,
    Equiv.trans_apply, schemeModuleSectionsEquivOfIso]
  rw [pushforwardUnitSectionsEquiv_apply I i,
    pushforwardUnitSectionsEquiv_apply I i,
    pushforwardUnitSectionsEquiv_apply I i]
  let T := ProjectiveNegativeTwist.positiveSheafOfModules (grading I) 2
  let E := finiteProjectiveClosedSubschemePositiveTwoProjectionFormulaIso I i
  let S := closedImmersionIdealTwistSequence i T
  let L := schemeModuleTensorUnitLeftIso T
  let U := op (⊤ : (Proj (grading I)).Opens)
  let f1 := (L.inv.val.app U).hom.toAddMonoidHom
  let f2 := (S.g.val.app U).hom.toAddMonoidHom
  let f3 := (E.hom.val.app U).hom.toAddMonoidHom
  let F := f3.comp (f2.comp f1)
  have hadd := map_add F
    (PresheafOfModules.sections.eval
      (ProjectiveNegativeTwist.positiveGlobalSectionOfHomogeneous
        (grading I) 2 q) U)
    (PresheafOfModules.sections.eval
      (ProjectiveNegativeTwist.positiveGlobalSectionOfHomogeneous
        (grading I) 2 r) U)
  have hpos := positiveGlobalSection_eval_add I q r
  dsimp only [U] at hadd
  have hpre := congrArg F hpos
  have h := hpre.trans hadd
  dsimp only [F, f3, f2, f1, E, S, L, T, AddMonoidHom.comp_apply,
    LinearMap.coe_toAddHom] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
lemma finiteProjectiveClosedSubschemePositiveTwoRestriction_smul
    {K : Type u} {sigma : Type} [Field K] [Infinite K] [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ toBase I)]
    (a : K) (q : grading I 2) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    finiteProjectiveClosedSubschemePositiveTwoRestriction I i (a • q) =
      a • finiteProjectiveClosedSubschemePositiveTwoRestriction I i q := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := projectiveGlobalSectionsAlgebra I
  unfold finiteProjectiveClosedSubschemePositiveTwoRestriction
  dsimp only [finiteProjectiveClosedSubschemePositiveTwoTargetSectionsEquiv,
    Equiv.trans_apply, schemeModuleSectionsEquivOfIso]
  rw [pushforwardUnitSectionsEquiv_apply I i,
    pushforwardUnitSectionsEquiv_apply I i]
  let T := ProjectiveNegativeTwist.positiveSheafOfModules (grading I) 2
  let E := finiteProjectiveClosedSubschemePositiveTwoProjectionFormulaIso I i
  let S := closedImmersionIdealTwistSequence i T
  let L := schemeModuleTensorUnitLeftIso T
  let U := op (⊤ : (Proj (grading I)).Opens)
  let f1 := (L.inv.val.app U).hom
  let f2 := (S.g.val.app U).hom
  let f3 := (E.hom.val.app U).hom
  let F := f3.comp (f2.comp f1)
  have hsmul := F.map_smul (algebraMap K Γ(Proj (grading I), ⊤) a)
    (PresheafOfModules.sections.eval
      (ProjectiveNegativeTwist.positiveGlobalSectionOfHomogeneous
        (grading I) 2 q) U)
  have hpos := positiveGlobalSection_eval_smul I a q
  dsimp only [U] at hsmul
  have hpre := congrArg F hpos
  have h := hpre.trans hsmul
  dsimp only [F, f3, f2, f1, E, S, L, T, LinearMap.comp_apply] at h
  refine h.trans ?_
  let z := F (PresheafOfModules.sections.eval
    (ProjectiveNegativeTwist.positiveGlobalSectionOfHomogeneous
      (grading I) 2 q) U)
  change i.appTop.hom (algebraMap K Γ(Proj (grading I), ⊤) a) *
      (show Γ(Z, ⊤) from z) =
    algebraMap K Γ(Z, ⊤) a * (show Γ(Z, ⊤) from z)
  have hamb : affineFunctionHom (toBase I) =
      algebraMap K Γ(Proj (grading I), ⊤) := by
    rfl
  have htarget : affineFunctionHom (i ≫ toBase I) =
      algebraMap K Γ(Z, ⊤) :=
    affineFunctionHom_eq_finiteSchemeCoefficient_algebraMap (i ≫ toBase I)
  have hcoeffHom : i.appTop.hom.comp
      (algebraMap K Γ(Proj (grading I), ⊤)) =
      algebraMap K Γ(Z, ⊤) := by
    rw [← hamb, ← htarget]
    exact (affineFunctionHom_comp i (toBase I)).symm
  have hcoeff := DFunLike.congr_fun hcoeffHom a
  have hcoeff' : i.appTop.hom
      (algebraMap K Γ(Proj (grading I), ⊤) a) =
      algebraMap K Γ(Z, ⊤) a := hcoeff
  exact congrArg (fun c => c * (show Γ(Z, ⊤) from z)) hcoeff'

noncomputable def finiteProjectiveClosedSubschemePositiveTwoRestrictionLinearMap
    {K : Type u} {sigma : Type} [Field K] [Infinite K] [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ toBase I)] :
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    grading I 2 →ₗ[K] Γ(Z, ⊤) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  exact
    { toFun := finiteProjectiveClosedSubschemePositiveTwoRestriction I i
      map_add' := finiteProjectiveClosedSubschemePositiveTwoRestriction_add I i
      map_smul' := finiteProjectiveClosedSubschemePositiveTwoRestriction_smul I i }

end PfaffianDescent
