import PfaffianDescent.FiniteProjectiveChart
import PfaffianDescent.VoisinPositiveTwistTriviality
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal
import PfaffianDescent.BundleSectionZeroLocus
import PfaffianDescent.SchemePushforwardUnitSections

/-!
# Trivializing projective twists on finite chart factorizations

A finite projective subscheme lies in one projective chart.  This file starts
the corresponding sheaf-level bridge: a positive twist trivial on that chart
remains trivial after pullback to the finite subscheme.
-/

noncomputable section

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist
open HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A pullback-trivial module remains trivial after one further pullback.
This is the form used after first trivializing a projective twist on an
affine chart and then passing to a finite closed subscheme of that chart. -/
noncomputable def pullbackModuleIsoUnit_of_pullbackIsoUnit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : Z.Modules)
    (e : (Scheme.Modules.pullback g).obj L ≅
      SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback (f ≫ g)).obj L ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI : IsIso (BundleSectionZeroLocus.pullbackUnitComparison f) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison f
  exact asIso ((Scheme.Modules.pullbackComp f g).inv.app L) ≪≫
    (Scheme.Modules.pullback f).mapIso e ≪≫
    asIso (BundleSectionZeroLocus.pullbackUnitComparison f)

/-- A module that is trivial on an open chart remains trivial after pulling
back along any morphism that factors through that chart. -/
noncomputable def pullbackModuleIsoUnit_of_factors_through_open
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g]
    (L : Z.Modules)
    (e : (Scheme.Modules.restrictFunctor g).obj L ≅
      SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback (f ≫ g)).obj L ≅
      SheafOfModules.unit X.ringCatSheaf := by
  exact pullbackModuleIsoUnit_of_pullbackIsoUnit f g L
    (((Scheme.Modules.restrictFunctorIsoPullback g).app L).symm ≪≫ e)

/-- On a degree-one projective basic open, the positive degree-two twist is
trivial: first divide by the degree-one element, and then use its degree-one
trivialization. -/
noncomputable def restrictPositiveTwoTwistUnitIso_on_degreeOne_basicOpen
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (s : 𝒜 1)
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝒜 1 => (f : A)))) :
    (Scheme.Modules.restrictFunctor
      (homogeneousBasicOpen 𝒜 (s : A)).ι).obj
        (positiveSheafOfModules 𝒜 2) ≅
      SheafOfModules.unit
        ((homogeneousBasicOpen 𝒜 (s : A) : Scheme).ringCatSheaf) := by
  simpa only [Nat.one_add] using
    ((ProjectiveNegativeTwist.restrictPositiveMulHomogeneousIso_on_basicOpen
      𝒜 s 1 hspan).symm ≪≫
      ProjectiveNegativeTwist.restrictPositiveTwistUnitIso_on_basicOpen
        𝒜 s hspan)

/-- The degree-two positive twist of a homogeneous polynomial quotient is
trivial on every degree-one projective basic open. -/
noncomputable def quotientPositiveTwoTwistUnitIso_on_degreeOne_basicOpen
    {K : Type u} {σ : Type} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (s : grading I 1) :
    (Scheme.Modules.restrictFunctor
      (homogeneousBasicOpen (grading I) (s : CoordinateRing I)).ι).obj
        (positiveSheafOfModules (grading I) 2) ≅
      SheafOfModules.unit
        ((homogeneousBasicOpen (grading I) (s : CoordinateRing I) : Scheme).ringCatSheaf) :=
  restrictPositiveTwoTwistUnitIso_on_degreeOne_basicOpen (grading I) s
    (gradedSurjective_irrelevant_le_span_degreeOne
      (MvPolynomial.homogeneousSubmodule σ K) (grading I)
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small)

/-- The positive degree-two twist becomes the unit module after pullback to
any finite closed subscheme of a homogeneous projective polynomial quotient.
The proof chooses one degree-one chart containing the finite subscheme and
then transports its chart trivialization through the canonical affine
presentation of that subscheme. -/
noncomputable def finiteProjectiveClosedSubschemePositiveTwoTwistUnitIso
    {K : Type u} {σ : Type} [Field K] [Infinite K] [Finite σ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ toBase I)] :
    (Scheme.Modules.pullback i).obj
        (positiveSheafOfModules (grading I) 2) ≅
      SheafOfModules.unit Z.ringCatSheaf := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
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
  let q : Spec (.of (Away (grading I) z)) ⟶ scheme I :=
    Proj.awayι (grading I) z hz (by decide : 0 < 1)
  have eqChart :
      (Scheme.Modules.pullback q).obj
          (positiveSheafOfModules (grading I) 2) ≅
        SheafOfModules.unit (Spec (.of (Away (grading I) z))).ringCatSheaf := by
    dsimp only [q]
    exact pullbackModuleIsoUnit_of_factors_through_open
      (Proj.basicOpenIsoSpec (grading I) z hz (by decide : 0 < 1)).inv
      (Proj.basicOpen (grading I) z).ι
      (positiveSheafOfModules (grading I) 2)
      (quotientPositiveTwoTwistUnitIso_on_degreeOne_basicOpen I z1)
  let p : Spec (.of Γ(Z, ⊤)) ⟶ Spec (.of (Away (grading I) z)) :=
    Spec.map (CommRingCat.ofHom g)
  have eqAffine :
      (Scheme.Modules.pullback (p ≫ q)).obj
          (positiveSheafOfModules (grading I) 2) ≅
        SheafOfModules.unit (Spec (.of Γ(Z, ⊤))).ringCatSheaf :=
    pullbackModuleIsoUnit_of_pullbackIsoUnit p q
      (positiveSheafOfModules (grading I) 2) eqChart
  have hpq : p ≫ q = Z.isoSpec.inv ≫ i := by
    exact hfac
  have eqOnZ :
      (Scheme.Modules.pullback (Z.isoSpec.hom ≫ (p ≫ q))).obj
          (positiveSheafOfModules (grading I) 2) ≅
        SheafOfModules.unit Z.ringCatSheaf :=
    pullbackModuleIsoUnit_of_pullbackIsoUnit Z.isoSpec.hom (p ≫ q)
      (positiveSheafOfModules (grading I) 2) eqAffine
  have hfinal : Z.isoSpec.hom ≫ (p ≫ q) = i := by
    rw [hpq, ← Category.assoc, Z.isoSpec.hom_inv_id, Category.id_comp]
  exact (Scheme.Modules.pullbackCongr hfinal).symm.app
    (positiveSheafOfModules (grading I) 2) ≪≫ eqOnZ

/-- Pushing forward the finite-scheme trivialization identifies the direct
image of the pulled-back degree-two twist with the direct image of the
structure sheaf.  The only remaining projection-formula task is to compare
this source with the tensor term in the closed-immersion ideal sequence. -/
noncomputable def finiteProjectiveClosedSubschemePushforwardPositiveTwoUnitIso
    {K : Type u} {σ : Type} [Field K] [Infinite K] [Finite σ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ toBase I)] :
    (Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pullback i).obj
          (positiveSheafOfModules (grading I) 2)) ≅
      (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf) :=
  (Scheme.Modules.pushforward i).mapIso
    (finiteProjectiveClosedSubschemePositiveTwoTwistUnitIso I i)

/-- Global sections of the pushed-forward pulled-back positive degree-two
twist on a finite projective closed subscheme are its ordinary coordinate
algebra. -/
noncomputable def finiteProjectiveClosedSubschemePushforwardPositiveTwoSectionsEquiv
    {K : Type u} {σ : Type} [Field K] [Infinite K] [Finite σ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ toBase I)] :
    ((Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj
        (positiveSheafOfModules (grading I) 2))).sections ≃ Γ(Z, ⊤) :=
  (schemeModuleSectionsEquivOfIso
    (finiteProjectiveClosedSubschemePushforwardPositiveTwoUnitIso I i)).trans
      (pushforwardUnitSectionsEquiv i)

/-- Restricting the pushforward of a module whose supporting morphism factors
through an open immersion recovers the pushforward along the factor.  This is
the first local-support comparison needed for the Serre target: after the
finite subscheme is placed in one projective chart, its pushed-forward
structure sheaf has no additional contribution outside that chart. -/
noncomputable def restrictPushforwardUnitFactorThroughOpenIso
    {Z U X : Scheme.{u}} (j : Z ⟶ U) (u : U ⟶ X) [IsOpenImmersion u] :
    (Scheme.Modules.restrictFunctor u).obj
        ((Scheme.Modules.pushforward (j ≫ u)).obj
          (SheafOfModules.unit Z.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit Z.ringCatSheaf) :=
  (Scheme.Modules.restrictFunctor u).mapIso
    ((Scheme.Modules.pushforwardComp j u).app
      (SheafOfModules.unit Z.ringCatSheaf)).symm ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso u).app
      ((Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit Z.ringCatSheaf))

/-- The unit of restriction--pushforward is invertible after restricting back
to the open immersion.  This is the on-chart part of the local-to-global
comparison for a module supported inside that chart. -/
theorem restrictAdjunctionUnit_restrict_isIso
    {U X : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u]
    (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor u).map
      ((Scheme.Modules.restrictAdjunction u).unit.app M)) := by
  let R := Scheme.Modules.restrictFunctor u
  let A := Scheme.Modules.restrictAdjunction u
  let e := A.counit.app (R.obj M)
  haveI : IsIso e := by
    dsimp [A]
    infer_instance
  have htri : R.map (A.unit.app M) ≫ e = 𝟙 _ := by
    change (Scheme.Modules.restrictFunctor u).map
      ((Scheme.Modules.restrictAdjunction u).unit.app M) ≫
        (Scheme.Modules.restrictAdjunction u).counit.app
          ((Scheme.Modules.restrictFunctor u).obj M) = 𝟙 _
    exact (Scheme.Modules.restrictAdjunction u).left_triangle_components M
  haveI : IsIso (R.map (A.unit.app M) ≫ e) := by
    rw [htri]
    infer_instance
  exact IsIso.of_isIso_comp_right _ e

/-- On an open chart through which a finite subscheme factors, tensoring its
pushforward with a locally trivial module is the ordinary local pushforward.
This is the local projection-formula comparison required for the target of
the twisted closed-immersion ideal sequence. -/
noncomputable def restrictTensorPushforwardUnitFactorThroughOpenIso
    {X Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    (T : X.Modules)
    (eT : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (Scheme.Modules.restrictFunctor U.ι).obj
        (schemeModuleTensor
          ((Scheme.Modules.pushforward (j ≫ U.ι)).obj
            (SheafOfModules.unit Z.ringCatSheaf)) T) ≅
      (Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit Z.ringCatSheaf) := by
  let E := Scheme.Modules.overEquiv U
  let F := SheafOfModules.overFunctor X.ringCatSheaf U
  let R := SheafOfModules.commRingSheafOver X.sheaf U
  let M := (Scheme.Modules.pushforward (j ≫ U.ι)).obj
    (SheafOfModules.unit Z.ringCatSheaf)
  let eTOver := overFunctorIsoUnit_of_restrictIsoUnit U eT
  let n := Scheme.Modules.overFunctorEquiv U
  exact schemeModuleTensorRestrictOverIso U M T ≪≫
    E.functor.mapIso
      ((SheafOfModules.commRingSheafTensorRightIsoUnit R eTOver).app
        (F.obj M)) ≪≫
    n.app M ≪≫
    restrictPushforwardUnitFactorThroughOpenIso j U.ι

/-- The preceding local projection-formula comparison written directly for
the target of the twisted closed-immersion ideal sequence. -/
noncomputable def restrictClosedImmersionIdealTwistTargetFactorThroughOpenIso
    {X Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)]
    (T : X.Modules)
    (eT : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (Scheme.Modules.restrictFunctor U.ι).obj
        (closedImmersionIdealTwistSequence (j ≫ U.ι) T).X₃ ≅
      (Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit Z.ringCatSheaf) := by
  change (Scheme.Modules.restrictFunctor U.ι).obj
      (schemeModuleTensor
        ((Scheme.Modules.pushforward (j ≫ U.ι)).obj
          (SheafOfModules.unit Z.ringCatSheaf)) T) ≅ _
  exact restrictTensorPushforwardUnitFactorThroughOpenIso U j T eT

/-- Pushing the chart-level target identification forward identifies the
codomain of the restriction-adjunction unit with the ordinary pushforward
from the finite closed subscheme. -/
noncomputable def pushforwardRestrictClosedImmersionIdealTwistTargetFactorThroughOpenIso
    {X Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)]
    (T : X.Modules)
    (eT : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (Scheme.Modules.pushforward U.ι).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj
          (closedImmersionIdealTwistSequence (j ≫ U.ι) T).X₃) ≅
      (Scheme.Modules.pushforward (j ≫ U.ι)).obj
        (SheafOfModules.unit Z.ringCatSheaf) :=
  (Scheme.Modules.pushforward U.ι).mapIso
    (restrictClosedImmersionIdealTwistTargetFactorThroughOpenIso U j T eT) ≪≫
  (Scheme.Modules.pushforwardComp j U.ι).app
    (SheafOfModules.unit Z.ringCatSheaf)

end PfaffianDescent
