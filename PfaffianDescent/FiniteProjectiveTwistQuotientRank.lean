import PfaffianDescent.FiniteProjectiveProjectionFormula
import PfaffianDescent.SchemeModuleSupportedFiberGroundDimension

/-! SOURCE ONLY / UNVERIFIED158. Every actual positive twist of the entire
finite ideal-sequence quotient is isomorphic to i_*O_Z. Its original-base
H0 is finite of actual native rank. This produces a genuine Euler input,
not the desired elliptic section bound. No new numerical options. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
open TopologicalSpace AllCharacteristics AllCharacteristics.HomogeneousProjective
open HomogeneousLocalization ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every positive twist is trivial on a single degree-one basic open.
This is the literal coordinate-chart induction with an arbitrary degree-one
homogeneous section in place of a coordinate. Degree zero is included. -/
noncomputable def quotientPositiveTwistUnitIso_on_degreeOne_basicOpen_all
    {K : Type u} {σ : Type} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (s : grading I 1) (d : ℕ) :
    (Scheme.Modules.restrictFunctor
      (homogeneousBasicOpen (grading I) (s : CoordinateRing I)).ι).obj
        (positiveSheafOfModules (grading I) d) ≅
      SheafOfModules.unit
        ((homogeneousBasicOpen (grading I) (s : CoordinateRing I) : Scheme).ringCatSheaf) := by
  let 𝓑 := grading I
  let U := homogeneousBasicOpen 𝓑 (s : CoordinateRing I)
  let F := Scheme.Modules.restrictFunctor U.ι
  let hspan : (HomogeneousIdeal.irrelevant 𝓑).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝓑 1 => (f : CoordinateRing I))) :=
    gradedSurjective_irrelevant_le_span_degreeOne
      (MvPolynomial.homogeneousSubmodule σ K) 𝓑
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  induction d with
  | zero =>
      exact F.mapIso (positiveZeroTwistIso 𝓑) ≪≫
        (F.mapIso (unitIsoZeroTwist 𝓑)).symm ≪≫
          Scheme.Modules.restrictUnitIso U.ι
  | succ d ih =>
      letI : IsIso (F.map (positiveMulHomogeneous 𝓑 s d)) :=
        restrict_positiveMulHomogeneous_isIso_on_basicOpen 𝓑 s d hspan
      exact (asIso (F.map (positiveMulHomogeneous 𝓑 s d))).symm ≪≫ ih

/-- The actual finite closed subscheme lies in a constructed single linear
chart; every positive twist is trivial there. The supported projection
formula consequently identifies the literal twisted quotient with i_*O_Z,
without assuming a frame or a quotient comparison. -/
noncomputable def finiteProjectiveClosedSubschemePositiveTwistProjectionFormulaIso
    {K : Type u} {sigma : Type} [Field K] [Infinite K] [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K)) (d : ℕ)
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ AllCharacteristics.HomogeneousProjective.toBase I)] :
    (closedImmersionIdealTwistSequence i
      (positiveSheafOfModules (grading I) d)).X₃ ≅
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
      (positiveSheafOfModules (grading I) d) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf := by
    exact quotientPositiveTwistUnitIso_on_degreeOne_basicOpen_all I z1 d
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
        (positiveSheafOfModules (grading I) d) ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver (scheme I).sheaf (V k))) := fun k =>
    overFunctorIsoUnit_of_restrictIsoUnit (V k)
      (quotientCoordinatePositiveTwistUnitIso_all I k.down d)
  let E := closedImmersionIdealTwistTargetProjectionFormulaIso
    U j (positiveSheafOfModules (grading I) d) eT
      (I := ULift.{u} sigma) V hV eV
  change schemeModuleTensor
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf))
      (positiveSheafOfModules (grading I) d) ≅
    (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)
  exact (schemeModuleTensorRight
      (positiveSheafOfModules (grading I) d)).mapIso
        ((Scheme.Modules.pushforwardCongr hji).symm.app
          (SheafOfModules.unit Z.ringCatSheaf)) ≪≫
    E ≪≫
    (Scheme.Modules.pushforwardCongr hji).app
      (SheafOfModules.unit Z.ringCatSheaf)


end PfaffianDescent

namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual unit top sections are the entire finite coefficient algebra
linearly for their independently existing structural-morphism action. -/
def finiteSchemeUnitTopCoefficientLinearEquiv
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K)) [IsFinite g] :
    letI := PfaffianDescent.finiteSchemeCoefficientAlgebra g
    SchemeModuleOpenSectionsOver g (SheafOfModules.unit Z.ringCatSheaf) ⊤ ≃ₗ[K]
      Γ(Z, ⊤) := by
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra g
  refine
    { toFun := fun s => (show Γ(Z, ⊤) from s)
      invFun := fun s => (show SchemeModuleOpenSectionsOver g
        (SheafOfModules.unit Z.ringCatSheaf) ⊤ from s)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := ?_ }
  intro c s
  change schemeOpenBaseRingHom g ⊤ c * (show Γ(Z, ⊤) from s) =
    algebraMap K Γ(Z, ⊤) c * (show Γ(Z, ⊤) from s)
  rw [schemeOpenBaseRingHom_top_apply,
    PfaffianDescent.affineFunctionHom_eq_finiteSchemeCoefficient_algebraMap g]

/-- Direct-image unit sections have exact native finite-scheme rank over
the original field. The two scalar actions are those induced by pi and
i≫pi, and their compatibility is the existing native pushforward comparison. -/
theorem finitePushforwardUnit_topSections_finite_and_nativeRank
    {X Z : Scheme.{u}} (pi : X ⟶ Spec (.of K)) (i : Z ⟶ X)
    [IsFinite (i ≫ pi)] :
    Module.Finite K (SchemeModuleOpenSectionsOver pi
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) ⊤) ∧
    Module.finrank K (SchemeModuleOpenSectionsOver pi
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) ⊤) =
        finiteSchemeRank (i ≫ pi) := by
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (i ≫ pi)
  letI : Module.Finite K Γ(Z, ⊤) :=
    PfaffianDescent.finiteSchemeCoefficient_finite (i ≫ pi)
  let E := (schemeModulePushforward_topSectionsLinearEquiv pi i
    (SheafOfModules.unit Z.ringCatSheaf)).trans
      (finiteSchemeUnitTopCoefficientLinearEquiv (i ≫ pi))
  exact ⟨Module.Finite.equiv E.symm,
    E.finrank_eq.trans (PfaffianDescent.finiteSchemeCoefficient_finrank (i ≫ pi))⟩

/-- For EVERY degree d, the literal twisted ideal-sequence quotient has
finite original-field H0 of actual native whole finite-scheme rank. This
is derived from a constructed projection-formula iso, not a supplied
quotient section rank or supplied finite-scheme trivialization. -/
theorem finiteProjectivePositiveTwistQuotient_topSections_finite_and_nativeRank
    {σ : Type} [Finite σ] [Infinite K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) (d : ℕ)
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ toBase I)] :
    Module.Finite K (SchemeModuleOpenSectionsOver (toBase I)
      (closedImmersionIdealTwistSequence i (positiveSheafOfModules (grading I) d)).X₃ ⊤) ∧
    Module.finrank K (SchemeModuleOpenSectionsOver (toBase I)
      (closedImmersionIdealTwistSequence i (positiveSheafOfModules (grading I) d)).X₃ ⊤) =
        finiteSchemeRank (i ≫ toBase I) := by
  have h := finitePushforwardUnit_topSections_finite_and_nativeRank (toBase I) i
  letI := h.1
  let E := schemeModuleOpenTopIsoLinearEquivOver (toBase I)
    (PfaffianDescent.finiteProjectiveClosedSubschemePositiveTwistProjectionFormulaIso I d i)
  exact ⟨Module.Finite.equiv E.symm, E.finrank_eq.trans h.2⟩

end PfaffianDescent.Coray
