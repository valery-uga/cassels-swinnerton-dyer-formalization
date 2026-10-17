import PfaffianDescent.OriginalRectangularPlaneNonpositiveEulerCasesBeyond230
import PfaffianDescent.PlaneClosedIdealPositiveZeroCoefficientIsoBeyond230
import PfaffianDescent.CorayActualWholeCutPlaneIdealEuler
import PfaffianDescent.CorayOwnMinimalComponentDegreePositiveAnyField
import PfaffianDescent.CorayProjectiveIntersectionIntrinsicH1Finite

/-! d=0 uses the actual untwisted Euler number−m and the genuine positive
OWN selected degree. The canonical coefficient Iso carries the whole ideal
and its original pi-actions into the literal positive-zero-twist first term. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem hOne_rank_of_negativeEuler_and_zero_hZero
    (a b m : ℕ) (hEuler : (a : ℤ) - (b : ℤ) = -(m : ℤ))
    (hZero : a = 0) : b = m := by
  omega

/-- A generic bounded native coefficient transport. Both scalar actions are
constructed from the SAME pi, and the cohomology dictionary is explicit. -/
private theorem wholeIdeal_nativeCoefficientIso_zeroRanks_cut004
    {F : Type u} [Field F] {Y : Scheme.{u}} [hExt : HasExt.{u} Y.Modules]
    (pi : Y ⟶ Spec (CommRingCat.of F)) {M N : Y.Modules} (e : M ≅ N) (m : ℕ) :
    letI : Linear F Y.Modules := schemeModulesLinearOver pi
    Module.Finite F (SchemeModuleOpenSectionsOver pi N ⊤) ∧
      Module.Finite F (schemeModuleCohomology Y N 1) ∧
      Subsingleton (SchemeModuleOpenSectionsOver pi N ⊤) ∧
      Module.finrank F (SchemeModuleOpenSectionsOver pi N ⊤) = 0 ∧
      Module.finrank F (schemeModuleCohomology Y N 1) = m →
    Module.Finite F (SchemeModuleOpenSectionsOver pi M ⊤) ∧
      Module.Finite F (schemeModuleCohomology Y M 1) ∧
      Subsingleton (SchemeModuleOpenSectionsOver pi M ⊤) ∧
      Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) = 0 ∧
      Module.finrank F (schemeModuleCohomology Y M 1) = m := by
  letI : Linear F Y.Modules := schemeModulesLinearOver pi
  intro h
  letI : Module.Finite F (SchemeModuleOpenSectionsOver pi N ⊤) := h.1
  letI : Module.Finite F (schemeModuleCohomology Y N 1) := h.2.1
  letI : Subsingleton (SchemeModuleOpenSectionsOver pi N ⊤) := h.2.2.1
  let e0 := schemeModuleOpenTopIsoLinearEquivOver pi e
  let e1 := @schemeModuleCohomologyIsoLinearEquivOver F inferInstance Y hExt pi M N e 1
  exact ⟨Module.Finite.equiv e0.symm, Module.Finite.equiv e1.symm,
    ⟨fun s t => e0.injective (Subsingleton.elim _ _)⟩,
    e0.finrank_eq.trans h.2.2.2.1, e1.finrank_eq.trans h.2.2.2.2⟩

/-- The actual positive-zero coefficient conversion is checked over an
arbitrary plane ideal, before specializing to the original enormous cut. -/
private theorem planeClosedIdeal_positiveZero_zeroRanks_cut005
    {F : Type u} [Field F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F))
    (pi : scheme I ⟶ Spec (CommRingCat.of F))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i] (m : ℕ) :
    let X := scheme I
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    letI : Linear F X.Modules := schemeModulesLinearOver pi
    let J := IdealSheafDataModule.closedImmersionModule i
    let S := PfaffianDescent.closedImmersionIdealTwistSequence i
      (positiveSheafOfModules (grading I) 0)
    Module.Finite F (SchemeModuleOpenSectionsOver pi J ⊤) ∧
      Module.Finite F (schemeModuleCohomology X J 1) ∧
      Subsingleton (SchemeModuleOpenSectionsOver pi J ⊤) ∧
      Module.finrank F (SchemeModuleOpenSectionsOver pi J ⊤) = 0 ∧
      Module.finrank F (schemeModuleCohomology X J 1) = m →
    Module.Finite F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) ∧
      Module.Finite F (schemeModuleCohomology X S.X₁ 1) ∧
      Subsingleton (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) ∧
      Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) = 0 ∧
      Module.finrank F (schemeModuleCohomology X S.X₁ 1) = m := by
  dsimp only
  let X := scheme I
  letI : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI : Linear F X.Modules := schemeModulesLinearOver pi
  let J : X.Modules := IdealSheafDataModule.closedImmersionModule i
  let S := PfaffianDescent.closedImmersionIdealTwistSequence i
    (positiveSheafOfModules (grading I) 0)
  let e : S.X₁ ≅ J := planeClosedIdeal_positiveZeroCoefficientIso_beyond230 I i
  exact @wholeIdeal_nativeCoefficientIso_zeroRanks_cut004 F inferInstance X
    (schemeModules_hasExt X) pi S.X₁ J e m

/-- The actual rectangular plane negative-Euler calculation is isolated
with its native dictionaries. The final original caller derives every input. -/
private theorem actualPlane_negativeEuler_zeroRanks_cut004
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    let F := GenericHyperplaneField K
    let pE := PfaffianDescent.rectangularSubstitution
      (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
    let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
      (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
    let X := scheme (equationIdeal pE hpE)
    let pi := hypersurfaceToBase pE hpE
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    letI : Linear F X.Modules := schemeModulesLinearOver pi
    ∀ (M : X.Modules) (m : ℕ), schemeModuleLocallyRankOne M →
      Module.Finite F (SchemeModuleOpenSectionsOver pi M ⊤) →
      Module.Finite F (schemeModuleCohomology X M 1) →
      ((Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X M 1) = -(m : ℤ)) → 0 < m →
      Module.Finite F (SchemeModuleOpenSectionsOver pi M ⊤) ∧
        Module.Finite F (schemeModuleCohomology X M 1) ∧
        Subsingleton (SchemeModuleOpenSectionsOver pi M ⊤) ∧
        Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) = 0 ∧
        Module.finrank F (schemeModuleCohomology X M 1) = m := by
  classical
  dsimp only
  let F := GenericHyperplaneField K
  let pE := PfaffianDescent.rectangularSubstitution
    (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
  let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
    (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
  let X := scheme (equationIdeal pE hpE)
  let pi := hypersurfaceToBase pE hpE
  letI : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI : Linear F X.Modules := schemeModulesLinearOver pi
  intro M m hM h0 h1 hBalance hm
  have hNegative :
      (Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X M 1) < 0 :=
    hBalance.trans_lt (by omega)
  have hTop := smoothCubic_actualPlane_negativeEuler_topSections_subsingleton_beyond230
    p hp hp0 M hM hNegative
  letI : Subsingleton (SchemeModuleOpenSectionsOver pi M ⊤) := hTop
  have hZero : Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) = 0 :=
    Module.finrank_zero_of_subsingleton
  have hOne : Module.finrank F (schemeModuleCohomology X M 1) = m :=
    hOne_rank_of_negativeEuler_and_zero_hZero _ _ _ hBalance hZero
  exact ⟨h0, h1, hTop, hZero, hOne⟩

private theorem selectedOriginalWholeCurve_sameE_entireIdeal_zeroRanks_cut004
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ hpC : p ∈ C.toIdeal,
      let F := GenericHyperplaneField K
      let pE := PfaffianDescent.rectangularSubstitution
        (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
      let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
        (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
      let I := equationIdeal pE hpE
      let X := scheme I
      let pi := hypersurfaceToBase pE hpE
      letI : HasExt.{u} X.Modules := schemeModules_hasExt X
      letI : Linear F X.Modules := schemeModulesLinearOver pi
      let i := wholeGenericCutPlaneImmersion C p hp hpC
      let J := IdealSheafDataModule.closedImmersionModule i
      Module.Finite F (SchemeModuleOpenSectionsOver pi J ⊤) ∧
        Module.Finite F (schemeModuleCohomology X J 1) ∧
        Subsingleton (SchemeModuleOpenSectionsOver pi J ⊤) ∧
        Module.finrank F (SchemeModuleOpenSectionsOver pi J ⊤) = 0 ∧
        Module.finrank F (schemeModuleCohomology X J 1) =
          actualCurveCoordinateHilbertDegree C := by
  classical
  obtain ⟨hpC, hIdealData⟩ :=
    selectedOriginalWholeCurve_sameE_entireIdeal_locallyRankOne_finite_euler_neg_degree
      p q hp hp0 n hq hnot C hCmin
  have hDegree :=
    (selectedProjectiveMinimalComponent_hilbertDegree_pos_bound_and_eventualIncrement_anyField
      p q hp hp0 n hq hnot C hCmin).1
  let F := GenericHyperplaneField K
  let pE := PfaffianDescent.rectangularSubstitution
    (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
  let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
    (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
  let I := equationIdeal pE hpE
  let X := scheme I
  let pi := hypersurfaceToBase pE hpE
  let i := wholeGenericCutPlaneImmersion C p hp hpC
  letI : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI : Linear F X.Modules := schemeModulesLinearOver pi
  let J : X.Modules := IdealSheafDataModule.closedImmersionModule i
  refine ⟨hpC, ?_⟩
  exact actualPlane_negativeEuler_zeroRanks_cut004 p hp hp0 J
    (actualCurveCoordinateHilbertDegree C) hIdealData.1 hIdealData.2.1
    hIdealData.2.2.1 hIdealData.2.2.2 hDegree

/-- The public d=0 theorem retains its original exact header. The native
untwisted zero ranks and generic coefficient transport are separate opaque cuts. -/
theorem selectedOriginalWholeCurve_sameE_wholeTwistedIdeal_degreeZero_cohomology_beyond230
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ hpC : p ∈ C.toIdeal,
      let F := GenericHyperplaneField K
      let pE := PfaffianDescent.rectangularSubstitution
        (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
      let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
        (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
      let I := equationIdeal pE hpE
      let X := scheme I
      let pi := hypersurfaceToBase pE hpE
      letI : HasExt.{u} X.Modules := schemeModules_hasExt X
      letI : Linear F X.Modules := schemeModulesLinearOver pi
      let i := wholeGenericCutPlaneImmersion C p hp hpC
      let S := PfaffianDescent.closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading I) 0)
      Module.Finite F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) ∧
        Module.Finite F (schemeModuleCohomology X S.X₁ 1) ∧
        Subsingleton (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) ∧
        Module.finrank F (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) = 0 ∧
        Module.finrank F (schemeModuleCohomology X S.X₁ 1) =
          actualCurveCoordinateHilbertDegree C := by
  obtain ⟨hpC, hUntwisted⟩ :=
    selectedOriginalWholeCurve_sameE_entireIdeal_zeroRanks_cut004
      p q hp hp0 n hq hnot C hCmin
  refine ⟨hpC, ?_⟩
  let F := GenericHyperplaneField K
  let pE := PfaffianDescent.rectangularSubstitution
    (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
  let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
    (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
  let I := equationIdeal pE hpE
  let pi := hypersurfaceToBase pE hpE
  let i := wholeGenericCutPlaneImmersion C p hp hpC
  exact planeClosedIdeal_positiveZero_zeroRanks_cut005 I pi i
    (actualCurveCoordinateHilbertDegree C) hUntwisted

end PfaffianDescent.Coray
