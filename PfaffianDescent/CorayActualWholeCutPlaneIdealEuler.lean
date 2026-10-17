import PfaffianDescent.FiniteClosedImmersionIdealEuler
import PfaffianDescent.CorayActualWholeCutPlaneCartier
import PfaffianDescent.RegularPrincipalImmersionNativeRankOne
import PfaffianDescent.CorayActualWholeCutPlaneDivisorCycleDegree
import PfaffianDescent.CorayProperGeometricallyIntegralUnitSectionsRankOne
import PfaffianDescent.CorayActualGenericPlaneSectionH1RankOne

/-! SOURCE ONLY / UNVERIFIED162. Entire actual Z→SAME E constructs its
literal invertible ideal, finite original-field H0/H1 and Euler number −m,
where m is the ORIGINAL Hilbert degree, retaining full cut thickness. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial AllCharacteristics
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem nativeFiniteRank_congr162
    {F : Type u} [Field F] {Z : Scheme.{u}}
    (g h : Z ⟶ Spec (.of F)) [IsFinite g] [IsFinite h] (e : g = h) :
    finiteSchemeRank g = finiteSchemeRank h := by
  subst h
  rfl

private theorem finiteClosedImmersionIdeal_finite_euler_neg_rank_cut162
    {X Z : Scheme.{u}} (pi : X ⟶ Spec (.of K)) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsFinite (i ≫ pi)] [HasExt.{u} X.Modules]
    (m : ℕ) (hrank : finiteSchemeRank (i ≫ pi) = m) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi
      (SheafOfModules.unit X.ringCatSheaf) ⊤) →
    Module.finrank K (SchemeModuleOpenSectionsOver pi
      (SheafOfModules.unit X.ringCatSheaf) ⊤) = 1 →
    Module.Finite K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) →
    Module.finrank K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) = 1 →
    Module.Finite K (SchemeModuleOpenSectionsOver pi
      (IdealSheafDataModule.closedImmersionModule i) ⊤) ∧
      Module.Finite K (schemeModuleCohomology X
        (IdealSheafDataModule.closedImmersionModule i) 1) ∧
      ((Module.finrank K (SchemeModuleOpenSectionsOver pi
          (IdealSheafDataModule.closedImmersionModule i) ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology X
          (IdealSheafDataModule.closedImmersionModule i) 1) = -(m : ℤ)) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro h0 h0rank h1 h1rank
  have h := finiteClosedImmersionIdeal_finite_and_h0_h1_change pi i h0 h1
  have hEuler := h.2.2
  rw [h0rank, h1rank, hrank, Nat.cast_one, sub_self, zero_sub] at hEuler
  exact ⟨h.1, h.2.1, hEuler⟩

private theorem nativeFiniteRank_exists_transport_cut162
    {F : Type u} [Field F] {Z : Scheme.{u}}
    (g h : Z ⟶ Spec (.of F)) (e : g = h) (m : ℕ) :
    (∃ hh : IsFinite h, letI := hh; finiteSchemeRank h = m) →
      ∃ hg : IsFinite g, letI := hg; finiteSchemeRank g = m := by
  subst h
  exact fun H => H

private theorem selectedOriginalWholeCurve_wholeCut_finiteRankOnly_cut162
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ hfinite : IsFinite (toBase (wholeGenericCutIdeal C)),
      letI := hfinite
      finiteSchemeRank (toBase (wholeGenericCutIdeal C)) =
        actualCurveCoordinateHilbertDegree C := by
  obtain ⟨hfinite, hrank, _hcut, _hgrades⟩ :=
    selectedOriginalWholeCurve_genericCut_finite_rank_degree p q hp hp0 n hq hnot C hCmin
  exact ⟨hfinite, hrank⟩

private theorem wholeGenericCut_sameE_finiteRank_transport_cut162
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpC : p ∈ C.toIdeal) (m : ℕ) :
    (∃ hfinite : IsFinite (toBase (wholeGenericCutIdeal C)),
      letI := hfinite
      finiteSchemeRank (toBase (wholeGenericCutIdeal C)) = m) →
    (let L := GenericHyperplaneField K
     let pE := PfaffianDescent.rectangularSubstitution
       (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K L))
     let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
       (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K L))
     let pi := hypersurfaceToBase pE hpE
     let i := wholeGenericCutPlaneImmersion C p hp hpC
     ∃ hfinite : IsFinite (i ≫ pi),
       letI := hfinite
       finiteSchemeRank (i ≫ pi) = m) := by
  exact nativeFiniteRank_exists_transport_cut162 _ (toBase (wholeGenericCutIdeal C))
    (wholeGenericCutPlaneImmersion_toBase C p hp hpC) m

private theorem selectedOriginalWholeCurve_sameE_entireFiniteRank_cut162
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hpC : p ∈ C.toIdeal) :
    let L := GenericHyperplaneField K
    let pE := PfaffianDescent.rectangularSubstitution
      (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K L))
    let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
      (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K L))
    let E := hypersurface pE hpE
    let pi := hypersurfaceToBase pE hpE
    let i := wholeGenericCutPlaneImmersion C p hp hpC
    ∃ hfinite : IsFinite (i ≫ pi),
      letI := hfinite
      finiteSchemeRank (i ≫ pi) = actualCurveCoordinateHilbertDegree C := by
  exact wholeGenericCut_sameE_finiteRank_transport_cut162 C p hp hpC
    (actualCurveCoordinateHilbertDegree C)
    (selectedOriginalWholeCurve_wholeCut_finiteRankOnly_cut162
      p q hp hp0 n hq hnot C hCmin)

private theorem selectedOriginalWholeCurve_sameE_entireIdeal_rankOne_cut162
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hpC : p ∈ C.toIdeal) :
    schemeModuleLocallyRankOne (IdealSheafDataModule.closedImmersionModule
      (wholeGenericCutPlaneImmersion C p hp hpC)) := by
  obtain ⟨H⟩ := selectedOriginalWholeCurve_genericCutPlane_regularPrincipalImmersion
    p q hp hp0 n hq hnot C hCmin hpC
  exact H.inverseCartierTwist_locallyRankOne

private theorem selectedOriginalWholeCurve_sameE_entireIdeal_finiteEuler_cut162
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hpC : p ∈ C.toIdeal) :
    let L := GenericHyperplaneField K
    let pE := PfaffianDescent.rectangularSubstitution
      (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K L))
    let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
      (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K L))
    let E := hypersurface pE hpE
    let pi := hypersurfaceToBase pE hpE
    let i := wholeGenericCutPlaneImmersion C p hp hpC
    let J := IdealSheafDataModule.closedImmersionModule i
    letI : EnoughInjectives E.Modules := sheafOfModules_enoughInjectives E.ringCatSheaf
    letI : HasExt.{u} E.Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} E.Modules
    letI : Linear L E.Modules := schemeModulesLinearOver pi
    Module.Finite L (SchemeModuleOpenSectionsOver pi J ⊤) ∧
      Module.Finite L (schemeModuleCohomology E J 1) ∧
      ((Module.finrank L (SchemeModuleOpenSectionsOver pi J ⊤) : ℤ) -
        Module.finrank L (schemeModuleCohomology E J 1) =
        -(actualCurveCoordinateHilbertDegree C : ℤ)) := by
  let L := GenericHyperplaneField K
  let pE := PfaffianDescent.rectangularSubstitution
      (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K L))
  let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
      (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K L))
  let E := hypersurface pE hpE
  let pi := hypersurfaceToBase pE hpE
  let i := wholeGenericCutPlaneImmersion C p hp hpC
  let J := IdealSheafDataModule.closedImmersionModule i
  letI : EnoughInjectives E.Modules := sheafOfModules_enoughInjectives E.ringCatSheaf
  letI : HasExt.{u} E.Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} E.Modules
  letI : Linear L E.Modules := schemeModulesLinearOver pi
  obtain ⟨hfinite, hrank⟩ := selectedOriginalWholeCurve_sameE_entireFiniteRank_cut162
    p q hp hp0 n hq hnot C hCmin hpC
  letI := hfinite
  have h0E := smoothCubic_actualLinearGenericPlaneSection_unitTopSections_finite_and_finrank_one
    p hp hp0
  have h1E := smoothCubic_actualLinearGenericPlaneSection_unit_cohomology_one_finite_finrank_eq_one
    p hp hp0
  exact finiteClosedImmersionIdeal_finite_euler_neg_rank_cut162 pi i
    (actualCurveCoordinateHilbertDegree C) hrank h0E.1 h0E.2 h1E.1 h1E.2

/-- ORIGINAL inputs construct the entire cut's literal locally rank-one
ideal on SAME E, finite H0/H1 and χ(I_Z)=−m. This is the actual untwisted
Euler bridge; no degree definition, Euler/Cartier or cohomology conclusion
is supplied to the caller. -/
theorem selectedOriginalWholeCurve_sameE_entireIdeal_locallyRankOne_finite_euler_neg_degree
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ hpC : p ∈ C.toIdeal,
      let L := GenericHyperplaneField K
      let pE := PfaffianDescent.rectangularSubstitution
        (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K L))
      let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
        (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K L))
      let E := hypersurface pE hpE
      let pi := hypersurfaceToBase pE hpE
      let i := wholeGenericCutPlaneImmersion C p hp hpC
      let J := IdealSheafDataModule.closedImmersionModule i
      letI : EnoughInjectives E.Modules := sheafOfModules_enoughInjectives E.ringCatSheaf
      letI : HasExt.{u} E.Modules :=
        CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} E.Modules
      letI : Linear L E.Modules := schemeModulesLinearOver pi
      schemeModuleLocallyRankOne J ∧
        Module.Finite L (SchemeModuleOpenSectionsOver pi J ⊤) ∧
        Module.Finite L (schemeModuleCohomology E J 1) ∧
        ((Module.finrank L (SchemeModuleOpenSectionsOver pi J ⊤) : ℤ) -
          Module.finrank L (schemeModuleCohomology E J 1) =
          -(actualCurveCoordinateHilbertDegree C : ℤ)) := by
  have hpC : p ∈ C.toIdeal := by
    apply hCmin.le
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (by simp)
  refine ⟨hpC, ?_⟩
  exact ⟨selectedOriginalWholeCurve_sameE_entireIdeal_rankOne_cut162
      p q hp hp0 n hq hnot C hCmin hpC,
    selectedOriginalWholeCurve_sameE_entireIdeal_finiteEuler_cut162
      p q hp hp0 n hq hnot C hCmin hpC⟩

end PfaffianDescent.Coray
