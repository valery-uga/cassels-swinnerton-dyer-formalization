import PfaffianDescent.P3PositiveTwistGlobalSections
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentSectionChartCoefficient
import AllCharacteristics.AmbientChartPresentation

/- SOURCE ONLY / UNVERIFIED. Literal raw-PS homogeneous fractions and actual
P3 chart trivializations; no quotient-by-zero grading or geometric certificate. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open HomogeneousLocalization AllCharacteristics.HomogeneousProjective
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
local notation "PS" => homogeneousSubmodule (Fin 4) K
local notation "S" => MvPolynomial (Fin 4) K

/-- Multiplication by the actual chart basis restores the actual homogeneous
section from its literal normalized fraction, in every degree. -/
lemma p3ActualChartBasisInvHom_fraction (j : Fin 4) (m : ℕ) (p : PS m) :
    ((Scheme.Modules.toPresheaf (Proj PS)).map
      (p3PositiveTwistTrivializationInvHom K j m)).app
      (op (p3StandardOpen (K := K) j))
      ((Proj.awayToSection PS (X j)).hom (ambientChartEvaluation j (p : S))) =
    (positiveGlobalSectionOfHomogeneous PS m p).val
      (op (p3StandardOpen (K := K) j)) := by
  let U := p3StandardOpen (K := K) j
  let r := (Proj.awayToSection PS (X j)).hom (ambientChartEvaluation j (p : S))
  let z₀ := ((Scheme.Modules.toPresheaf (Proj PS)).map
    (unitToZeroTwist PS)).app (op U) r
  let p₀ := ((Scheme.Modules.toPresheaf (Proj PS)).map
    (zeroTwistToPositiveZero PS)).app (op U) z₀
  let zm := (positiveMulHomogeneous PS
    (degreeOnePower PS (p3Coordinate K j) m) 0).val.app (op U) p₀
  let eadd : positiveSheafOfModules PS (0 + m) ≅ positiveSheafOfModules PS m :=
    eqToIso (by rw [zero_add])
  apply Subtype.ext
  funext x
  change (((eadd.hom.val.app (op U)) zm).1 x) = _
  rw [positiveZeroAddCast_apply_val K m (op U) zm x]
  change algebraMap S (Localization.AtPrime (positivePointIdeal PS x.1))
      ((degreeOnePower PS (p3Coordinate K j) m : PS m) : S) *
    (((Proj.awayToSection PS (X j)).hom
      (ambientChartEvaluation j (p : S))).val x).val =
    Localization.mk (p : S) ⟨1, Submonoid.one_mem _⟩
  rw [ambientChartEvaluation_homogeneous j (p : S) p.property]
  have ha := ProjectiveSpectrum.Proj.awayToSection_apply PS (X j)
    (Away.mk PS (isHomogeneous_X K j) m (p : S) (by simpa using p.property)) x
  erw [ha, Away.val_mk]
  rw [Localization.mk_eq_mk', IsLocalization.map_mk']
  simp only [RingHom.id_apply]
  erw [Localization.mk_one_eq_algebraMap]
  have he : (X j : S) ∈ (positivePointIdeal PS x.1).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    exact (ProjectiveSpectrum.mem_basicOpen PS (X j) x.1).mp x.2
  exact IsLocalization.mk'_spec'
    (M := (positivePointIdeal PS x.1).primeCompl)
    (Localization.AtPrime (positivePointIdeal PS x.1))
    (p : S) ⟨(X j : S) ^ m, Submonoid.pow_mem _ he m⟩

/-- The canonical actual P3 section trivialization computes exactly the
normalized homogeneous fraction; no unspecified unit factor is introduced. -/
lemma p3ActualHomogeneousSectionsChartCoefficient (j : Fin 4) (m : ℕ) (p : PS m) :
    (p3PositiveTwistSectionsIsoStructure K (p3StandardOpen (K := K) j) j le_rfl m).hom
      ((positiveGlobalSectionOfHomogeneous PS m p).val
        (op (p3StandardOpen (K := K) j))) =
      (Proj.awayToSection PS (X j)).hom (ambientChartEvaluation j (p : S)) := by
  let e := p3PositiveTwistSectionsIsoStructure K
    (p3StandardOpen (K := K) j) j le_rfl m
  apply (e.addCommGroupIsoToAddEquiv.symm).injective
  change e.inv (e.hom ((positiveGlobalSectionOfHomogeneous PS m p).val
    (op (p3StandardOpen (K := K) j)))) =
      e.inv ((Proj.awayToSection PS (X j)).hom (ambientChartEvaluation j (p : S)))
  rw [Iso.hom_inv_id_apply]
  rw [p3PositiveTwistSectionsIsoStructure_inv]
  exact (p3ActualChartBasisInvHom_fraction K j m p).symm

/-- The actual module-unit coordinate agrees with the canonical section
coordinate. This compares the two existing top-open identifications directly. -/
lemma p3ActualLocalUnitCoordinate_eq_sectionsChart
    (j : Fin 4) (m : ℕ) (hm : 0 < m)
    (y : Γ(positiveSheafOfModules PS m, p3StandardOpen (K := K) j)) :
    schemeModuleLocalUnitSectionAddEquiv (p3StandardOpen (K := K) j)
      (positiveSheafOfModules PS m) (p3PositiveTwistStandardOpenIsoUnit K j m hm) y =
    (p3PositiveTwistSectionsIsoStructure K
      (p3StandardOpen (K := K) j) j le_rfl m).hom y := by
  let U := p3StandardOpen (K := K) j
  let T := positiveSheafOfModules PS m
  let e := p3PositiveTwistOpenIsoUnit K U j le_rfl m
  let R := Scheme.Modules.restrictFunctor U.ι
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  change (((moduleRestrictTopIso T U).inv ≫
    (((Scheme.Modules.toPresheaf (U : Scheme)).mapIso e).app (op ⊤)).hom ≫
    (((Scheme.Modules.toPresheaf (U : Scheme)).map
      (Scheme.Modules.restrictUnitIso U.ι).inv).app (op ⊤)) ≫
    (moduleRestrictTopIso (SheafOfModules.unit (Proj PS).ringCatSheaf) U).hom) y) =
    (((moduleRestrictTopIso T U).inv ≫
      (((Scheme.Modules.toPresheaf (U : Scheme)).mapIso e).app (op ⊤)).hom ≫
      F.map U.topIso.hom) y)
  rw [restrictUnit_inv_comp_moduleRestrictTop K U]
  rfl

/-- The actual canonical module-unit coefficient of the actual homogeneous
section is the actual chart fraction as a function on the open subscheme. -/
lemma p3ActualHomogeneousUnitEndomorphismCoefficient
    (j : Fin 4) (m : ℕ) (hm : 0 < m) (p : PS m) :
    BundleSectionZeroLocus.unitEndomorphismValue
      ((Scheme.Modules.restrictUnitIso (p3StandardOpen (K := K) j).ι).inv ≫
        (Scheme.Modules.restrictFunctor (p3StandardOpen (K := K) j).ι).map
          ((positiveSheafOfModules PS m).unitHomEquiv.symm
            (positiveGlobalSectionOfHomogeneous PS m p)) ≫
        (p3PositiveTwistStandardOpenIsoUnit K j m hm).hom) =
      ((p3StandardOpen (K := K) j).topIso.inv).hom
        ((Proj.awayToSection PS (X j)).hom (ambientChartEvaluation j (p : S))) := by
  rw [PfaffianDescent.cubicClosedPointSerreSurfaceJetCotangent_sectionChartCoefficient,
    p3ActualLocalUnitCoordinate_eq_sectionsChart,
    p3ActualHomogeneousSectionsChartCoefficient]

end PfaffianDescent.ProjectiveNegativeTwist
