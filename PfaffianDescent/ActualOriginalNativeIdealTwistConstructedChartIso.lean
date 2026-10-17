import PfaffianDescent.ActualOriginalIdealTwistSourceRefinement
import PfaffianDescent.ActualNamedIdealTwistChartFactory
import PfaffianDescent.ActualNamedIdealTwistChartData
import PfaffianDescent.ActualOriginalQuarticCotangentChartChoice
import PfaffianDescent.ActualPositiveTwistChartUnit

/- SOURCE ONLY / UNVERIFIED. The SAME native chart Iso is the ideal
   projection of one internally constructed package. That package retains
   its whole original source construction, including inverse, and proves
   the inclusion/local-section laws together before specialization. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Construct all native chart Isos and proved laws ONCE from the SAME
original residue/factorization/chart data. No desired comparison is input. -/
def actualOriginalNativeIdealTwistConstructedChartData
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :=
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let ell : grading I 1 := ⟨coordinate I C.index, coordinate_mem I C.index⟩
  let U := Proj.basicOpen (grading I) (coordinate I C.index)
  let e := Proj.basicOpenIsoSpec (grading I) (coordinate I C.index)
    (coordinate_mem I C.index) Nat.zero_lt_one
  let j := Spec.map (CommRingCat.ofHom C.residue)
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  let hfac : (j ≫ e.inv) ≫ U.ι = q := by
    rw [Category.assoc]
    exact C.factorization
  actualNamedIdealTwistChartData U e.inv (chartι I C.index)
    (hf0 := isOpenImmersion_chartι I C.index) (by rfl) q j hfac
    (positiveSheafOfModules (grading I) 2) (actualPositiveTwistChartUnitIso I ell 2)

def actualOriginalNativeIdealTwistConstructedChartIso
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    (Scheme.Modules.restrictFunctor (chartι I C.index)).obj
      (closedImmersionIdealTwist q (positiveSheafOfModules (grading I) 2)) ≅
    closedImmersionModule (Spec.map (CommRingCat.ofHom C.residue)) := by
  dsimp only
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom C.residue)) :=
    IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  exact (actualOriginalNativeIdealTwistConstructedChartData p hp P C).idealIso


/-- Inferred proof of the actual inclusion square for the SAME original chart.
All closedness/factorization/twist data are constructed internally. -/
def actualOriginalNativeIdealTwistConstructedChartIso_toInclusion
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (C : ActualOriginalQuarticCotangentChart p hp P) :=
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let ell : grading I 1 := ⟨coordinate I C.index, coordinate_mem I C.index⟩
  let U := Proj.basicOpen (grading I) (coordinate I C.index)
  let e := Proj.basicOpenIsoSpec (grading I) (coordinate I C.index)
    (coordinate_mem I C.index) Nat.zero_lt_one
  let j := Spec.map (CommRingCat.ofHom C.residue)
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ C.residue_surjective
  let hfac : (j ≫ e.inv) ≫ U.ι = q := by
    rw [Category.assoc]
    exact C.factorization
  actualOriginalIdealTwistSourceRefinementIso_toInclusion U e.inv q j hfac
    (positiveSheafOfModules (grading I) 2) (actualPositiveTwistChartUnitIso I ell 2)

end PfaffianDescent
