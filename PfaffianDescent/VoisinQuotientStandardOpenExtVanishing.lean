import PfaffianDescent.VoisinStandardOpenExtVanishing
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal

/-!
# Ext acyclicity on the coordinate cover of a projective quotient

This file supplies the local input for the degree-two Cech calculation on a
cubic surface.  It proves that every ordered intersection of quotient
coordinate opens is affine and that the intrinsic negative twists restrict
to the unit module there.  Affine quasicoherent acyclicity then gives the
required degree-one and degree-two Ext vanishings.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry MvPolynomial Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped DirectSum
open DirectSum SetLike

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} {sigma : Type} [Field K] [Finite sigma]

local notation "A" => MvPolynomial sigma K
local notation "AA" => MvPolynomial.homogeneousSubmodule sigma K

/-- A finite intersection of projective basic opens is the basic open of
the product, for the quotient grading used by a projective hypersurface. -/
theorem quotient_projective_basicOpen_finset_inf
    (I : HomogeneousIdeal AA) {iota : Type*} (s : Finset iota)
    (f : iota → CoordinateRing I) :
    AlgebraicGeometry.Proj.basicOpen (grading I) (∏ i ∈ s, f i) =
      s.inf (fun i => AlgebraicGeometry.Proj.basicOpen (grading I) (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert, ha, not_false_eq_true,
        Finset.inf_insert]
      rw [AlgebraicGeometry.Proj.basicOpen_mul, ih]

/-- The coordinate product defining an ordered intersection in the quotient
coordinate cover. -/
def quotientCechDenominator (I : HomogeneousIdeal AA) (n : ℕ)
    (f : Fin (n + 1) → sigma) : CoordinateRing I :=
  ∏ a, coordinate I (f a)

/-- The coordinate product of an ordered intersection is homogeneous of
degree `n+1`. -/
theorem quotientCechDenominator_mem (I : HomogeneousIdeal AA) (n : ℕ)
    (f : Fin (n + 1) → sigma) :
    quotientCechDenominator I n f ∈ grading I (n + 1) := by
  classical
  simpa [quotientCechDenominator] using
    SetLike.prod_mem_graded (grading I)
      (fun _ : Fin (n + 1) => (1 : ℕ))
      (fun a => coordinate I (f a))
      (F := Finset.univ) (fun a _ => coordinate_mem I (f a))

/-- The first coordinate of a nonempty ordered intersection divides its
coordinate product. -/
theorem quotientCoordinate_zero_dvd_cechDenominator
    (I : HomogeneousIdeal AA) (n : ℕ)
    (f : Fin (n + 1) → sigma) :
    coordinate I (f 0) ∣ quotientCechDenominator I n f := by
  simpa [quotientCechDenominator] using
    (Finset.dvd_prod_of_mem
      (fun a : Fin (n + 1) => coordinate I (f a))
      (Finset.mem_univ (0 : Fin (n + 1))))

/-- An ordered quotient-coordinate intersection is the basic open of its
coordinate product. -/
theorem quotientCechBasicOpen_eq_inf
    (I : HomogeneousIdeal AA) (n : ℕ)
    (f : Fin (n + 1) → sigma) :
    AlgebraicGeometry.Proj.basicOpen (grading I)
        (quotientCechDenominator I n f) =
      ⨅ a, quotientCoordinateOpen I (f a) := by
  classical
  change AlgebraicGeometry.Proj.basicOpen (grading I)
      (∏ a, coordinate I (f a)) =
    ⨅ a, AlgebraicGeometry.Proj.basicOpen (grading I) (coordinate I (f a))
  rw [← Finset.inf_univ_eq_iInf]
  simpa using quotient_projective_basicOpen_finset_inf I
    (Finset.univ : Finset (Fin (n + 1)))
    (fun a => coordinate I (f a))

/-- Every ordered intersection in the quotient coordinate cover is affine. -/
theorem quotientCoordinateOpen_cech_inter_affine
    (I : HomogeneousIdeal AA) (n : ℕ) (f : Fin (n + 1) → sigma) :
    IsAffineOpen (⨅ i, quotientCoordinateOpen I (f i)) := by
  classical
  change IsAffineOpen
    (⨅ i, AlgebraicGeometry.Proj.basicOpen (grading I) (coordinate I (f i)))
  rw [← Finset.inf_univ_eq_iInf,
    ← quotient_projective_basicOpen_finset_inf I]
  exact AlgebraicGeometry.Proj.isAffineOpen_basicOpen (grading I)
    (quotientCechDenominator I n f) (m := n + 1)
    (quotientCechDenominator_mem I n f) (Nat.succ_pos n)

/-- A projective quotient of a polynomial ring in finitely many variables is
locally noetherian. -/
theorem quotientProj_isLocallyNoetherian (I : HomogeneousIdeal AA) :
    IsLocallyNoetherian (Proj (grading I)) := by
  letI : IsScalarTower K ((grading I) 0) (CoordinateRing I) := by
    constructor
    intro x y z
    change (x • (y : CoordinateRing I)) * z = x • ((y : CoordinateRing I) * z)
    exact smul_mul_assoc x (y : CoordinateRing I) z
  letI : Algebra.FiniteType ((grading I) 0) (CoordinateRing I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K ((grading I) 0)
      (CoordinateRing I)
  exact LocallyOfFiniteType.isLocallyNoetherian (Proj.toSpecZero (grading I))

/-- Multiplication by a power of a quotient coordinate is invertible after
restriction to any open contained in its coordinate chart. -/
theorem restrict_mulQuotientCoordinatePower_isIso_of_le
    (I : HomogeneousIdeal AA) (U : Scheme.Opens (Proj (grading I)))
    (j : sigma) (m : ℕ) (hU : U ≤ quotientCoordinateOpen I j) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (mulHomogeneous (grading I)
        (degreeOnePower (grading I)
          (⟨coordinate I j, coordinate_mem I j⟩ : grading I 1) m) 0)) := by
  apply restrict_map_isIso_of_stalk U
  intro x
  letI : (pointIdeal (grading I) (U.ι x)).IsPrime :=
    ProjectiveSpectrum.isPrime (U.ι x)
  have hx : coordinate I j ∈ (pointIdeal (grading I) (U.ι x)).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    exact (ProjectiveSpectrum.mem_basicOpen (grading I)
      (coordinate I j) (U.ι x)).mp (hU x.property)
  have hsx :
      (degreeOnePower (grading I)
        (⟨coordinate I j, coordinate_mem I j⟩ : grading I 1) m :
          CoordinateRing I) ∈
        (pointIdeal (grading I) (U.ι x)).primeCompl := by
    change (coordinate I j) ^ m ∈
      (pointIdeal (grading I) (U.ι x)).primeCompl
    exact Submonoid.pow_mem _ hx m
  change IsIso ((TopCat.Presheaf.stalkFunctor _ (U.ι x)).map
    (mulHomogeneousPresheaf (grading I)
      (degreeOnePower (grading I)
        (⟨coordinate I j, coordinate_mem I j⟩ : grading I 1) m) 0))
  apply mulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
    (grading I)
    (degreeOnePower (grading I)
      (⟨coordinate I j, coordinate_mem I j⟩ : grading I 1) m)
    0 (U.ι x) hsx
  exact gradedSurjective_irrelevant_le_span_degreeOne AA (grading I)
    (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
    mvPolynomial_irrelevant_le_span_degreeOne_small

/-- The intrinsic negative twist is the unit module on every open contained
in a quotient coordinate chart. -/
noncomputable def quotientNegativeTwistOpenIsoUnit
    (I : HomogeneousIdeal AA) (U : Scheme.Opens (Proj (grading I)))
    (j : sigma) (hU : U ≤ quotientCoordinateOpen I j) (m : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).obj
        (sheafOfModules (grading I) m) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let s := degreeOnePower (grading I)
    (⟨coordinate I j, coordinate_mem I j⟩ : grading I 1) m
  let q : sheafOfModules (grading I) m ⟶ sheafOfModules (grading I) 0 := by
    simpa using mulHomogeneous (grading I) s 0
  letI : IsIso (F.map q) := by
    dsimp only [q, s]
    simpa using restrict_mulQuotientCoordinatePower_isIso_of_le I U j m hU
  exact asIso (F.map q) ≪≫
    (F.mapIso (unitIsoZeroTwist (grading I))).symm ≪≫
    Scheme.Modules.restrictUnitIso U.ι

/-- Sections of a negative twist on an open contained in one quotient
coordinate chart are canonically structure-sheaf sections. -/
noncomputable def quotientNegativeTwistSectionsIsoUnit
    (I : HomogeneousIdeal AA) (U : Scheme.Opens (Proj (grading I)))
    (j : sigma) (hU : U ≤ quotientCoordinateOpen I j) (m : ℕ) :
    Γ(sheafOfModules (grading I) m, U) ≅
      AddCommGrpCat.of Γ((U : Scheme), ⊤) := by
  let e := quotientNegativeTwistOpenIsoUnit I U j hU m
  exact (moduleRestrictTopIso (sheafOfModules (grading I) m) U).symm ≪≫
    ((Scheme.Modules.toPresheaf (U : Scheme)).mapIso e).app (op ⊤)

/-- On a homogeneous quotient basic open lying in a coordinate chart,
negative-twist sections are the degree-zero homogeneous localization. -/
noncomputable def quotientNegativeTwistBasicOpenIsoAway
    (I : HomogeneousIdeal AA) (f : CoordinateRing I) (d : ℕ)
    (hf : f ∈ grading I d) (hd : 0 < d)
    (j : sigma) (hdiv : coordinate I j ∣ f) (m : ℕ) :
    Γ(sheafOfModules (grading I) m,
        AlgebraicGeometry.Proj.basicOpen (grading I) f) ≅
      AddCommGrpCat.of (HomogeneousLocalization.Away (grading I) f) := by
  let U := AlgebraicGeometry.Proj.basicOpen (grading I) f
  have hU : U ≤ quotientCoordinateOpen I j :=
    AlgebraicGeometry.Proj.basicOpen_mono (grading I)
      (coordinate I j) f hdiv
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  exact quotientNegativeTwistSectionsIsoUnit I U j hU m ≪≫
    F.mapIso U.topIso ≪≫
    F.mapIso (AlgebraicGeometry.Proj.basicOpenIsoAway
      (grading I) f hf hd).symm

/-- Every summand of the quotient coordinate-cover Cech complex has an
explicit homogeneous-localization model. -/
noncomputable def quotientNegativeTwistCechSummandIsoAway
    (I : HomogeneousIdeal AA) (m n : ℕ)
    (f : Fin (n + 1) → sigma) :
    Γ(sheafOfModules (grading I) m,
        ⨅ a, quotientCoordinateOpen I (f a)) ≅
      AddCommGrpCat.of (HomogeneousLocalization.Away (grading I)
        (quotientCechDenominator I n f)) :=
  (modulePresheaf (grading I) m).presheaf.mapIso
      (eqToIso (quotientCechBasicOpen_eq_inf I n f)).op ≪≫
    quotientNegativeTwistBasicOpenIsoAway I
      (quotientCechDenominator I n f) (n + 1)
      (quotientCechDenominator_mem I n f) (Nat.succ_pos n)
      (f 0) (quotientCoordinate_zero_dvd_cechDenominator I n f) m

/-- Every ordered coordinate intersection has vanishing degree-one and
degree-two section-representer Ext into an intrinsic negative twist. -/
theorem quotientNegativeTwistCechInter_sectionRepresenter_ext_one_and_two_subsingleton
    (I : HomogeneousIdeal AA) (m n : ℕ)
    [HasExt.{u} (Proj (grading I)).Modules]
    (f : Fin (n + 1) → sigma) :
    let U : Scheme.Opens (Proj (grading I)) :=
      ⨅ i, quotientCoordinateOpen I (f i)
    Subsingleton
        (Ext.{u}
          (show (Proj (grading I)).Modules from
            sectionRepresenter (Proj (grading I)).ringCatSheaf U)
          (sheafOfModules (grading I) m) 1) ∧
      Subsingleton
        (Ext.{u}
          (show (Proj (grading I)).Modules from
            sectionRepresenter (Proj (grading I)).ringCatSheaf U)
          (sheafOfModules (grading I) m) 2) := by
  let U : Scheme.Opens (Proj (grading I)) :=
    ⨅ i, quotientCoordinateOpen I (f i)
  have hAff : IsAffineOpen U :=
    quotientCoordinateOpen_cech_inter_affine I n f
  letI : IsLocallyNoetherian (Proj (grading I)) :=
    quotientProj_isLocallyNoetherian I
  letI : IsLocallyNoetherian (U : Scheme) := inferInstance
  letI : IsAffine (U : Scheme) := hAff
  letI : IsNoetherianRing Γ((U : Scheme), ⊤) :=
    IsLocallyNoetherian.component_noetherian
      ⟨⊤, isAffineOpen_top (U : Scheme)⟩
  have hUle : U ≤ quotientCoordinateOpen I (f 0) :=
    iInf_le_of_le (0 : Fin (n + 1)) le_rfl
  let e : (Scheme.Modules.restrictFunctor U.ι).obj
      (sheafOfModules (grading I) m) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    quotientNegativeTwistOpenIsoUnit I U (f 0) hUle m
  exact
    sectionRepresenter_ext_one_and_two_subsingleton_of_affineOpen_of_restrictIsoUnit
      U hAff (sheafOfModules (grading I) m) e

end PfaffianDescent.ProjectiveNegativeTwist
