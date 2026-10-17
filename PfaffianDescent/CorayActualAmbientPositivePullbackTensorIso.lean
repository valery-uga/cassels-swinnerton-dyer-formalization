import PfaffianDescent.CorayActualPositiveWeightedNativeChartEntries
import PfaffianDescent.ActualPositiveTwistPullbackTensorIso

/-! Canonical positive-twist tensor pullback for the RAW original ambient
Proj PS, without replacing it by Proj of the bot quotient.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open ProjectiveNegativeTwist AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

private theorem mappedFour_isIso
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X₀ X₁ X₂ X₃ X₄ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄)
    [IsIso (F.map a)] [IsIso (F.map b)] [IsIso (F.map c)] [IsIso (F.map d)] :
    IsIso (F.map (a ≫ b ≫ c ≫ d)) := by
  have hmap : F.map (a ≫ b ≫ c ≫ d) =
      F.map a ≫ F.map b ≫ F.map c ≫ F.map d := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp]
  exact hmap.symm ▸ (inferInstance : IsIso
    (F.map a ≫ F.map b ≫ F.map c ≫ F.map d))

/-- The actual global Xi^m section, as a unit-to-positive-twist morphism. -/
def actualAmbientPositiveChartBasisInvHom (j : Fin 4) (m : ℕ) :
    SheafOfModules.unit (Proj PS).ringCatSheaf ⟶ positiveSheafOfModules PS m :=
  unitToZeroTwist PS ≫ zeroTwistToPositiveZero PS ≫
    positiveMulHomogeneous PS (degreeOnePower PS (p3Coordinate K j) m) 0 ≫
      (eqToIso (congrArg (positiveSheafOfModules PS) (Nat.zero_add m))).hom

/-- The original Xi^m global section is invertible on the SAME Xi chart. -/
theorem actualAmbientPositiveChartBasisInvHom_isIso (j : Fin 4) (m : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (p3StandardOpen (K := K) j).ι).map
      (actualAmbientPositiveChartBasisInvHom (K := K) j m)) := by
  let U := p3StandardOpen (K := K) j
  let F := Scheme.Modules.restrictFunctor U.ι
  let ell : PS 1 := p3Coordinate K j
  have hspan : (HomogeneousIdeal.irrelevant PS).toIdeal ≤
      Ideal.span (Set.range (fun f : PS 1 => (f : A))) :=
    mvPolynomial_irrelevant_le_span_degreeOne_small
  have hmul : IsIso (F.map (positiveMulHomogeneous PS (degreeOnePower PS ell m) 0)) := by
    apply restrict_map_isIso_of_stalk U
    intro x
    letI : (positivePointIdeal PS (U.ι x)).IsPrime := ProjectiveSpectrum.isPrime (U.ι x)
    have hxell : (ell : A) ∈ (positivePointIdeal PS (U.ι x)).primeCompl := by
      rw [Ideal.mem_primeCompl_iff]
      exact (ProjectiveSpectrum.mem_basicOpen PS (X j) (U.ι x)).mp x.2
    have hs : ((degreeOnePower PS ell m : PS m) : A) ∈
        (positivePointIdeal PS (U.ι x)).primeCompl := Submonoid.pow_mem _ hxell m
    change IsIso ((TopCat.Presheaf.stalkFunctor _ (U.ι x)).map
      (positiveMulHomogeneousPresheaf PS (degreeOnePower PS ell m) 0))
    exact positiveMulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
      PS (degreeOnePower PS ell m) 0 (U.ι x) hs hspan
  have hunit : @IsIso (Proj PS).Modules
      (inferInstance : Category (Proj PS).Modules) _ _ (unitToZeroTwist PS) :=
    unitToZeroTwist_isIso PS
  have hunitMapped : @IsIso U.toScheme.Modules
      (inferInstance : Category U.toScheme.Modules) _ _
      (F.map (unitToZeroTwist PS)) :=
    @CategoryTheory.Functor.map_isIso (Proj PS).Modules
      (inferInstance : Category (Proj PS).Modules)
      (SheafOfModules.unit (Proj PS).ringCatSheaf) (sheafOfModules PS 0)
      U.toScheme.Modules (inferInstance : Category U.toScheme.Modules)
      F (unitToZeroTwist PS) hunit
  have hzeroMapped : @IsIso U.toScheme.Modules
      (inferInstance : Category U.toScheme.Modules) _ _
      (F.map (zeroTwistToPositiveZero PS)) := by
    change IsIso (F.map (positiveZeroTwistIso PS).inv)
    infer_instance
  let e : @Iso (Proj PS).Modules (inferInstance : Category (Proj PS).Modules)
      (positiveSheafOfModules PS (0 + m)) (positiveSheafOfModules PS m) :=
    eqToIso (congrArg (positiveSheafOfModules PS) (Nat.zero_add m))
  have hcastMapped : @IsIso U.toScheme.Modules
      (inferInstance : Category U.toScheme.Modules) _ _ (F.map e.hom) :=
    (F.mapIso e).isIso_hom
  exact @mappedFour_isIso (Proj PS).Modules U.toScheme.Modules
    (inferInstance : Category (Proj PS).Modules)
    (inferInstance : Category U.toScheme.Modules) F _ _ _ _ _
    (unitToZeroTwist PS) (zeroTwistToPositiveZero PS)
    (positiveMulHomogeneous PS (degreeOnePower PS (p3Coordinate K j) m) 0)
    e.hom hunitMapped hzeroMapped hmul hcastMapped

/-- The actual tensor-pullback comparison is an isomorphism for every native
module and every nonnegative original ambient positive twist. Local generators
are constructed from the original coordinate sections, not supplied. -/
theorem actualAmbientPositiveTwist_pullbackTensorMap_isIso
    {X : Scheme.{u}} (f : X ⟶ Proj PS) (M : (Proj PS).Modules) (m : ℕ) :
    IsIso (PfaffianDescent.cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
      (positiveSheafOfModules PS m)) := by
  letI := PfaffianDescent.cubicClosedPointSerreTensorStalk_pullbackTensorMap_unit_isIso f M
  apply PfaffianDescent.cubicClosedPointSerreTensorStalk_pullbackTensorMap_isIso_of_generators
  intro x
  have hx : f x ∈ (⨆ j : Fin 4, p3StandardOpen (K := K) j) := by
    rw [p3StandardOpen_iSup K]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨p3StandardOpen (K := K) j,
    actualAmbientPositiveChartBasisInvHom (K := K) j m, hj,
    actualAmbientPositiveChartBasisInvHom_isIso (K := K) j m⟩

/-- Constructed isomorphism on the actual pullback tensor map itself. -/
def actualAmbientPositiveTwistPullbackTensorIso
    {X : Scheme.{u}} (f : X ⟶ Proj PS) (M : (Proj PS).Modules) (m : ℕ) :
    (Scheme.Modules.pullback f).obj
        (PfaffianDescent.schemeModuleTensor M (positiveSheafOfModules PS m)) ≅
      PfaffianDescent.schemeModuleTensor ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj (positiveSheafOfModules PS m)) := by
  letI := actualAmbientPositiveTwist_pullbackTensorMap_isIso (K := K) f M m
  exact asIso (PfaffianDescent.cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
    (positiveSheafOfModules PS m))

end PfaffianDescent.Coray
