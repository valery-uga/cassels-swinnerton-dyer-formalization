import PfaffianDescent.CorayOwnCoordinateCartierCut
import PfaffianDescent.CorayNativeStalkCokernelZero
import PfaffianDescent.CorayNormalizationNonzeroSignedWordStalkQuotient
import PfaffianDescent.CorayNormalizationDefectFiniteLength
import PfaffianDescent.SchemeModuleFiniteClosedSupportOriginalBaseGerms
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal

/-! SOURCE ONLY / UNCHECKED. The actual positive-coordinate multiplication
cokernel has finite ORIGINAL-K H0. Native rank-one frames, actual monicity,
finite torsion lengths and genuine original-base germs derive the result.
No DVR, Infinite, CharZero, constants=K, finite-H0 or length input. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- All twists, including zero, have actual native rank-one coordinate charts. -/
theorem actualComponent_positiveTwist_locallyRankOne
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) (m : ℕ) :
    schemeModuleLocallyRankOne (positiveSheafOfModules (grading C) m) := by
  intro x
  have hx : x ∈ (⨆ j : Fin 4, quotientCoordinateOpen C j) := by
    rw [quotientCoordinateOpen_iSup]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  let U := quotientCoordinateOpen C j
  let M := positiveSheafOfModules (grading C) m
  let O : (scheme C).Modules := SheafOfModules.unit (scheme C).ringCatSheaf
  exact ⟨U, hj, ⟨overFunctorIsoUnit_of_restrictIsoUnit U
    (quotientCoordinatePositiveTwistUnitIso_all C j m) ≪≫
      (PfaffianDescent.SheafOfModules.overFunctor_globalUnitIso U (Iso.refl O)).symm⟩⟩

/-- Literal positive multiplication by the actual coordinate class. -/
def ownPositiveCoordinateMultiplication
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) :
    positiveSheafOfModules (grading C) m ⟶ positiveSheafOfModules (grading C) (m + 1) :=
  positiveMulHomogeneous (grading C) ⟨coordinate C j, coordinate_mem C j⟩ m

/-- The actual cokernel sequence is ShortExact by original coordinate
nonvanishing at P and primality, not by an assumed Cartier exact sequence. -/
theorem ownPositiveCoordinateMultiplication_cokernelSequence_shortExact
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime) (P : scheme C) (j : Fin 4)
    (hj : coordinate C j ∉ P.asHomogeneousIdeal) (m : ℕ) :
    (ShortComplex.cokernelSequence (ownPositiveCoordinateMultiplication C j m)).ShortExact := by
  letI : C.toIdeal.IsPrime := hprime
  letI : IsDomain (CoordinateRing C) :=
    (Ideal.Quotient.isDomain_iff_prime C.toIdeal).mpr hprime
  letI : Mono (ownPositiveCoordinateMultiplication C j m) :=
    positiveMulHomogeneous_mono (grading C) ⟨coordinate C j, coordinate_mem C j⟩
      (coordinate_notMem_at_point_ne_zero_and_notMem_component C P j hj).1 m
  refine ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _) ?_ ?_
  · change Mono (ownPositiveCoordinateMultiplication C j m)
    infer_instance
  · infer_instance

/-- Native frames turn the SAME monic morphism between rank-one modules
into a monic R-to-R map. Its actual nonzero value on 1 kills the actual range
quotient, so genuine torsion gives finite length even at singular points. -/
theorem rankOneMono_actualStalkCokernel_isFiniteLength
    {X : Scheme.{u}} (L M : X.Modules)
    (hL : schemeModuleLocallyRankOne L) (hM : schemeModuleLocallyRankOne M)
    (f : L ⟶ M) [Mono f] (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsNoetherianRing (X.presheaf.stalk x)]
    [Ring.DimensionLEOne (X.presheaf.stalk x)] :
    IsFiniteLength (X.presheaf.stalk x)
      ((schemeModuleStalkModuleFunctor X x).obj (cokernel f)) := by
  let R := X.presheaf.stalk x
  let F := schemeModuleStalkModuleFunctor X x
  obtain ⟨eL⟩ := schemeModuleLocallyRankOne_nativeStalkFrame L hL x
  obtain ⟨eM⟩ := schemeModuleLocallyRankOne_nativeStalkFrame M hM x
  let g : ModuleCat.of R R ⟶ ModuleCat.of R R := eL.inv ≫ F.map f ≫ eM.hom
  letI : Mono (F.map f) := schemeModuleStalkModuleFunctor_map_mono f x
  letI : Mono g := by dsimp only [g]; infer_instance
  let V : Submodule R R := LinearMap.range g.hom
  let a : R := g.hom 1
  have ha : a ≠ 0 := by
    intro h
    exact one_ne_zero ((ModuleCat.mono_iff_injective g).mp inferInstance
      (h.trans g.hom.map_zero.symm))
  have haV : a ∈ V := ⟨1, rfl⟩
  have ht : Module.IsTorsion R (R ⧸ V) := by
    intro z
    obtain ⟨r, rfl⟩ := V.mkQ_surjective z
    refine ⟨⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩, ?_⟩
    change a • V.mkQ r = 0
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero V).mpr
    simpa only [smul_eq_mul, mul_comm] using V.smul_mem r haV
  have hlength : IsFiniteLength R (R ⧸ V) :=
    finiteTorsion_isFiniteLength_of_dimensionLEOne R (R ⧸ V) ht
  have hsquare : F.map f ≫ eM.hom = eL.hom ≫ g := by
    simp only [g, Category.assoc, Iso.hom_inv_id_assoc]
  let E : F.obj (cokernel f) ≅ ModuleCat.of R (R ⧸ V) :=
    PreservesCokernel.iso F f ≪≫ cokernel.mapIso (F.map f) g eL eM hsquare ≪≫
      ModuleCat.cokernelIsoRangeQuotient g
  exact E.toLinearEquiv.symm.isFiniteLength hlength

/-- Outside the actual coordinate zero locus the SAME positive cokernel
stalk is zero, by the actual positive multiplication stalk map. -/
theorem ownPositiveCoordinateCokernel_support_subset_coordinateZero
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) :
    schemeModuleStalkSupport (cokernel (ownPositiveCoordinateMultiplication C j m)) ⊆
      {x : scheme C | coordinate C j ∈ x.asHomogeneousIdeal} := by
  intro x hx
  by_contra h
  let f := ownPositiveCoordinateMultiplication C j m
  have hsub : Subsingleton ((Scheme.Modules.presheaf (X := scheme C) (cokernel f)).stalk x) :=
    nativeSchemeModule_cokernelStalk_subsingleton_of_bijective f x
      (positiveMulHomogeneous_stalkMap_bijective_of_mem_primeCompl
        (grading C) ⟨coordinate C j, coordinate_mem C j⟩ m x h
        ⟨coordinate C j, coordinate_mem C j⟩ h)
  exact (not_nontrivial_iff_subsingleton.mpr hsub) hx

/-- Original selected p/q data derive finite closed coordinate-zero support,
native finite lengths of the ACTUAL positive multiplication cokernel and
finite ORIGINAL-K top sections by original germs. No H0-finiteness input. -/
theorem selectedProjectivePrimeComponent_ownPositiveCoordinateCokernel_topSections_finite
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) (j : Fin 4)
    (hj : coordinate C j ∉ P.asHomogeneousIdeal) (m : ℕ) :
    Module.Finite K (SchemeModuleOpenSectionsOver (toBase C)
      (cokernel (ownPositiveCoordinateMultiplication C j m)) ⊤) := by
  classical
  let X := scheme C
  letI : IsIntegral X := homogeneousPrime_projectiveScheme_isIntegral C hprime P
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (toBase C)
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (toBase C)
  letI : IsNoetherian X := ⟨⟩
  let Z : Set X := {x | coordinate C j ∈ x.asHomogeneousIdeal}
  let U := Proj.basicOpen (grading C) (coordinate C j)
  have hZeq : Z = U.1ᶜ := by
    ext x
    change coordinate C j ∈ x.asHomogeneousIdeal ↔ ¬ coordinate C j ∉ x.asHomogeneousIdeal
    exact not_not.symm
  have hZclosed : IsClosed Z := by
    rw [hZeq]
    exact U.isOpen.isClosed_compl
  have hgeneric : genericPoint X ∉ Z := by
    exact (genericPoint_specializes P).mem_open U.isOpen hj
  have hdim (x : X) : Ring.DimensionLEOne (X.presheaf.stalk x) := by
    letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := Ring.krullDimLE_iff.mpr
      (selectedProjectiveComponent_original_stalk_ringKrullDim_le_one
        p q hp hp0 n hq hnot C hIC x)
    exact ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩
  obtain ⟨hfinite, hclosed⟩ := integralCurve_closed_avoiding_generic_finite_and_closedPoints
    X hdim Z hZclosed hgeneric
  let f := ownPositiveCoordinateMultiplication C j m
  let Q := cokernel f
  letI : Mono f :=
    (ownPositiveCoordinateMultiplication_cokernelSequence_shortExact C hprime P j hj m).mono_f
  have hlength (x : Z) : IsFiniteLength (X.presheaf.stalk x.1)
      ((schemeModuleStalkModuleFunctor X x.1).obj Q) := by
    letI : IsDomain ((Proj (grading C)).presheaf.stalk x.1) :=
      inferInstanceAs (IsDomain (X.presheaf.stalk x.1))
    letI : IsNoetherianRing ((Proj (grading C)).presheaf.stalk x.1) :=
      inferInstanceAs (IsNoetherianRing (X.presheaf.stalk x.1))
    letI : Ring.DimensionLEOne ((Proj (grading C)).presheaf.stalk x.1) := hdim x.1
    exact rankOneMono_actualStalkCokernel_isFiniteLength _ _
      (actualComponent_positiveTwist_locallyRankOne C m)
      (actualComponent_positiveTwist_locallyRankOne C (m + 1)) f x.1
  exact (schemeModuleOriginalBaseTopSections_finite_and_weighted_finrank
    (toBase C) Q Z hfinite hclosed
      (ownPositiveCoordinateCokernel_support_subset_coordinateZero C j m) hlength).1

end PfaffianDescent.Coray
