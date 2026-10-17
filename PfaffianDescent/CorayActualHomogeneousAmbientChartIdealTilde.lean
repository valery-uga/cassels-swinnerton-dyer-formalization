import PfaffianDescent.CorayActualDegreeZeroChartPresentation
import PfaffianDescent.SurjectiveAffineIdealIsoInclusion
import PfaffianDescent.ClosedImmersionIdealPullbackMonoOnOpen

/-! The OWN ambient degree-zero Proj chart of the actual homogeneous quotient
immersion. The affine ideal comparison is derived from the actual cartesian
square and canonical ideal base change; nilpotents are retained.
SOURCE ONLY UNVERIFIED; root owns all compiler and audit checks. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open PfaffianDescent.IdealSheafDataModule
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Surjectivity for the actual ambient chart map of any homogeneous ideal,
not just a principal hypersurface. Homogeneous quotient representatives are
lifted at exactly their original degree. -/
theorem actualAmbientHomogeneousQuotientChartMap_surjective
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    Function.Surjective (PfaffianDescent.quotientAmbientChartMap I j) := by
  intro y
  obtain ⟨n, q, hq, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading I) (coordinate_mem I j) y
  obtain ⟨r, hr, hrq⟩ := hq
  let hx : X j ∈ PS 1 := isHomogeneous_X K j
  refine ⟨HomogeneousLocalization.Away.mk PS hx n r hr, ?_⟩
  change (AllCharacteristics.gradedAwayMapOfEq (quotientGradedRingHom I)
    (X j) (coordinate I j) (quotientGradedRingHom_coordinate I j))
      (HomogeneousLocalization.Away.mk PS hx n r hr) = _
  rw [AllCharacteristics.gradedAwayMapOfEq_mk (quotientGradedRingHom I)
    (X j) (coordinate I j) (quotientGradedRingHom_coordinate I j)
    hx (coordinate_mem I j) n r hr]
  change HomogeneousLocalization.Away.mk (grading I) (coordinate_mem I j) n
    (Ideal.Quotient.mk I.toIdeal r) _ =
    HomogeneousLocalization.Away.mk (grading I) (coordinate_mem I j) n q _
  congr 1

/-- Equality of open ranges can be transported through inverse image at
arbitrary schemes, before any Proj chart or homogeneous proof is inserted. -/
private theorem nativeOpensPreimageRangeEquality003
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U U' : Y.Opens) (V V' : X.Opens)
    (hU : U = U') (hbasic : f ⁻¹ᵁ U' = V') (hV : V = V') :
    f ⁻¹ᵁ U = V :=
  (congrArg (fun W : Y.Opens => f ⁻¹ᵁ W) hU).trans (hbasic.trans hV.symm)

/-- The ORIGINAL ambient chart range, with the homogeneity proof explicitly
at membership type PS1. No tactic rewrites an ill-typed implicit-transparency term. -/
private theorem actualAmbientOriginalChart_opensRange003 (j : Fin 4) :
    (Proj.awayι PS (X j)
      (show X j ∈ PS 1 from isHomogeneous_X K j) (Nat.zero_lt_succ 0)).opensRange =
      Proj.basicOpen PS (X j) :=
  Proj.opensRange_awayι PS (X j)
    (show X j ∈ PS 1 from isHomogeneous_X K j) (Nat.zero_lt_succ 0)

/-- The SAME quotient coordinate chart range, captured separately before
its range equality is used inside an original ambient preimage expression. -/
private theorem actualQuotientCoordinateChart_opensRange003
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    (chartι I j).opensRange = Proj.basicOpen (grading I) (coordinate I j) :=
  Proj.opensRange_awayι (grading I) (coordinate I j)
    (coordinate_mem I j) (Nat.zero_lt_succ 0)

/-- The actual homogeneous quotient's basic-open preimage follows from
native Proj.map preimage and the original coordinate equality by congrArg. -/
private def actualHomogeneousQuotient_basicOpenPreimage003
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  (Proj.map_preimage_basicOpen (f := quotientGradedRingHom I)
    (hf := irrelevant_le_map_quotientGradedRingHom I) (X j)).trans
    (congrArg (Proj.basicOpen (grading I)) (quotientGradedRingHom_coordinate I j))

/-- The actual coordinate chart square over the original ambient Proj,
with no substitution by a quotient of the ambient ring by zero. -/
theorem isPullback_actualAmbientHomogeneousQuotientChart
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (PfaffianDescent.quotientAmbientChartMap I j)))
      (chartι I j)
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))
      (quotientProjMap I) := by
  letI : IsOpenImmersion
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)) :=
    Proj.instIsOpenImmersionAwayι PS (X j)
      (isHomogeneous_X K j) (by decide : 0 < 1)
  apply IsOpenImmersion.isPullback
  · exact PfaffianDescent.chartι_comp_quotientProjMap I j
  · exact nativeOpensPreimageRangeEquality003 (quotientProjMap I)
      (Proj.awayι PS (X j)
        (show X j ∈ PS 1 from isHomogeneous_X K j) (Nat.zero_lt_succ 0)).opensRange
      (Proj.basicOpen PS (X j)) (chartι I j).opensRange
      (Proj.basicOpen (grading I) (coordinate I j))
      (actualAmbientOriginalChart_opensRange003 j)
      (actualHomogeneousQuotient_basicOpenPreimage003 I j)
      (actualQuotientCoordinateChart_opensRange003 I j)

/-- The affine chart closed immersion has exactly the restriction of the
original homogeneous quotient's ideal-sheaf data, including nilpotents. -/
theorem actualAmbientHomogeneousQuotientChart_kernel
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    (Spec.map (CommRingCat.ofHom (PfaffianDescent.quotientAmbientChartMap I j))).ker =
      (pullback.fst
        (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))
        (quotientProjMap I)).ker := by
  let H := isPullback_actualAmbientHomogeneousQuotientChart I j
  rw [← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

/-- Canonical native chart comparison of the actual homogeneous ideal
module with tilde of the literal quotient-chart ring kernel. No ideal
identification or pullback comparison is supplied as a premise. -/
def actualAmbientHomogeneousQuotientChartIdealTildeIso
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    (tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).obj
        (ModuleCat.of (HomogeneousLocalization.Away PS (X j))
          (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j))) ≅
      (Scheme.Modules.pullback
        (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).obj
          (closedImmersionModule (quotientProjMap I)) := by
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let i := quotientProjMap I
  let rho := PfaffianDescent.quotientAmbientChartMap I j
  let a := PfaffianDescent.surjectiveAffineActualIdealTildeIso rho
    (actualAmbientHomogeneousQuotientChartMap_surjective I j)
  let b := PfaffianDescent.idealModuleTransport
    (actualAmbientHomogeneousQuotientChart_kernel I j)
  letI : IsOpenImmersion q :=
    Proj.instIsOpenImmersionAwayι PS (X j)
      (isHomogeneous_X K j) (by decide : 0 < 1)
  letI : Flat q := inferInstance
  letI : IsIso (PfaffianDescent.closedImmersionIdealBaseChangeHom q i) :=
    PfaffianDescent.isIso_flatClosedImmersionIdealBaseChangeHom_general q i
  exact a ≪≫ b ≪≫ (asIso (PfaffianDescent.closedImmersionIdealBaseChangeHom q i)).symm

private lemma idealChartIso_inclusion_chain
    {C : Type*} [Category C] {A B D E U : C}
    (a : A ≅ B) (b : B ≅ D) (c : E ≅ D)
    (vB : B ⟶ U) (vD : D ⟶ U) (vE : E ⟶ U) (w : A ⟶ U)
    (ha : a.hom ≫ vB = w) (hb : b.hom ≫ vD = vB)
    (hc : c.hom ≫ vD = vE) :
    (a ≪≫ b ≪≫ c.symm).hom ≫ vE = w := by
  change (a.hom ≫ b.hom ≫ c.inv) ≫ vE = w
  rw [← hc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hb, ha]

/-- The asIso Hom is the SAME original morphism; convert the law before
any native ideal images or projective localization dictionaries are inserted. -/
private theorem nativeAsIsoHomInclusion004
    {C : Type*} [Category C] {E D U : C}
    (f : E ⟶ D) [IsIso f] (v : D ⟶ U) (w : E ⟶ U)
    (h : f ≫ v = w) : (asIso f).hom ≫ v = w := h

/-- Transport a diagram using a WHOLE Iso equality at fixed category objects. -/
private theorem nativeIsoHomPostcompositionTransport004
    {C : Type*} [Category C] {A E U : C}
    (a a' : A ≅ E) (hmap : a = a') (v : E ⟶ U) (w : A ⟶ U)
    (h : a'.hom ≫ v = w) : a.hom ≫ v = w := by
  cases hmap
  exact h

/-- Capture the first ACTUAL affine inclusion law independently of the chain. -/
private def actualAmbientIdealChartFirstLaw004
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  PfaffianDescent.surjectiveAffineActualIdealTildeIso_hom_toUnit
    (R := HomogeneousLocalization.Away PS (X j)) (L := ChartRing I j)
    (PfaffianDescent.quotientAmbientChartMap I j)
    (actualAmbientHomogeneousQuotientChartMap_surjective I j)

/-- Capture the original kernel-equality ideal transport inclusion law alone. -/
private def actualAmbientIdealChartTransportLaw004
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  PfaffianDescent.idealModuleTransport_hom_toUnit
    (actualAmbientHomogeneousQuotientChart_kernel I j)

/-- Capture the CANONICAL ideal base-change morphism law, before asIso projection. -/
private def actualAmbientIdealChartBaseChangeLaw004
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  PfaffianDescent.closedImmersionIdealBaseChangeHom_toUnit
    (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))
    (quotientProjMap I)

/-- The original open chart proves the original ideal base-change map isIso. -/
private theorem actualAmbientIdealChartBaseChange_isIso004
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    IsIso (PfaffianDescent.closedImmersionIdealBaseChangeHom
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))
      (quotientProjMap I)) := by
  letI : IsOpenImmersion
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)) :=
    Proj.instIsOpenImmersionAwayι PS (X j)
      (isHomogeneous_X K j) (Nat.zero_lt_succ 0)
  letI : Flat
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)) := inferInstance
  exact PfaffianDescent.isIso_flatClosedImmersionIdealBaseChangeHom_general
    (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))
    (quotientProjMap I)

/-- Specialize the generic asIso Hom law at EXPLICIT native object parameters;
the actual canonical map and its own inclusion law remain unchanged. -/
private def actualAmbientIdealChartAsIsoLaw004
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  @nativeAsIsoHomInclusion004
    (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules (inferInstance : Category (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules)
    ((Scheme.Modules.pullback (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))).obj (closedImmersionModule (quotientProjMap I))) (closedImmersionModule (pullback.fst (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)) (quotientProjMap I))) (SheafOfModules.unit (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf)
    (PfaffianDescent.closedImmersionIdealBaseChangeHom (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)) (quotientProjMap I))
    (actualAmbientIdealChartBaseChange_isIso004 I j)
    (closedImmersionModuleToUnit (pullback.fst (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)) (quotientProjMap I)))
    ((Scheme.Modules.pullback (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))).map (closedImmersionModuleToUnit (quotientProjMap I)) ≫ BundleSectionZeroLocus.pullbackUnitComparison (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))) (actualAmbientIdealChartBaseChangeLaw004 I j)

/-- The EXACT passed constructor, named as a separate value before its law. -/
private def actualAmbientIdealChartOriginalChainValue004
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    (tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).obj
        (ModuleCat.of (HomogeneousLocalization.Away PS (X j))
          (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j))) ≅
      (Scheme.Modules.pullback
        (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).obj
          (closedImmersionModule (quotientProjMap I)) := by
  let q := Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let i := quotientProjMap I
  let rho := PfaffianDescent.quotientAmbientChartMap I j
  let a := PfaffianDescent.surjectiveAffineActualIdealTildeIso rho
    (actualAmbientHomogeneousQuotientChartMap_surjective I j)
  let b := PfaffianDescent.idealModuleTransport
    (actualAmbientHomogeneousQuotientChart_kernel I j)
  letI : IsOpenImmersion q :=
    Proj.instIsOpenImmersionAwayι PS (X j)
      (isHomogeneous_X K j) (by decide : 0 < 1)
  letI : Flat q := inferInstance
  letI : IsIso (PfaffianDescent.closedImmersionIdealBaseChangeHom q i) :=
    PfaffianDescent.isIso_flatClosedImmersionIdealBaseChangeHom_general q i
  exact a ≪≫ b ≪≫ (asIso (PfaffianDescent.closedImmersionIdealBaseChangeHom q i)).symm

/-- Whole-Iso identity for the original public value and its literal
constructor copy; isolates map unfolding from every diagram proof. -/
private theorem actualAmbientIdealChartIso_originalChain004
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    actualAmbientHomogeneousQuotientChartIdealTildeIso I j =
      actualAmbientIdealChartOriginalChainValue004 I j := rfl

/-- The SAME original base-change asIso, with its native objects and the
already proved isIso dictionary fixed before any composite law is elaborated. -/
private def actualAmbientIdealChartOriginalAsIsoValue006
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  @asIso (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules (inferInstance : Category (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules)
    ((Scheme.Modules.pullback (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))).obj (closedImmersionModule (quotientProjMap I))) (closedImmersionModule (pullback.fst (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)) (quotientProjMap I)))
    (PfaffianDescent.closedImmersionIdealBaseChangeHom (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)) (quotientProjMap I))
    (actualAmbientIdealChartBaseChange_isIso004 I j)

/-- A separately typed value for exactly the ORIGINAL three-arrow chain.
There is no map replacement; the whole-Iso identity below is mandatory. -/
private def actualAmbientIdealChartExplicitOriginalChain006
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    ((tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).obj (ModuleCat.of (HomogeneousLocalization.Away PS (X j)) (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))) ≅ ((Scheme.Modules.pullback (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))).obj (closedImmersionModule (quotientProjMap I))) :=
  (PfaffianDescent.surjectiveAffineActualIdealTildeIso (PfaffianDescent.quotientAmbientChartMap I j) (actualAmbientHomogeneousQuotientChartMap_surjective I j)) ≪≫ (PfaffianDescent.idealModuleTransport (actualAmbientHomogeneousQuotientChart_kernel I j)) ≪≫ (actualAmbientIdealChartOriginalAsIsoValue006 I j).symm

/-- Fix the original constructor conversion independently of every law. -/
private theorem actualAmbientIdealChartOriginalChain_explicit006
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    actualAmbientIdealChartOriginalChainValue004 I j =
      actualAmbientIdealChartExplicitOriginalChain006 I j := rfl

/-- Fix only native category and all five actual objects; no map or law supplied. -/
private def actualAmbientIdealChartFactoryObjects007
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  @idealChartIso_inclusion_chain (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules (inferInstance : Category (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules)
    ((tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).obj (ModuleCat.of (HomogeneousLocalization.Away PS (X j)) (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))) (closedImmersionModule (Spec.map (CommRingCat.ofHom (PfaffianDescent.quotientAmbientChartMap I j)))) (closedImmersionModule (pullback.fst (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)) (quotientProjMap I))) ((Scheme.Modules.pullback (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))).obj (closedImmersionModule (quotientProjMap I))) (SheafOfModules.unit (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf)

/-- Supply only the ORIGINAL affine ideal Iso. -/
private def actualAmbientIdealChartFactoryFirstIso007
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientIdealChartFactoryObjects007 (K := K) I j
    (PfaffianDescent.surjectiveAffineActualIdealTildeIso (PfaffianDescent.quotientAmbientChartMap I j) (actualAmbientHomogeneousQuotientChartMap_surjective I j))

/-- Supply the ORIGINAL kernel-equality transport Iso; no laws yet. -/
private def actualAmbientIdealChartFactoryTransportIso007
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientIdealChartFactoryFirstIso007 (K := K) I j
    (PfaffianDescent.idealModuleTransport (actualAmbientHomogeneousQuotientChart_kernel I j))

/-- Supply the passed ORIGINAL native base-change asIso value. -/
private def actualAmbientIdealChartFactoryBaseChangeIso007
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientIdealChartFactoryTransportIso007 (K := K) I j
    (actualAmbientIdealChartOriginalAsIsoValue006 I j)

/-- Fix all ORIGINAL inclusions and the canonical affine unit composite; laws remain curried. -/
private def actualAmbientIdealChartFactoryInclusions007
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientIdealChartFactoryBaseChangeIso007 (K := K) I j
    (closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom (PfaffianDescent.quotientAmbientChartMap I j)))) (closedImmersionModuleToUnit (pullback.fst (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)) (quotientProjMap I))) ((Scheme.Modules.pullback (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))).map (closedImmersionModuleToUnit (quotientProjMap I)) ≫ BundleSectionZeroLocus.pullbackUnitComparison (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))) ((tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).map (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫ (PfaffianDescent.affineGlobalSectionsUnitTildeIso (A := HomogeneousLocalization.Away PS (X j))).hom)

/-- Convert a VARIABLE raw sheaf Iso-inclusion equation to native
Scheme.Modules composition before any affine kernel/image is substituted. -/
private theorem nativeRawIsoInclusionToOwn008
    {X : Scheme.{u}} {M N U : SheafOfModules X.ringCatSheaf}
    (a : M ≅ N) (v : N ⟶ U) (w : M ⟶ U) (h : a.hom ≫ v = w) :
    @CategoryStruct.comp X.Modules
      (inferInstance : Category X.Modules).toCategoryStruct M N U
      (@Iso.hom X.Modules (inferInstance : Category X.Modules) M N a) v = w := h

/-- Build the ORIGINAL affine law in the native category at arbitrary
CommRing R/L first; rho and its actual surjectivity proof are the only inputs. -/
private def nativeSurjectiveAffineIsoInclusion008
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho) :=
  @nativeRawIsoInclusionToOwn008 (Spec (CommRingCat.of R))
    ((tilde.functor (CommRingCat.of R)).obj
      (ModuleCat.of R (RingHom.ker rho)))
    (closedImmersionModule (Spec.map (CommRingCat.ofHom rho)))
    (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf)
    (PfaffianDescent.surjectiveAffineActualIdealTildeIso rho hrho)
    (closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom rho)))
    ((tilde.functor (CommRingCat.of R)).map
      (ModuleCat.ofHom (RingHom.ker rho).subtype) ≫
      (PfaffianDescent.affineGlobalSectionsUnitTildeIso (A := R)).hom)
    (PfaffianDescent.surjectiveAffineActualIdealTildeIso_hom_toUnit rho hrho)

/-- Specialize the already native affine inclusion proof, with BOTH
coefficient rings explicit, separately from the chart-chain application. -/
private def actualAmbientIdealChartNativeFirstLaw008
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  nativeSurjectiveAffineIsoInclusion008
    (R := HomogeneousLocalization.Away PS (X j)) (L := ChartRing I j)
    (PfaffianDescent.quotientAmbientChartMap I j) (actualAmbientHomogeneousQuotientChartMap_surjective I j)

/-- The exact first-law proposition expected by the native chain factory,
with its original Iso/object arguments made explicit. This is not a premise. -/
private def actualAmbientIdealChartFirstLawPredicate008
    (I : HomogeneousIdeal PS) (j : Fin 4) : Prop :=
  @CategoryStruct.comp (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules
    (inferInstance : Category (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules).toCategoryStruct
    ((tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).obj (ModuleCat.of (HomogeneousLocalization.Away PS (X j)) (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))) (closedImmersionModule (Spec.map (CommRingCat.ofHom (PfaffianDescent.quotientAmbientChartMap I j)))) (SheafOfModules.unit (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf)
    (@Iso.hom (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules (inferInstance : Category (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules) ((tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).obj (ModuleCat.of (HomogeneousLocalization.Away PS (X j)) (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))) (closedImmersionModule (Spec.map (CommRingCat.ofHom (PfaffianDescent.quotientAmbientChartMap I j)))) (PfaffianDescent.surjectiveAffineActualIdealTildeIso (PfaffianDescent.quotientAmbientChartMap I j) (actualAmbientHomogeneousQuotientChartMap_surjective I j))) (closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom (PfaffianDescent.quotientAmbientChartMap I j)))) = ((tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).map (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫ (PfaffianDescent.affineGlobalSectionsUnitTildeIso (A := HomogeneousLocalization.Away PS (X j))).hom)

/-- The ORIGINAL raw affine equation at EXACTLY the already checked
factory objects and original maps. This tests the source predicate independently
of native Scheme.Modules composition or the curried three-arrow law. -/
private def actualAmbientIdealChartExactRawFirstPredicate009
    (I : HomogeneousIdeal PS) (j : Fin 4) : Prop :=
  @CategoryStruct.comp (SheafOfModules (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf)
    (inferInstance : Category (SheafOfModules (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf)).toCategoryStruct
    ((tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).obj (ModuleCat.of (HomogeneousLocalization.Away PS (X j)) (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))) (closedImmersionModule (Spec.map (CommRingCat.ofHom (PfaffianDescent.quotientAmbientChartMap I j)))) (SheafOfModules.unit (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf)
    (@Iso.hom (SheafOfModules (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf) (inferInstance : Category (SheafOfModules (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf)) ((tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).obj (ModuleCat.of (HomogeneousLocalization.Away PS (X j)) (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)))) (closedImmersionModule (Spec.map (CommRingCat.ofHom (PfaffianDescent.quotientAmbientChartMap I j)))) (PfaffianDescent.surjectiveAffineActualIdealTildeIso (PfaffianDescent.quotientAmbientChartMap I j) (actualAmbientHomogeneousQuotientChartMap_surjective I j))) (closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom (PfaffianDescent.quotientAmbientChartMap I j)))) = ((tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).map (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫ (PfaffianDescent.affineGlobalSectionsUnitTildeIso (A := HomogeneousLocalization.Away PS (X j))).hom)

/-- Consume the first law BEFORE fixing independently elaborated objects.
Its category, source/target/unit, original affine Iso, inclusion and RHS are
inferred from that accepted equation. Remaining objects/maps follow afterwards. -/
private def nativeChartDataFromFirstLaw010
    {C : Type*} [Category C] {A B U : C}
    {a : A ≅ B} {vB : B ⟶ U} {w : A ⟶ U}
    (ha : a.hom ≫ vB = w) (D E : C) (b : B ≅ D) (c : E ≅ D)
    (vD : D ⟶ U) (vE : E ⟶ U) :
    {t : A ≅ E // (b.hom ≫ vD = vB) → (c.hom ≫ vD = vE) →
      t.hom ≫ vE = w} :=
  ⟨a ≪≫ b ≪≫ c.symm, fun hb hc =>
    idealChartIso_inclusion_chain a b c vB vD vE w ha hb hc⟩

/-- The proof-first factory stores exactly the ORIGINAL right-associated
Iso chain. This value law is established before any scheme/ring substitution. -/
private theorem nativeChartDataFromFirstLaw_value010
    {C : Type*} [Category C] {A B U : C}
    {a : A ≅ B} {vB : B ⟶ U} {w : A ⟶ U}
    (ha : a.hom ≫ vB = w) (D E : C) (b : B ≅ D) (c : E ≅ D)
    (vD : D ⟶ U) (vE : E ⟶ U) :
    (nativeChartDataFromFirstLaw010 ha D E b c vD vE).val =
      a ≪≫ b ≪≫ c.symm := rfl

/-- Whole-Iso transport with object/map parameters inferred from the
already proved diagram first. No new concrete equality predicate is formed. -/
private theorem nativeIsoLawReplaceValue010
    {C : Type*} [Category C] {A E U : C}
    {a a' : A ≅ E} {v : E ⟶ U} {w : A ⟶ U}
    (h : a'.hom ≫ v = w) (he : a = a') : a.hom ≫ v = w := by
  cases he
  exact h

/-- Fix the native tilde target category, its original affine Iso, closed/unit
objects, inclusions, and FIRST law while the coefficient ring is still abstract.
Mathlib tilde.functor re-bundles R : CommRingCat in its target Scheme; the
raw closed/unit objects are normalized HERE, before inserting an actual Away. -/
private def nativeSurjectiveAffineFirstChartData015
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho) :=
  nativeChartDataFromFirstLaw010
    (PfaffianDescent.surjectiveAffineActualIdealTildeIso_hom_toUnit
      (R := R) (L := L) rho hrho)

/-- Capture objects and first affine map/inclusion/RHS FROM the passed original law; no manual category/object choices. -/
private def actualAmbientChartFirstLawCapture010
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  @nativeSurjectiveAffineFirstChartData015
    (HomogeneousLocalization.Away PS (X j)) (ChartRing I j)
    (inferInstance : CommRing (HomogeneousLocalization.Away PS (X j)))
    (inferInstance : CommRing (ChartRing I j))
    (PfaffianDescent.quotientAmbientChartMap I j)
    (actualAmbientHomogeneousQuotientChartMap_surjective I j)

/-- Only now supply the actual other two objects; the first-law objects remain inferred from that proof. -/
private def actualAmbientChartOtherObjects010
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientChartFirstLawCapture010 (K := K) I j
    (closedImmersionModule (pullback.fst (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)) (quotientProjMap I))) ((Scheme.Modules.pullback (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))).obj (closedImmersionModule (quotientProjMap I)))

/-- Insert the ORIGINAL ideal equality-transport Iso while the coefficient
rings remain abstract. This performs the raw/native Iso representation check
before substituting the actual projective localization or pullback kernel. -/
private def nativeSurjectiveAffineTransportChartSlot017
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho)
    (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (h : (Spec.map (CommRingCat.ofHom rho)).ker = J)
    (E : (Spec (CommRingCat.of (CommRingCat.of R))).Modules) :=
  nativeSurjectiveAffineFirstChartData015 (R := R) (L := L) rho hrho
    (idealModule J) E (PfaffianDescent.idealModuleTransport h)

/-- WHOLE value identity at abstract rings: the slot stores exactly the
ORIGINAL first Iso, ideal equality-transport Iso and final inverse. -/
private theorem nativeSurjectiveAffineTransportChartSlot_value017
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho)
    (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (h : (Spec.map (CommRingCat.ofHom rho)).ker = J)
    (E : (Spec (CommRingCat.of (CommRingCat.of R))).Modules)
    (c : E ≅ idealModule J)
    (vD : idealModule J ⟶ SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf)
    (vE : E ⟶ SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) :
    (nativeSurjectiveAffineTransportChartSlot017 rho hrho J h E c vD vE).val =
      PfaffianDescent.surjectiveAffineActualIdealTildeIso rho hrho ≪≫
        PfaffianDescent.idealModuleTransport h ≪≫ c.symm := rfl

/-- Ordinary native object carrier conversion at an ABSTRACT ring. The
object is returned unchanged; this fixes the same Spec rebundling used by
the already-proved transport slot BEFORE actual Away/pullback substitution. -/
private def nativeSpecModuleRebundleCarrier018
    {R : Type u} [CommRing R]
    (M : (Spec (CommRingCat.of R)).Modules) :
    (Spec (CommRingCat.of (CommRingCat.of R))).Modules := M

/-- WHOLE object identity: the native carrier adapter creates no new
module, transport arrow, frame, action or mathematical data. -/
private theorem nativeSpecModuleRebundleCarrier_value018
    {R : Type u} [CommRing R]
    (M : (Spec (CommRingCat.of R)).Modules) :
    nativeSpecModuleRebundleCarrier018 M = M := rfl

/-- The ORIGINAL last pullback module, typed independently of every
transport-slot application; it is exactly the original module value. -/
private def actualAmbientChartOriginalOtherObject018
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules :=
  ((Scheme.Modules.pullback (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))).obj (closedImmersionModule (quotientProjMap I)))

/-- Supply the SAME original module to the abstract ring carrier adapter;
its returned category is precisely the original transport slot's category. -/
private def actualAmbientChartSlotOtherObject018
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  @nativeSpecModuleRebundleCarrier018 (HomogeneousLocalization.Away PS (X j))
    (inferInstance : CommRing (HomogeneousLocalization.Away PS (X j)))
    (actualAmbientChartOriginalOtherObject018 (K := K) I j)

/-- Supply ONLY the ORIGINAL underlying source ring TYPE. Neither the
target ring type nor either CommRing dictionary has been substituted.
All unsupplied type/dictionary arguments remain EXPLICIT via @; this is
only an ordinary partial application of the passed original slot. -/
private def actualAmbientChartTransportRFactory019
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  @nativeSurjectiveAffineTransportChartSlot017.{u}
    (HomogeneousLocalization.Away PS (X j))

/-- Supply ONLY the ORIGINAL target ring TYPE, after the original R.
Both ring dictionaries are still unsupplied at this boundary.
All unsupplied type/dictionary arguments remain EXPLICIT via @; this is
only an ordinary partial application of the passed original slot. -/
private def actualAmbientChartTransportLFactory019
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  @actualAmbientChartTransportRFactory019 K (inferInstance : Field K) I j
    (ChartRing I j)

/-- SAME original ambient CommRingCat value already used by tilde and
Spec. This constructs no new underlying ring or operations. -/
private def actualAmbientOriginalRingBundle020 (j : Fin 4) : CommRingCat.{u} :=
  CommRingCat.of (HomogeneousLocalization.Away PS (X j))

/-- Select the exact canonical scalar dictionary FROM the original
bundled ambient ring, independently of the returned chart-factory type.
This ordinary named value has no instance/reducibility attribute. -/
private def actualAmbientOriginalCommRingRValue020 (j : Fin 4) :
    CommRing (HomogeneousLocalization.Away PS (X j)) :=
  (actualAmbientOriginalRingBundle020 (K := K) j).commRing

/-- WHOLE dictionary equality: every ring operation and proof field is
exactly the original canonical instance, not a replacement scalar action. -/
private theorem actualAmbientOriginalCommRingRValue_eq020 (j : Fin 4) :
    actualAmbientOriginalCommRingRValue020 (K := K) j =
      (inferInstance : CommRing (HomogeneousLocalization.Away PS (X j))) := rfl

/-- Supply ONLY the canonical ORIGINAL CommRing R dictionary.
The canonical target-ring dictionary remains a separate future argument.
All unsupplied type/dictionary arguments remain EXPLICIT via @; this is
only an ordinary partial application of the passed original slot. -/
private def actualAmbientChartTransportCommRingRFactory019
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  @actualAmbientChartTransportLFactory019 K (inferInstance : Field K) I j
    (actualAmbientOriginalCommRingRValue020 (K := K) j)


/-- SAME original quotient-chart CommRingCat value used by the actual
Spec map. Underlying ChartRing and all original operations are retained. -/
private def actualAmbientOriginalTargetRingBundle021
    (I : HomogeneousIdeal PS) (j : Fin 4) : CommRingCat.{u} :=
  CommRingCat.of (ChartRing I j)

/-- Select the canonical ORIGINAL target-ring scalar dictionary directly
from the SAME quotient-chart ring bundle, independently of factory return
type conversion. No instance or reducibility attribute is installed. -/
private def actualAmbientOriginalCommRingLValue021
    (I : HomogeneousIdeal PS) (j : Fin 4) : CommRing (ChartRing I j) :=
  (actualAmbientOriginalTargetRingBundle021 (K := K) I j).commRing

/-- WHOLE target-ring dictionary equality to the original canonical
instance, including every operation and proof field. -/
private theorem actualAmbientOriginalCommRingLValue_eq021
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    actualAmbientOriginalCommRingLValue021 (K := K) I j =
      (inferInstance : CommRing (ChartRing I j)) := rfl

/-- Bounded ORIGINAL transport-slot insertion018: capture ONLY the two original rings and their canonical dictionaries.
Every remaining argument is still explicit; no desired law is assumed. -/
private def actualAmbientChartTransportRingFactory018
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  @actualAmbientChartTransportCommRingRFactory019 K (inferInstance : Field K) I j
    (actualAmbientOriginalCommRingLValue021 (K := K) I j)



/-- Bounded ORIGINAL transport-slot insertion018: supply ONLY the original quotient chart ring map.
Every remaining argument is still explicit; no desired law is assumed. -/
private def actualAmbientChartTransportRhoFactory018
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientChartTransportRingFactory018 (K := K) I j
    (PfaffianDescent.quotientAmbientChartMap I j)

/-- Bounded ORIGINAL transport-slot insertion018: supply ONLY original proved chart-map surjectivity.
Every remaining argument is still explicit; no desired law is assumed. -/
private def actualAmbientChartTransportSurjectiveFactory018
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientChartTransportRhoFactory018 (K := K) I j
    (actualAmbientHomogeneousQuotientChartMap_surjective I j)

/-- SAME ORIGINAL pullback first arrow on separately stated native
Scheme carriers; no module image, transport Iso or inclusion outcome enters. -/
private def actualAmbientOriginalPullbackFirstMapValue022
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    pullback (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)) (quotientProjMap I) ⟶
      Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j))) :=
  pullback.fst (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)) (quotientProjMap I)

/-- WHOLE original Scheme.Hom equality, retaining every morphism field
and its exact original source/target; no replacement chart map is chosen. -/
private theorem actualAmbientOriginalPullbackFirstMapValue_eq022
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    actualAmbientOriginalPullbackFirstMapValue022 (K := K) I j =
      pullback.fst (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)) (quotientProjMap I) := rfl

/-- The SAME original ideal-sheaf data kernel of the original first
arrow, typed independently of the returned transport-slot diagram. All
recorded affine ideals and nilpotents are retained in this whole value. -/
private def actualAmbientOriginalPullbackIdealValue022
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).IdealSheafData :=
  (actualAmbientOriginalPullbackFirstMapValue022 (K := K) I j).ker

/-- WHOLE IdealSheafData identity with the exact original raw pullback
kernel. This is stronger than a scalar/stalk equality and asserts no new
comparison with the Spec.map kernel; that original theorem is supplied later. -/
private theorem actualAmbientOriginalPullbackIdealValue_eq022
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    actualAmbientOriginalPullbackIdealValue022 (K := K) I j =
      (pullback.fst (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)) (quotientProjMap I)).ker := rfl

/-- Bounded ORIGINAL transport-slot insertion018: supply ONLY the ideal-sheaf kernel of the original pullback first map.
Every remaining argument is still explicit; no desired law is assumed. -/
private def actualAmbientChartTransportIdealFactory018
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientChartTransportSurjectiveFactory018 (K := K) I j
    (actualAmbientOriginalPullbackIdealValue022 (K := K) I j)


/-- Bounded ORIGINAL transport-slot insertion018: supply ONLY the already proved original kernel equality.
Every remaining argument is still explicit; no desired law is assumed. -/
private def actualAmbientChartTransportEqualityFactory018
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientChartTransportIdealFactory018 (K := K) I j
    (actualAmbientHomogeneousQuotientChart_kernel I j)

/-- Supply the same ORIGINAL kernel-equality transport Iso. -/
private def actualAmbientChartTransportMap010
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientChartTransportEqualityFactory018 (K := K) I j
    (actualAmbientChartSlotOtherObject018 (K := K) I j)


/-- Supply the same passed ORIGINAL native base-change asIso. -/
private def actualAmbientChartBaseChangeMap010
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientChartTransportMap010 (K := K) I j
    (actualAmbientIdealChartOriginalAsIsoValue006 I j)

/-- Store the ORIGINAL triple value and its still-curried remaining two laws together. -/
private def actualAmbientChartProofFirstData010
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientChartBaseChangeMap010 (K := K) I j
    (closedImmersionModuleToUnit (pullback.fst (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)) (quotientProjMap I))) ((Scheme.Modules.pullback (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))).map (closedImmersionModuleToUnit (quotientProjMap I)) ≫ BundleSectionZeroLocus.pullbackUnitComparison (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)))

/-- Expose the actual ORIGINAL triple value independently of remaining laws. -/
private def actualAmbientChartProofFirstValue010
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  (actualAmbientChartProofFirstData010 (K := K) I j).val

/-- Mandatory WHOLE Iso identity with the passed literal ORIGINAL
constructor; this rules out an abstract replacement of the native chart map. -/
private theorem actualAmbientChartProofFirstValue_original010
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    actualAmbientChartProofFirstValue010 I j =
      actualAmbientIdealChartOriginalChainValue004 I j := rfl

/-- Extract the remaining law function separately from actual proof arguments. -/
private def actualAmbientChartProofFirstRemainingLaws010
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  (actualAmbientChartProofFirstData010 (K := K) I j).property

/-- Ordinary proposition VALUE selector for a nondependent two-law
function. This asserts no P, Q, T or diagram: it merely names Q→T, using
the exact already-typed function to infer P/Q/T before proof application. -/
private def nativeSecondLawResultProposition023
    {P Q T : Prop} (_f : P → Q → T) : Prop := Q → T

/-- The selected result is WHOLE exactly the original Q→T proposition;
no logical weakening or proof-bearing construction hypothesis is inserted. -/
private theorem nativeSecondLawResultProposition_eq023
    {P Q T : Prop} (f : P → Q → T) :
    nativeSecondLawResultProposition023 f = (Q → T) := rfl

/-- EXACT remaining result proposition from the already-passed ORIGINAL
native law function, without rebuilding concrete objects/maps/categories
or asserting that result. Every P/Q/T is inferred from that exact function. -/
private def actualAmbientOriginalSecondLawResultProposition023
    (I : HomogeneousIdeal PS) (j : Fin 4) : Prop :=
  nativeSecondLawResultProposition023
    (actualAmbientChartProofFirstRemainingLaws010 (K := K) I j)

/-- Native Scheme.Modules composition proved directly by equality elimination.
The canonical transport and actual ideal inclusions are unchanged. -/
private theorem nativeIdealModuleTransport_hom_toUnit030
    {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    @CategoryStruct.comp X.Modules
      (inferInstance : Category X.Modules).toCategoryStruct
      (idealModule I) (idealModule J) (SheafOfModules.unit X.ringCatSheaf)
      (PfaffianDescent.idealModuleTransport h).hom (idealModuleToUnit J) =
        idealModuleToUnit I := by
  cases h
  simp [PfaffianDescent.idealModuleTransport]
  rfl

private def nativeFirstLawDomain034 {P Q T : Prop} (_f : P → Q → T) : Prop := P

private theorem nativeCanonicalTransportConsumerLaw034
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho)
    (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (h : (Spec.map (CommRingCat.ofHom rho)).ker = J)
    (E : (Spec (CommRingCat.of (CommRingCat.of R))).Modules)
    (c : E ≅ idealModule J)
    (vE : E ⟶ SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) :
    nativeFirstLawDomain034
      (nativeSurjectiveAffineTransportChartSlot017 rho hrho J h E c (idealModuleToUnit J) vE).property := by
  cases h
  rfl


/-- Insert ORIGINAL canonical idealModuleTransport_hom_toUnit while R,
L, rho, J and h remain abstract. The SAME original Iso value is paired with
its remaining base-change-law function. No transport diagram is assumed;
vD is exactly idealModuleToUnit J and the original transport law is proved. -/
private def nativeSurjectiveAffineCanonicalTransportLawPair024
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho)
    (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (h : (Spec.map (CommRingCat.ofHom rho)).ker = J)
    (E : (Spec (CommRingCat.of (CommRingCat.of R))).Modules)
    (c : E ≅ idealModule J)
    (vE : E ⟶ SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) :=
  let data := nativeSurjectiveAffineTransportChartSlot017
    rho hrho J h E c (idealModuleToUnit J) vE
  PProd.mk data.val (data.property (nativeCanonicalTransportConsumerLaw034 rho hrho J h E c vE))

/-- WHOLE generic Iso identity: early canonical transport-law insertion
keeps EXACTLY the original a≪≫b≪≫c.symm, including all morphism fields. -/
private theorem nativeSurjectiveAffineCanonicalTransportLawPair_value024
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho)
    (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (h : (Spec.map (CommRingCat.ofHom rho)).ker = J)
    (E : (Spec (CommRingCat.of (CommRingCat.of R))).Modules)
    (c : E ≅ idealModule J)
    (vE : E ⟶ SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) :
    (nativeSurjectiveAffineCanonicalTransportLawPair024 rho hrho J h E c vE).1 =
      PfaffianDescent.surjectiveAffineActualIdealTildeIso rho hrho ≪≫
        PfaffianDescent.idealModuleTransport h ≪≫ c.symm := rfl

/-- Bounded specialization024: supply SAME independently checked R/L dictionary values.
Remaining native inputs stay explicit; no desired law/IsIso/geometry input. -/
private def actualAmbientEarlyTransportRingFactory024
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  @nativeSurjectiveAffineCanonicalTransportLawPair024
    (HomogeneousLocalization.Away PS (X j)) (ChartRing I j)
    (actualAmbientOriginalCommRingRValue020 (K := K) j)
    (actualAmbientOriginalCommRingLValue021 (K := K) I j)

/-- Bounded specialization024: supply SAME original quotient ring map.
Remaining native inputs stay explicit; no desired law/IsIso/geometry input. -/
private def actualAmbientEarlyTransportRhoFactory024
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientEarlyTransportRingFactory024 (K := K) I j
    (PfaffianDescent.quotientAmbientChartMap I j)

/-- Bounded specialization024: supply SAME proved original surjectivity.
Remaining native inputs stay explicit; no desired law/IsIso/geometry input. -/
private def actualAmbientEarlyTransportSurjectiveFactory024
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientEarlyTransportRhoFactory024 (K := K) I j
    (actualAmbientHomogeneousQuotientChartMap_surjective I j)

/-- Bounded specialization024: supply SAME checked WHOLE original pullback kernel.
Remaining native inputs stay explicit; no desired law/IsIso/geometry input. -/
private def actualAmbientEarlyTransportIdealFactory024
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientEarlyTransportSurjectiveFactory024 (K := K) I j
    (actualAmbientOriginalPullbackIdealValue022 (K := K) I j)

/-- Bounded specialization024: supply SAME original proved kernel equality.
Remaining native inputs stay explicit; no desired law/IsIso/geometry input. -/
private def actualAmbientEarlyTransportEqualityFactory024
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientEarlyTransportIdealFactory024 (K := K) I j
    (actualAmbientHomogeneousQuotientChart_kernel I j)

/-- Bounded specialization024: supply SAME checked original native pullback module.
Remaining native inputs stay explicit; no desired law/IsIso/geometry input. -/
private def actualAmbientEarlyTransportModuleFactory024
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientEarlyTransportEqualityFactory024 (K := K) I j
    (actualAmbientChartSlotOtherObject018 (K := K) I j)

/-- Bounded specialization024: supply SAME original base-change asIso with proved invertibility.
Remaining native inputs stay explicit; no desired law/IsIso/geometry input. -/
private def actualAmbientEarlyTransportBaseChangeFactory024
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientEarlyTransportModuleFactory024 (K := K) I j
    (actualAmbientIdealChartOriginalAsIsoValue006 I j)

/-- Bounded specialization024: supply SAME original pullback/unit inclusion composite.
Remaining native inputs stay explicit; no desired law/IsIso/geometry input. -/
private def actualAmbientEarlyTransportPair024
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientEarlyTransportBaseChangeFactory024 (K := K) I j
    ((Scheme.Modules.pullback (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))).map (closedImmersionModuleToUnit (quotientProjMap I)) ≫ BundleSectionZeroLocus.pullbackUnitComparison (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)))

/-- Extract the SAME original triple Iso independently of every actual
remaining proof argument. No replacement map is accepted. -/
private def actualAmbientEarlyTransportValue024
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  (actualAmbientEarlyTransportPair024 (K := K) I j).1

/-- Mandatory WHOLE actual Iso equality to the literal ORIGINAL
constructor. This must pass before using the early-law producer as bridge. -/
private theorem actualAmbientEarlyTransportValue_original024
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    actualAmbientEarlyTransportValue024 (K := K) I j =
      actualAmbientIdealChartOriginalChainValue004 I j := rfl

/-- The ORIGINAL transport law is ALREADY internally inserted at
abstract rings. Only the original base-change diagram remains conditional. -/
private def actualAmbientEarlyTransportRemainingLaw024
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  (actualAmbientEarlyTransportPair024 (K := K) I j).2

/-- Supply the independently proved ORIGINAL kernel-transport law. -/
private def actualAmbientChartProofFirstTransportLaw010
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    actualAmbientOriginalSecondLawResultProposition023 (K := K) I j := by
  intro hc
  exact nativeIsoLawReplaceValue010
    (actualAmbientEarlyTransportRemainingLaw024 (K := K) I j hc)
    ((actualAmbientChartProofFirstValue_original010 (K := K) I j).trans
      (actualAmbientEarlyTransportValue_original024 (K := K) I j).symm)



/-- Complete the actual ORIGINAL chain diagram with the already proved
original base-change asIso inclusion law; no outcome premise is supplied. -/
private def actualAmbientChartProofFirstCompleteLaw010
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  actualAmbientChartProofFirstTransportLaw010 (K := K) I j
    (actualAmbientIdealChartAsIsoLaw004 (K := K) I j)

/-- Infer the ORIGINAL literal-constructor diagram from the completed
proof-first producer and its separately checked WHOLE original Iso identity. -/
private def actualAmbientIdealChartOriginalChainInclusion004
    (I : HomogeneousIdeal PS) (j : Fin 4) :=
  nativeIsoLawReplaceValue010
    (actualAmbientChartProofFirstCompleteLaw010 (K := K) I j)
    (actualAmbientChartProofFirstValue_original010 (K := K) I j).symm


/-- The native chart comparison identifies the ACTUAL pulled-back ideal
inclusion with tilde of the literal quotient-kernel inclusion, through the
original canonical unit comparison. -/
theorem actualAmbientHomogeneousQuotientChartIdealTildeIso_hom_toUnit
    (I : HomogeneousIdeal PS) (j : Fin 4) :
    (actualAmbientHomogeneousQuotientChartIdealTildeIso I j).hom ≫
        (Scheme.Modules.pullback
          (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).map
            (closedImmersionModuleToUnit (quotientProjMap I)) ≫
          BundleSectionZeroLocus.pullbackUnitComparison
            (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)) =
      (tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).map
          (ModuleCat.ofHom (RingHom.ker
            (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
        (PfaffianDescent.affineGlobalSectionsUnitTildeIso
          (A := HomogeneousLocalization.Away PS (X j))).hom := by
  exact @nativeIsoHomPostcompositionTransport004
    (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules (inferInstance : Category (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules)
    ((tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).obj
      (ModuleCat.of (HomogeneousLocalization.Away PS (X j))
        (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j))))
    ((Scheme.Modules.pullback (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))).obj (closedImmersionModule (quotientProjMap I))) (SheafOfModules.unit (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf)
    (actualAmbientHomogeneousQuotientChartIdealTildeIso I j)
    (actualAmbientIdealChartOriginalChainValue004 I j)
    (actualAmbientIdealChartIso_originalChain004 I j)
    ((Scheme.Modules.pullback (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0))).map (closedImmersionModuleToUnit (quotientProjMap I)) ≫ BundleSectionZeroLocus.pullbackUnitComparison (Proj.awayι PS (X j) (isHomogeneous_X K j) (Nat.zero_lt_succ 0)))
    ((tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).map
      (ModuleCat.ofHom (RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j)).subtype) ≫
      (PfaffianDescent.affineGlobalSectionsUnitTildeIso
        (A := HomogeneousLocalization.Away PS (X j))).hom)
    (actualAmbientIdealChartOriginalChainInclusion004 I j)

end PfaffianDescent.Coray
