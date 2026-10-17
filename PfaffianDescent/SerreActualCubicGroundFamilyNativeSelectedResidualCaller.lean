import PfaffianDescent.SerreActualCubicGroundFamilyOldSelectedNativeResidual
import PfaffianDescent.SerreActualIncidenceMarkedFamilyTransport
import PfaffianDescent.SerreActualConfigurationGenericGoodData
import PfaffianDescent.CubicConfigurationRankGenericField
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicNativeSelectedOriginalParameter

/-! Unpack one actual native ground selection, preserve all its witnesses,
transport the proved marked-family identity, and construct native residual eight. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[irreducible]
def serreActualCubicGroundFamily_retainedGenericGood_nativeSelectedResidualEight
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    [IsIntegral (cubicConfigurationBase p hp 3)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3)
    (ι : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion ι]
    (hι : ι ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : finrank K L = 11)
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist ι (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {Rk : Scheme.{u}} [IsAffine Rk] [IsIntegral Rk]
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    [IsOpenImmersion aRank]
    [IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    (chart : Fin 3 → C.ι)
    (markedU : ∀ n, Rk ⟶ (C.U (chart n)).toScheme)
    (hmarkedU : ∀ n, markedU n ≫ (C.U (chart n)).ι =
      (aRank ≫ (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 n).left)
    (minor : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9)
    (hminor : IsUnit (Matrix.det (Matrix.submatrix
      (serreIncidenceNativeAffineEvaluationMatrix (hypersurfaceToBase p hp)
        e C h9 chart markedU) id minor))) :=
  let F := (cubicConfigurationBase p hp 3).functionField
  let E := Rk.residueField (genericPoint Rk)
  letI : Algebra K F := a.hom.toAlgebra
  letI : CharZero F := charZero_cubicConfigurationFunctionField_of_flat p hp 3
  let cA := Rk.fromSpecResidueField (genericPoint Rk)
  let c := cA ≫ aRank
  let cfg := aRank ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom
  let hb := serreIncidenceCubicNativeRank_marked_toBase p hp e C aRank chart markedU hmarkedU
  let markedOld : Fin 3 → (Rk ⟶ hypersurface p hp) := fun n => markedU n ≫ (C.U (chart n)).ι
  let markedLiteral : Fin 3 → (Rk ⟶ hypersurface p hp) := fun n =>
    aRank ≫ (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 n).left
  let hmLiteral : ∀ n, markedLiteral n ≫ hypersurfaceToBase p hp = cfg := fun n => by
    simp only [markedLiteral, cfg, Category.assoc, orderedFamilyCoordinate_toBase,
      (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).w]
  let hMarkedFamily : markedOld = markedLiteral := by
    funext n
    exact (hmarkedU n).trans (Category.assoc _ _ _)
  let Cv := serreIncidenceRankTwoAffineCover e C
  let base := hypersurfaceToBase p hp
  let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base e.E
  let zero := Cv.projectiveSectionLocalZeroGluedToAmbient base e.E
  letI := Cv.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base e.E
  letI := serreSectionUniversalZeroToParameters_isProper base e.E Cv
  let g := serreThreePointSectionIncidenceZeroFamily cfg base pp markedOld hb zero
  let W := serreIncidenceGoodOpen g
    (cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen cfg base pp markedOld hb zero)
  fun (hInitial : SerreActualConfigurationGenericGoodAtChart base e C cfg chart markedU hb) =>
    let initial := hInitial.choose
    let hInitialSeed := hInitial.choose_spec
    let βdata := cubicConfigurationRankChart_exists_genericFieldEmbedding p hp 3 aRank
    let β := βdata.choose
    let hβ := βdata.choose_spec
    letI : Algebra F E := β.toAlgebra
    letI : Algebra K E := (β.comp a.hom).toAlgebra
    letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun k => rfl)
    let ρ : Fin 6 ≃ (Fin 3 × ULift.{u} (Fin 2)) :=
      Fintype.equivOfCardEq (by simp)
    let selection := serreIncidenceCubicNativeRank_exists_ground_selection
      p hp c β hβ a ha e C h9 aRank chart markedU hmarkedU minor hminor cA rfl ρ
      W initial hInitialSeed.1 (IsLocalRing.closedPoint E) hInitialSeed.2.1
    let h3 := selection.choose
    let selection₁ := selection.choose_spec
    let H := selection₁.choose
    let selection₂ := selection₁.choose_spec
    let hHG := selection₂.choose
    let selection₃ := selection₂.choose_spec
    let qF := selection₃.choose
    let selection₄ := selection₃.choose_spec
    let qSelected := selection₄.choose
    let selected := selection₄.choose_spec
    let G := serreIncidenceCubicNativeGroundKernelMatrix p hp a ha e C h9 h3
    let eK := serreThreePointSectionIncidence_nativeKernelFieldIso
      base e.E Cv cfg chart markedU hb h9 ρ
      (fieldPointΓevaluation cA) cA (serreIncidenceAffineFieldPoint_spec cA)
    let U := (eK.hom ≫ pullback.fst
      (serreIncidenceBundleKernelConfiguration base e.E Cv cfg chart markedU hb) cA) ⁻¹ᵁ W
    let sSelected := qSelected ≫ U.ι ≫ eK.hom ≫ pullback.fst
      (serreIncidenceBundleKernelConfiguration base e.E Cv cfg chart markedU hb) cA
    let hSelectedCfg := selected.2.1
    let hSelectedW := selected.2.2.1 (IsLocalRing.closedPoint E)
    let hSelectedParam := serreIncidenceCubicNativeRank_selected_originalParameter
      p hp c β hβ a ha e C h9 aRank chart markedU hmarkedU cA rfl ρ
      G H hHG qF (qSelected ≫ U.ι) selected.2.2.2
    let hspSelected : sSelected ≫ serreThreePointSectionIncidenceToParameters
        cfg base pp markedOld hb zero =
        (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ qF) ≫
          serreActualGroundPlaneOriginalParameters base e.E h9 G H hHG := by
      run_tac do
        let h ← Lean.Meta.getFVarFromUserName `hSelectedParam
        Lean.Meta.withTransparency .all do
          Lean.Elab.Tactic.closeMainGoal `exact h
    let transport := serreActualIncidenceMarkedFamilyIso cfg base pp zero
      markedOld markedLiteral hb hmLiteral hMarkedFamily
    let sLiteral := sSelected ≫ transport.hom
    let hcfgLiteral : sLiteral ≫ serreThreePointSectionIncidenceToConfiguration
        cfg base pp markedLiteral hmLiteral zero = cA := by
      dsimp only [sLiteral, transport]
      rw [Category.assoc, serreActualIncidenceMarkedFamilyIso_toConfiguration]
      exact hSelectedCfg
    let hspLiteral : sLiteral ≫ serreThreePointSectionIncidenceToParameters
        cfg base pp markedLiteral hmLiteral zero =
        (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ qF) ≫
          serreActualGroundPlaneOriginalParameters base e.E h9 G H hHG := by
      dsimp only [sLiteral, transport]
      rw [Category.assoc, serreActualIncidenceMarkedFamilyIso_toParameters]
      exact hspSelected
    let hGoodLiteral := serreActualIncidenceMarkedFamilyIso_goodMarked
      cfg base pp zero markedOld markedLiteral hb hmLiteral hMarkedFamily
      sSelected (IsLocalRing.closedPoint E) hSelectedW.1 hSelectedW.2
    serreActualCubicGroundFamily_oldSelectedSeed_nativeResidualEight
      p hp hp0 a ha ι hι hL e C h9 aRank β hβ G H hHG qF selected.1
      sLiteral hspLiteral hcfgLiteral hGoodLiteral.1 hGoodLiteral.2

end PfaffianDescent
