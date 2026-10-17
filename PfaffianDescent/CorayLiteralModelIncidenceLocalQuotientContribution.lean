import PfaffianDescent.CorayLiteralModelIncidenceAffineEvaluation
import PfaffianDescent.CorayOriginalIncidenceScalarRankBridges
import PfaffianDescent.CorayLinearEntireFiberQuotientContribution
import PfaffianDescent.CorayModelIncidencePositive

/-! Native original-K local gluing contribution on the SAME entire model fibre.
No source quotient finiteness, gluing lower bound or incidence count is assumed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem nativeLocalContribution_finiteRank_morphism_congr
    {F : Type u} [Field F] {X : Scheme.{u}}
    {f g : X ⟶ Spec (.of F)} [IsFinite f] [IsFinite g] (h : f = g) :
    finiteSchemeRank f = finiteSchemeRank g := by
  cases h
  rfl

variable {K M : Type u} [Field K] [Field M] [Algebra K M] [Module.Finite K M]

set_option maxHeartbeats 250000 in
/-- Natural actual original prime/model minimality constructs the ENTIRE
finite point fibre, its original K-linear evaluation square, kappa(P) injection,
finite target rank d*s and canonical gluing quotient surjection. The target
quotient has exact dimension (s-1)d. Source Cardinal-rank lower bound is
unconditional; its finrank statement keeps separate genuine source finiteness.
No gluing/genus/incidence/small-point outcome or transitivity is supplied. -/
theorem originalPrime_minimalCoefficientComponent_entireFiber_localQuotientContribution001
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ I)
    (D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) M))
    (hDmin : D.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes)
    (P : closedPoints (scheme I)) (U : (scheme I).Opens) (hU : IsAffineOpen U) (hPU : P.1 ∈ U) :
    let piI := toBase I
    let ep := (scheme I).fromSpecResidueField P.1
    let f := coefficientComponentToOriginal I D hDmin.le
    let Z := pullback ep f
    let a := pullback.snd ep f
    let c := pullback.fst ep f
    let L := (scheme I).residueField P.1
    let piL := ep ≫ piI
    let piB := f ≫ piI
    let piC := c ≫ piL
    let V := f ⁻¹ᵁ U
    let A := Γ(scheme I, U)
    let B := Γ(scheme D, V)
    let C := Γ(Z, ⊤)
    letI := pointAlgebra piI P.1
    letI : Algebra K A := (schemeOpenBaseRingHom piI U).toAlgebra
    letI : Algebra K B := (schemeOpenBaseRingHom piB V).toAlgebra
    letI : Algebra K C := (schemeOpenBaseRingHom piC ⊤).toAlgebra
    ∃ hfiniteP : IsFinite c,
      letI := hfiniteP
      let d := piI.residueDegree P.1
      let s := @finiteSchemeRank.{u} L inferInstance Z c hfiniteP
      ∃ hA : (⊤ : Z.Opens) ≤ a ⁻¹ᵁ V,
      ∃ hE : (⊤ : (Spec L).Opens) ≤ ep ⁻¹ᵁ U,
      ∃ (sigma : A →ₐ[K] B) (alpha : A →ₐ[K] L) (j : L →ₐ[K] C) (beta : B →ₐ[K] C),
        sigma.toRingHom = (f.app U).hom ∧
          alpha.toRingHom = (ep.appLE U ⊤ hE ≫ (Scheme.ΓSpecIso L).hom).hom ∧
          j.toRingHom = ((Scheme.ΓSpecIso L).inv ≫ c.appLE ⊤ ⊤ (by simp)).hom ∧
          beta.toRingHom = (a.appLE V ⊤ hA).hom ∧
          ∃ hSquare : beta.comp sigma = j.comp alpha,
          Function.Surjective beta ∧ Function.Injective j ∧
          Module.Finite K C ∧ Module.finrank K L = d ∧ Module.finrank K C = d * s ∧
          ∃ q : (B ⧸ LinearMap.range sigma.toLinearMap) →ₗ[K] (C ⧸ LinearMap.range j.toLinearMap),
            q = linearResidueFiberDiagramQuotientMap001 sigma.toLinearMap alpha.toLinearMap
              j.toLinearMap beta.toLinearMap (by ext x; exact AlgHom.congr_fun hSquare x) ∧
            Function.Surjective q ∧ Module.finrank K (C ⧸ LinearMap.range j.toLinearMap) = d * (s - 1) ∧
            ((d * (s - 1) : ℕ) : Cardinal.{u}) ≤ Module.rank K (B ⧸ LinearMap.range sigma.toLinearMap) ∧
            (∀ hFinite : Module.Finite K (B ⧸ LinearMap.range sigma.toLinearMap),
              letI := hFinite
              d * (s - 1) ≤ Module.finrank K (B ⧸ LinearMap.range sigma.toLinearMap)) := by
  let piI := toBase I
  let ep := (scheme I).fromSpecResidueField P.1
  let f := coefficientComponentToOriginal I D hDmin.le
  let Z := pullback ep f
  let a := pullback.snd ep f
  let c := pullback.fst ep f
  let L := (scheme I).residueField P.1
  let piL := ep ≫ piI
  let piB := f ≫ piI
  let piC := c ≫ piL
  let V := f ⁻¹ᵁ U
  let A := Γ(scheme I, U)
  let B := Γ(scheme D, V)
  let C := Γ(Z, ⊤)
  letI := pointAlgebra piI P.1
  letI : Module.Finite K L := closedPoint_moduleFinite piI P
  letI : Algebra K A := (schemeOpenBaseRingHom piI U).toAlgebra
  letI : Algebra K B := (schemeOpenBaseRingHom piB V).toAlgebra
  letI : Algebra K C := (schemeOpenBaseRingHom piC ⊤).toAlgebra
  obtain ⟨_hfiniteM, hfiniteP, _hNuPositive, hSPositive, _hCount⟩ :=
    originalPrime_minimalCoefficientComponent_incidence_ranks_positive I hIrel D hDmin P
  letI : IsFinite c := hfiniteP
  letI : IsFinite piL := isFinite_closedPointToBase piI P
  letI : IsFinite piC := inferInstance
  let d := piI.residueDegree P.1
  let s := @finiteSchemeRank.{u} L inferInstance Z c hfiniteP
  obtain ⟨hA, hE, hBetaRaw, hSquareRaw⟩ :=
    originalPointModelIncidence_entireFiber_affineEvaluation_surjective_and_residueFactorSquare001
      I D hDmin.le P U hU hPU
  have hMap : a ≫ f = c ≫ ep := (pullback.condition (f := ep) (g := f)).symm
  have hBaseA : a ≫ piB = piC := by
    calc
      a ≫ (f ≫ piI) = (a ≫ f) ≫ piI := (Category.assoc a f piI).symm
      _ = (c ≫ ep) ≫ piI := congrArg (fun g : Z ⟶ scheme I => g ≫ piI) hMap
      _ = c ≫ (ep ≫ piI) := Category.assoc c ep piI
  letI : Algebra K Γ(Spec L, ⊤) := (schemeOpenBaseRingHom piL ⊤).toAlgebra
  let eL := originalPointResidueSpectrumGlobalSectionsAlgEquiv001 piI P.1
  let sigma : A →ₐ[K] B := originalOpenSectionPullbackAlgHom f piI U
  let alpha : A →ₐ[K] L := eL.toAlgHom.comp
    (originalSectionAppLEAlgHom_of_baseSquare001 ep piI piL rfl U ⊤ hE)
  let j : L →ₐ[K] C := (originalSectionAppLEAlgHom_of_baseSquare001
    c piL piC rfl ⊤ ⊤ (by simp)).comp eL.symm.toAlgHom
  let beta : B →ₐ[K] C := originalSectionAppLEAlgHom_of_baseSquare001 a piB piC hBaseA V ⊤ hA
  have hSquare : beta.comp sigma = j.comp alpha := by
    ext t
    change (a.appLE V ⊤ hA).hom ((f.app U).hom t) =
      (c.appLE ⊤ ⊤ (by simp)).hom
        (eL.symm (eL ((ep.appLE U ⊤ hE).hom t)))
    rw [eL.symm_apply_apply]
    exact ConcreteCategory.congr_hom hSquareRaw t
  have hBeta : Function.Surjective beta := hBetaRaw
  have hNontrivial : Nontrivial C := by
    letI : Algebra L C := @PfaffianDescent.finiteSchemeCoefficientAlgebra.{u} L inferInstance Z c hfiniteP
    have hPos : 0 < Module.finrank L C := hSPositive
    exact Module.nontrivial_of_finrank_pos hPos
  letI : Nontrivial C := hNontrivial
  have hJ : Function.Injective j := j.injective
  obtain ⟨hCFinite, hCNative⟩ := finiteScheme_originalOpenTopRing_finite_and_finrank001 piC
  letI : Module.Finite K C := hCFinite
  have hLRank : Module.finrank K L = d := closedPoint_finrank_eq_residueDegree piI P
  have hPiL : piL = Spec.map (CommRingCat.ofHom (algebraMap K L)) := (pointAlgebra_spec piI P.1).symm
  have hPiC : piC = c ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
    congrArg (fun g : Spec L ⟶ Spec (.of K) => c ≫ g) hPiL
  letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hTower : finiteSchemeRank piC = d * s := by
    have h := finiteSchemeRank_original_eq_modelFieldDegree_mul (K := K) (M := L) c
    rw [hLRank] at h
    have hRankCongr := @nativeLocalContribution_finiteRank_morphism_congr.{u}
      K inferInstance Z piC
      (c ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)))
      inferInstance (hPiC ▸ (inferInstance : IsFinite piC)) hPiC
    exact hRankCongr.trans h
  have hCRank : Module.finrank K C = d * s := hCNative.trans hTower
  have hLinearSquare : beta.toLinearMap.comp sigma.toLinearMap = j.toLinearMap.comp alpha.toLinearMap := by
    ext t
    exact AlgHom.congr_fun hSquare t
  let q := linearResidueFiberDiagramQuotientMap001 sigma.toLinearMap alpha.toLinearMap
    j.toLinearMap beta.toLinearMap hLinearSquare
  have hQSurjective : Function.Surjective q := linearResidueFiberDiagramQuotientMap_surjective001
    sigma.toLinearMap alpha.toLinearMap j.toLinearMap beta.toLinearMap hLinearSquare hBeta
  obtain ⟨hTarget, hRank, hFiniteLower⟩ :=
    linearResidueFiberDiagram_quotient_target_finrank_and_source_rank001
      sigma.toLinearMap alpha.toLinearMap j.toLinearMap beta.toLinearMap hLinearSquare hBeta
      hJ d s hLRank hCRank
  refine ⟨hfiniteP, hA, hE, sigma, alpha, j, beta, rfl, rfl, rfl, rfl,
    hSquare, hBeta, hJ, hCFinite, hLRank, hCRank, q, ?_, hQSurjective, hTarget, hRank, hFiniteLower⟩
  rfl

end PfaffianDescent.Coray
