import PfaffianDescent.CorayLiteralModelIncidenceLocalQuotientContribution
import PfaffianDescent.CorayLiteralModelUnitCokernelGroundAffineSections
import PfaffianDescent.CorayFiniteSupportOriginalOpenRankBound
import PfaffianDescent.CorayLiteralModelGlobalGluingUpperBound

/-! SAME original prime, closed P and coefficient-model map. Actual local
fibre contribution and genuine global upper bound are joined through the
actual native affine quotient comparison. Finite CLOSED support of SAME Q
remains explicit until its geometric stabilizer producer is accepted. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K M : Type u} [Field K] [CharZero K] [Field M]
variable [Algebra K M] [Module.Finite K M]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Project only SAME sigma and its conditional finite local rank lower
bound from the genuine original entire-fibre producer. Its finite fibre and
all morphisms are constructed upstream, not outcome premises here. -/
private theorem originalModelLocalContribution_sigmaFiniteLowerCut001
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ I)
    (D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) M))
    (hDmin : D.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes)
    (P : closedPoints (scheme I)) (U : (scheme I).Opens) (hU : IsAffineOpen U)
    (hPU : P.1 ∈ U) :
    let piI := toBase I
    let ep := (scheme I).fromSpecResidueField P.1
    let f := coefficientComponentToOriginal I D hDmin.le
    let Z := pullback ep f
    let c := pullback.fst ep f
    let L := (scheme I).residueField P.1
    let V := f ⁻¹ᵁ U
    let A := Γ(scheme I, U)
    let B := Γ(scheme D, V)
    letI : Algebra K A := (schemeOpenBaseRingHom piI U).toAlgebra
    letI : Algebra K B := (schemeOpenBaseRingHom (f ≫ piI) V).toAlgebra
    ∃ hfiniteP : IsFinite c,
      letI := hfiniteP
      let d := piI.residueDegree P.1
      let s := @finiteSchemeRank.{u} L inferInstance Z c hfiniteP
      ∃ sigma : A →ₐ[K] B,
        sigma.toRingHom = (f.app U).hom ∧
          (∀ hFinite : Module.Finite K (B ⧸ LinearMap.range sigma.toLinearMap),
            letI := hFinite
            d * (s - 1) ≤ Module.finrank K (B ⧸ LinearMap.range sigma.toLinearMap)) := by
  dsimp only
  obtain ⟨hfiniteP, _hA, _hE, sigma, _alpha, _j, _beta,
      hsigma, _halpha, _hj, _hbeta, _hSquare, _hBetaSurj, _hJInj,
      _hCF, _hLR, _hCR, _q, _hq, _hQSurj, _hTargetRank, _hCard, hLower⟩ :=
    originalPrime_minimalCoefficientComponent_entireFiber_localQuotientContribution001
      I hIrel D hDmin P U hU hPU
  exact ⟨hfiniteP, sigma, hsigma, hLower⟩

/-- Actual same-model lower and upper bounds give d(s−1)≤r+G_n−1. The only
remaining geometric witness is finite closed support of the literal global
unit cokernel. No desired local/global finiteness, rank or incidence bound
is among the original curve/point/model hypotheses. -/
theorem selectedOriginalPrime_actualCoefficientModel_localGlobalIncidence_gluingInequality
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) M))
    (hDmin : D.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes)
    [GeometricallyIntegral (toBase D)] (P : closedPoints (scheme I)) :
    let X := scheme I
    let piI := toBase I
    let ep := X.fromSpecResidueField P.1
    let f := coefficientComponentToOriginal I D hDmin.le
    let Z := pullback ep f
    let c := pullback.fst ep f
    let L := X.residueField P.1
    let a := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
    let Q := cokernel (C := X.Modules) a
    ∀ (T : Set X), T.Finite → (∀ x ∈ T, IsClosed ({x} : Set X)) →
      schemeModuleStalkSupport Q ⊆ T →
        ∃ hfiniteP : IsFinite c,
          letI := hfiniteP
          piI.residueDegree P.1 *
              (@finiteSchemeRank.{u} L inferInstance Z c hfiniteP - 1) ≤
            Module.finrank K M + 3 * n * (n - 1) / 2 := by
  classical
  letI : I.toIdeal.IsPrime := hI.isPrime
  let X := scheme I
  let piI := toBase I
  let ep := X.fromSpecResidueField P.1
  let f := coefficientComponentToOriginal I D hDmin.le
  let Z := pullback ep f
  let c := pullback.fst ep f
  let L := X.residueField P.1
  let a := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let Q := cokernel (C := X.Modules) a
  dsimp only
  intro T hT hClosed hSupport
  obtain ⟨U, hU, hPU, _hUTop⟩ :=
    exists_isAffineOpen_mem_and_subset (show P.1 ∈ (⊤ : X.Opens) from trivial)
  have hIrel := selectedProjectiveMinimalComponent_homogeneous_relevant
    p q hp hp0 n hq hnot I hI
  let V := f ⁻¹ᵁ U
  let A := Γ(X, U)
  let B := Γ(scheme D, V)
  letI : Algebra K A := (schemeOpenBaseRingHom piI U).toAlgebra
  letI : Algebra K B := (schemeOpenBaseRingHom (f ≫ piI) V).toAlgebra
  obtain ⟨hfiniteP, sigma, hsigma, hLower⟩ :=
    originalModelLocalContribution_sigmaFiniteLowerCut001 I hIrel D hDmin P U hU hPU
  letI : IsFinite c := hfiniteP
  obtain ⟨E, _hProjection⟩ :=
    coefficientComponentToOriginal_unitCokernel_affineGroundQuotient_exists_preserving_projection
      I D hDmin.le U hU sigma hsigma
  have hGlobal := selectedOriginalPrime_actualCoefficientModel_globalGluingHZero_finite_finrank_le
    p q hp hp0 n hn hq hnot I hI D hDmin
  letI : Module.Finite K (SchemeModuleOpenSectionsOver piI Q ⊤) := hGlobal.1
  have hOpen := schemeModuleFiniteClosedSupport_openSections_finite_finrank_le_top
    piI Q T hT hClosed hSupport U
  letI : Module.Finite K (SchemeModuleOpenSectionsOver piI Q U) := hOpen.1
  have hLocalFinite : Module.Finite K (B ⧸ LinearMap.range sigma.toLinearMap) :=
    Module.Finite.of_surjective E.toLinearMap E.surjective
  refine ⟨hfiniteP, ?_⟩
  calc
    piI.residueDegree P.1 *
        (@finiteSchemeRank.{u} L inferInstance Z c hfiniteP - 1) ≤
        Module.finrank K (B ⧸ LinearMap.range sigma.toLinearMap) := hLower hLocalFinite
    _ = Module.finrank K (SchemeModuleOpenSectionsOver piI Q U) := E.finrank_eq.symm
    _ ≤ Module.finrank K (SchemeModuleOpenSectionsOver piI Q ⊤) := hOpen.2
    _ ≤ Module.finrank K M + 3 * n * (n - 1) / 2 := hGlobal.2

end PfaffianDescent.Coray
