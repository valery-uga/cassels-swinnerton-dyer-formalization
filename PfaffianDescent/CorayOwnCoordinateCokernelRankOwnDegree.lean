import PfaffianDescent.CorayOwnCoordinateCanonicalCutIso
import PfaffianDescent.CorayOwnPositiveRestrictionNativeEpi
import PfaffianDescent.FiniteProjectiveTwistQuotientRank
import PfaffianDescent.CorayOwnCoordinateHilbertDegreeAnyField
import PfaffianDescent.CorayOwnPositiveCoordinateNativeEulerStep
import Mathlib.Algebra.CharZero.Infinite

/-! SOURCE ONLY / UNVERIFIED. Exact original-field rank of the SAME literal
positive-coordinate-multiplication cokernel, and native Euler increment mu.
The canonical WHOLE-cut cokernel comparison and both coefficient comparisons
are derived, never supplied. The geometric endpoints honestly use CharZero
only to derive Infinite for the existing finite-cut twist-rank API. No future
unit-H1, eventual-H1, GI/constants=K, genus or vanishing producer is imported. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem finiteSchemeRank_eq_of_originalBaseEq001
    {Z : Scheme.{u}} (g h : Z ⟶ Spec (CommRingCat.of K))
    [IsFinite g] [IsFinite h] (heq : g = h) :
    finiteSchemeRank g = finiteSchemeRank h := by
  subst h
  rfl

/-- Construct the header's actual closed immersion before the ideal-twist
quotient type is elaborated. This is an internal theorem/local instance,
not an extra public construction hypothesis. -/
private theorem ownCoordinateWholeCut_isClosedImmersion002
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4) :
    IsClosedImmersion (schemeQuotientMap C
      (C ⊔ equationIdeal (X j) (isHomogeneous_X K j)) le_sup_left) :=
  schemeQuotientMap_closedImmersion C _ le_sup_left

attribute [local instance] ownCoordinateWholeCut_isClosedImmersion002

/-- The literal coordinate-multiplication cokernel identifies with the
ENTIRE coordinate-cut ideal-twist quotient. The first comparison is the
existing canonical cokernel.desc Iso; both following comparisons are the
actual canonical fiber projection and the actual graded restriction adjunct. -/
def ownCoordinateCokernelWholeCutIdealTwistQuotientIso001
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) :
    cokernel (ownPositiveCoordinateMultiplication C j m) ≅
      (closedImmersionIdealTwistSequence
        (schemeQuotientMap C
          (C ⊔ equationIdeal (X j) (isHomogeneous_X K j)) le_sup_left)
        (positiveSheafOfModules (grading C) (m + 1))).X₃ := by
  let D := C ⊔ equationIdeal (X j) (isHomogeneous_X K j)
  let i := schemeQuotientMap C D le_sup_left
  letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion C D le_sup_left
  let T : (scheme C).Modules := positiveSheafOfModules (grading C) (m + 1)
  let f := gradedQuotientMap C D le_sup_left
  let hf := gradedSurjective_irrelevant_le f (gradedQuotientMap_surjective C D le_sup_left)
  let c := cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom
    (grading C) (grading D) f hf (m + 1)
  let pr := schemeModuleCanonicalFiberProjection i T
  have hc : IsIso c := ownQuotientPositiveGradedPullbackHom_isIso C D le_sup_left (m + 1)
  have hpr : IsIso pr := schemeModuleCanonicalFiberProjection_isIso_of_locallyRankOne
    i T (actualComponent_positiveTwist_locallyRankOne C (m + 1))
  let epr := @asIso _ _ _ _ pr hpr
  let ec := @asIso _ _ _ _ c hc
  let e := epr ≪≫ (Scheme.Modules.pushforward i).mapIso ec
  exact ownCoordinateCokernelWholeCutPositiveTwistIso C j m ≪≫ e.symm

/-- With an actual finite whole cut over an infinite field, its literal
coordinate cokernel has finite native H0 of the SAME finite-scheme rank.
No cokernel comparison, section-rank or degree certificate is a hypothesis. -/
theorem ownCoordinateCokernel_topSections_finite_and_cutRank001
    [Infinite K] (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ)
    [hFiniteCut : IsFinite (toBase (C ⊔ equationIdeal (X j) (isHomogeneous_X K j)))] :
    Module.Finite K (SchemeModuleOpenSectionsOver (toBase C)
      (cokernel (ownPositiveCoordinateMultiplication C j m)) ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver (toBase C)
        (cokernel (ownPositiveCoordinateMultiplication C j m)) ⊤) =
        finiteSchemeRank (toBase (C ⊔ equationIdeal (X j) (isHomogeneous_X K j))) := by
  let D := C ⊔ equationIdeal (X j) (isHomogeneous_X K j)
  let i := schemeQuotientMap C D le_sup_left
  letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion C D le_sup_left
  have hbase : i ≫ toBase C = toBase D := schemeQuotientMap_toBase C D le_sup_left
  letI : IsFinite (i ≫ toBase C) := hbase.symm ▸ hFiniteCut
  let T : (scheme C).Modules := positiveSheafOfModules (grading C) (m + 1)
  let S : ShortComplex (scheme C).Modules := closedImmersionIdealTwistSequence i T
  have hS := finiteProjectivePositiveTwistQuotient_topSections_finite_and_nativeRank
    C (m + 1) i
  letI : Module.Finite K (SchemeModuleOpenSectionsOver (toBase C) S.X₃ ⊤) := hS.1
  let Q : (scheme C).Modules := cokernel (ownPositiveCoordinateMultiplication C j m)
  let e : Q ≅ S.X₃ := ownCoordinateCokernelWholeCutIdealTwistQuotientIso001 C j m
  let E : SchemeModuleOpenSectionsOver (toBase C) Q ⊤ ≃ₗ[K]
      SchemeModuleOpenSectionsOver (toBase C) S.X₃ ⊤ :=
    schemeModuleOpenTopIsoLinearEquivOver (toBase C) e
  refine ⟨Module.Finite.equiv E.symm, ?_⟩
  exact E.finrank_eq.trans (hS.2.trans
    (finiteSchemeRank_eq_of_originalBaseEq001 (i ≫ toBase C) (toBase D) hbase))

/-- CHARACTERISTIC ZERO geometric endpoint. Original selected p/q and SAME
prime C/P/j construct the finite WHOLE coordinate cut and its OWN degree mu.
The literal positive coordinate cokernel has native original-K H0 rank mu
in EVERY degree, including m=0. No constants=K or cohomology premise. -/
theorem charZero_selectedProjectivePrimeComponent_ownCoordinateCokernel_finite_rank_ownDegree001
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) (j : Fin 4)
    (hj : coordinate C j ∉ P.asHomogeneousIdeal) (m : ℕ) :
    Module.Finite K (SchemeModuleOpenSectionsOver (toBase C)
      (cokernel (ownPositiveCoordinateMultiplication C j m)) ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver (toBase C)
        (cokernel (ownPositiveCoordinateMultiplication C j m)) ⊤) =
        actualCurveCoordinateHilbertDegree C := by
  letI : Infinite K := CharZero.infinite K
  letI : C.toIdeal.IsPrime := hprime
  have hnotC : X j ∉ C.toIdeal :=
    (coordinate_notMem_at_point_ne_zero_and_notMem_component C P j hj).2
  let D := C ⊔ equationIdeal (X j) (isHomogeneous_X K j)
  letI : IsFinite (toBase D) := integralProjectiveComponent_coordinateCut_isFinite
    C hprime P (selectedProjectiveComponent_original_stalk_ringKrullDim_le_one
      p q hp hp0 n hq hnot C hIC) j hj
  have hcut := ownCoordinateCokernel_topSections_finite_and_cutRank001 C j m
  have hdegree := (primeComponent_linearSection_degree_and_eventualIncrement_anyField
    C (X j) (isHomogeneous_X K j) hnotC).1
  exact ⟨hcut.1, hcut.2.trans hdegree.symm⟩

/-- Exact native original-K Euler increment mu for the SAME coordinate map
and SAME intrinsic twists. Finiteness of the preceding coefficient remains
only the honest induction input of the existing native Euler-step API.
Neither finite unit H1 nor an eventual-vanishing certificate is asserted. -/
theorem charZero_selectedProjectivePrimeComponent_ownPositiveCoordinate_nativeEuler_step_ownDegree001
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) (j : Fin 4)
    (hj : coordinate C j ∉ P.asHomogeneousIdeal) [HasExt.{u} (scheme C).Modules]
    (m : ℕ) :
    letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
    let L : (scheme C).Modules := positiveSheafOfModules (grading C) m
    let M : (scheme C).Modules := positiveSheafOfModules (grading C) (m + 1)
    Module.Finite K (SchemeModuleOpenSectionsOver (toBase C) L ⊤) →
    Module.Finite K (schemeModuleCohomology (scheme C) L 1) →
    Module.Finite K (SchemeModuleOpenSectionsOver (toBase C) M ⊤) ∧
      Module.Finite K (schemeModuleCohomology (scheme C) M 1) ∧
      ((Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) M ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology (scheme C) M 1) =
        (Module.finrank K (SchemeModuleOpenSectionsOver (toBase C) L ⊤) : ℤ) -
          Module.finrank K (schemeModuleCohomology (scheme C) L 1) +
            (actualCurveCoordinateHilbertDegree C : ℤ)) := by
  letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
  dsimp only
  intro h0 h1
  have h := selectedProjectivePrimeComponent_ownPositiveCoordinate_finite_and_nativeEuler_step
    p q hp hp0 n hq hnot C hIC hprime P j hj m h0 h1
  have hrank := charZero_selectedProjectivePrimeComponent_ownCoordinateCokernel_finite_rank_ownDegree001
    p q hp hp0 n hq hnot C hIC hprime P j hj m
  refine ⟨h.1, h.2.1, ?_⟩
  simpa only [hrank.2] using h.2.2

end PfaffianDescent.Coray
