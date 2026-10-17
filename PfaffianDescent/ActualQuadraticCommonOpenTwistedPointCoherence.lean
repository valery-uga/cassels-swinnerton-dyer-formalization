import PfaffianDescent.ActualRelativeDifferentialCommonOpenPointClass
import PfaffianDescent.ActualPositiveTwoCommonOpenBasisClass
import PfaffianDescent.ActualFieldPointTensorSectionBalance
import PfaffianDescent.ActualHomogeneousQuadraticOverlapSheafDifferential
import PfaffianDescent.ActualPositiveTwistPullbackTensorIso

/- SOURCE ONLY / UNVERIFIED. Actual DQ_f tensor e_f = DQ_h tensor e_h
in the SAME genuinely pulled-back Omega(2) at the original point.
Quadratic and basis transitions, point scalar transport and tensor balance
are all derived internally. The ordinary hypothesis says Q vanishes at the
point; no desired differential/coordinate comparison is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective AllCharacteristics.GradedChart
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def actualPositiveTwistPointTensorSection
    {K L : Type u} [Field K] [Field L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (q : Spec (.of L) ⟶ scheme I) (M : (scheme I).Modules) (m : ℕ)
    (s : (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj M))
    (t : (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback q).obj (positiveSheafOfModules (grading I) m))) :
    (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback q).obj
        (schemeModuleTensor M (positiveSheafOfModules (grading I) m))) :=
  (moduleSpecΓFunctor (R := .of L)).map
    (actualPositiveTwistPullbackTensorIso I q M m).inv
    (actualFieldPointTensorSection ((Scheme.Modules.pullback q).obj M)
      ((Scheme.Modules.pullback q).obj (positiveSheafOfModules (grading I) m)) s t)

lemma actualPositiveTwistPointTensorSection_balance
    {K L : Type u} [Field K] [Field L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (q : Spec (.of L) ⟶ scheme I) (M : (scheme I).Modules) (m : ℕ) (c : L)
    (s : (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj M))
    (t : (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback q).obj (positiveSheafOfModules (grading I) m))) :
    actualPositiveTwistPointTensorSection I q M m (c • s) t =
      actualPositiveTwistPointTensorSection I q M m s (c • t) := by
  unfold actualPositiveTwistPointTensorSection
  rw [actualFieldPointTensorSection_balance]

lemma actualQuadratic_commonOpen_twisted_point_coherence
    {K L : Type u} [Field K] [Field L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {f h : CoordinateRing I} (hf : f ∈ grading I 1) (hh : h ∈ grading I 1)
    (g : scheme I ⟶ Spec (.of K))
    (q : Spec (.of L) ⟶ (Proj.basicOpen (grading I) (f * h) : Scheme))
    (Q : CoordinateRing I) (hQ : Q ∈ grading I 2)
    (hzero : actualOpenPointResidue (Proj.basicOpen (grading I) (f * h)) q
      ((Proj.awayToSection (grading I) (f * h)).hom
        (awayMap (grading I) hf (mul_comm f h) (Away.mk (grading I) hh 2 Q hQ))) = 0) :
    let W := Proj.basicOpen (grading I) (f * h)
    let qf := actualHomogeneousQuadraticProductOpenSection (grading I) hf hh Q hQ
    let qh := (Proj.awayToSection (grading I) (f * h)).hom
      (awayMap (grading I) hf (mul_comm f h) (Away.mk (grading I) hh 2 Q hQ))
    let f2 : grading I 2 := ⟨f ^ 2, by simpa using pow_mem_graded 2 hf⟩
    let h2 : grading I 2 := ⟨h ^ 2, by simpa using pow_mem_graded 2 hh⟩
    actualPositiveTwistPointTensorSection I (q ≫ W.ι) (schemeRelativeDifferentials g) 2
      (actualRelativeDifferentialCommonOpenPointClass g W q qf)
      (actualModuleOpenPointSectionClass g W q (positiveSheafOfModules (grading I) 2)
        ((positiveGlobalSectionOfHomogeneous (grading I) 2 f2).val (op W))) =
    actualPositiveTwistPointTensorSection I (q ≫ W.ι) (schemeRelativeDifferentials g) 2
      (actualRelativeDifferentialCommonOpenPointClass g W q qh)
      (actualModuleOpenPointSectionClass g W q (positiveSheafOfModules (grading I) 2)
        ((positiveGlobalSectionOfHomogeneous (grading I) 2 h2).val (op W))) := by
  dsimp only
  let W := Proj.basicOpen (grading I) (f * h)
  let ratio : Γ(scheme I, W) := (Proj.awayToSection (grading I) (f * h)).hom
    (awayMap (grading I) hh rfl (normalized (grading I) hf h hh))
  let qh : Γ(scheme I, W) := (Proj.awayToSection (grading I) (f * h)).hom
    (awayMap (grading I) hf (mul_comm f h) (Away.mk (grading I) hh 2 Q hQ))
  have hd : actualRelativeDifferentialCommonOpenPointClass g W q
      (actualHomogeneousQuadraticProductOpenSection (grading I) hf hh Q hQ) =
        actualOpenPointResidue W q ratio ^ 2 •
          actualRelativeDifferentialCommonOpenPointClass g W q qh := by
    rw [actualHomogeneousQuadratic_productOpenSection_transition,
      actualRelativeDifferentialCommonOpenPointClass_mul_of_residue_zero g W q _ _ hzero,
      map_pow]
  have hb := actualPositiveTwo_commonOpen_point_basis_transition (grading I) hf hh g q
  dsimp only at hb
  rw [hd, hb, actualPositiveTwistPointTensorSection_balance]

end PfaffianDescent
