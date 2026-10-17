import PfaffianDescent.CoraySelectedCurveSameOriginalAuxiliaryNativeJet
import PfaffianDescent.CorayOriginalRegularClosedPointNormalizationLift
import Mathlib.AlgebraicGeometry.Noetherian

/-! SOURCE ONLY / UNVERIFIED. Actual full-jet selection and exact original
point recovery force nonregularity of the SAME AX's OWN native curve stalk.
Neither native surjectivity, cotangent rank, nor nonregularity is supplied. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Constructed SAME-AX full jet gives its OWN residue cotangent rank >=2,
and actual native dimension <=1 forces nonregularity. No curve integrality
is required; the smooth cubic and q outside its ideal derive dimension. -/
theorem selectedCurve_sameOriginalAuxiliaryPoint_cotangent_ge_two_and_nonregular
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hqhom : q.IsHomogeneous n)
    (hqnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (A : closedPoints (hypersurface p hp))
    (AX : closedPoints (scheme (projectiveIntersectionIdeal p q hp hqhom)))
    (hAX : cubicSecondEquationCurveImmersion p q hp n hqhom AX.1 = A.1) :
    let S := hypersurface p hp
    letI := pointAlgebra (hypersurfaceToBase p hp) A.1
    ∀ (anchor : Fin 4) (g : ChartRing (equationIdeal p hp) anchor →+* S.residueField A.1),
      g.comp (chartBaseMap (equationIdeal p hp) anchor) = algebraMap K (S.residueField A.1) →
      Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) anchor =
        S.fromSpecResidueField A.1 →
      ∀ pivot : Fin 3,
        let x : Fin 4 → S.residueField A.1 := fun j => g (chartCoordinate (equationIdeal p hp) anchor j)
        (pderiv (anchor.succAbove pivot) p).eval₂ (algebraMap K (S.residueField A.1)) x ≠ 0 →
        q.eval₂ ((algebraMap (S.residueField A.1)
            (PfaffianDescent.CubicSurfaceFirstJet (S.residueField A.1))).comp
          (algebraMap K (S.residueField A.1)))
          (PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet
            (p.map (algebraMap K (S.residueField A.1))) anchor x pivot) = 0 →
        let R := (scheme (projectiveIntersectionIdeal p q hp hqhom)).presheaf.stalk AX.1
        2 ≤ Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) ∧
          ¬ IsRegularLocalRing R := by
  classical
  intro S
  letI := pointAlgebra (hypersurfaceToBase p hp) A.1
  intro anchor g hgbase hgpoint pivot x hpivot hqjet R
  let J := projectiveIntersectionIdeal p q hp hqhom
  let X := scheme J
  letI : LocallyOfFiniteType (toBase J) := inferInstance
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (toBase J)
  letI : IsNoetherianRing R := inferInstanceAs (IsNoetherianRing (X.presheaf.stalk AX.1))
  obtain ⟨φ, hφ, _hcoeff⟩ := selectedCurve_sameOriginalAuxiliaryPoint_exists_nativeFullJet
    (K := K) p q hp n hqhom A AX hAX anchor g hgbase hgpoint pivot hpivot hqjet
  have hlarge : 2 ≤ Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :=
    cotangent_finrank_ge_two_of_surjective_fullJet φ hφ
  refine ⟨hlarge, ?_⟩
  intro hregular
  have heq := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp hregular
  have hdim : ringKrullDim R ≤ 1 :=
    projectiveIntersection_original_stalk_ringKrullDim_le_one p q hp hp0 n hqhom hqnot AX.1
  have htwo : (2 : WithBot ℕ∞) ≤
      (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) : WithBot ℕ∞) := by
    exact_mod_cast hlarge
  have hsmall : (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :
      WithBot ℕ∞) ≤ 1 := by
    rw [heq]
    exact hdim
  have hfalse : (2 : WithBot ℕ∞) ≤ 1 := htwo.trans hsmall
  norm_num at hfalse

end PfaffianDescent.Coray
