import PfaffianDescent.VoisinFieldPointEquationParameter
import PfaffianDescent.VoisinRelativeTwoCubicIntersection

/-!
# Regular two-cubic fibres of the actual relative zero locus

The regular equation obtained from a field point of the flat graded moving
family is precisely the equation whose hypersurface occurs in the actual
relative zero-locus fibre. Thus the scheme-level fibre comparison and the
regular principal chart equations refer to the same cubic.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K R S : Type u} [Field K] [CommRing R] [IsDomain R]
  [IsNoetherianRing R] [Algebra K R] [Field S] [Algebra R S]
  [Algebra K S] [IsScalarTower K R S]
variable (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
variable [Module.Flat R (CoordinateRing J)]
variable (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
variable (hRank : ∀ x : PrimeSpectrum R,
  Module.rankAtStalk (grading J 3) x = q)
variable (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
variable (hmap : Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal = C.toIdeal)
variable (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
variable [Smooth (hypersurfaceToBase (a.map (algebraMap K S))
  (ha.map (algebraMap K S)))]
variable (s : Spec (.of S) ⟶
  pullback (flatGradedProjectiveFamilyNontrivialOpenToBase
    J r q e hRank a ha ha0)
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))
variable (hs : s ≫ pullback.snd
  (flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0)
  (Spec.map (CommRingCat.ofHom (algebraMap R S))) = 𝟙 _)

include J r q e hRank hmap ha0 s hs in
/-- Every field point of the actual relative nontrivial-equation family has
an explicit two-cubic zero-locus fibre whose second cubic has regular
principal equations on all standard charts of the smooth first cubic. -/
theorem flatGradedNontrivialRelativeZeroLocus_fieldPoint_twoCubic_regularCharts :
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3)
      (j : Monomials (Fin 4) 3) (_hj : p.coeff j.1 ≠ 0),
      ∃ (_fibreIso : (pullback (flatGradedNontrivialRelativeZeroLocusToParameters
          a ha J r q e hRank ha0)
        (s ≫ pullback.fst
          (flatGradedProjectiveFamilyNontrivialOpenToBase
            J r q e hRank a ha ha0)
          (Spec.map (CommRingCat.ofHom (algebraMap R S))))) ≅
        pullback
          (prod.lift
            (hypersurfaceToAmbient (a.map (algebraMap K S))
              (ha.map (algebraMap K S)) ≫
                ambientCoefficientMap (algebraMap K S))
            (hypersurfaceToBase (a.map (algebraMap K S))
              (ha.map (algebraMap K S))))
          (prod.lift
            (hypersurfaceToAmbient p hp ≫
              ambientCoefficientMap (algebraMap K S))
            (hypersurfaceToBase p hp))),
        p ∈ C.toIdeal ∧
        CubicIntersectionRegularOnCharts (a.map (algebraMap K S))
          (ha.map (algebraMap K S)) p hp := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let m : Spec (.of S) ⟶
      flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0 :=
    s ≫ pullback.fst _ g
  let h := flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0
  let k := flatGradedProjectiveFamilyNontrivialOpenToBase
    J r q e hRank a ha ha0 ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R))
  obtain ⟨p, hp, j, hj, hpC, _hreg, hcharts, heq⟩ :=
    flatGradedProjectiveFamilyNontrivialOpen_baseChange_fieldPoint_regularCharts_equationParameter
      J r q e hRank C hmap a ha ha0 s hs
  have heq' : m ≫ h = projectiveEquationParameter (algebraMap K S) p j hj := heq
  have hm : m ≫ k = Spec.map (CommRingCat.ofHom (algebraMap K S)) := by
    calc
      m ≫ k = m ≫ (h ≫ projectiveParametersToBase K (Fin 4) 3) := by
        exact congrArg (m ≫ ·)
          (flatGradedNontrivialOpenToGlobalParameters_toBase
            a ha J r q e hRank ha0).symm
      _ = (m ≫ h) ≫ projectiveParametersToBase K (Fin 4) 3 :=
        (Category.assoc _ _ _).symm
      _ = Spec.map (CommRingCat.ofHom (algebraMap K S)) := by
        rw [heq', projectiveEquationParameter_toBase]
  let fibreIso := fixedCubicSurfaceEquationZeroLocusTwoCubicFibreIso
    a ha k h (algebraMap K S) m hm p hp j hj heq'
  exact ⟨p, hp, j, hj, fibreIso, hpC, hcharts⟩

end PfaffianDescent
