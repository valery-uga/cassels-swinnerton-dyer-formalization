import PfaffianDescent.VoisinProjectiveNontrivialEquationOpen
import PfaffianDescent.VoisinFieldPointIntersectionChart
import PfaffianDescent.VoisinRelativeUniversalDivisor

/-!
# The regular field-point cubic represents its actual projective parameter

The regularity witness for a point of the relative nontrivial-equation open
must be the same equation used to construct the universal incidence fibre.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

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
variable (t : Spec (.of S) ⟶
  flatGradedProjectiveFibreNontrivialOpen (S := S) J r q e hRank a ha ha0)
variable (ht : let W := flatGradedGrassmannian J 3 r q e hRank
  let f := grassmannianQuotientMorphism K W
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let P := pullback.fst
    (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g ≫
    grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f
  (t ≫ pullback.fst P (nontrivialSurfaceEquationOpen a ha ha0).ι) ≫
    pullback.snd
      (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g = 𝟙 _)

include J r q e hRank hmap ha0 t ht in
/-- A field point of the actual nontrivial-equation fibre gives a regular
cubic whose projective class is exactly that field point's equation
parameter, together with regular principal intersection charts. -/
theorem flatGradedProjectiveFibreNontrivialOpen_fieldPoint_regularCharts_parameter :
    let W := flatGradedGrassmannian J 3 r q e hRank
    let f := grassmannianQuotientMorphism K W
    let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let P := pullback.fst
      (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g ≫
      grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0),
      p ∈ C.toIdeal ∧
      IsRegular (Ideal.Quotient.mk
        (equationIdeal (a.map (algebraMap K S))
          (ha.map (algebraMap K S))).toIdeal p) ∧
      CubicIntersectionRegularOnCharts (a.map (algebraMap K S))
        (ha.map (algebraMap K S)) p hp ∧
      (t ≫ pullback.fst P (nontrivialSurfaceEquationOpen a ha ha0).ι) ≫ P =
        projectiveClassifyingMap p hp hp0 (algebraMap K S) := by
  let W := flatGradedGrassmannian J 3 r q e hRank
  let f := grassmannianQuotientMorphism K W
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let P := pullback.fst
    (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g ≫
    grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f
  let v := t ≫ pullback.fst P (nontrivialSurfaceEquationOpen a ha ha0).ι
  have hopen : (v ≫ P) (IsLocalRing.closedPoint S) ∈
      nontrivialSurfaceEquationOpen a ha ha0 :=
    nontrivialEquationFamily_fieldPoint_mem P a ha ha0 t
  obtain ⟨p, hp, hp0, _, hpC, _, hregular, _, hparam⟩ :=
    flatGradedProjectiveFamily_fibrePoint_regular_on_nontrivialOpen
      J r q e hRank C hmap a ha ha0 v ht hopen
  have haS0 : a.map (algebraMap K S) ≠ 0 := by
    intro hzero
    apply ha0
    exact MvPolynomial.map_injective (algebraMap K S)
      (RingHom.injective (algebraMap K S)) (by simpa using hzero)
  refine ⟨p, hp, hp0, hpC, ?_,
    cubicIntersectionRegularOnCharts_of_regularModSurface
      (a.map (algebraMap K S)) (ha.map (algebraMap K S)) haS0
      p hp hregular, ?_⟩
  · exact isRegular_iff_mem_nonZeroDivisors.mpr
      (quotient_mk_mem_nonZeroDivisors_of_regular_mod_ideal _ p hregular)
  simpa only [projectiveClassifyingMap_comp_projectiveParametersCoefficientMap]
    using hparam

include hmap in
/-- The same regular cubic represents the parameter of the actual
base-changed relative open, before identifying it with the fibre open. -/
theorem flatGradedProjectiveFamilyNontrivialOpen_baseChange_fieldPoint_regularCharts_parameter
    (s : Spec (.of S) ⟶
      pullback (flatGradedProjectiveFamilyNontrivialOpenToBase
        J r q e hRank a ha ha0)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hs : s ≫ pullback.snd
      (flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) = 𝟙 _) :
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0),
      p ∈ C.toIdeal ∧
      IsRegular (Ideal.Quotient.mk
        (equationIdeal (a.map (algebraMap K S))
          (ha.map (algebraMap K S))).toIdeal p) ∧
      CubicIntersectionRegularOnCharts (a.map (algebraMap K S))
        (ha.map (algebraMap K S)) p hp ∧
      s ≫ pullback.fst
        (flatGradedProjectiveFamilyNontrivialOpenToBase
          J r q e hRank a ha ha0)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫
          flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0 =
        projectiveClassifyingMap p hp hp0 (algebraMap K S) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let φ := flatGradedProjectiveFamilyNontrivialOpen_baseChangeIso
    (S := S) J r q e hRank a ha ha0
  let t : Spec (.of S) ⟶
      flatGradedProjectiveFibreNontrivialOpen (S := S) J r q e hRank a ha ha0 :=
    s ≫ φ.hom
  have ht : let W := flatGradedGrassmannian J 3 r q e hRank
      let f := grassmannianQuotientMorphism K W
      let P := pullback.fst
        (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g ≫
        grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f
      (t ≫ pullback.fst P (nontrivialSurfaceEquationOpen a ha ha0).ι) ≫
        pullback.snd
          (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g = 𝟙 _ := by
    dsimp only [t, φ, flatGradedProjectiveFamilyNontrivialOpen_baseChangeIso]
    rw [Category.assoc, Category.assoc]
    rw [independentPullbackIso_hom_toT]
    exact hs
  obtain ⟨p, hp, hp0, hpC, hreg, hcharts, hparam⟩ :=
    flatGradedProjectiveFibreNontrivialOpen_fieldPoint_regularCharts_parameter
      J r q e hRank C hmap a ha ha0 t ht
  refine ⟨p, hp, hp0, hpC, hreg, hcharts, ?_⟩
  let W := flatGradedGrassmannian J 3 r q e hRank
  let f := grassmannianQuotientMorphism K W
  let P := pullback.fst
    (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g ≫
    grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f
  have hcompare :
      t ≫ pullback.fst P (nontrivialSurfaceEquationOpen a ha ha0).ι ≫ P =
        s ≫ pullback.fst
          (flatGradedProjectiveFamilyNontrivialOpenToBase
            J r q e hRank a ha ha0) g ≫
            flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0 := by
    dsimp only [t, φ, flatGradedProjectiveFamilyNontrivialOpen_baseChangeIso]
    rw [Category.assoc]
    rw [pullback.condition]
    simpa only [Category.assoc, flatGradedProjectiveFamilyNontrivialOpenToBase,
      flatGradedNontrivialOpenToGlobalParameters, P, f, W, g] using
      (congrArg
        (fun z => s ≫ z ≫ (nontrivialSurfaceEquationOpen a ha ha0).ι)
        (independentPullbackIso_hom_toU
          (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f)
          (grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f)
          (nontrivialSurfaceEquationOpen a ha ha0).ι g))
  exact hcompare.symm.trans hparam

include hmap in
/-- The regular chart witness can be chosen with a nonzero coefficient chart,
so its equation parameter is exactly the parameter of the base-changed
relative open. -/
theorem flatGradedProjectiveFamilyNontrivialOpen_baseChange_fieldPoint_regularCharts_equationParameter
    (s : Spec (.of S) ⟶
      pullback (flatGradedProjectiveFamilyNontrivialOpenToBase
        J r q e hRank a ha ha0)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hs : s ≫ pullback.snd
      (flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) = 𝟙 _) :
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3)
      (j : Monomials (Fin 4) 3) (hj : p.coeff j.1 ≠ 0),
      p ∈ C.toIdeal ∧
      IsRegular (Ideal.Quotient.mk
        (equationIdeal (a.map (algebraMap K S))
          (ha.map (algebraMap K S))).toIdeal p) ∧
      CubicIntersectionRegularOnCharts (a.map (algebraMap K S))
        (ha.map (algebraMap K S)) p hp ∧
      s ≫ pullback.fst
        (flatGradedProjectiveFamilyNontrivialOpenToBase
          J r q e hRank a ha ha0)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫
          flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0 =
        projectiveEquationParameter (algebraMap K S) p j hj := by
  obtain ⟨p, hp, hp0, hpC, hreg, hcharts, hparam⟩ :=
    flatGradedProjectiveFamilyNontrivialOpen_baseChange_fieldPoint_regularCharts_parameter
      J r q e hRank C hmap a ha ha0 s hs
  let j := chosenEquationCoefficient p hp hp0
  let hj := chosenEquationCoefficient_ne_zero p hp hp0
  refine ⟨p, hp, j, hj, hpC, hreg, hcharts, ?_⟩
  rw [← projectiveClassifyingMap_eq_chart p hp hp0 (algebraMap K S) j hj]
  exact hparam

end PfaffianDescent
