import PfaffianDescent.ActualPositiveTwistChartUnit
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveTwistCoordinate
import AllCharacteristics.AffineChartPresentation
/- SOURCE ONLY / UNVERIFIED. Actual positive twist fractions in every degree. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

private lemma actualPositiveZeroAddCast_apply_val
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (m : ℕ) (U : (Scheme.Opens (scheme I))ᵒᵖ)
    (z : (positiveSheafOfModules (grading I) (0 + m)).val.obj U)
    (x : U.unop) :
    (((eqToIso (by rw [zero_add]) :
      positiveSheafOfModules (grading I) (0 + m) ≅
        positiveSheafOfModules (grading I) m).hom.val.app U z).1 x) = z.1 x := by
  let p : positiveSheafOfModules (grading I) (0 + m) =
      positiveSheafOfModules (grading I) m :=
    congrArg (positiveSheafOfModules (grading I)) (Nat.zero_add m)
  change ((((eqToHom p : positiveSheafOfModules (grading I) (0 + m) ⟶
      positiveSheafOfModules (grading I) m).val.app U) z).1 x) = z.1 x
  have h :
      (((Scheme.Modules.toPresheaf (scheme I)).map
        (eqToHom p)).app U z) ≍ z := by
    have hmor :
        (eqToHom p : positiveSheafOfModules (grading I) (0 + m) ⟶
          positiveSheafOfModules (grading I) m) ≍
            𝟙 (positiveSheafOfModules (grading I) (0 + m)) :=
      eqToHom_heq_id_dom _ _ _
    have hout :
        (((Scheme.Modules.toPresheaf (scheme I)).map
          (eqToHom p)).app U) z ≍
        (((Scheme.Modules.toPresheaf (scheme I)).map
          (𝟙 (positiveSheafOfModules (grading I) (0 + m)))).app U) z := by
      congr <;> first | exact hmor | simp only [Nat.zero_add] | rfl
    have hid :
        (((Scheme.Modules.toPresheaf (scheme I)).map
          (𝟙 (positiveSheafOfModules (grading I) (0 + m)))).app U) z = z := by
      rfl
    exact hout.trans (heq_of_eq hid)
  have hcoe :
      (((((Scheme.Modules.toPresheaf (scheme I)).map
        (eqToHom p)).app U) z).1) = z.1 :=
    (Subtype.heq_iff_coe_eq (fun q => by simp only [zero_add])).mp h
  exact congrFun hcoe x

/-- The actual basis morphism acts on every unit section by the actual
homogeneous multiplier, after the genuine arithmetic degree transport. -/
private lemma actualPositiveTwistChartBasisInvHom_apply_value
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (ell : grading I 1) (m : ℕ) (U : (Scheme.Opens (scheme I))ᵒᵖ)
    (y : Γ(scheme I, U.unop)) (x : U.unop) :
    let basisMap :
        (schemeModuleUnit (scheme I)).presheaf ⟶
          (positiveSheafOfModules (grading I) m).presheaf :=
      (Scheme.Modules.toPresheaf (scheme I)).map
        (actualPositiveTwistChartBasisInvHom I ell m)
    (basisMap.app U y).1 x =
      algebraMap (CoordinateRing I)
        (Localization.AtPrime (positivePointIdeal (grading I) x.1))
        ((degreeOnePower (grading I) ell m : grading I m) : CoordinateRing I) *
        (y.val x).val := by
  dsimp only
  let z : (positiveSheafOfModules (grading I) (0 + m)).val.obj U :=
    ((Scheme.Modules.toPresheaf (scheme I)).map
      (unitToZeroTwist (grading I) ≫ zeroTwistToPositiveZero (grading I) ≫
        positiveMulHomogeneous (grading I) (degreeOnePower (grading I) ell m) 0)).app U y
  change (((eqToIso (congrArg (positiveSheafOfModules (grading I))
    (Nat.zero_add m))).hom.val.app U z).1 x) = _
  rw [actualPositiveZeroAddCast_apply_val]
  rfl

/-- The actual homogeneous Away section cancels its degree-one denominator.
The proof is independent of any quotient presentation or twist-basis map. -/
private lemma actualHomogeneousAwaySection_mul_degreeOnePower
    {A R : Type u} [CommRing A] [SetLike R A] [AddSubgroupClass R A]
    (G : ℕ → R) [GradedRing G]
    (ell : G 1) (m : ℕ) (q : G m)
    (x : Proj.basicOpen G (ell : A)) :
    algebraMap A (Localization.AtPrime (positivePointIdeal G x.1))
        ((degreeOnePower G ell m : G m) : A) *
      (((ProjectiveSpectrum.Proj.awayToSection G (ell : A)).hom
        (Away.mk G ell.2 m (q : A)
          (by simpa only [smul_eq_mul, mul_one] using q.2))).val x).val =
      Localization.mk (q : A) ⟨1, Submonoid.one_mem _⟩ := by
  have he : (ell : A) ∈ (positivePointIdeal G x.1).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    exact (ProjectiveSpectrum.mem_basicOpen G (ell : A) x.1).mp x.2
  have ha := ProjectiveSpectrum.Proj.awayToSection_apply G (ell : A)
    (Away.mk G ell.2 m (q : A)
      (by simpa only [smul_eq_mul, mul_one] using q.2)) x
  erw [ha, Away.val_mk]
  rw [Localization.mk_eq_mk', IsLocalization.map_mk']
  simp only [RingHom.id_apply]
  erw [Localization.mk_one_eq_algebraMap]
  exact IsLocalization.mk'_spec'
    (M := (positivePointIdeal G x.1).primeCompl)
    (Localization.AtPrime (positivePointIdeal G x.1))
    (q : A) ⟨(ell : A) ^ m, Submonoid.pow_mem _ he m⟩

theorem actualPositiveTwistChartBasisInvHom_fraction
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (ell : grading I 1) (m : ℕ) (q : grading I m) :
    let basisMap :
        (schemeModuleUnit (scheme I)).presheaf ⟶
          (positiveSheafOfModules (grading I) m).presheaf :=
      (Scheme.Modules.toPresheaf (scheme I)).map
        (actualPositiveTwistChartBasisInvHom I ell m)
    basisMap.app
      (op (Proj.basicOpen (grading I) (ell : CoordinateRing I)))
      ((ProjectiveSpectrum.Proj.awayToSection (grading I) (ell : CoordinateRing I)).hom
        (Away.mk (grading I) ell.2 m (q : CoordinateRing I)
          (by simpa using q.2))) =
    (positiveSheafOfModules (grading I) m).presheaf.map
      (homOfLE (show Proj.basicOpen (grading I) (ell : CoordinateRing I) ≤ ⊤ from le_top)).op
      (PresheafOfModules.sections.eval
        (positiveGlobalSectionOfHomogeneous (grading I) m q) (op ⊤)) := by
  dsimp only
  apply Subtype.ext
  funext x
  rw [actualPositiveTwistChartBasisInvHom_apply_value]
  change algebraMap (CoordinateRing I)
      (Localization.AtPrime (positivePointIdeal (grading I) x.1))
      ((degreeOnePower (grading I) ell m : grading I m) : CoordinateRing I) *
    (((ProjectiveSpectrum.Proj.awayToSection (grading I) (ell : CoordinateRing I)).hom
      (Away.mk (grading I) ell.2 m (q : CoordinateRing I)
        (by simpa using q.2))).val x).val =
    Localization.mk (q : CoordinateRing I) ⟨1, Submonoid.one_mem _⟩
  exact actualHomogeneousAwaySection_mul_degreeOnePower (grading I) ell m q x



lemma actualChartToPresentation_injective
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4) :
    Function.Injective (chartToPresentation I j) := by
  have hl (z : ChartRing I j) : chartPresentationEquiv I j (chartToPresentation I j z) = z := by
    obtain ⟨p, rfl⟩ := eval₂_chartCoordinate_surjective I j z
    change chartPresentationEquiv I j
      (chartToPresentation I j (p.eval₂ (chartBaseMap I j) (chartCoordinate I j))) =
        p.eval₂ (chartBaseMap I j) (chartCoordinate I j)
    exact (congrArg (chartPresentationEquiv I j) (chartToPresentation_eval I j p)).trans
      (chartPresentationEquiv_mk I j p)
  intro a b h
  have h' := congrArg (chartPresentationEquiv I j) h
  simpa only [hl] using h'

lemma actualChartHomogeneousFraction_eq_aeval
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4)
    (m : ℕ) (Q : homogeneousSubmodule (Fin 4) K m) :
    letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
    Away.mk (grading I) (coordinate_mem I j) m
      (Ideal.Quotient.mk I.toIdeal Q) (by
        simpa only [smul_eq_mul, mul_one] using
          (show Ideal.Quotient.mk I.toIdeal (Q : MvPolynomial (Fin 4) K) ∈ grading I m from
            ⟨(Q : MvPolynomial (Fin 4) K), Q.property, rfl⟩)) =
    aeval (chartCoordinate I j) (Q : MvPolynomial (Fin 4) K) := by
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  apply actualChartToPresentation_injective I j
  change AllCharacteristics.GradedChart.liftCoordinateOne (grading I) (coordinate I j)
      (coordinateRingToChartPresentation I j)
      (coordinateRingToChartPresentation_coordinate I j)
      (Away.mk (grading I) (coordinate_mem I j) m
        (Ideal.Quotient.mk I.toIdeal Q) (by
        simpa only [smul_eq_mul, mul_one] using
          (show Ideal.Quotient.mk I.toIdeal (Q : MvPolynomial (Fin 4) K) ∈ grading I m from
            ⟨(Q : MvPolynomial (Fin 4) K), Q.property, rfl⟩))) = _
  rw [AllCharacteristics.GradedChart.liftCoordinateOne_mk]
  change Ideal.Quotient.mk (chartPresentationIdeal I j) (Q : MvPolynomial (Fin 4) K) =
    chartToPresentation I j
      ((Q : MvPolynomial (Fin 4) K).eval₂ (chartBaseMap I j) (chartCoordinate I j))
  exact (chartToPresentation_eval I j Q).symm

end PfaffianDescent
