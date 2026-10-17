import PfaffianDescent.CubicAffineChartFieldPoint
import PfaffianDescent.CubicConfigurationOrderedFieldCanonicalPoint
import PfaffianDescent.CubicGroundChartConfigurationCoordinates

/-! Actual canonical finite-configuration component points have the literal
normalized coordinates of the original affine configuration field point. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicConfigurationAffineField_normalized_components
    {K E : Type u} [Field K] [Field E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    [IsIntegral (cubicConfigurationBase p hp n)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp n).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp n ≫
      cubicConfigurationToBase p hp n)
    (U : Scheme.{u}) [IsAffine U]
    (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
    (c : Fin 4 → K)
    (t : Fin n → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
      (cubicGroundChartClass p hp c)))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
        (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c)
        (by decide : 0 < 1) =
      (i ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) n k).left)
    (b : K →+* Γ(U, ⊤))
    (hb : b = voisinDegreeTenSelectedAvoidance_affineBaseRingMap U
      (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom))
    (x : Fin n → Fin 4 → Γ(U, ⊤))
    (hx : x = fun k r => pulledLinearChartCoordinate (equationIdeal p hp)
      (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c) U (t k) r)
    (h : Γ(U, ⊤) →+* E)
    (β : (cubicConfigurationBase p hp n).functionField →+* E)
    (hβ : Spec.map (CommRingCat.ofHom β) ≫
        (cubicConfigurationBase p hp n).fromSpecStalk
          (genericPoint (cubicConfigurationBase p hp n)) =
      (voisinDegreeTenSelectedAvoidance_affineFieldPoint h ≫ i) ≫
        configurationQuotientMap (equationIdeal p hp) n) :
    let F := (cubicConfigurationBase p hp n).functionField
    let P := p.map a.hom
    let hP := hp.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp n a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra F E := β.toAlgebra
    letI : Algebra K E := (h.comp b).toAlgebra
    let w : Fin n → Fin 4 → E := fun k r => h (x k r)
    ∃ (he : ∀ k q, q ∈ (equationIdeal p hp).toIdeal →
        q.eval₂ (algebraMap K E) (w k) = 0)
      (hn : ∀ k, (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
          (eval₂Hom (algebraMap K E) (w k)) (he k))
        (cubicGroundChartClass p hp c) = 1),
      ∀ k, Spec.map (CommRingCat.ofHom
          (cubicConfigurationOrderedFieldComponentAlgHom p hp n
            (voisinDegreeTenSelectedAvoidance_affineFieldPoint h ≫ i) β hβ a ha k).toRingHom) ≫
        finiteSubschemeDatumSpecMap (hypersurfaceToBase P hP) D ≫
        hypersurfaceToAmbient P hP ≫ ambientCoefficientMap a.hom =
      linearNormalizedPointAt (equationIdeal p hp) (w k) (he k)
        (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c) (hn k) ≫
        hypersurfaceToAmbient p hp := by
  subst b
  dsimp only
  let b := voisinDegreeTenSelectedAvoidance_affineBaseRingMap U
    (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom)
  let F := (cubicConfigurationBase p hp n).functionField
  let D := cubicConfigurationGenericFiniteSubscheme p hp n a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp n a ha
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra F E := β.toAlgebra
  letI : Algebra K E := (h.comp b).toAlgebra
  let w : Fin n → Fin 4 → E := fun k r => h (x k r)
  have hnormalized : ∀ k,
      ∃ (he : ∀ q ∈ (equationIdeal p hp).toIdeal, q.eval₂ (algebraMap K E) (w k) = 0),
      ∃ (hn : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
        (eval₂Hom (algebraMap K E) (w k)) he) (cubicGroundChartClass p hp c) = 1),
      linearNormalizedPointAt (equationIdeal p hp) (w k) he
        (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c) hn =
        (voisinDegreeTenSelectedAvoidance_affineFieldPoint h ≫ t k) ≫
          Proj.awayι (grading (equationIdeal p hp))
            (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c)
            (by decide : 0 < 1) := by
    intro k
    have hnat := affineFieldPoint_normalizedPointAt (equationIdeal p hp)
      (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c)
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c) rfl U (t k)
      (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom)
      (cubicGroundChart_orderedChartLift_baseMap p hp c n U i t ht k) h
    dsimp only at hnat
    have hw : (fun r => h (pulledLinearChartCoordinate (equationIdeal p hp)
        (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c) U (t k) r)) = w k := by
      funext r
      exact congrArg h (congrFun (congrFun hx k) r).symm
    rw [hw] at hnat
    exact hnat.2
  choose he hn hpoint using hnormalized
  refine ⟨he, hn, ?_⟩
  intro k
  have hcanonical := cubicConfigurationOrderedFieldComponentAlgHom_canonicalPoint_actualMarkedPoint
    p hp n (voisinDegreeTenSelectedAvoidance_affineFieldPoint h ≫ i) β hβ a ha k
  have hmarked : linearNormalizedPointAt (equationIdeal p hp) (w k) (he k)
      (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c) (hn k) ≫
        hypersurfaceToAmbient p hp =
      (((voisinDegreeTenSelectedAvoidance_affineFieldPoint h ≫ i) ≫
        Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) n k).left) ≫
            hypersurfaceToAmbient p hp := by
    rw [hpoint, Category.assoc _ (t k) _, ht]
    simp only [Category.assoc]
  exact hcanonical.trans hmarked.symm

end PfaffianDescent
