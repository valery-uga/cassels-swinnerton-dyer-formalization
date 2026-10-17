import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridCanonicalRestrictionTransport
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericWitnessData
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridMinorKernelRank
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridNativeCurveAvoidance
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridWitnessResidueFactor
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridAffineFieldValues
import PfaffianDescent.VoisinGenericCubicSixteenSurjectivity

/-! The explicit grid constructs actual native generic-sixteen cubic curve
avoidance on every normalized chart of the coefficient-changed finite datum. -/
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_genericSixteen_nativeCubicKernel_noFixedHeightTwoPrime
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (cubicConfigurationBase p hp 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 16 ≫
      cubicConfigurationToBase p hp 16)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    let Q := cubicConfigurationBase p hp 16
    let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp 16 a ha
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    let j := D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
      hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom)
    ∀ T : NormalizedAmbientChart Q.functionField Γ(D.val.subscheme, ⊤) (Fin 4)
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q.functionField)) j,
      ¬ ∃ C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q.functionField),
        C.toIdeal.IsPrime ∧ C.toIdeal.height = 2 ∧ p.map a.hom ∈ C.toIdeal ∧
        (∀ s : homogeneousSubmodule (Fin 4) Q.functionField 3,
          s ∈ LinearMap.ker (homogeneousSectionRestriction T.x 3) → s.1 ∈ C.toIdeal) := by
  let w : VoisinDegreeTenSelectedAvoidanceGridGenericFiniteWitness p hp :=
    Classical.choice (voisinDegreeTenSelectedAvoidance_exists_gridGenericFiniteWitness
      (K := K) (L := L) p hp hno)
  dsimp only
  let Q := cubicConfigurationBase p hp 16
  letI : Field Q.functionField := inferInstance
  let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
  letI : CommRing Γ(D.val.subscheme, ⊤) := inferInstance
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 16 a ha
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : FiniteDimensional Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  letI : IsIntegral (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 16).toScheme := by
    change IsIntegral Q
    infer_instance
  intro T
  let U : Scheme.{u} := w.U
  let i := w.i
  let t := w.t
  let β : K →+* Γ(U, ⊤) := w.b
  let x : Fin 16 → Fin 4 → Γ(U, ⊤) := w.x
  letI : CommRing Γ(U, ⊤) := inferInstance
  letI : IsAffine U := w.affine
  letI : IsIntegral U := w.integral
  letI : IsOpenImmersion i := w.openImmersion
  letI : IsDomain Γ(U, ⊤) := w.hdom
  have hβ := w.baseMap
  have hx := w.coordinates
  have ht := w.markedPoints
  let m : Fin 16 ↪ Monomials (Fin 4) 3 := w.m
  have hdet : homogeneousMinorDet m x ≠ 0 := w.hdet
  let S := Localization.Away (homogeneousMinorDet m x)
  letI : IsDomain S := Localization.Away.isDomain hdet
  have hzero := w.finiteWitness.1
  have hfinite := w.finiteWitness.2
  let E := FractionRing S
  letI : Field E := inferInstance
  let h : Γ(U, ⊤) →+* E := (algebraMap S E).comp (algebraMap Γ(U, ⊤) S)
  let c := voisinDegreeTenSelectedAvoidance_affineFieldPoint h
  have hp0 := voisinDegreeTenSelectedAvoidance_cubic_ne_zero_of_no_section p hp hno
  have hIntegral := voisinDegreeTenSelectedAvoidance_configuration_integral_of_fieldPoint
    (K := K) (L := E) p hp hp0 16 (c ≫ i)
  letI : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left :=
    hIntegral.1
  letI : IsIntegral (orderedFamilyConfigurationOver
      (toBase (equationIdeal p hp)) 16).left := by
    change IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left
    exact hIntegral.1
  letI : IsIntegral (configurationQuotientOpen (equationIdeal p hp) 16).toScheme := by
    change IsIntegral Q
    infer_instance
  let O := (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left
  let z := genericPoint O
  have hfactor := voisinDegreeTenSelectedAvoidance_gridWitness_exists_orderedResidueFactor
    (K := K) p hp w
  let hz := Classical.choose hfactor
  let g := Classical.choose (Classical.choose_spec hfactor)
  have hg := Classical.choose_spec (Classical.choose_spec hfactor)
  let b := cubicSixteenOrderedLiftFunctionFieldHom p hp z hz
  letI : Algebra Q.functionField E := (g.comp b).toAlgebra
  have hcoeff := voisinDegreeTenSelectedAvoidance_canonicalSixteen_coefficients_at_residueFactor
    p hp a ha z hz (c ≫ i) g hg
  have hβvalue : h.comp β =
      (Spec.preimage (c ≫ i ≫ (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 16).hom)).hom :=
    voisinDegreeTenSelectedAvoidance_affineFieldPoint_baseCoefficientHom h
      (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).hom) β hβ
  have hβcoeff : h.comp β = (g.comp b).comp a.hom := hβvalue.trans hcoeff.symm
  have hpmap : (((p.map β).map (algebraMap Γ(U, ⊤) S)).map (algebraMap S E)) =
      (p.map a.hom).map (algebraMap Q.functionField E) := by
    rw [MvPolynomial.map_map, MvPolynomial.map_map, MvPolynomial.map_map]
    exact congrArg (fun f : K →+* E => p.map f) hβcoeff
  let q := (homogeneousMinorCorrectedPolynomial m x
    ((voisinDegreeTenSelectedAvoidance_gridCubic K 1).map β)).map (algebraMap S E)
  let r := (homogeneousMinorCorrectedPolynomial m x
    ((voisinDegreeTenSelectedAvoidance_gridCubic K 2).map β)).map (algebraMap S E)
  have hq : q.IsHomogeneous 3 :=
    (homogeneousMinorCorrectedPolynomial_isHomogeneous m x _
      ((voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 1).map β)).map _
  have hr : r.IsHomogeneous 3 :=
    (homogeneousMinorCorrectedPolynomial_isHomogeneous m x _
      ((voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 2).map β)).map _
  letI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      ((p.map a.hom).map (algebraMap Q.functionField E)) q r
      ((hp.map a.hom).map (algebraMap Q.functionField E)) hq hr)) := by
    change IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (((p.map β).map (algebraMap Γ(U, ⊤) S)).map (algebraMap S E)) q r
      (((hp.map β).map (algebraMap Γ(U, ⊤) S)).map (algebraMap S E)) hq hr)) at hfinite
    have hI : tripleCompleteIntersectionHomogeneousIdeal
        (((p.map β).map (algebraMap Γ(U, ⊤) S)).map (algebraMap S E)) q r
        (((hp.map β).map (algebraMap Γ(U, ⊤) S)).map (algebraMap S E)) hq hr =
        tripleCompleteIntersectionHomogeneousIdeal
        ((p.map a.hom).map (algebraMap Q.functionField E)) q r
        ((hp.map a.hom).map (algebraMap Q.functionField E)) hq hr := by
      apply HomogeneousIdeal.ext
      simp only [tripleCompleteIntersectionHomogeneousIdeal_toIdeal, hpmap]
    rw [← hI]
    exact hfinite
  let y : Fin 16 → Fin 4 → E := fun k l => h (x k l)
  let R : homogeneousSubmodule (Fin 4) E 3 →ₗ[E] (Fin 16 → E) :=
    homogeneousSectionRestriction (fun l k => y k l) 3
  have hRsurj : Function.Surjective R :=
    voisinDegreeTenSelectedAvoidance_restriction_surjective_on_minorOpen_fieldPoint
      (R := Γ(U, ⊤)) (F := E) m x (algebraMap S E)
  have hRrank := voisinDegreeTenSelectedAvoidance_cubicProductKernel_finrank_four_of_surjective
    R hRsurj
  have hy : (fun l k => (Spec.preimage (c ≫ t k)).hom
      (linearChartCoordinate (equationIdeal p hp) (coordinate (equationIdeal p hp) 0)
        (coordinate_mem (equationIdeal p hp) 0) l)) = (fun l k => y k l) :=
    voisinDegreeTenSelectedAvoidance_affineFieldPoint_pulledCoordinateMatrix
      (equationIdeal p hp) 16 h t x hx
  have htransport : ∀ s : homogeneousSubmodule (Fin 4) Q.functionField 3,
      s ∈ LinearMap.ker (homogeneousSectionRestriction T.x 3) →
      voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E) s ∈ LinearMap.ker R := by
    intro s hs
    have htr := voisinDegreeTenSelectedAvoidance_canonicalSixteen_nativeKernel_orderedTransport
      (K := K) (E := E) p hp a ha z hz U i t ht c g hg T s hs
    rw [hy] at htr
    exact htr
  have hqker : (⟨q, hq⟩ : homogeneousSubmodule (Fin 4) E 3) ∈ LinearMap.ker R := by
    rw [LinearMap.mem_ker]
    funext k
    simp only [R, homogeneousSectionRestriction_apply, finite_product_evaluation_apply,
      Pi.zero_apply]
    dsimp only [q]
    rw [MvPolynomial.aeval_eq_eval]
    exact (hzero k).1
  have hrker : (⟨r, hr⟩ : homogeneousSubmodule (Fin 4) E 3) ∈ LinearMap.ker R := by
    rw [LinearMap.mem_ker]
    funext k
    simp only [R, homogeneousSectionRestriction_apply, finite_product_evaluation_apply,
      Pi.zero_apply]
    dsimp only [r]
    rw [MvPolynomial.aeval_eq_eval]
    exact (hzero k).2
  have hA : finrank Q.functionField Γ(D.val.subscheme, ⊤) ≤ 16 :=
    le_of_eq (cubicConfigurationGenericSixteen_coefficientFinrank p hp a ha)
  exact voisinDegreeTenSelectedAvoidance_nativeCubicKernel_noFixedHeightTwoPrime_of_orderedTransport
    (K := Q.functionField) (A := Γ(D.val.subscheme, ⊤)) (L := E) T.x hA R hRrank htransport (p.map a.hom) (hp.map a.hom)
    ⟨q, hq⟩ ⟨r, hr⟩ hqker hrker

end PfaffianDescent
