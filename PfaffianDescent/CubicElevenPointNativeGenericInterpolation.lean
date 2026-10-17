import PfaffianDescent.CubicElevenPointGenericJetWitness

/-! A smooth cubic over the original ground field internally constructs
full interpolation over an actual point of its unordered generic
eleven-point configuration. The coordinates are literal normalized
coordinates of the actual ordered configuration chart. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem exists_cubicSurfaceElevenPoint_native_generic_interpolation
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (U : Scheme.{u}) (_ : IsAffine U) (_ : IsIntegral U)
      (c : Fin 4 → K)
      (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left)
      (t : Fin 11 → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
        (cubicGroundChartClass p hp c)))))
      (b : K →+* Γ(U, ⊤)) (x : Fin 11 → Fin 4 → Γ(U, ⊤))
      (anchor : Fin 11 → Fin 4) (pivot : Fin 3 → Fin 3)
      (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3)
      (hd : cubicCoordinateDenominator x anchor ≠ 0)
      (_ : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left)
      (_ : IsIntegral (cubicConfigurationBase p hp 11)),
      IsOpenImmersion i ∧
      b = voisinDegreeTenSelectedAvoidance_affineBaseRingMap U
        (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom) ∧
      x = (fun k z => pulledLinearChartCoordinate (equationIdeal p hp)
        (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c) U (t k) z) ∧
      (∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
          (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c)
          (by decide : 0 < 1) =
        (i ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 11)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 k).left) ∧
      let S := Localization.Away (cubicCoordinateDenominator x anchor)
      letI : _root_.IsDomain S := Localization.Away.isDomain hd
      let E := FractionRing S
      let f : S →+* E := algebraMap S E
      let h := f.comp (algebraMap Γ(U, ⊤) S)
      let a := voisinDegreeTenSelectedAvoidance_affineFieldPoint h
      let y : Fin 11 → Fin 4 → E := fun k j =>
        f (cubicCoordinateLocalizedVector x anchor k j)
      voisinDegreeTenSelectedAvoidance_fieldPointSpecialization a = h ∧
        a (IsLocalRing.closedPoint E) = genericPoint U ∧
        (a ≫ i) (IsLocalRing.closedPoint E) =
          genericPoint (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left ∧
        (∃ β : (cubicConfigurationBase p hp 11).functionField →+* E,
          Spec.map (CommRingCat.ofHom β) ≫ (cubicConfigurationBase p hp 11).fromSpecStalk
              (genericPoint (cubicConfigurationBase p hp 11)) =
            (a ≫ i) ≫ configurationQuotientMap (equationIdeal p hp) 11) ∧
        (∀ k j, y k j = (h (x k (anchor k)))⁻¹ * h (x k j)) ∧
        (∀ k, y k (anchor k) = 1) ∧
        (∀ k, (p.map (h.comp b)).eval (y k) = 0) ∧
        Function.Surjective (cubicElevenPointFullJetRestriction y
          (cubicFullJetCoordinates y
            (cubicPolynomialSurfaceTangentRows (p.map (h.comp b)) y
              (fun k => anchor (k.castAdd 8)) pivot))) := by
  classical
  obtain ⟨U, hUa, hUint, c, i, _, t, b, x, anchor, pivot, m,
      hi, _, hb, hx, ht, hpx, _, hd, _, hm⟩ :=
    exists_cubicSurfaceElevenPoint_native_localizedJet_witness
      (L := AlgebraicClosure K) p hp hp0
  letI : IsAffine U := hUa
  letI : IsIntegral U := hUint
  letI : IsOpenImmersion i := hi
  obtain ⟨hO, hB⟩ := cubicSurfaceElevenPoint_native_configuration_integral p hp hp0
  letI : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left := hO
  letI : IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 11).left := hO
  letI : IsIntegral (cubicConfigurationBase p hp 11) := hB
  letI : IsIntegral (configurationQuotientOpen (equationIdeal p hp) 11).toScheme := hB
  let π := configurationQuotientMap (equationIdeal p hp) 11
  let S := Localization.Away (cubicCoordinateDenominator x anchor)
  letI : _root_.IsDomain S := Localization.Away.isDomain hd
  let E := FractionRing S
  let f : S →+* E := algebraMap S E
  let h : Γ(U, ⊤) →+* E := f.comp (algebraMap Γ(U, ⊤) S)
  let a := voisinDegreeTenSelectedAvoidance_affineFieldPoint h
  let y : Fin 11 → Fin 4 → E := fun k j => f (cubicCoordinateLocalizedVector x anchor k j)
  obtain ⟨ha, hgU, hgO, hβ, hfull⟩ :=
    cubicElevenPoint_localizedFractionPoint_fullInterpolation i π (p.map b) x anchor pivot m hd hm
  have hy : ∀ k j, y k j = (h (x k (anchor k)))⁻¹ * h (x k j) :=
    cubicCoordinateFieldMap_vector x anchor f
  have hpy : ∀ k, (p.map (h.comp b)).eval (y k) = 0 := by
    intro k
    have hpxF : (p.map (h.comp b)).eval (fun j => h (x k j)) = 0 := by
      rw [← MvPolynomial.map_map]
      change (eval (h ∘ x k)) ((p.map b).map h) = 0
      rw [← MvPolynomial.map_eval, hpx k, map_zero]
    have hscale := cubicClosedPointSerreSurfaceJetCotangent_aeval_mul_homogeneous
      (p.map (h.comp b)) (hp.map (h.comp b)) (h (x k (anchor k)))⁻¹
      (fun j => h (x k j))
    have hy' : y k = fun j => (h (x k (anchor k)))⁻¹ * h (x k j) := funext (hy k)
    rw [hy']
    simpa only [aeval_eq_eval, hpxF, mul_zero] using hscale
  refine ⟨U, hUa, hUint, c, i, t, b, x, anchor, pivot, m, hd, hO, hB, hi, hb, hx, ht,
    ha, hgU, hgO, hβ, hy, ?_, hpy, ?_⟩
  · intro k
    change f (cubicCoordinateLocalizedVector x anchor k (anchor k)) = 1
    rw [cubicCoordinateLocalizedVector_anchor, map_one]
  · rw [MvPolynomial.map_map] at hfull
    exact hfull

end PfaffianDescent
