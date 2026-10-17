import PfaffianDescent.CubicElevenPointAffineJetWitness

/-!
The full-jet determinant is nonzero on the literal localized coordinate
ring of an actual integral eleven-point configuration chart over the
original ground field. All chart denominators and their specialization
are constructed from that chart's actual coordinates.
-/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicCoordinateSpecialization_exists_recover_normalized
    {R : Type u} [CommRing R] {F : Type v} [Field F]
    (x : Fin 11 → Fin 4 → R) (anchor : Fin 11 → Fin 4) (f : R →+* F)
    (v : Fin 11 → Fin 4 → F) (s : Fin 11 → F)
    (hs : ∀ i, s i ≠ 0) (hv : ∀ i, v i (anchor i) = 1)
    (hx : ∀ i j, f (x i j) = (s i)⁻¹ * v i j) :
    f (cubicCoordinateDenominator x anchor) ≠ 0 ∧
    ∃ g : Localization.Away (cubicCoordinateDenominator x anchor) →+* F,
      g.comp (algebraMap R (Localization.Away (cubicCoordinateDenominator x anchor))) = f ∧
      ∀ i j, g (cubicCoordinateLocalizedVector x anchor i j) = v i j := by
  have hf : ∀ i, f (x i (anchor i)) ≠ 0 := by
    intro i
    rw [hx, hv, mul_one]
    exact inv_ne_zero (hs i)
  refine ⟨cubicCoordinateDenominator_specialization_ne_zero x anchor f hf,
    cubicCoordinateSpecializationLift x anchor f hf, ?_, ?_⟩
  · ext r
    exact cubicCoordinateSpecializationLift_algebraMap x anchor f hf r
  · intro i j
    rw [cubicCoordinateSpecializationLift_vector, hx, hx, hv, mul_one, inv_inv]
    rw [← mul_assoc, mul_inv_cancel₀ (hs i), one_mul]

theorem cubicPolynomialJetMinorDet_localized_ne_zero_of_normalized_specialization
    {R : Type u} [CommRing R] {F : Type v} [Field F]
    (p : MvPolynomial (Fin 4) R) (x : Fin 11 → Fin 4 → R)
    (anchor : Fin 11 → Fin 4) (pivot : Fin 3 → Fin 3)
    (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3)
    (f : R →+* F) (v : Fin 11 → Fin 4 → F) (s : Fin 11 → F)
    (hs : ∀ i, s i ≠ 0) (hv : ∀ i, v i (anchor i) = 1)
    (hx : ∀ i j, f (x i j) = (s i)⁻¹ * v i j)
    (hm : IsUnit (cubicPolynomialJetMinorDet (p.map f) v
      (fun i => anchor (i.castAdd 8)) pivot m)) :
    cubicPolynomialJetMinorDet
      (p.map (algebraMap R (Localization.Away (cubicCoordinateDenominator x anchor))))
      (cubicCoordinateLocalizedVector x anchor)
      (fun i => anchor (i.castAdd 8)) pivot m ≠ 0 := by
  obtain ⟨_, g, hgf, hgv⟩ :=
    cubicCoordinateSpecialization_exists_recover_normalized x anchor f v s hs hv hx
  have hmap := cubicPolynomialJetMinorDet_map g
    (p.map (algebraMap R (Localization.Away (cubicCoordinateDenominator x anchor))))
    (cubicCoordinateLocalizedVector x anchor) (fun i => anchor (i.castAdd 8)) pivot m
  rw [MvPolynomial.map_map, hgf, show
    (fun i j => g (cubicCoordinateLocalizedVector x anchor i j)) = v from
      funext (fun i => funext (hgv i))] at hmap
  intro hz
  have hzero := congrArg g hz
  rw [map_zero, hmap] at hzero
  exact hm.ne_zero hzero

theorem exists_cubicSurfaceElevenPoint_native_localizedJet_witness
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (U : Scheme.{u}) (_ : IsAffine U) (_ : IsIntegral U)
      (c : Fin 4 → K)
      (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left)
      (a : Spec (.of L) ⟶ U)
      (t : Fin 11 → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
        (cubicGroundChartClass p hp c)))))
      (b : K →+* Γ(U, ⊤)) (x : Fin 11 → Fin 4 → Γ(U, ⊤))
      (anchor : Fin 11 → Fin 4) (pivot : Fin 3 → Fin 3)
      (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3),
      IsOpenImmersion i ∧ _root_.IsDomain Γ(U, ⊤) ∧
      b = voisinDegreeTenSelectedAvoidance_affineBaseRingMap U
        (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom) ∧
      x = (fun k z => pulledLinearChartCoordinate (equationIdeal p hp)
        (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c) U (t k) z) ∧
      (∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
          (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c)
          (by decide : 0 < 1) =
        (i ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 11)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 k).left) ∧
      (∀ k, (p.map b).eval (x k) = 0) ∧
      (∀ k, ((homogeneousLinearForm c).map b).eval (x k) = 1) ∧
      cubicCoordinateDenominator x anchor ≠ 0 ∧
      _root_.IsDomain (Localization.Away (cubicCoordinateDenominator x anchor)) ∧
      cubicPolynomialJetMinorDet
        ((p.map b).map (algebraMap Γ(U, ⊤)
          (Localization.Away (cubicCoordinateDenominator x anchor))))
        (cubicCoordinateLocalizedVector x anchor)
        (fun k => anchor (k.castAdd 8)) pivot m ≠ 0 := by
  classical
  obtain ⟨U, hUa, hUint, c, i, a, t, b, f, x, v, anchor, pivot, m,
      hi, hdomain, hb, hf, hx, hfb, ht, hpx, hellx, hfx, hs, hv, hm⟩ :=
    exists_cubicSurfaceElevenPoint_native_affineJet_witness (L := L) p hp hp0
  let s : Fin 11 → L := fun k => (homogeneousLinearForm c).eval₂ (algebraMap K L) (v k)
  have hfx' : ∀ k z, f (x k z) = (s k)⁻¹ * v k z := hfx
  have hd : cubicCoordinateDenominator x anchor ≠ 0 := by
    have h := (cubicCoordinateSpecialization_exists_recover_normalized
      x anchor f v s hs hv hfx').1
    intro hz
    exact h (by rw [hz, map_zero])
  letI : _root_.IsDomain Γ(U, ⊤) := hdomain
  have hlocalizedDomain : _root_.IsDomain
      (Localization.Away (cubicCoordinateDenominator x anchor)) :=
    Localization.Away.isDomain hd
  have hminor : IsUnit (cubicPolynomialJetMinorDet ((p.map b).map f) v
      (fun k => anchor (k.castAdd 8)) pivot m) := by
    rw [MvPolynomial.map_map, hfb]
    exact hm
  exact ⟨U, hUa, hUint, c, i, a, t, b, x, anchor, pivot, m, hi, hdomain, hb, hx, ht,
    hpx, hellx, hd, hlocalizedDomain,
    cubicPolynomialJetMinorDet_localized_ne_zero_of_normalized_specialization
      (p.map b) x anchor pivot m f v s hs hv hfx' hminor⟩

end PfaffianDescent
