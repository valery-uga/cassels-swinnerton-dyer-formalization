import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridAffineWitness
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGenericFiniteFibre
import PfaffianDescent.HomogeneousInterpolationFiniteWitness

/-! Actual finite cubic base locus on the generic ordered sixteen-point chart.
The affine chart and its normalized coordinates come from the original
configuration scheme; interpolation and the finite neighborhood are constructed
from the explicit grid specialization. -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_exists_sixteen_grid_generic_finite
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ (U : Scheme.{u}) (_ : IsAffine U) (_ : IsIntegral U)
      (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left)
      (t : Fin 16 → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
        (coordinate (equationIdeal p hp) 0)))))
      (b : K →+* Γ(U, ⊤)) (x : Fin 16 → Fin 4 → Γ(U, ⊤)),
      IsOpenImmersion i ∧ _root_.IsDomain Γ(U, ⊤) ∧
      b = voisinDegreeTenSelectedAvoidance_affineBaseRingMap U
        (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).hom) ∧
      x = (fun k z => pulledLinearChartCoordinate (equationIdeal p hp)
        (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0) U (t k) z) ∧
      (∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
          (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0)
          (by decide : 0 < 1) =
        (i ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 16)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 16 k).left) ∧
      (∀ k, x k 0 = 1) ∧ (∀ k, (p.map b).eval (x k) = 0) ∧
      ∃ (m : Fin 16 ↪ Monomials (Fin 4) 3) (hdet : homogeneousMinorDet m x ≠ 0),
        let S := Localization.Away (homogeneousMinorDet m x)
        letI : IsDomain S := Localization.Away.isDomain hdet
        let g := algebraMap S (FractionRing S)
        let q := homogeneousMinorCorrectedPolynomial m x
          ((voisinDegreeTenSelectedAvoidance_gridCubic K 1).map b)
        let r := homogeneousMinorCorrectedPolynomial m x
          ((voisinDegreeTenSelectedAvoidance_gridCubic K 2).map b)
        (∀ k, (q.map g).eval (fun z => g (algebraMap Γ(U, ⊤) S (x k z))) = 0 ∧
          (r.map g).eval (fun z => g (algebraMap Γ(U, ⊤) S (x k z))) = 0) ∧
        IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
          (((p.map b).map (algebraMap Γ(U, ⊤) S)).map g)
          (q.map g) (r.map g)
          (((hp.map b).map (algebraMap Γ(U, ⊤) S)).map g)
          ((homogeneousMinorCorrectedPolynomial_isHomogeneous m x
            ((voisinDegreeTenSelectedAvoidance_gridCubic K 1).map b)
            ((voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 1).map b)).map g)
          ((homogeneousMinorCorrectedPolynomial_isHomogeneous m x
            ((voisinDegreeTenSelectedAvoidance_gridCubic K 2).map b)
            ((voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 2).map b)).map g))) := by
  classical
  obtain ⟨U, hUa, hUi, i, a, t, b, f, x, hi, hdom, hb, hf, hx,
    hfb, ht, hx0, hpzero, hsurj, hqzero, hrzero, hfinite⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_sixteen_grid_affine_witness (L := L) p hp hno
  letI : IsDomain Γ(U, ⊤) := hdom
  let q := (voisinDegreeTenSelectedAvoidance_gridCubic K 1).map b
  let r := (voisinDegreeTenSelectedAvoidance_gridCubic K 2).map b
  have hq : q.IsHomogeneous 3 :=
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 1).map b
  have hr : r.IsHomogeneous 3 :=
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 2).map b
  letI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      ((p.map b).map f) (q.map f) (r.map f)
      ((hp.map b).map f) (hq.map f) (hr.map f))) := hfinite
  obtain ⟨m, hdet, hzero, V, hη, hV⟩ :=
    cubicMonomialCorrection_exists_genericFiniteNeighborhood_of_finiteWitness
      f x hsurj (p.map b) q r (hp.map b) hq hr hqzero hrzero
  let S := Localization.Away (homogeneousMinorDet m x)
  letI : IsDomain S := Localization.Away.isDomain hdet
  letI := hV
  refine ⟨U, hUa, hUi, i, t, b, x, hi, hdom, hb, hx, ht, hx0, hpzero,
    m, hdet, ?_, ?_⟩
  · intro k
    constructor
    · change ((homogeneousMinorCorrectedPolynomial m x q).map
        (algebraMap S (FractionRing S))).eval
          ((algebraMap S (FractionRing S)) ∘
            (fun z => algebraMap Γ(U, ⊤) S (x k z))) = 0
      rw [← MvPolynomial.map_eval, (hzero k).1, map_zero]
    · change ((homogeneousMinorCorrectedPolynomial m x r).map
        (algebraMap S (FractionRing S))).eval
          ((algebraMap S (FractionRing S)) ∘
            (fun z => algebraMap Γ(U, ⊤) S (x k z))) = 0
      rw [← MvPolynomial.map_eval, (hzero k).2, map_zero]
  · exact voisinDegreeTenSelectedAvoidance_triple_generic_isFinite
      ((p.map b).map (algebraMap Γ(U, ⊤) S))
      (homogeneousMinorCorrectedPolynomial m x q)
      (homogeneousMinorCorrectedPolynomial m x r)
      ((hp.map b).map (algebraMap Γ(U, ⊤) S))
      (homogeneousMinorCorrectedPolynomial_isHomogeneous m x q hq)
      (homogeneousMinorCorrectedPolynomial_isHomogeneous m x r hr) V hη

end PfaffianDescent
