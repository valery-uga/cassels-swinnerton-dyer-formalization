import AllCharacteristics.AdjoinRootQuadraticConjugateTangentRationalMap
import PfaffianDescent.CubicLineResidualConjugate

open AlgebraicGeometry CategoryTheory Polynomial
open scoped AlgebraicGeometry

namespace AllCharacteristics
namespace HomogeneousProjective

open PfaffianDescent Module

universe u

theorem rationalMap_of_lineResidual_conjugate_tangent_secant_coordinates_of_charZero
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (xbase : X ⟶ Spec (.of k)) [IsIntegral X]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (c : Cubic k 4) (hc : c.toMvPolynomial = F)
    (φ : CommRingCat.of k ⟶ X.functionField)
    (hφ : Spec.map φ = X.fromSpecStalk _ ≫ xbase)
    (p d : Vec X.functionField 4)
    (hp : (c.map φ.hom).eval p = 0)
    (hdir : (c.map φ.hom).eval d ≠ 0)
    (hirr : Irreducible (Cubic.lineResidualPolynomial (c.map φ.hom) p d))
    (dp : Vec (AdjoinRoot (Cubic.lineResidualPolynomial (c.map φ.hom) p d)) 4)
    (htp : ((c.map φ.hom).map
      (algebraMap X.functionField
        (AdjoinRoot (Cubic.lineResidualPolynomial (c.map φ.hom) p d)))).mixed
      ((fun i => algebraMap X.functionField
        (AdjoinRoot (Cubic.lineResidualPolynomial (c.map φ.hom) p d)) (p i)) +
        (AdjoinRoot.root (Cubic.lineResidualPolynomial (c.map φ.hom) p d)) •
          (fun i => algebraMap X.functionField
            (AdjoinRoot (Cubic.lineResidualPolynomial (c.map φ.hom) p d)) (d i))) dp = 0)
    (hr0 : ∀ (σ : AdjoinRoot (Cubic.lineResidualPolynomial (c.map φ.hom) p d)
        ≃ₐ[X.functionField] AdjoinRoot (Cubic.lineResidualPolynomial (c.map φ.hom) p d)),
      σ ≠ AlgEquiv.refl →
      Cubic.secantResidualPoint ((c.map φ.hom).map
        (algebraMap X.functionField
          (AdjoinRoot (Cubic.lineResidualPolynomial (c.map φ.hom) p d))))
        (Cubic.tangentResidualPoint ((c.map φ.hom).map
          (algebraMap X.functionField
            (AdjoinRoot (Cubic.lineResidualPolynomial (c.map φ.hom) p d))))
          ((fun i => algebraMap X.functionField
            (AdjoinRoot (Cubic.lineResidualPolynomial (c.map φ.hom) p d)) (p i)) +
            (AdjoinRoot.root (Cubic.lineResidualPolynomial (c.map φ.hom) p d)) •
              (fun i => algebraMap X.functionField
                (AdjoinRoot (Cubic.lineResidualPolynomial (c.map φ.hom) p d)) (d i))) dp)
        (Cubic.tangentResidualPoint ((c.map φ.hom).map
          (algebraMap X.functionField
            (AdjoinRoot (Cubic.lineResidualPolynomial (c.map φ.hom) p d))))
          ((fun i => algebraMap X.functionField
            (AdjoinRoot (Cubic.lineResidualPolynomial (c.map φ.hom) p d)) (p i)) +
            (σ (AdjoinRoot.root (Cubic.lineResidualPolynomial (c.map φ.hom) p d))) •
              (fun i => algebraMap X.functionField
                (AdjoinRoot (Cubic.lineResidualPolynomial (c.map φ.hom) p d)) (d i)))
          (fun i => σ (dp i))) ≠ 0) :
    ∃ f : X ⤏ hypersurface F hF,
      f.compHom (hypersurfaceToBase F hF) = xbase.toRationalMap := by
  let K := X.functionField
  let _ : CharZero K := ⟨fun m n hmn => by
    apply Nat.cast_injective (R := k)
    apply φ.hom.injective
    simpa using hmn⟩
  let q := Cubic.lineResidualPolynomial (c.map φ.hom) p d
  let _ : Fact (Irreducible q) := ⟨hirr⟩
  let L := AdjoinRoot q
  let _ : FiniteDimensional K L :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hirr.ne_zero).basis
  let _ : Algebra.IsSeparable K L :=
    adjoinRoot_isSeparable_of_irreducible_separable q hirr hirr.separable
  let _ : IsGalois K L :=
    adjoinRoot_isGalois_of_irreducible_separable_natDegree_two hirr.separable
      (Cubic.lineResidualPolynomial_natDegree_eq_two (c.map φ.hom) p d hdir)
  have hdim : finrank K L = 2 := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
    exact Cubic.lineResidualPolynomial_natDegree_eq_two (c.map φ.hom) p d hdir
  obtain ⟨σ, hσ⟩ := exists_nontrivial_galois_aut_of_finrank_two hdim
  let a : L := AdjoinRoot.root q
  let x : Vec L 4 := (fun i => algebraMap K L (p i)) +
    a • (fun i => algebraMap K L (d i))
  let y : Vec L 4 := (fun i => algebraMap K L (p i)) +
    (σ a) • (fun i => algebraMap K L (d i))
  have ha : Polynomial.eval₂ (algebraMap K L) a q = 0 := by
    change Polynomial.eval₂ (algebraMap K (AdjoinRoot q)) (AdjoinRoot.root q) q = 0
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root q
  have hσa : Polynomial.eval₂ (algebraMap K L) (σ a) q = 0 := by
    change Polynomial.eval₂ (algebraMap K (AdjoinRoot q))
      (σ (AdjoinRoot.root q)) q = 0
    exact Cubic.eval₂_adjoinRoot_root_apply_algEquiv q σ
  have hx : ((c.map φ.hom).map (algebraMap K L)).eval x = 0 := by
    exact Cubic.eval_linePoint_of_lineResidual_root (algebraMap K L)
      (c.map φ.hom) p d hp a ha
  have hy : ((c.map φ.hom).map (algebraMap K L)).eval y = 0 := by
    exact Cubic.eval_linePoint_of_lineResidual_root (algebraMap K L)
      (c.map φ.hom) p d hp (σ a) hσa
  have hxy : (fun i => σ (x i)) = y := by
    exact Cubic.algEquiv_linePoint p d σ a
  have hσsq : σ.trans σ = AlgEquiv.refl :=
    galois_involution_of_finrank_two σ hσ hdim
  have hyx : (fun i => σ (y i)) = x := by
    funext i
    rw [← congrFun hxy i]
    have h := DFunLike.congr_fun hσsq (x i)
    change σ (σ (x i)) = x i at h
    exact h
  have htdq : ((c.map φ.hom).map (algebraMap K L)).mixed y
      (fun i => σ (dp i)) = 0 := by
    have hmix := Cubic.mixed_map σ.toRingHom
      ((c.map φ.hom).map (algebraMap K L)) x dp
    have hfix : ((c.map φ.hom).map (algebraMap K L)).map σ.toRingHom =
        ((c.map φ.hom).map (algebraMap K L)) :=
      cubic_map_algebraMap_fixed_by_algEquiv (c.map φ.hom) σ
    rw [hfix] at hmix
    have hxy' : (fun i => σ.toRingHom (x i)) = y := hxy
    rw [hxy', htp, map_zero] at hmix
    exact hmix
  apply rationalMap_of_adjoinRoot_quadratic_conjugate_tangent_secant_coordinates
    xbase F hF c hc φ hφ q hirr.separable
    (Cubic.lineResidualPolynomial_natDegree_eq_two (c.map φ.hom) p d hdir)
    σ hσ x y dp (fun i => σ (dp i))
  · exact hx
  · exact hy
  · simpa only [x, a, K, L, q] using htp
  · exact htdq
  · exact hxy
  · exact hyx
  · rfl
  · funext i
    have h := DFunLike.congr_fun hσsq (dp i)
    change σ (σ (dp i)) = dp i at h
    exact h
  · simpa only [x, y, a, K, L, q] using hr0 σ hσ

end HomogeneousProjective
end AllCharacteristics
