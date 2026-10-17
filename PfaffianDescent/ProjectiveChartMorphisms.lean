import AllCharacteristics.ProjectiveSpaceChartEvaluation
import AllCharacteristics.ProjectiveOverlapLifting
import PfaffianDescent.SchemeAffineFunctions

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K A : Type u} [CommRing K] [CommRing A] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))

/-- Normalized tuples related by an invertible coordinate ratio give equal actual Proj morphisms. -/
theorem projectiveChartSpec_eq_of_ratio (i j : σ)
    (φ : ChartRing I₀ i →+* A) (ψ : ChartRing I₀ j →+* A)
    (hb : φ.comp (chartBaseMap I₀ i) = ψ.comp (chartBaseMap I₀ j))
    (hu : IsUnit (φ (chartCoordinate I₀ i j)))
    (hc : ∀ m, φ (chartCoordinate I₀ i m) =
      φ (chartCoordinate I₀ i j) * ψ (chartCoordinate I₀ j m)) :
    Spec.map (CommRingCat.ofHom φ) ≫ chartι I₀ i =
      Spec.map (CommRingCat.ofHom ψ) ≫ chartι I₀ j := by
  obtain ⟨γ, hγ⟩ := exists_chartOverlap_hom I₀ i j φ hu
  have hr : γ.comp (chartOverlapRightMap I₀ i j) = ψ := by
    apply projectiveChartMap_ext j
    · apply RingHom.ext
      intro r
      change γ (chartOverlapRightMap I₀ i j (chartBaseMap I₀ j r)) = ψ (chartBaseMap I₀ j r)
      exact (congrArg γ ((chartOverlapRightMap_baseMap I₀ i j r).trans
        (chartOverlapLeftMap_baseMap I₀ i j r).symm)).trans
          ((RingHom.congr_fun hγ (chartBaseMap I₀ i r)).trans (RingHom.congr_fun hb r))
    · intro m
      have he := congrArg γ (chartOverlap_coordinate_relation I₀ i j m)
      have hj : γ (↑((chartOverlapUnit I₀ i j)⁻¹)) = φ (chartCoordinate I₀ i j) :=
        (congrArg γ (chartOverlapUnit_inv I₀ i j)).trans
          (RingHom.congr_fun hγ (chartCoordinate I₀ i j))
      rw [map_mul, hj] at he
      have he' : φ (chartCoordinate I₀ i m) =
          φ (chartCoordinate I₀ i j) * γ (chartOverlapRightMap I₀ i j (chartCoordinate I₀ j m)) :=
        (RingHom.congr_fun hγ (chartCoordinate I₀ i m)).symm.trans he
      exact hu.mul_left_cancel (he'.symm.trans (hc m))
  have hl : Spec.map (CommRingCat.ofHom γ) ≫ Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I₀ i j)) =
      Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hγ]
  have hr' : Spec.map (CommRingCat.ofHom γ) ≫ Spec.map (CommRingCat.ofHom (chartOverlapRightMap I₀ i j)) =
      Spec.map (CommRingCat.ofHom ψ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hr]
  exact (congrArg (fun f => f ≫ chartι I₀ i) hl.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => Spec.map (CommRingCat.ofHom γ) ≫ f) (isPullback_chartOverlap I₀ i j).w).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ chartι I₀ j) hr'))))

/-- The normalized-coordinate comparison also holds on arbitrary test schemes. -/
theorem projectiveChartMorphisms_eq_of_ratio {X : Scheme.{u}} (i j : σ)
    (f : X ⟶ Spec (.of (ChartRing I₀ i))) (g : X ⟶ Spec (.of (ChartRing I₀ j)))
    (hb : (affineFunctionHom f).comp (chartBaseMap I₀ i) =
      (affineFunctionHom g).comp (chartBaseMap I₀ j))
    (hu : IsUnit (affineFunctionHom f (chartCoordinate I₀ i j)))
    (hc : ∀ m, affineFunctionHom f (chartCoordinate I₀ i m) =
      affineFunctionHom f (chartCoordinate I₀ i j) * affineFunctionHom g (chartCoordinate I₀ j m)) :
    f ≫ chartι I₀ i = g ≫ chartι I₀ j := by
  have h := projectiveChartSpec_eq_of_ratio i j (affineFunctionHom f) (affineFunctionHom g) hb hu hc
  exact (congrArg (fun q => q ≫ chartι I₀ i) (from_affineFunctionHom f).symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (fun q => X.toSpecΓ ≫ q) h).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun q => q ≫ chartι I₀ j) (from_affineFunctionHom g)))))

/-- The normalized-coordinate comparison works for charts of an arbitrary
homogeneous projective quotient, not only for projective space. -/
theorem projectiveQuotientChartSpec_eq_of_ratio
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) (i j : σ)
    (φ : ChartRing I i →+* A) (ψ : ChartRing I j →+* A)
    (hb : φ.comp (chartBaseMap I i) = ψ.comp (chartBaseMap I j))
    (hu : IsUnit (φ (chartCoordinate I i j)))
    (hc : ∀ m, φ (chartCoordinate I i m) =
      φ (chartCoordinate I i j) * ψ (chartCoordinate I j m)) :
    Spec.map (CommRingCat.ofHom φ) ≫ chartι I i =
      Spec.map (CommRingCat.ofHom ψ) ≫ chartι I j := by
  obtain ⟨γ, hγ⟩ := exists_chartOverlap_hom I i j φ hu
  have hr : γ.comp (chartOverlapRightMap I i j) = ψ := by
    let e := MvPolynomial.eval₂Hom (chartBaseMap I j) (chartCoordinate I j)
    have he : (γ.comp (chartOverlapRightMap I i j)).comp e = ψ.comp e := by
      apply MvPolynomial.ringHom_ext
      · intro r
        have hbase : γ (chartOverlapRightMap I i j (chartBaseMap I j r)) =
            ψ (chartBaseMap I j r) := (congrArg γ ((chartOverlapRightMap_baseMap I i j r).trans
          (chartOverlapLeftMap_baseMap I i j r).symm)).trans
            ((RingHom.congr_fun hγ (chartBaseMap I i r)).trans (RingHom.congr_fun hb r))
        simpa [e] using hbase
      · intro m
        have htransition := congrArg γ (chartOverlap_coordinate_relation I i j m)
        have hj : γ (↑((chartOverlapUnit I i j)⁻¹)) = φ (chartCoordinate I i j) :=
          (congrArg γ (chartOverlapUnit_inv I i j)).trans
            (RingHom.congr_fun hγ (chartCoordinate I i j))
        rw [map_mul, hj] at htransition
        have h' : φ (chartCoordinate I i m) =
            φ (chartCoordinate I i j) * γ (chartOverlapRightMap I i j (chartCoordinate I j m)) :=
          (RingHom.congr_fun hγ (chartCoordinate I i m)).symm.trans htransition
        have hcoordinate : γ (chartOverlapRightMap I i j (chartCoordinate I j m)) =
            ψ (chartCoordinate I j m) := hu.mul_left_cancel (h'.symm.trans (hc m))
        simpa [e] using hcoordinate
    apply RingHom.ext
    intro x
    obtain ⟨p, rfl⟩ := eval₂_chartCoordinate_surjective I j x
    exact DFunLike.congr_fun he p
  have hl : Spec.map (CommRingCat.ofHom γ) ≫
      Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I i j)) =
      Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hγ]
  have hr' : Spec.map (CommRingCat.ofHom γ) ≫
      Spec.map (CommRingCat.ofHom (chartOverlapRightMap I i j)) =
      Spec.map (CommRingCat.ofHom ψ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hr]
  exact (congrArg (fun f => f ≫ chartι I i) hl.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => Spec.map (CommRingCat.ofHom γ) ≫ f)
        (isPullback_chartOverlap I i j).w).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ chartι I j) hr'))))

end
end PfaffianDescent
