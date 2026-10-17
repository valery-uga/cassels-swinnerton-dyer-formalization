import PfaffianDescent.QuadraticSkewActualMatchingInverseDomainRingEquivalence
import Mathlib.AlgebraicGeometry.Birational.Birational
/-! SOURCE ONLY / UNVERIFIED. Genuine dense-open isomorphism and
BirationalOver endpoint for the SAME original smooth cubic. The original
geometric caller internally constructs both ring inverses; no rationality,
birationality, dense-open isomorphism, or coordinate-reconstruction
certificate occurs among its premises. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.SecondComposite005
open MvPolynomial Module AlgebraicGeometry CategoryTheory QuarticNet
open AllCharacteristics.HomogeneousProjective InverseChart ForwardChart004
open scoped AlgebraicGeometry
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k K : Type u} [Field k] [Field K] [Algebra k K]

def originalInverseDomainChartι
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (R : PlaneIndex → MvPolynomial (Fin 4) k) (hR : ∀ i, (R i).IsHomogeneous 2)
    (N : PlanePolynomial k) :
    Spec (.of (Localization.Away
      (inverseCoordinateRingHom (equationIdeal F hF) Q hQ R hR N))) ⟶ hypersurface F hF :=
  Spec.map (CommRingCat.ofHom (algebraMap (QuadraticChartRing (equationIdeal F hF) Q)
    (Localization.Away (inverseCoordinateRingHom (equationIdeal F hF) Q hQ R hR N)))) ≫
      quadraticChartι (equationIdeal F hF) Q hQ

instance originalInverseDomainChartι_isOpenImmersion
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (R : PlaneIndex → MvPolynomial (Fin 4) k) (hR : ∀ i, (R i).IsHomogeneous 2)
    (N : PlanePolynomial k) : IsOpenImmersion (originalInverseDomainChartι F hF Q hQ R hR N) := by
  let H := QuadraticChartRing (equationIdeal F hF) Q
  let θ := inverseCoordinateRingHom (equationIdeal F hF) Q hQ R hR
  let T := Localization.Away (θ N)
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap H T))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of H) (θ N)
  letI : IsOpenImmersion (quadraticChartι (equationIdeal F hF) Q hQ) :=
    quadraticChartι_isOpenImmersion (equationIdeal F hF) Q hQ
  exact IsOpenImmersion.comp (Spec.map (CommRingCat.ofHom (algebraMap H T)))
    (quadraticChartι (equationIdeal F hF) Q hQ)

theorem principalPlaneι_toBase (N : PlanePolynomial k) :
    principalPlaneι N ≫ (AffineSpace PlaneIndex (Spec (.of k)) ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (PlaneLocalization N))) := by
  unfold principalPlaneι
  rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((algebraMap (PlanePolynomial k) (PlaneLocalization N)).comp
      (algebraMap k (PlanePolynomial k)))) = _
  rw [← IsScalarTower.algebraMap_eq]

/-- General geometry assembly from the constructed coordinate-ring
equivalence. This helper is used below with a ring equivalence constructed
internally from the original cubic and exchanged skew-line projector. -/
theorem original_inverse_domain_ring_equivalence_gives_partial_iso
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (R : PlaneIndex → MvPolynomial (Fin 4) k) (hR : ∀ i, (R i).IsHomogeneous 2)
    (N : PlanePolynomial k) (hN : N ≠ 0)
    (e : PlaneLocalization N ≃+* Localization.Away
      (inverseCoordinateRingHom (equationIdeal F hF) Q hQ R hR N))
    (he : e.toRingHom = inverseLocalizationHom N
      (inverseCoordinateRingHom (equationIdeal F hF) Q hQ R hR)) :
    ∃ p : (hypersurface F hF).PartialIso (AffineSpace PlaneIndex (Spec (.of k))),
      p.IsOver (hypersurfaceToBase F hF)
        (AffineSpace PlaneIndex (Spec (.of k)) ↘ Spec (.of k)) := by
  let H := QuadraticChartRing (equationIdeal F hF) Q
  let θ := inverseCoordinateRingHom (equationIdeal F hF) Q hQ R hR
  let S := PlaneLocalization N
  let T := Localization.Away (θ N)
  let b : k →+* T := (algebraMap H T).comp (quadraticChartBaseMap (equationIdeal F hF) Q)
  let j := originalInverseDomainChartι F hF Q hQ R hR N
  have hjbase : j ≫ hypersurfaceToBase F hF = Spec.map (CommRingCat.ofHom b) := by
    change (Spec.map (CommRingCat.ofHom (algebraMap H T)) ≫
      quadraticChartι (equationIdeal F hF) Q hQ) ≫ toBase (equationIdeal F hF) = _
    rw [Category.assoc, quadraticChartι_toBase, ← Spec.map_comp]
    rfl
  have hebase : e.toRingHom.comp (algebraMap k S) = b := by
    ext a
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (PlanePolynomial k) S]
    change e.toRingHom (algebraMap (PlanePolynomial k) S (MvPolynomial.C a)) = _
    rw [he, inverseLocalizationHom_base]
    change algebraMap H T (θ (MvPolynomial.C a)) =
      algebraMap H T (quadraticChartBaseMap (equationIdeal F hF) Q a)
    congr 1
    exact MvPolynomial.eval₂Hom_C _ _ a
  have heinvbase : e.symm.toRingHom.comp b = algebraMap k S := by
    ext a
    change e.symm (b a) = algebraMap k S a
    exact (congrArg e.symm (RingHom.congr_fun hebase a).symm).trans
      (e.symm_apply_apply (algebraMap k S a))
  let q := Scheme.Spec.mapIso e.toCommRingCatIso.symm.op
  let g : Spec (.of S) ⟶ hypersurface F hF := q.hom ≫ j
  letI : IsOpenImmersion g := by dsimp [g]; infer_instance
  have hgbase : g ≫ hypersurfaceToBase F hF = Spec.map (CommRingCat.ofHom (algebraMap k S)) := by
    change (q.hom ≫ j) ≫ hypersurfaceToBase F hF = _
    rw [Category.assoc, hjbase]
    change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom b) = _
    rw [← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) heinvbase
  letI : Nonempty (Spec (.of S)) := principalPlane_nonempty N hN
  letI : Nonempty (hypersurface F hF) := Nonempty.map g inferInstance
  letI : IsIntegral (hypersurface F hF) :=
    isIntegral_hypersurface_of_smooth_of_principalIdeal_prime F hF
      (principalIdeal_prime_of_smooth_homogeneous_cubic F hF hF₀)
  have hgDense : Dense (g.opensRange : Set (hypersurface F hF)) := by
    apply g.opensRange.isOpen.dense
    obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (.of S)))
    exact ⟨g z, z, rfl⟩
  letI : IsDominant g := ⟨hgDense⟩
  let a := principalPlaneι N
  have haDense : Dense (a.opensRange : Set (AffineSpace PlaneIndex (Spec (.of k)))) := by
    rw [principalPlaneι_opensRange]
    exact principalPlaneOpen_dense N hN
  letI : IsDominant a := ⟨haDense⟩
  have hgOver := g.birationalOver (hypersurfaceToBase F hF)
    (Spec.map (CommRingCat.ofHom (algebraMap k S))) hgbase
  have haOver := a.birationalOver (AffineSpace PlaneIndex (Spec (.of k)) ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k S))) (principalPlaneι_toBase N)
  exact hgOver.symm.trans haOver

/-- Genuine original-input dense-open isomorphism. The actual frame,
residual, inverse functions, injective field evaluation, and both inverse
identities are constructed internally in the preceding source modules. -/
theorem actual_matching_exists_original_plane_partial_iso
    (E : IntermediateField k K) [FiniteDimensional k E] [IsGalois k E]
    (h₂ : finrank k E = 2)
    (P : Matrix (Fin 4) (Fin 4) E) (B : Basis (Fin 4) K (Fin 4 → K))
    (hP : P.map E.val.toRingHom = matchingEdgeProjectorMatrix B)
    (σ : E ≃ₐ[k] E) (hσ : σ ≠ AlgEquiv.refl)
    (hExchange : P.map σ.toRingHom = 1 - P)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (hLines : MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal P).toIdeal ∧
      MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal (1 - P)).toIdeal) :
    ∃ p : (hypersurface F hF).PartialIso (AffineSpace PlaneIndex (Spec (.of k))),
      p.IsOver (hypersurfaceToBase F hF)
        (AffineSpace PlaneIndex (Spec (.of k)) ↘ Spec (.of k)) := by
  obtain ⟨Q, hQ, R, hR, N, hN, e, he⟩ :=
    actual_matching_exists_inverse_domain_ring_equivalence E h₂ P B hP σ hσ hExchange F hF hF₀ hLines
  exact original_inverse_domain_ring_equivalence_gives_partial_iso F hF hF₀ Q hQ R hR N hN e he

theorem actual_matching_original_cubic_birationalOver_plane
    (E : IntermediateField k K) [FiniteDimensional k E] [IsGalois k E]
    (h₂ : finrank k E = 2)
    (P : Matrix (Fin 4) (Fin 4) E) (B : Basis (Fin 4) K (Fin 4 → K))
    (hP : P.map E.val.toRingHom = matchingEdgeProjectorMatrix B)
    (σ : E ≃ₐ[k] E) (hσ : σ ≠ AlgEquiv.refl)
    (hExchange : P.map σ.toRingHom = 1 - P)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (hLines : MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal P).toIdeal ∧
      MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal (1 - P)).toIdeal) :
    Scheme.BirationalOver (hypersurfaceToBase F hF)
      (AffineSpace PlaneIndex (Spec (.of k)) ↘ Spec (.of k)) :=
  actual_matching_exists_original_plane_partial_iso E h₂ P B hP σ hσ hExchange F hF hF₀ hLines

theorem actual_matching_original_cubic_isRationalOver
    (E : IntermediateField k K) [FiniteDimensional k E] [IsGalois k E]
    (h₂ : finrank k E = 2)
    (P : Matrix (Fin 4) (Fin 4) E) (B : Basis (Fin 4) K (Fin 4 → K))
    (hP : P.map E.val.toRingHom = matchingEdgeProjectorMatrix B)
    (σ : E ≃ₐ[k] E) (hσ : σ ≠ AlgEquiv.refl)
    (hExchange : P.map σ.toRingHom = 1 - P)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (hLines : MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal P).toIdeal ∧
      MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal (1 - P)).toIdeal) :
    Scheme.IsRationalOver (hypersurfaceToBase F hF) := by
  exact ⟨PlaneIndex,
    actual_matching_original_cubic_birationalOver_plane E h₂ P B hP σ hσ hExchange F hF hF₀ hLines⟩

end PfaffianDescent.QuadraticSkewRationality.SecondComposite005
