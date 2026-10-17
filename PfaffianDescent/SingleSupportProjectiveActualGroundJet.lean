import PfaffianDescent.SingleSupportProjectiveCoordinates
import PfaffianDescent.HomogeneousVanishingLinearSystem

/-! Actual ground tangent coordinates of EVERY supplied rank-eight scheme
supported at a separable quartic closed point. The algebra, support, residue,
chart, nonzero tangent, and entire evaluation kernel belong to that SAME Z. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- No public local-algebra, residue, coordinate, or covariance certificate
is needed for the actual ground jet of the supplied scheme. -/
theorem singleSupport_projective_actual_ground_jet
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (P : closedPoints (scheme I))
    (hSupport : Set.range i = {P.1})
    (hP : (toBase I).residueDegree P.1 = 4)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 8) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    letI := AllCharacteristics.pointAlgebra (toBase I) P.1
    ∃ j : Fin 4, ∃ (g : ChartRing I j →+* Γ(Z, ⊤))
      (x : Fin 4 → Γ(Z, ⊤))
      (e : Γ(Z, ⊤) ≃ₐ[k] DualNumber ((scheme I).residueField P.1))
      (p v : Fin 4 → (scheme I).residueField P.1),
      x j = 1 ∧ p j = 1 ∧ v j = 0 ∧ v ≠ 0 ∧
      Function.Surjective (aeval x) ∧
      (∀ r, x r = g (chartCoordinate I j r)) ∧
      e.toAlgHom.comp (aeval x) =
        aeval (fun r => TrivSqZeroExt.inl (p r) + TrivSqZeroExt.inr (v r)) ∧
      (∀ r, p r = singleClosedSupportResidueAlgHom i (toBase I) P hSupport (x r)) ∧
      (∀ q ∈ I.toIdeal, aeval x q = 0) ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι I j = Z.isoSpec.inv ≫ i := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := AllCharacteristics.pointAlgebra (toBase I) P.1
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  letI := AllCharacteristics.closedPoint_moduleFinite (toBase I) P
  letI : IsLocalRing Γ(Z, ⊤) := singleSupport_globalSections_isLocalRing i P.1 hSupport
  let rho := singleClosedSupportResidueAlgHom i (toBase I) P hSupport
  have hrho : Function.Surjective rho :=
    singleClosedSupportResidueAlgHom_surjective i (toBase I) P hSupport
  have hL : finrank k ((scheme I).residueField P.1) = 4 :=
    (AllCharacteristics.closedPoint_finrank_eq_residueDegree (toBase I) P).trans hP
  have hA : finrank k Γ(Z, ⊤) = 8 :=
    (finiteSchemeCoefficient_finrank (i ≫ toBase I)).trans hZ
  obtain ⟨e0, he0⟩ := lengthEightLocal_quarticResidue_dual_equiv_with_residue rho hrho hL hA
  let e := e0.symm
  obtain ⟨j, g, x, hxj, hxs, hxg, hxI, hpoint⟩ :=
    singleSupport_projective_generating_coordinates I i P hSupport
  let p : Fin 4 → (scheme I).residueField P.1 := fun r => (e (x r)).fst
  let v : Fin 4 → (scheme I).residueField P.1 := fun r => (e (x r)).snd
  let phi := e.toAlgHom.comp (aeval x)
  have hjet : phi = aeval (fun r => TrivSqZeroExt.inl (p r) + TrivSqZeroExt.inr (v r)) := by
    apply MvPolynomial.algHom_ext
    intro r
    simp only [phi, AlgHom.comp_apply, aeval_X]
    apply TrivSqZeroExt.ext <;> simp [p, v]
  have hpj : p j = 1 := by simp [p, hxj]
  have hvj : v j = 0 := by simp [v, hxj]
  have hv : v ≠ 0 := by
    intro hv0
    have hsnd (r : Fin 4) : (e (x r)).snd = 0 := congrFun hv0 r
    have hconstant : phi =
        (TrivSqZeroExt.inlAlgHom k ((scheme I).residueField P.1)
          ((scheme I).residueField P.1)).comp (aeval p) := by
      apply MvPolynomial.algHom_ext
      intro r
      simp only [phi, AlgHom.comp_apply, aeval_X]
      apply TrivSqZeroExt.ext <;> simp [p, hsnd]
    have hsurj : Function.Surjective phi := e.surjective.comp hxs
    obtain ⟨q, hq⟩ := hsurj (TrivSqZeroExt.inr (1 : (scheme I).residueField P.1))
    rw [hconstant] at hq
    have h := congrArg TrivSqZeroExt.snd hq
    exact zero_ne_one (by simpa using h)
  refine ⟨j, g, x, e, p, v, hxj, hpj, hvj, hv, hxs, hxg, hjet, ?_, hxI, hpoint⟩
  intro r
  have h := he0 (e (x r))
  simpa [p, e] using h.symm

/-- Evaluation through an actual algebra equivalence preserves the entire
nilpotent-sensitive homogeneous restriction kernel, including its dimension. -/
theorem homogeneous_kernel_transport_actual_algebra_equiv
    {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [FiniteDimensional k A] [FiniteDimensional k B]
    (e : A ≃ₐ[k] B) (x : Fin 4 → A) (d : ℕ) :
    homogeneousVanishingPolynomialSubmodule x d =
      homogeneousVanishingPolynomialSubmodule (fun r => e (x r)) d := by
  ext q
  rw [mem_homogeneousVanishingPolynomialSubmodule_iff,
    mem_homogeneousVanishingPolynomialSubmodule_iff]
  have heval : aeval (fun r => e (x r)) q = e (aeval x q) :=
    (comp_aeval_apply x e.toAlgHom q).symm
  change (q.IsHomogeneous d ∧ aeval x q = 0) ↔
    (q.IsHomogeneous d ∧ aeval (fun r => e (x r)) q = 0)
  have hz : e (aeval x q) = 0 ↔ aeval x q = 0 :=
    ⟨fun h => e.injective (by simpa using h), fun h => by simp [h]⟩
  rw [heval, hz]

end PfaffianDescent
